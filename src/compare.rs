//! Compare two exports up to id numbering, record order and binders.
//!
//! lean4export shares subterms by Lean's `BEq`, which ignores binders, so where two
//! alpha-equivalent terms meet it may write either's binders. Both streams are hash-consed
//! into one table, so equal terms get equal ids on either side and a declaration compares
//! by `==` in time linear in its DAG, never its tree.

use crate::{
    blean,
    env::escape,
    error::{corrupt, Result},
    ndjson,
    record::{Decl, Head, IndCtor, IndRec, IndRule, IndType, Record, Sink, Table},
};
use hashbrown::{hash_table::Entry, HashTable};
use parking_lot::Mutex;
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};
use std::{cell::Cell, hash::BuildHasher, mem, thread};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Key {
    Anon,
    Zero,
    NameStr(u32, Box<str>),
    NameNum(u32, u64),
    Succ(u32),
    Max(u32, u32),
    IMax(u32, u32),
    Param(u32),
    BVar(u64),
    Sort(u32),
    Const(u32, Box<[u32]>),
    App(u32, u32),
    Lam(u32, u32),
    Pi(u32, u32),
    Let(u32, u32, u32, bool),
    Nat(Box<str>),
    Str(Box<str>),
    Proj(u32, u64, u32),
}

const SHARDS: usize = 256;

#[derive(Debug, Default)]
struct Shard {
    nodes: Vec<Key>,
    index: HashTable<u32>,
}

/// The shared table, sharded so both streams can intern at once. Node `i` lives in shard
/// `i % SHARDS`.
#[derive(Debug)]
struct Canon(Vec<Mutex<Shard>>);

impl Canon {
    fn new() -> Self {
        Self((0..SHARDS).map(|_| Mutex::default()).collect())
    }

    fn intern(&self, k: Key) -> u32 {
        let h = FxBuildHasher.hash_one(&k);
        let s = (h.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> 56) as usize % SHARDS;
        let mut shard = self.0[s].lock();
        let Shard { nodes, index } = &mut *shard;
        let local = match index.entry(
            h,
            |&i| nodes[i as usize] == k,
            |&i| FxBuildHasher.hash_one(&nodes[i as usize]),
        ) {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(e) => {
                let i = u32::try_from(nodes.len()).expect("table overflow");
                nodes.push(k);
                e.insert(i);
                i
            }
        };
        drop(shard);
        u32::try_from(local as usize * SHARDS + s).expect("table overflow")
    }

    fn get(&self, n: u32) -> Key {
        let n = n as usize;
        self.0[n % SHARDS].lock().nodes[n / SHARDS].clone()
    }

    fn name(&self, n: u32) -> String {
        let join = |p: u32, s: &str| match self.get(p) {
            Key::Anon => s.to_string(),
            _ => format!("{}.{s}", self.name(p)),
        };
        match self.get(n) {
            Key::NameStr(p, s) => join(p, &escape(&s)),
            Key::NameNum(p, i) => join(p, &i.to_string()),
            _ => String::new(),
        }
    }
}

/// One stream's ids mapped into the shared table, and its declarations by first name.
struct Side<'c> {
    canon: &'c Canon,
    names: Vec<u32>,
    levels: Vec<u32>,
    exprs: Vec<u32>,
    decls: FxHashMap<u32, Decl>,
    dups: Vec<u32>,
    count: usize,
    /// The first reference to an id not yet defined, if any.
    dangling: Cell<Option<u32>>,
}

impl<'c> Side<'c> {
    fn new(canon: &'c Canon) -> Self {
        let names = vec![canon.intern(Key::Anon)];
        let levels = vec![canon.intern(Key::Zero)];
        Self {
            canon,
            names,
            levels,
            exprs: Vec::new(),
            decls: FxHashMap::default(),
            dups: Vec::new(),
            count: 0,
            dangling: Cell::new(None),
        }
    }

    fn id(&self, table: &[u32], i: u32) -> u32 {
        table.get(i as usize).copied().unwrap_or_else(|| {
            self.dangling.set(self.dangling.get().or(Some(i)));
            0
        })
    }

    fn n(&self, i: u32) -> u32 {
        self.id(&self.names, i)
    }

    fn ns(&self, is: &[u32]) -> Vec<u32> {
        is.iter().map(|&i| self.n(i)).collect()
    }

    fn l(&self, i: u32) -> u32 {
        self.id(&self.levels, i)
    }

    fn e(&self, i: u32) -> u32 {
        self.id(&self.exprs, i)
    }

    fn head(&self, h: &Head) -> Head {
        Head {
            name: self.n(h.name),
            level_params: self.ns(&h.level_params),
            ty: self.e(h.ty),
        }
    }

    /// `d` over shared ids, with what lean4export may vary dropped: the `all` of axioms
    /// and opaques and the inductive flags, which only some versions write, and the order of
    /// a block's recursors.
    fn decl(&self, d: &Decl) -> Decl {
        match d {
            Decl::Axiom {
                head, is_unsafe, ..
            } => Decl::Axiom {
                head: self.head(head),
                is_unsafe: *is_unsafe,
                all: None,
            },
            Decl::Def {
                head,
                value,
                hints,
                safety,
                all,
            } => Decl::Def {
                head: self.head(head),
                value: self.e(*value),
                hints: *hints,
                safety: *safety,
                all: self.ns(all),
            },
            Decl::Thm { head, value, all } => Decl::Thm {
                head: self.head(head),
                value: self.e(*value),
                all: self.ns(all),
            },
            Decl::Opaque {
                head,
                value,
                is_unsafe,
                ..
            } => Decl::Opaque {
                head: self.head(head),
                value: self.e(*value),
                is_unsafe: *is_unsafe,
                all: None,
            },
            Decl::Quot { head, kind } => Decl::Quot {
                head: self.head(head),
                kind: *kind,
            },
            Decl::Inductive { types, ctors, recs } => {
                let mut recs: Vec<IndRec> = recs
                    .iter()
                    .map(|r| IndRec {
                        head: self.head(&r.head),
                        all: self.ns(&r.all),
                        rules: r
                            .rules
                            .iter()
                            .map(|u| IndRule {
                                ctor: self.n(u.ctor),
                                nfields: u.nfields,
                                rhs: self.e(u.rhs),
                            })
                            .collect(),
                        ..r.clone()
                    })
                    .collect();
                recs.sort_by_key(|r| r.head.name);
                Decl::Inductive {
                    types: types
                        .iter()
                        .map(|t| IndType {
                            head: self.head(&t.head),
                            all: self.ns(&t.all),
                            ctors: self.ns(&t.ctors),
                            flags: None,
                            ..t.clone()
                        })
                        .collect(),
                    ctors: ctors
                        .iter()
                        .map(|c| IndCtor {
                            head: self.head(&c.head),
                            induct: self.n(c.induct),
                            ..c.clone()
                        })
                        .collect(),
                    recs,
                }
            }
        }
    }
}

impl Side<'_> {
    fn check(&self) -> Result<()> {
        self.dangling.get().map_or(Ok(()), |i| {
            Err(corrupt(format!("reference to undefined id {i}")))
        })
    }
}

impl Sink for &mut Side<'_> {
    type Output = ();

    fn record(&mut self, _: Option<u32>, r: &Record<'_>) -> Result<()> {
        let key = match r {
            Record::Meta(_) | Record::End(_) => return Ok(()),
            Record::Decl(d) => {
                let d = self.decl(d);
                let k = first(&d);
                self.count += 1;
                if self.decls.insert(k, d).is_some() {
                    self.dups.push(k);
                }
                return self.check();
            }
            Record::NameStr { pre, str } => Key::NameStr(self.n(*pre), (**str).into()),
            Record::NameNum { pre, i } => Key::NameNum(self.n(*pre), *i),
            Record::Succ(l) => Key::Succ(self.l(*l)),
            Record::Max(a, b) => Key::Max(self.l(*a), self.l(*b)),
            Record::IMax(a, b) => Key::IMax(self.l(*a), self.l(*b)),
            Record::Param(n) => Key::Param(self.n(*n)),
            Record::BVar(i) => Key::BVar(*i),
            Record::Sort(l) => Key::Sort(self.l(*l)),
            Record::Const { name, us } => {
                Key::Const(self.n(*name), us.iter().map(|&u| self.l(u)).collect())
            }
            Record::App { fun, arg } => Key::App(self.e(*fun), self.e(*arg)),
            Record::Lam(b) => Key::Lam(self.e(b.ty), self.e(b.body)),
            Record::Pi(b) => Key::Pi(self.e(b.ty), self.e(b.body)),
            Record::Let {
                ty,
                value,
                body,
                nondep,
                ..
            } => Key::Let(self.e(*ty), self.e(*value), self.e(*body), *nondep),
            Record::Nat(s) => Key::Nat((**s).into()),
            Record::Str(s) => Key::Str((**s).into()),
            Record::Proj {
                type_name,
                idx,
                struct_,
            } => Key::Proj(self.n(*type_name), *idx, self.e(*struct_)),
            // lean4export's kernels read mdata as the term it wraps, and so does the exporter
            Record::MData(e) => {
                let id = self.e(*e);
                self.exprs.push(id);
                return self.check();
            }
        };
        let table = r.table();
        let id = self.canon.intern(key);
        match table {
            Some(Table::Names) => self.names.push(id),
            Some(Table::Levels) => self.levels.push(id),
            _ => self.exprs.push(id),
        }
        self.check()
    }

    fn finish(self) -> Result<()> {
        Ok(())
    }
}

fn first(d: &Decl) -> u32 {
    match d {
        Decl::Axiom { head, .. }
        | Decl::Def { head, .. }
        | Decl::Thm { head, .. }
        | Decl::Opaque { head, .. }
        | Decl::Quot { head, .. } => head.name,
        Decl::Inductive { types, .. } => types.first().map_or(0, |t| t.head.name),
    }
}

/// Which part of two declarations under one name first differs.
fn what(a: &Decl, b: &Decl) -> &'static str {
    let parts = |d: &Decl| match d {
        Decl::Axiom { head, .. } | Decl::Quot { head, .. } => Some((head.clone(), None)),
        Decl::Def { head, value, .. }
        | Decl::Thm { head, value, .. }
        | Decl::Opaque { head, value, .. } => Some((head.clone(), Some(*value))),
        Decl::Inductive { .. } => None,
    };
    if mem::discriminant(a) != mem::discriminant(b) {
        return "kind";
    }
    match (parts(a), parts(b)) {
        (Some((x, _)), Some((y, _))) if x.level_params != y.level_params => "level params",
        (Some((x, _)), Some((y, _))) if x.ty != y.ty => "type",
        (Some((_, v)), Some((_, w))) if v != w => "value",
        (None, None) => "inductive block",
        _ => "attributes",
    }
}

/// How two exports differ, every list sorted by name.
#[derive(Debug, Default)]
pub struct Diff {
    pub decls: (usize, usize),
    pub only_a: Vec<String>,
    pub only_b: Vec<String>,
    pub differ: Vec<(String, &'static str)>,
    pub dups: (Vec<String>, Vec<String>),
}

impl Diff {
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.only_a.is_empty()
            && self.only_b.is_empty()
            && self.differ.is_empty()
            && self.dups.0.is_empty()
            && self.dups.1.is_empty()
    }
}

type Loaded = (FxHashMap<u32, Decl>, usize, Vec<u32>);

fn load_both(canon: &Canon, a: &[u8], b: &[u8]) -> Result<(Loaded, Loaded)> {
    let side = |bytes: &[u8]| {
        let mut s = Side::new(canon);
        if blean::sniff(bytes) {
            blean::read(bytes, &mut s)?;
        } else {
            ndjson::read(bytes, &mut s)?;
        }
        Ok::<_, crate::Error>((s.decls, s.count, s.dups))
    };
    let (ra, rb) = thread::scope(|t| {
        let a = t.spawn(|| side(a));
        let b = side(b);
        (a.join().expect("compare thread panicked"), b)
    });
    Ok((ra?, rb?))
}

fn sorted(canon: &Canon, ks: impl Iterator<Item = u32>) -> Vec<String> {
    let mut v: Vec<String> = ks.map(|k| canon.name(k)).collect();
    v.sort_unstable();
    v
}

/// Compare two exports, each NDJSON or blean.
pub fn compare(a: &[u8], b: &[u8]) -> Result<Diff> {
    let canon = Canon::new();
    let ((da, ca, pa), (db, cb, pb)) = load_both(&canon, a, b)?;
    let mut differ: Vec<_> = da
        .iter()
        .filter_map(|(k, x)| {
            let y = db.get(k)?;
            (x != y).then(|| (canon.name(*k), what(x, y)))
        })
        .collect();
    differ.sort_unstable();
    Ok(Diff {
        decls: (ca, cb),
        only_a: sorted(&canon, da.keys().copied().filter(|k| !db.contains_key(k))),
        only_b: sorted(&canon, db.keys().copied().filter(|k| !da.contains_key(k))),
        differ,
        dups: (
            sorted(&canon, pa.into_iter()),
            sorted(&canon, pb.into_iter()),
        ),
    })
}

/// Whether a target states the same thing in both exports.
#[derive(Debug, PartialEq, Eq)]
pub enum Verdict {
    /// Its statement cone is stated alike in both.
    Kept,
    /// These declarations in its statement cone are stated differently or missing in `b`.
    Changed(Vec<String>),
    /// Not in `a`.
    Missing,
}

/// How two builds of a cone differ, statements apart from proofs. Every list is sorted.
#[derive(Debug, Default)]
pub struct Drift {
    pub decls: (usize, usize),
    pub same: usize,
    /// Stated alike, proved differently.
    pub proofs: Vec<String>,
    /// Stated differently, with what differs first.
    pub statements: Vec<(String, &'static str)>,
    /// Names only in `a` and only in `b` whose declarations are alike but for the name.
    pub renamed: Vec<(String, String)>,
    pub removed: Vec<String>,
    pub added: Vec<String>,
    pub targets: Vec<(String, Verdict)>,
}

const PROOF: u32 = u32::MAX;

/// `d` with the values of theorems and opaques left out, which nothing else can unfold.
fn stated(d: &Decl) -> Decl {
    let mut d = d.clone();
    if let Decl::Thm { value, .. } | Decl::Opaque { value, .. } = &mut d {
        *value = PROOF;
    }
    d
}

/// The statement of a declaration other than an inductive, without its name.
fn shape(d: &Decl) -> Option<Decl> {
    let mut d = stated(d);
    match &mut d {
        Decl::Inductive { .. } => return None,
        Decl::Def { head, all, .. } | Decl::Thm { head, all, .. } => {
            head.name = PROOF;
            all.clear();
        }
        Decl::Axiom { head, .. } | Decl::Opaque { head, .. } | Decl::Quot { head, .. } => {
            head.name = PROOF;
        }
    }
    Some(d)
}

/// What a declaration's statement mentions: every term but the values of theorems and
/// opaques.
fn statement_terms(d: &Decl) -> Vec<u32> {
    match d {
        Decl::Axiom { head, .. }
        | Decl::Quot { head, .. }
        | Decl::Thm { head, .. }
        | Decl::Opaque { head, .. } => vec![head.ty],
        Decl::Def { head, value, .. } => vec![head.ty, *value],
        Decl::Inductive { types, ctors, recs } => types
            .iter()
            .map(|t| t.head.ty)
            .chain(ctors.iter().map(|c| c.head.ty))
            .chain(recs.iter().map(|r| r.head.ty))
            .chain(recs.iter().flat_map(|r| r.rules.iter().map(|u| u.rhs)))
            .collect(),
    }
}

/// The first names of the declarations the statement of `t` rests on, `t` included.
fn statement_cone(canon: &Canon, decls: &FxHashMap<u32, Decl>, t: u32) -> Vec<u32> {
    let mut owner = FxHashMap::default();
    for (&k, d) in decls {
        if let Decl::Inductive { types, ctors, recs } = d {
            let heads = types
                .iter()
                .map(|t| &t.head)
                .chain(ctors.iter().map(|c| &c.head))
                .chain(recs.iter().map(|r| &r.head));
            heads.for_each(|h| {
                owner.insert(h.name, k);
            });
        }
    }
    let first = |n: u32| owner.get(&n).copied().unwrap_or(n);
    let (mut out, mut seen, mut exprs) = (Vec::new(), FxHashSet::default(), FxHashSet::default());
    let mut todo = vec![t];
    while let Some(c) = todo.pop() {
        if !seen.insert(c) {
            continue;
        }
        out.push(c);
        let Some(d) = decls.get(&c) else { continue };
        let mut terms = statement_terms(d);
        while let Some(e) = terms.pop() {
            if !exprs.insert(e) {
                continue;
            }
            match canon.get(e) {
                Key::Const(n, _) => todo.push(first(n)),
                Key::Proj(n, _, x) => {
                    todo.push(first(n));
                    terms.push(x);
                }
                Key::App(x, y) | Key::Lam(x, y) | Key::Pi(x, y) => terms.extend([x, y]),
                Key::Let(x, y, z, _) => terms.extend([x, y, z]),
                _ => {}
            }
        }
    }
    out
}

/// Compare two builds of a cone, each exported as NDJSON or blean, and say for each of
/// `targets` whether its statement was kept exactly.
pub fn drift(a: &[u8], b: &[u8], targets: &[String]) -> Result<Drift> {
    let canon = Canon::new();
    let ((da, ca, _), (db, cb, _)) = load_both(&canon, a, b)?;
    let mut d = Drift {
        decls: (ca, cb),
        ..Drift::default()
    };
    for (k, x) in &da {
        let Some(y) = db.get(k) else { continue };
        if x == y {
            d.same += 1;
        } else if stated(x) == stated(y) {
            d.proofs.push(canon.name(*k));
        } else {
            d.statements.push((canon.name(*k), what(x, y)));
        }
    }
    let gone = |from: &FxHashMap<u32, Decl>, to: &FxHashMap<u32, Decl>| {
        let mut by: FxHashMap<Option<Vec<u8>>, Vec<u32>> = FxHashMap::default();
        for (k, x) in from.iter().filter(|(k, _)| !to.contains_key(k)) {
            let s = shape(x).and_then(|s| postcard::to_allocvec(&s).ok());
            by.entry(s).or_default().push(*k);
        }
        by
    };
    let (mut ga, mut gb) = (gone(&da, &db), gone(&db, &da));
    let pairs: Vec<_> = ga
        .iter()
        .filter(|(s, v)| s.is_some() && v.len() == 1 && gb.get(*s).is_some_and(|w| w.len() == 1))
        .map(|(s, _)| s.clone())
        .collect();
    for s in pairs {
        let (x, y) = (
            ga.remove(&s).unwrap_or_default(),
            gb.remove(&s).unwrap_or_default(),
        );
        d.renamed.push((canon.name(x[0]), canon.name(y[0])));
    }
    d.removed = sorted(&canon, ga.into_values().flatten());
    d.added = sorted(&canon, gb.into_values().flatten());
    d.proofs.sort_unstable();
    d.statements.sort_unstable();
    d.renamed.sort_unstable();
    let names: FxHashMap<String, u32> = da.keys().map(|&k| (canon.name(k), k)).collect();
    for t in targets {
        let v = names.get(t).map_or(Verdict::Missing, |&k| {
            let changed: Vec<u32> = statement_cone(&canon, &da, k)
                .into_iter()
                .filter(|c| match (da.get(c), db.get(c)) {
                    (Some(x), Some(y)) => stated(x) != stated(y),
                    (x, _) => x.is_some(),
                })
                .collect();
            if changed.is_empty() {
                Verdict::Kept
            } else {
                let gone = |n: String| {
                    if names.get(&n).is_some_and(|k| db.contains_key(k)) {
                        n
                    } else {
                        format!("{n} (removed)")
                    }
                };
                Verdict::Changed(
                    sorted(&canon, changed.into_iter())
                        .into_iter()
                        .map(gone)
                        .collect(),
                )
            }
        });
        d.targets.push((t.clone(), v));
    }
    Ok(d)
}
