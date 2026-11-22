//! Which constant names which, read straight from the oleans without decoding a term. A
//! catalog of every constant comes first, then only the terms a question reaches are read,
//! and nothing of them is kept but the names they mention.

use super::{
    discover_all,
    table::{Shared, Table},
    term::{Name, NameId, ANON},
};
use crate::{
    error::{at, corrupt, Error, Result},
    inspect::Import,
    olean::{
        is_scalar, small_nat, Image, Safety, AXIOM, CTOR, DEFN, INDUCT, OPAQUE, QUOT, REC, THM,
    },
};
use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};
use std::path::{Path, PathBuf};

/// What kind of constant a node is, with the names that tie an inductive block together.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Shape {
    Axiom,
    Defn,
    Thm,
    Opaque,
    Quot,
    Induct {
        all: Vec<NameId>,
        ctors: Vec<NameId>,
    },
    Ctor {
        induct: NameId,
    },
    Rec {
        all: Vec<NameId>,
    },
}

impl Shape {
    /// The kind as `inspect` names it.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::Axiom => "axiom",
            Self::Defn => "def",
            Self::Thm => "theorem",
            Self::Opaque => "opaque",
            Self::Quot => "quot",
            Self::Induct { .. } => "inductive",
            Self::Ctor { .. } => "ctor",
            Self::Rec { .. } => "recursor",
        }
    }
}

#[derive(Debug)]
pub struct Node {
    pub name: NameId,
    pub module: u32,
    pub shape: Shape,
    /// The address of its `ConstantInfo` in the module's olean.
    info: u64,
}

/// The constants a node's terms name, in id order, and the kinds of literal in them.
#[derive(Debug, Default)]
pub struct Refs {
    pub names: Box<[NameId]>,
    nat: bool,
    str: bool,
}

/// Every constant of a set of root modules and their imports, in load order, with what
/// their terms name once [`Graph::reach`] or [`Graph::scan`] has read them.
#[derive(Debug)]
pub struct Graph {
    pub names: Table<Name>,
    pub modules: Vec<String>,
    pub paths: Vec<PathBuf>,
    /// The direct imports of each module.
    pub imports: Vec<Vec<Import>>,
    pub nodes: Vec<Node>,
    pub skipped: usize,
    /// Where each module's nodes end.
    ends: Vec<usize>,
    /// The last node of each name, as [`super::Env`] keeps the last module's copy.
    index: FxHashMap<NameId, u32>,
    recursors: FxHashMap<NameId, Vec<NameId>>,
    refs: Vec<Option<Refs>>,
    builtins: [Option<NameId>; 8],
    pool: rayon::ThreadPool,
}

/// `Nat`, `Char.ofNat`, `String.ofList`, then `Eq` and the quotient constants.
const BUILTINS: [&str; 8] = [
    "Nat",
    "Char.ofNat",
    "String.ofList",
    "Eq",
    "Quot",
    "Quot.mk",
    "Quot.lift",
    "Quot.ind",
];

struct Catalog {
    nodes: Vec<Node>,
    imports: Vec<Import>,
    skipped: usize,
}

impl Graph {
    /// Catalog `roots` and their transitive imports on `jobs` threads, reading only each
    /// constant's name and kind. No term is read until something asks for it.
    pub fn load(search: &[PathBuf], roots: &[&str], jobs: usize) -> Result<Self> {
        let found = discover_all(search, roots, Image::peek)?;
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(jobs.max(1))
            .build()?;
        let names = Shared::new(Name::Anon, found.len() * 64);
        let cats = pool.install(|| {
            found
                .par_iter()
                .enumerate()
                .map(|(m, (_, p))| catalog(&names, m, p).map_err(at(p)))
                .collect::<Result<Vec<_>>>()
        })?;
        let names = names.freeze();
        let (mut nodes, mut imports, mut ends, mut skipped) =
            (Vec::new(), Vec::new(), Vec::new(), 0);
        for c in cats {
            nodes.extend(c.nodes);
            imports.push(c.imports);
            ends.push(nodes.len());
            skipped += c.skipped;
        }
        let mut index = FxHashMap::default();
        let mut recursors: FxHashMap<NameId, Vec<NameId>> = FxHashMap::default();
        for (i, n) in nodes.iter().enumerate() {
            index.insert(n.name, u32::try_from(i).expect("node count"));
            if let Shape::Rec { all } = &n.shape {
                for &ind in all {
                    let r = recursors.entry(ind).or_default();
                    if !r.contains(&n.name) {
                        r.push(n.name);
                    }
                }
            }
        }
        let builtins = BUILTINS.map(|b| names.find(b));
        let (modules, paths) = found.into_iter().unzip();
        Ok(Self {
            refs: (0..nodes.len()).map(|_| None).collect(),
            names,
            modules,
            paths,
            imports,
            nodes,
            skipped,
            ends,
            index,
            recursors,
            builtins,
            pool,
        })
    }

    /// The nodes of module `m`, as indices into [`Graph::nodes`].
    #[must_use]
    pub fn module_nodes(&self, m: usize) -> std::ops::Range<usize> {
        m.checked_sub(1).map_or(0, |p| self.ends[p])..self.ends[m]
    }

    /// The node a name stands for, the last module's when two declare it.
    #[must_use]
    pub fn node(&self, n: NameId) -> Option<&Node> {
        self.index.get(&n).map(|&i| &self.nodes[i as usize])
    }

    /// The position of a name's node in load order.
    #[must_use]
    pub fn position(&self, n: NameId) -> Option<usize> {
        self.index.get(&n).map(|&i| i as usize)
    }

    /// What node `i`'s terms name, if they have been read.
    #[must_use]
    pub fn refs(&self, i: usize) -> Option<&Refs> {
        self.refs[i].as_ref()
    }

    #[must_use]
    pub fn find_name(&self, dotted: &str) -> Option<NameId> {
        self.names.find(dotted)
    }

    #[must_use]
    pub fn display(&self, n: NameId) -> String {
        self.names.join(n, true)
    }

    #[must_use]
    pub fn is_internal(&self, n: NameId) -> bool {
        self.names.is_internal(n)
    }

    /// The recursors of the inductive `n`.
    #[must_use]
    pub fn recursors(&self, n: NameId) -> &[NameId] {
        self.recursors.get(&n).map_or(&[], Vec::as_slice)
    }

    /// Every name an export of `roots` would visit, proofs included, reading the terms of
    /// the nodes reached as it goes. A module's terms are read together, on parallel
    /// threads, following references within the module before leaving it.
    pub fn reach(&mut self, roots: &[NameId]) -> Result<FxHashSet<NameId>> {
        let (mut seen, mut front) = (FxHashSet::default(), Vec::new());
        for &r in roots {
            self.visit(r, &mut seen, &mut front);
        }
        while !front.is_empty() {
            self.read(&front, true)?;
            let mut next = Vec::new();
            for &i in &front {
                let refs = self.refs[i as usize].as_ref().expect("read");
                self.succ(i as usize, refs, |n| self.visit(n, &mut seen, &mut next));
            }
            front = next;
        }
        Ok(seen)
    }

    fn visit(&self, n: NameId, seen: &mut FxHashSet<NameId>, front: &mut Vec<u32>) {
        if seen.insert(n) {
            if let Some(&i) = self.index.get(&n) {
                front.push(i);
            }
        }
    }

    /// The nodes an export of `roots` writes, proofs included, in load order.
    pub fn cone(&mut self, roots: &[NameId]) -> Result<Vec<usize>> {
        if let Some(&r) = roots.iter().find(|r| !self.index.contains_key(r)) {
            return Err(Error::UnknownConstant(self.display(r)));
        }
        let seen = self.reach(roots)?;
        Ok((0..self.nodes.len())
            .filter(|&i| seen.contains(&self.nodes[i].name))
            .collect())
    }

    /// Read the terms of `nodes`, and only theirs.
    pub fn scan(&mut self, nodes: &[usize]) -> Result<()> {
        let nodes: Vec<u32> = nodes
            .iter()
            .map(|&i| u32::try_from(i).expect("node count"))
            .collect();
        self.read(&nodes, false)
    }

    /// The names node `i` leads an export to: those its terms name, the constants its
    /// literals stand for, and the rest of its inductive or quotient block.
    fn succ(&self, i: usize, refs: &Refs, mut f: impl FnMut(NameId)) {
        let [nat, chr, string, eq, quot @ ..] = self.builtins;
        refs.names.iter().for_each(|&n| f(n));
        let nat = nat.filter(|_| refs.nat);
        let str = [chr, string].map(|b| b.filter(|_| refs.str));
        std::iter::once(nat).chain(str).flatten().for_each(&mut f);
        let node = &self.nodes[i];
        match &node.shape {
            Shape::Quot => quot.into_iter().chain([eq]).flatten().for_each(f),
            Shape::Induct { all, ctors } => {
                let recs = self.recursors(node.name);
                all.iter().chain(ctors).chain(recs).for_each(|&n| f(n));
            }
            Shape::Ctor { induct } => f(*induct),
            Shape::Rec { all } => all.iter().for_each(|&n| f(n)),
            Shape::Axiom | Shape::Defn | Shape::Thm | Shape::Opaque => {}
        }
    }

    /// Read the terms of `nodes` not yet read, a module per task, and with `follow` also of
    /// whatever else in the same module they lead to.
    fn read(&mut self, nodes: &[u32], follow: bool) -> Result<()> {
        let mut by: FxHashMap<u32, Vec<u32>> = FxHashMap::default();
        for &i in nodes {
            if self.refs[i as usize].is_none() {
                by.entry(self.nodes[i as usize].module).or_default().push(i);
            }
        }
        if by.is_empty() {
            return Ok(());
        }
        let mut by: Vec<_> = by.into_iter().collect();
        by.sort_unstable_by_key(|&(m, _)| m);
        let g = &*self;
        let read = g.pool.install(|| {
            by.into_par_iter()
                .map(|(m, start)| {
                    let path = &g.paths[m as usize];
                    g.read_module(m, start, follow).map_err(at(path))
                })
                .collect::<Result<Vec<_>>>()
        })?;
        for (i, r) in read.into_iter().flatten() {
            self.refs[i as usize] = Some(r);
        }
        Ok(())
    }

    fn read_module(&self, m: u32, start: Vec<u32>, follow: bool) -> Result<Vec<(u32, Refs)>> {
        let img = Image::peek_module(&self.paths[m as usize])?;
        let mut s = Scanner::new(&img, &self.names);
        let (mut done, mut out, mut todo) = (FxHashSet::default(), Vec::new(), start);
        while let Some(i) = todo.pop() {
            if !done.insert(i) {
                continue;
            }
            let r = s.refs(self.nodes[i as usize].info)?;
            if follow {
                self.succ(i as usize, &r, |n| {
                    if let Some(&j) = self.index.get(&n) {
                        if self.nodes[j as usize].module == m && self.refs[j as usize].is_none() {
                            todo.push(j);
                        }
                    }
                });
            }
            out.push((i, r));
        }
        Ok(out)
    }
}

/// Catalog module `m`: each kernel-safe constant's name, kind and address.
fn catalog(names: &Shared<Name>, m: usize, path: &Path) -> Result<Catalog> {
    let img = Image::peek_module(path)?;
    let module = u32::try_from(m).expect("module count");
    let mut memo = vec![0u32; img.slots()];
    let mut name = |o: u64| intern(&img, names, &mut memo, o);
    let (mut nodes, mut skipped) = (Vec::new(), 0);
    for info in img.array(img.field(img.root, 2)?)? {
        if img.safety(info)? != Safety::Safe {
            skipped += 1;
            continue;
        }
        let val = img.field(info, 0)?;
        let f = |i| img.field(val, i);
        let mut list =
            |o: u64| -> Result<Vec<NameId>> { img.list(o)?.into_iter().map(&mut name).collect() };
        let cv = f(0)?;
        let shape = match img.tag(info)? {
            AXIOM => Shape::Axiom,
            DEFN => Shape::Defn,
            THM => Shape::Thm,
            OPAQUE => Shape::Opaque,
            QUOT => Shape::Quot,
            INDUCT => Shape::Induct {
                all: list(f(3)?)?,
                ctors: list(f(4)?)?,
            },
            CTOR => Shape::Ctor {
                induct: name(f(1)?)?,
            },
            REC => Shape::Rec { all: list(f(1)?)? },
            t => return Err(corrupt(format!("unexpected constant tag {t}"))),
        };
        nodes.push(Node {
            name: name(img.field(cv, 0)?)?,
            module,
            shape,
            info,
        });
    }
    Ok(Catalog {
        nodes,
        imports: img.imports()?,
        skipped,
    })
}

fn intern(img: &Image, names: &Shared<Name>, memo: &mut [u32], o: u64) -> Result<NameId> {
    if is_scalar(o) || img.tag(o)? == 0 {
        return Ok(ANON);
    }
    let slot = img.slot(o)?;
    if let Some(id) = memo[slot].checked_sub(1) {
        return Ok(super::Id::new(id));
    }
    let pre = intern(img, names, memo, img.field(o, 0)?)?;
    let arg = img.field(o, 1)?;
    let n = match img.tag(o)? {
        1 => Name::Str(pre, img.str(arg)?.into()),
        _ => Name::Num(pre, small_nat(arg)?),
    };
    let id = names.intern(n);
    memo[slot] = id.0 + 1;
    Ok(id)
}

/// Collects the constants terms name, by walking their objects in the olean.
struct Scanner<'a> {
    img: &'a Image,
    names: &'a Table<Name>,
    /// Each name object's id plus one, or [`NONE`] if it was never interned.
    memo: Vec<u32>,
    /// The term an object was last visited for.
    seen: Vec<u32>,
    term: u32,
}

const NONE: u32 = u32::MAX;

impl<'a> Scanner<'a> {
    fn new(img: &'a Image, names: &'a Table<Name>) -> Self {
        Self {
            img,
            names,
            memo: vec![0; img.slots()],
            seen: vec![0; img.slots()],
            term: 0,
        }
    }

    fn name(&mut self, o: u64) -> Result<Option<NameId>> {
        let img = self.img;
        if is_scalar(o) || img.tag(o)? == 0 {
            return Ok(Some(ANON));
        }
        let slot = img.slot(o)?;
        match self.memo[slot] {
            0 => {}
            NONE => return Ok(None),
            id => return Ok(Some(super::Id::new(id - 1))),
        }
        let id = match self.name(img.field(o, 0)?)? {
            None => None,
            Some(pre) => {
                let arg = img.field(o, 1)?;
                let n = match img.tag(o)? {
                    1 => Name::Str(pre, img.str(arg)?.into()),
                    _ => Name::Num(pre, small_nat(arg)?),
                };
                self.names.get(&n)
            }
        };
        self.memo[slot] = id.map_or(NONE, |id| id.0 + 1);
        Ok(id)
    }

    /// What the type and value of the `ConstantInfo` at `info` name, recursor rules
    /// included.
    fn refs(&mut self, info: u64) -> Result<Refs> {
        let img = self.img;
        self.term += 1;
        let val = img.field(info, 0)?;
        let mut todo = vec![img.field(img.field(val, 0)?, 2)?];
        match img.tag(info)? {
            DEFN | THM | OPAQUE => todo.push(img.field(val, 1)?),
            REC => {
                for r in img.list(img.field(val, 6)?)? {
                    todo.push(img.field(r, 2)?);
                }
            }
            _ => {}
        }
        let (mut out, mut names) = (Refs::default(), Vec::new());
        while let Some(o) = todo.pop() {
            let slot = img.slot(o)?;
            if std::mem::replace(&mut self.seen[slot], self.term) == self.term {
                continue;
            }
            let f = |i| img.field(o, i);
            match img.tag(o)? {
                0 | 3 => {}
                4 => names.extend(self.name(f(0)?)?),
                5 => todo.extend([f(0)?, f(1)?]),
                6 | 7 => todo.extend([f(1)?, f(2)?]),
                8 => todo.extend([f(1)?, f(2)?, f(3)?]),
                9 => {
                    if img.tag(f(0)?)? == 0 {
                        out.nat = true;
                    } else {
                        out.str = true;
                    }
                }
                10 => todo.push(f(1)?),
                11 => todo.push(f(2)?),
                t => {
                    return Err(corrupt(format!(
                        "unexpected expression tag {t} (free or meta variable in a declaration)"
                    )))
                }
            }
        }
        names.sort_unstable_by_key(|n| n.index());
        names.dedup();
        out.names = names.into();
        Ok(out)
    }
}
