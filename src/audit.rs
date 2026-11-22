//! Questions about a cone: what it leaves unused, which axioms each declaration rests on,
//! and closure keys of its statement and of the whole of it.

use crate::{
    env::{resolve, Builtins, Dep, Env, ExprId, Kind, NameId},
    error::{corrupt, Result},
    export::Exporter,
    key::{Key, Keys},
    olean::{is_scalar, Image},
    statement::{at, ranges, trusted},
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{fmt::Write as _, io::Write, path::PathBuf};

/// The closure keys of a constant: of its statement cone, theorems taken as stated, and of
/// its full cone, with the number of declarations in each.
#[derive(Debug)]
pub struct Digest {
    pub name: String,
    pub statement: (Option<Key>, usize),
    pub full: (Option<Key>, usize),
}

/// Digests of `roots`. Every theorem in their full cone must have its value loaded.
pub fn digest(env: &Env, roots: &[NameId]) -> Result<Vec<Digest>> {
    let key = |statements: bool| -> Result<FxHashMap<String, Option<Key>>> {
        let mut k = Keys::new();
        let mut ex = Exporter::with_sink(env, &mut k);
        if statements {
            ex = ex.statements();
        }
        ex.meta()?;
        roots.iter().try_for_each(|&c| ex.constant(c))?;
        ex.finish()?;
        Ok(k.into_keys().into_iter().map(|d| (d.name, d.key)).collect())
    };
    let (s, f) = (key(true)?, key(false)?);
    roots
        .iter()
        .map(|&c| {
            let name = env.dotted(c);
            Ok(Digest {
                statement: (s[&name], env.statement(&[c])?.len()),
                full: (f[&name], env.cone(&[c])?.len()),
                name: env.display(c),
            })
        })
        .collect()
}

/// Print what the full cone of `roots` leaves unused outside the modules `trust` names.
///
/// First each module with nothing used, then every declaration with a source range that is
/// not, with the attributes and extensions that mention it, which may use it while
/// elaborating.
pub fn unused(
    env: &Env,
    search: &[PathBuf],
    roots: &[NameId],
    trust: &[String],
    out: &mut dyn Write,
) -> Result<()> {
    let used: FxHashSet<NameId> = env.cone(roots)?.into_iter().map(|(_, c)| c).collect();
    let (mut empty, mut lines, mut total) = (Vec::new(), Vec::new(), 0);
    for (m, module) in env.modules.iter().enumerate() {
        let consts = env.module_consts(m);
        if trusted(module, trust) || consts.is_empty() {
            continue;
        }
        let path = resolve(search, module)?;
        let spans = ranges(&path)?;
        let own: Vec<(NameId, (u64, u64))> = consts
            .iter()
            .filter(|&&c| !matches!(env.consts[&c].kind, Kind::Ctor(_) | Kind::Rec(_)))
            .filter_map(|&c| Some((c, *spans.get(&env.display(c))?)))
            .collect();
        total += own.len();
        if !consts.iter().any(|c| used.contains(c)) {
            empty.push((at(module, None), own.len()));
            continue;
        }
        let mut idle: Vec<_> = own.into_iter().filter(|(c, _)| !used.contains(c)).collect();
        idle.sort_unstable_by_key(|&(_, span)| span);
        if idle.is_empty() {
            continue;
        }
        let names: FxHashSet<String> = idle.iter().map(|&(c, _)| env.display(c)).collect();
        let tags = tags(&Image::open_module(&path)?, &names)?;
        for (c, span) in idle {
            let name = env.display(c);
            let tag = tags
                .get(&name)
                .map_or_else(String::new, |t| format!(" [{}]", t.join(", ")));
            lines.push(format!("{} {name}{tag}", at(module, Some(span))));
        }
    }
    let n: usize = empty.iter().map(|&(_, n)| n).sum::<usize>() + lines.len();
    writeln!(
        out,
        "-- {n} of {total} declarations unused, in {} unused files",
        empty.len()
    )?;
    for (file, n) in &empty {
        writeln!(out, "{file} ({n} declarations)")?;
    }
    for l in &lines {
        writeln!(out, "{l}")?;
    }
    Ok(())
}

/// Extensions, by short name, that every declaration of a kind gets or that serve only the
/// compiler, which say nothing about how it is used.
const QUIET: &[&str] = &[
    "auxParentProjInfo",
    "backwardDefeq",
    "base",
    "baseType",
    "ctorLayout",
    "declMap",
    "declMeta",
    "declRange",
    "docString",
    "eqnInfo",
    "existingToIncorrect",
    "exportedAxioms",
    "extern",
    "extType",
    "functionSummaries",
    "implementedBy",
    "impureSig",
    "impureTrivialStructureInfo",
    "impureType",
    "incorrectToExisting",
    "inheritDocString",
    "inlineAttrs",
    "methodSpecs",
    "mono",
    "monoType",
    "namespaces",
    "neverExtract",
    "noncomputable",
    "privateConstKinds",
    "projectionFnInfo",
    "rec",
    "recommendedSpellingByName",
    "reducibilityCore",
    "specCache",
    "specialize",
    "specInfo",
    "structure",
    "taggedReturn",
    "trivialStructureInfo",
    "unbox",
    "versoDocString",
    "weakSpecialize",
];

/// The extensions of a module that mention each of `names`, without their namespace and
/// `Ext` suffix: `instance` for `Lean.Meta.instanceExtension`.
fn tags(img: &Image, names: &FxHashSet<String>) -> Result<FxHashMap<String, Vec<String>>> {
    let mut out: FxHashMap<String, Vec<String>> = FxHashMap::default();
    for e in img.array(img.field(img.root, 4)?)? {
        let ext = img.str_name(img.field(e, 0)?)?;
        let last = ext.rsplit('.').next().unwrap_or(&ext);
        let short = ["Extension", "Ext", "Attribute", "Attr"]
            .iter()
            .find_map(|s| last.strip_suffix(s).filter(|t| !t.is_empty()))
            .unwrap_or(last);
        if QUIET.contains(&short) {
            continue;
        }
        let (mut seen, mut todo) = (FxHashSet::default(), vec![img.field(e, 1)?]);
        while let Some(o) = todo.pop() {
            if is_scalar(o) || !seen.insert(o) {
                continue;
            }
            if img.is_name_str(o)? {
                let n = img.display_name(o)?;
                if names.contains(&n) {
                    let t = out.entry(n).or_default();
                    if !t.iter().any(|x| x == short) {
                        t.push(short.to_owned());
                    }
                }
                continue;
            }
            img.children(o, |c| todo.push(c))?;
        }
    }
    Ok(out)
}

/// Which axioms what to report on rests on, and what to report.
#[derive(Debug, Default)]
pub struct Axioms<'a> {
    /// Only declarations resting on one of these.
    pub uses: &'a [String],
    /// Only declarations resting on an axiom not among these.
    pub only: Option<&'a [String]>,
    /// For each declaration listed, a chain of constants down to an axiom that selected it.
    pub why: bool,
}

/// Print the axioms each declaration rests on, as `#print axioms` collects them: the cone
/// of `roots`, or the whole environment without roots, outside the modules `trust` names.
pub fn axioms(
    env: &Env,
    roots: &[NameId],
    trust: &[String],
    q: &Axioms<'_>,
    out: &mut dyn Write,
) -> Result<()> {
    let find = |n: &String| {
        env.find_name(n)
            .filter(|c| matches!(env.consts.get(c).map(|k| &k.kind), Some(Kind::Axiom)))
            .ok_or_else(|| corrupt(format!("{n} is not an axiom")))
    };
    let uses = q.uses.iter().map(find).collect::<Result<Vec<_>>>()?;
    let only = q
        .only
        .map(|o| o.iter().map(find).collect::<Result<FxHashSet<_>>>())
        .transpose()?;
    let listed: Vec<NameId> = if roots.is_empty() {
        env.roots().collect()
    } else {
        env.cone(roots)?.into_iter().map(|(_, c)| c).collect()
    };
    let module: FxHashMap<NameId, usize> = (0..env.modules.len())
        .flat_map(|m| env.module_consts(m).iter().map(move |&c| (c, m)))
        .collect();
    let mut a = Sets::new(env);
    let (mut rows, mut count) = (Vec::new(), FxHashMap::<NameId, usize>::default());
    for c in listed {
        let k = &env.consts[&c];
        if env.is_internal(c)
            || matches!(k.kind, Kind::Ctor(_) | Kind::Rec(_))
            || trusted(&env.modules[module[&c]], trust)
        {
            continue;
        }
        let set = a.of(c)?;
        let hit: Vec<NameId> = if !uses.is_empty() {
            uses.iter().copied().filter(|x| set.contains(x)).collect()
        } else if let Some(o) = &only {
            set.iter().copied().filter(|x| !o.contains(x)).collect()
        } else {
            set.to_vec()
        };
        if hit.is_empty() && (!uses.is_empty() || only.is_some()) {
            continue;
        }
        for x in set {
            *count.entry(*x).or_default() += 1;
        }
        let mut names: Vec<String> = set.iter().map(|&x| env.display(x)).collect();
        names.sort_unstable();
        if names.is_empty() {
            names.push("none".into());
        }
        let mut line = format!("{}: {}", env.display(c), names.join(", "));
        if q.why {
            if let Some(&x) = hit.first().filter(|&&x| x != c) {
                let chain: Vec<String> = a.why(c, x)?.iter().map(|&n| env.display(n)).collect();
                let _ = write!(line, "\n  via {}", chain.join(" -> "));
            }
        }
        rows.push(line);
    }
    let mut by: Vec<(String, usize)> = count
        .into_iter()
        .map(|(x, n)| (env.display(x), n))
        .collect();
    by.sort_unstable();
    let by: Vec<String> = by.into_iter().map(|(x, n)| format!("{x} {n}")).collect();
    writeln!(
        out,
        "-- {} declarations; by axiom: {}",
        rows.len(),
        by.join(", ")
    )?;
    for r in rows {
        writeln!(out, "{r}")?;
    }
    Ok(())
}

/// Memoized axiom sets, one per declaration or inductive block, interned.
struct Sets<'e> {
    env: &'e Env,
    b: Builtins,
    of: FxHashMap<NameId, u32>,
    table: Vec<Box<[NameId]>>,
    index: FxHashMap<Box<[NameId]>, u32>,
}

impl<'e> Sets<'e> {
    fn new(env: &'e Env) -> Self {
        let mut s = Self {
            env,
            b: Builtins::find(env),
            of: FxHashMap::default(),
            table: Vec::new(),
            index: FxHashMap::default(),
        };
        s.intern(Vec::new());
        s
    }

    fn intern(&mut self, mut v: Vec<NameId>) -> u32 {
        v.sort_unstable_by_key(|n| n.index());
        v.dedup();
        let v = v.into_boxed_slice();
        if let Some(&i) = self.index.get(&v) {
            return i;
        }
        let i = u32::try_from(self.table.len()).expect("set count");
        self.table.push(v.clone());
        self.index.insert(v, i);
        i
    }

    /// The constant that stands for `c`'s whole inductive block, or `c`.
    fn block(&self, c: NameId) -> NameId {
        let base = match self.env.consts.get(&c).map(|k| &k.kind) {
            Some(Kind::Ctor(x)) => x.induct,
            Some(Kind::Rec(r)) => return r.all.first().copied().unwrap_or(c),
            _ => c,
        };
        match self.env.consts.get(&base).map(|k| &k.kind) {
            Some(Kind::Induct(i)) => i.all.first().copied().unwrap_or(base),
            _ => base,
        }
    }

    /// The blocks `c`'s block mentions, itself left out.
    fn deps(&self, c: NameId) -> Result<Vec<NameId>> {
        let env = self.env;
        let Some(k) = env.consts.get(&c) else {
            return Ok(Vec::new());
        };
        let terms: Vec<ExprId> = match &k.kind {
            Kind::Axiom => return Ok(Vec::new()),
            Kind::Induct(i) => env.family(k, i)?.terms().collect(),
            Kind::Thm(t) => {
                let v = t.value.ok_or_else(|| {
                    corrupt(format!("the value of {} is not loaded", env.display(c)))
                })?;
                vec![k.ty, v]
            }
            Kind::Defn(d) => vec![k.ty, d.value],
            Kind::Opaque(o) => vec![k.ty, o.value],
            Kind::Quot(_) | Kind::Ctor(_) | Kind::Rec(_) => vec![k.ty],
        };
        let (mut seen, mut consts) = (FxHashSet::default(), FxHashSet::default());
        let mut todo = terms;
        while let Some(e) = todo.pop() {
            if seen.insert(e) {
                env.children(e, &self.b, |d| match d {
                    Dep::Expr(x) => todo.push(x),
                    Dep::Const(n) => {
                        consts.insert(n);
                    }
                    _ => {}
                });
            }
        }
        let mut out: Vec<NameId> = consts.into_iter().map(|n| self.block(n)).collect();
        out.sort_unstable_by_key(|n| n.index());
        out.dedup();
        out.retain(|&n| n != c);
        Ok(out)
    }

    fn set(&self, c: NameId) -> &[NameId] {
        self.of
            .get(&c)
            .map_or(&[][..], |&i| &self.table[i as usize])
    }

    fn of(&mut self, c: NameId) -> Result<&[NameId]> {
        let c = self.block(c);
        let mut todo: Vec<(NameId, Option<Vec<NameId>>)> = vec![(c, None)];
        while let Some((n, deps)) = todo.pop() {
            if self.of.contains_key(&n) {
                continue;
            }
            if let Some(deps) = deps {
                let mut v: Vec<NameId> = deps.iter().flat_map(|&d| self.set(d)).copied().collect();
                if matches!(self.env.consts.get(&n).map(|k| &k.kind), Some(Kind::Axiom)) {
                    v.push(n);
                }
                let i = self.intern(v);
                self.of.insert(n, i);
            } else {
                let deps = self.deps(n)?;
                let more: Vec<_> = deps
                    .iter()
                    .filter(|d| !self.of.contains_key(d))
                    .map(|&d| (d, None))
                    .collect();
                todo.push((n, Some(deps)));
                todo.extend(more);
            }
        }
        Ok(self.set(c))
    }

    /// A chain from `c` to the axiom `x`, through constants that rest on it.
    fn why(&self, c: NameId, x: NameId) -> Result<Vec<NameId>> {
        let mut chain = vec![c];
        let mut at = self.block(c);
        while at != x {
            let next = self
                .deps(at)?
                .into_iter()
                .find(|&d| self.set(d).contains(&x))
                .ok_or_else(|| corrupt("axiom chain broken"))?;
            chain.push(next);
            at = next;
        }
        Ok(chain)
    }
}
