//! Questions about a cone: what it leaves unused, which axioms each declaration rests on,
//! and closure keys of its statement and of the whole of it.

use crate::{
    env::{Env, Graph, NameId, Shape},
    error::{corrupt, Error, Result},
    export::Exporter,
    key::{Key, Keys},
    olean::{is_scalar, Image},
    statement::{at, ranges, trusted},
};
use rustc_hash::{FxHashMap, FxHashSet};
use serde_json::json;
use std::{fmt::Write as _, io::Write};

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
    g: &mut Graph,
    roots: &[NameId],
    trust: &[String],
    out: &mut dyn Write,
) -> Result<()> {
    let used = g.reach(roots)?;
    let (mut empty, mut lines, mut total) = (Vec::new(), Vec::new(), 0);
    for (m, module) in g.modules.iter().enumerate() {
        let nodes = &g.nodes[g.module_nodes(m)];
        if trusted(module, trust) || nodes.is_empty() {
            continue;
        }
        let path = &g.paths[m];
        let spans = ranges(path)?;
        let own: Vec<(NameId, (u64, u64))> = nodes
            .iter()
            .filter(|n| !matches!(n.shape, Shape::Ctor { .. } | Shape::Rec { .. }))
            .filter_map(|n| Some((n.name, *spans.get(&g.display(n.name))?)))
            .collect();
        total += own.len();
        if !nodes.iter().any(|n| used.contains(&n.name)) {
            empty.push((at(module, None), own.len()));
            continue;
        }
        let mut idle: Vec<_> = own.into_iter().filter(|(c, _)| !used.contains(c)).collect();
        idle.sort_unstable_by_key(|&(_, span)| span);
        if idle.is_empty() {
            continue;
        }
        let names: FxHashSet<String> = idle.iter().map(|&(c, _)| g.display(c)).collect();
        let tags = tags(&Image::peek_module(path)?, &names)?;
        for (c, span) in idle {
            let name = g.display(c);
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
    "alias",
    "auxParentProjInfo",
    "backwardDefeq",
    "base",
    "baseType",
    "ctorLayout",
    "declMap",
    "declMeta",
    "declRange",
    "defeq",
    "deprecated",
    "docString",
    "eqnInfo",
    "existingToIncorrect",
    "exportedAxioms",
    "extension",
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
    "machineApplicableDeprecated",
    "methodSpecs",
    "mono",
    "monoType",
    "namespaces",
    "neverExtract",
    "nolint",
    "noncomputable",
    "privateConstKinds",
    "projectionFnInfo",
    "protected",
    "rec",
    "recommendedSpellingByName",
    "reducibilityCore",
    "sineQueNon",
    "sparseCasesOnInfo",
    "specCache",
    "specialize",
    "specInfo",
    "structure",
    "symbolFrequency",
    "tag",
    "taggedReturn",
    "translations",
    "trivialStructureInfo",
    "unbox",
    "versoDocString",
    "weakSpecialize",
];

/// The extensions of a module that mention each of `names`, without their namespace and
/// `Ext` suffix: `instance` for `Lean.Meta.instanceExtension`. A hygienic one, as
/// `register_simp_attr` makes, is named by the module that registered it.
fn tags(img: &Image, names: &FxHashSet<String>) -> Result<FxHashMap<String, Vec<String>>> {
    let mut out: FxHashMap<String, Vec<String>> = FxHashMap::default();
    for e in img.array(img.field(img.root, 4)?)? {
        let ext = img.str_name(img.field(e, 0)?)?;
        let short = if let Some((_, scope)) = ext.split_once("._@.") {
            let m: Vec<&str> = scope
                .split('.')
                .take_while(|c| !c.starts_with(|d: char| d.is_ascii_digit()))
                .collect();
            m[m.len().saturating_sub(2)..].join(".")
        } else {
            let last = ext.rsplit('.').next().unwrap_or(&ext);
            ["Extension", "Ext", "Attribute", "Attr"]
                .iter()
                .find_map(|s| last.strip_suffix(s).filter(|t| !t.is_empty()))
                .unwrap_or(last)
                .to_owned()
        };
        let short = short.as_str();
        if QUIET.contains(&short) || ext.starts_with("Lean.Compiler.") {
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
    g: &mut Graph,
    roots: &[NameId],
    trust: &[String],
    q: &Axioms<'_>,
    out: &mut dyn Write,
) -> Result<()> {
    let find = |n: &String| {
        g.find_name(n)
            .filter(|&c| g.node(c).is_some_and(|k| k.shape == Shape::Axiom))
            .ok_or_else(|| corrupt(format!("{n} is not an axiom")))
    };
    let uses = q.uses.iter().map(find).collect::<Result<Vec<_>>>()?;
    let only = q
        .only
        .map(|o| o.iter().map(find).collect::<Result<FxHashSet<_>>>())
        .transpose()?;
    let listed: Vec<NameId> = if roots.is_empty() {
        g.nodes.iter().map(|n| n.name).collect()
    } else {
        g.cone(roots)?
            .into_iter()
            .map(|i| g.nodes[i].name)
            .collect()
    };
    let listed: Vec<NameId> = listed
        .into_iter()
        .filter(|&c| {
            let k = g.node(c).expect("listed");
            !g.is_internal(c)
                && !matches!(k.shape, Shape::Ctor { .. } | Shape::Rec { .. })
                && !trusted(&g.modules[k.module as usize], trust)
        })
        .collect();
    g.reach(&listed)?;
    let env = &*g;
    let mut a = Sets::new(env);
    let (mut rows, mut count) = (Vec::new(), FxHashMap::<NameId, usize>::default());
    for c in listed {
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
struct Sets<'g> {
    g: &'g Graph,
    of: FxHashMap<NameId, u32>,
    table: Vec<Box<[NameId]>>,
    index: FxHashMap<Box<[NameId]>, u32>,
}

impl<'g> Sets<'g> {
    fn new(g: &'g Graph) -> Self {
        let mut s = Self {
            g,
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

    fn shape(&self, c: NameId) -> Option<&'g Shape> {
        self.g.node(c).map(|n| &n.shape)
    }

    /// The constant that stands for `c`'s whole inductive block, or `c`.
    fn block(&self, c: NameId) -> NameId {
        let base = match self.shape(c) {
            Some(Shape::Ctor { induct }) => *induct,
            Some(Shape::Rec { all }) => return all.first().copied().unwrap_or(c),
            _ => c,
        };
        match self.shape(base) {
            Some(Shape::Induct { all, .. }) => all.first().copied().unwrap_or(base),
            _ => base,
        }
    }

    /// What the terms of `c` name, as read by [`Graph::reach`].
    fn refs(&self, c: NameId) -> Result<&'g [NameId]> {
        let g = self.g;
        let i = g.position(c).expect("a node");
        g.refs(i)
            .map(|r| &*r.names)
            .ok_or_else(|| corrupt(format!("the terms of {} are not read", g.display(c))))
    }

    /// The blocks `c`'s block mentions, itself left out.
    fn deps(&self, c: NameId) -> Result<Vec<NameId>> {
        let g = self.g;
        let mut consts = Vec::new();
        match self.shape(c) {
            None | Some(Shape::Axiom) => return Ok(consts),
            Some(Shape::Induct { all, .. }) => {
                for &t in all {
                    if let Some(Shape::Induct { ctors, .. }) = self.shape(t) {
                        for &k in std::iter::once(&t).chain(ctors) {
                            if self.shape(k).is_some() {
                                consts.extend(self.refs(k)?);
                            }
                        }
                    }
                }
                for &r in g.recursors(c) {
                    consts.extend(self.refs(r)?);
                }
            }
            Some(_) => consts.extend(self.refs(c)?),
        }
        let mut out: Vec<NameId> = consts.into_iter().map(|n| self.block(n)).collect();
        out.sort_unstable_by_key(|&n| (g.position(n).unwrap_or(usize::MAX), n.index()));
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
                if self.shape(n) == Some(&Shape::Axiom) {
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

/// Write, as NDJSON, what each declaration's terms name.
///
/// Covers the cone of `roots`, or every loaded module without roots, outside the modules
/// `trust` names. With `modules`, one line per module instead, counting the references
/// into each module.
pub fn deps(
    g: &mut Graph,
    roots: &[NameId],
    trust: &[String],
    modules: bool,
    out: &mut dyn Write,
) -> Result<()> {
    let listed: Vec<usize> = if roots.is_empty() {
        (0..g.nodes.len()).collect()
    } else {
        g.cone(roots)?
    };
    let listed: Vec<usize> = listed
        .into_iter()
        .filter(|&i| !trusted(&g.modules[g.nodes[i].module as usize], trust))
        .collect();
    g.scan(&listed)?;
    let uses = |i: usize| {
        let mut u: Vec<usize> = g
            .refs(i)
            .expect("scanned")
            .names
            .iter()
            .filter_map(|&n| g.position(n))
            .collect();
        u.sort_unstable();
        u
    };
    let line = |out: &mut dyn Write, v: serde_json::Value| -> Result<()> {
        serde_json::to_writer(&mut *out, &v).map_err(|e| Error::Io(e.into()))?;
        Ok(writeln!(out)?)
    };
    if !modules {
        for &i in &listed {
            let n = &g.nodes[i];
            let uses: Vec<String> = uses(i)
                .into_iter()
                .map(|j| g.display(g.nodes[j].name))
                .collect();
            line(
                out,
                json!({
                    "name": g.display(n.name),
                    "module": g.modules[n.module as usize],
                    "kind": n.shape.kind(),
                    "uses": uses,
                }),
            )?;
        }
        return Ok(());
    }
    let mut by: Vec<(usize, FxHashMap<u32, usize>)> = vec![Default::default(); g.modules.len()];
    for &i in &listed {
        let m = g.nodes[i].module as usize;
        by[m].0 += 1;
        for j in uses(i) {
            *by[m].1.entry(g.nodes[j].module).or_default() += 1;
        }
    }
    for (m, (decls, to)) in by.into_iter().enumerate().filter(|(_, (d, _))| *d > 0) {
        let mut to: Vec<_> = to.into_iter().collect();
        to.sort_unstable();
        let uses: serde_json::Map<String, serde_json::Value> = to
            .into_iter()
            .map(|(t, n)| (g.modules[t as usize].clone(), n.into()))
            .collect();
        line(
            out,
            json!({"module": g.modules[m], "decls": decls, "uses": uses}),
        )?;
    }
    Ok(())
}
