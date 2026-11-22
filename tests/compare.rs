use olean_export::{blean::Blean, compare, ndjson::Ndjson, Env, Exporter, Sink};
use std::{fs, path::PathBuf, slice};

fn cases() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases")
}

fn export<S: Sink>(env: &Env, sink: S, consts: &[&str]) -> S::Output {
    let mut ex = Exporter::with_sink(env, sink);
    ex.meta().unwrap();
    if consts.is_empty() {
        ex.all().unwrap();
    }
    for c in consts {
        ex.constant(env.find_name(c).unwrap()).unwrap();
    }
    ex.finish().unwrap()
}

/// Every fixture, and one constant subset, against what lean4export wrote for it (`just
/// lean4export`).
#[test]
fn matches_lean4export() {
    let build = cases().join("build");
    let runs: [(&str, &str, &[&str]); 4] = [
        ("Base", "Base", &[]),
        ("Extra", "Extra", &[]),
        ("Top", "Top", &[]),
        ("Top", "Top-cone", &["Even.below.casesOn", "letty"]),
    ];
    for (module, file, consts) in runs {
        let want = fs::read(cases().join(format!("lean4export/{file}.ndjson"))).unwrap();
        let search = slice::from_ref(&build);
        let env = if consts.is_empty() {
            Env::load(search, &[module]).unwrap()
        } else {
            Env::load_cone(search, &[module], consts, 1, &|_, _| {}).unwrap()
        };
        let ndjson = export(&env, Ndjson::new(Vec::new()), consts);
        let blean = export(&env, Blean::new(Vec::new()), consts);
        for got in [ndjson, blean] {
            let d = compare(&want, &got).unwrap();
            assert!(d.is_empty() && d.decls.0 > 0, "{file}: {d:?}");
        }
    }
}

#[test]
fn reports_differences() {
    let dir = cases().join("lean4export");
    let top = fs::read(dir.join("Top.ndjson")).unwrap();
    let cone = fs::read(dir.join("Top-cone.ndjson")).unwrap();
    let d = compare(&top, &cone).unwrap();
    assert!(!d.only_a.is_empty() && d.only_b.is_empty() && d.differ.is_empty());
}

/// The fixtures against their edits in `cases/edit` (a new proof of `N.add_zero`, a new
/// value of `two`), and a rename made by hand.
#[test]
fn drift_tells_statements_from_names() {
    use olean_export::compare::{drift, Verdict};
    let load = |dirs: &[&str]| {
        let dirs: Vec<PathBuf> = dirs.iter().map(|d| cases().join(d)).collect();
        export(
            &Env::load(&dirs, &["Top"]).unwrap(),
            Ndjson::new(Vec::new()),
            &[],
        )
    };
    let a = load(&["build"]);
    let b = load(&["build/edit", "build"]);
    let targets = ["N.add_zero", "two", "letty", "nope"].map(String::from);
    let d = drift(&a, &b, &targets).unwrap();
    assert_eq!(d.statements, [("two".to_owned(), "value")]);
    assert_eq!(
        (d.removed, d.added),
        (vec!["letty".to_owned()], vec!["three".to_owned()])
    );
    assert_eq!(
        (d.proofs, d.renamed.len()),
        (vec!["N.add_zero".to_owned()], 0)
    );
    let v: Vec<&Verdict> = d.targets.iter().map(|(_, v)| v).collect();
    assert_eq!(v[0], &Verdict::Kept);
    assert_eq!(v[1], &Verdict::Changed(vec!["two".into()]));
    assert_eq!(v[2], &Verdict::Changed(vec!["letty (removed)".into()]));
    assert_eq!(v[3], &Verdict::Missing);

    let text = String::from_utf8(a.clone()).unwrap();
    let renamed = text.replace(r#""str":"add_zero""#, r#""str":"add_zero'""#);
    let d = drift(&a, renamed.as_bytes(), &[]).unwrap();
    assert_eq!(
        d.renamed,
        [("N.add_zero".to_owned(), "N.add_zero'".to_owned())]
    );
    assert!(d.statements.is_empty() && d.removed.is_empty() && d.added.is_empty());
}
