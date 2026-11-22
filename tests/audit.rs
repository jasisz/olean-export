use olean_export::{
    audit::{self, Axioms},
    Env,
};
use std::path::PathBuf;

fn env(dirs: &[&str]) -> Env {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases");
    let dirs: Vec<PathBuf> = dirs.iter().map(|d| root.join(d)).collect();
    Env::load(&dirs, &["Top"]).unwrap()
}

fn run(env: &Env, f: impl FnOnce(&Env, &mut Vec<u8>)) -> String {
    let mut out = Vec::new();
    f(env, &mut out);
    String::from_utf8(out).unwrap()
}

/// A digest moves only when something in its cone does.
#[test]
fn digest_follows_the_cone() {
    let (a, b) = (env(&["build"]), env(&["build/edit", "build"]));
    let dig = |e: &Env, n: &str| {
        audit::digest(e, &[e.find_name(n).unwrap()])
            .unwrap()
            .remove(0)
    };
    let (x, y) = (dig(&a, "N.add_zero"), dig(&b, "N.add_zero"));
    assert_eq!(x.statement, y.statement);
    assert_ne!(x.full, y.full);
    assert_ne!(x.statement.0, x.full.0);
    let (x, y) = (dig(&a, "Even"), dig(&b, "Even"));
    assert_eq!((x.statement, x.full), (y.statement, y.full));
    assert_ne!(dig(&a, "two").statement, dig(&b, "two").statement);
}

#[test]
fn unused_lists_what_the_cone_misses() {
    let e = env(&["build"]);
    let two = e.find_name("two").unwrap();
    let path = [PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases/build")];
    let s = run(&e, |e, out| {
        audit::unused(e, &path, &[two], &[], out).unwrap();
    });
    assert!(s.contains("Top.lean:16-18 letty\n"), "{s}");
    assert!(!s.contains(" two") && !s.contains(" N.add\n"), "{s}");
}

#[test]
fn axioms_by_query() {
    let e = env(&["build"]);
    let uses = ["choice".to_owned()];
    let q = Axioms {
        uses: &uses,
        why: true,
        ..Axioms::default()
    };
    let s = run(&e, |e, out| audit::axioms(e, &[], &[], &q, out).unwrap());
    assert_eq!(s, "-- 1 declarations; by axiom: choice 1\nchoice: choice\n");
    let only = Axioms {
        only: Some(&uses),
        ..Axioms::default()
    };
    let s = run(&e, |e, out| audit::axioms(e, &[], &[], &only, out).unwrap());
    assert_eq!(s, "-- 0 declarations; by axiom: \n");
}

/// Outside the trusted modules every proof is decoded, inside only those reached.
#[test]
fn load_outside_skips_unreached_proofs() {
    use olean_export::Kind;
    let dir = [PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases/build")];
    let loaded = |root: &str, trust: &[&str]| {
        let trust: Vec<String> = trust.iter().map(|&t| t.to_owned()).collect();
        let e = Env::load_outside(&dir, &[root], &trust, 1, &|_, _| {}).unwrap();
        let c = &e.consts[&e.find_name("N.add_zero").unwrap()];
        matches!(&c.kind, Kind::Thm(t) if t.value.is_some())
    };
    assert!(!loaded("Top", &["Base"]));
    assert!(loaded("Pinned", &["Base"]));
    assert!(loaded("Top", &[]));
}
