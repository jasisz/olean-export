use olean_export::{
    audit::{self, Axioms},
    Env, Graph,
};
use std::path::PathBuf;

fn dirs(dirs: &[&str]) -> Vec<PathBuf> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases");
    dirs.iter().map(|d| root.join(d)).collect()
}

fn env(d: &[&str]) -> Env {
    Env::load(&dirs(d), &["Top"]).unwrap()
}

fn graph(root: &str) -> Graph {
    Graph::load(&dirs(&["build"]), &[root], 1).unwrap()
}

fn run(g: &mut Graph, f: impl FnOnce(&mut Graph, &mut Vec<u8>)) -> String {
    let mut out = Vec::new();
    f(g, &mut out);
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
    let mut g = graph("Top");
    let two = g.find_name("two").unwrap();
    let s = run(&mut g, |g, out| audit::unused(g, &[two], &[], out).unwrap());
    assert!(s.contains("Top.lean:16-18 letty\n"), "{s}");
    assert!(!s.contains(" two") && !s.contains(" N.add\n"), "{s}");
}

#[test]
fn axioms_by_query() {
    let mut g = graph("Top");
    let uses = ["choice".to_owned()];
    let q = Axioms {
        uses: &uses,
        why: true,
        ..Axioms::default()
    };
    let s = run(&mut g, |g, out| {
        audit::axioms(g, &[], &[], &q, out).unwrap();
    });
    assert_eq!(s, "-- 1 declarations; by axiom: choice 1\nchoice: choice\n");
    let only = Axioms {
        only: Some(&uses),
        ..Axioms::default()
    };
    let s = run(&mut g, |g, out| {
        audit::axioms(g, &[], &[], &only, out).unwrap();
    });
    assert_eq!(s, "-- 0 declarations; by axiom: \n");
}

/// Outside the trusted modules every proof is read, inside only those reached.
#[test]
fn axioms_read_only_reached_proofs() {
    let read = |root: &str, trust: &[&str]| {
        let trust: Vec<String> = trust.iter().map(|&t| t.to_owned()).collect();
        let mut g = graph(root);
        run(&mut g, |g, out| {
            audit::axioms(g, &[], &trust, &Axioms::default(), out).unwrap();
        });
        let n = g.find_name("N.add_zero").unwrap();
        g.refs(g.position(n).unwrap()).is_some()
    };
    assert!(!read("Top", &["Base"]));
    assert!(read("Pinned", &["Base"]));
    assert!(read("Top", &[]));
}
