use kamo::{CheckedProgram, Options};
use std::hint::black_box;

fn main() {
    let prelude = include_str!("../examples/univalence.kamo");
    let mut cases = Vec::new();
    for depth in [1, 8, 32] {
        let mut body = "true".to_owned();
        for _ in 0..depth {
            body = format!("(coe i (at neg-path i) 0 1 {body})");
        }
        cases.push((
            format!("univalence-chain-{depth}"),
            "Bool".to_owned(),
            body,
            if depth % 2 == 0 { "true" } else { "false" }.to_owned(),
        ));
    }
    let mut shared = "true".to_owned();
    for _ in 0..32 {
        shared = format!("(coe i (at neg-path i) 0 1 {shared})");
    }
    let shared_definition = format!("(def bench-shared Bool {shared})");
    let mut reused = "true".to_owned();
    for _ in 0..16 {
        reused = format!("(bool-elim (lam b Bool) {reused} false bench-shared)");
    }
    cases.push((
        "shared-univalence-16x32".into(),
        "Bool".into(),
        reused,
        "true".into(),
    ));
    cases.push(("dependent-function".into(),"Bool".into(),
        "(fst (app (coe i (Pi b Bool (Sigma y (at neg-path i) (Path j (at neg-path i) y y))) 0 1 (lam b (pair b (path j b)))) true))".into(),"false".into()));
    cases.push(("dependent-pair".into(),"Bool".into(),
        "(fst (coe i (Sigma y (at neg-path i) (Path j (at neg-path i) y y)) 0 1 (pair true (path j true))))".into(),"false".into()));
    for depth in [1, 4, 8] {
        let mut ty = "Bool".to_owned();
        let mut value = "true".to_owned();
        for _ in 0..depth {
            ty = format!("(Glue {ty} ())");
            value = format!("(glue {ty} {value} ())");
        }
        cases.push((
            format!("nested-glue-{depth}"),
            ty.clone(),
            format!("(coe i {ty} 0 1 {value})"),
            value,
        ));
    }
    cases.push((
        "open-conversion".into(),
        "(Pi A (U 0) (Pi x A (Pi p (Path i A x x) (Path i A x x))))".into(),
        "(lam A (lam x (lam p (path i (at p i)))))".into(),
        "(lam A (lam x (lam p p)))".into(),
    ));
    println!(
        "case,mode,median_ns,value_nodes,environment_nodes,substitution_nodes,face_nodes,arena_capacity_bytes"
    );
    for (name, ty, left, right) in cases {
        // Parsing and proof checking happen before any timer starts.
        let source = format!(
            "{prelude}\n{shared_definition}\n(def bench-left {ty} {left})\n(def bench-right {ty} {right})"
        );
        let program = CheckedProgram::check(&source).unwrap_or_else(|e| panic!("{name}: {e}"));
        for optimized in [true, false] {
            let options = Options {
                optimized,
                ..Options::default()
            };
            let mut times = Vec::new();
            let mut stats = None;
            for _ in 0..5 {
                let (time, s, equal) = program
                    .benchmark_conversion("bench-left", "bench-right", options)
                    .unwrap_or_else(|e| panic!("{name}, optimized={optimized}: {e}"));
                assert!(black_box(equal), "{name} produced unequal results");
                times.push(time.as_nanos());
                stats = Some(s);
            }
            times.sort_unstable();
            let s = stats.unwrap();
            let mode = if optimized { "optimized" } else { "reference" };
            println!(
                "{name},{mode},{},{},{},{},{},{}",
                times[2],
                s.value_nodes,
                s.environment_nodes,
                s.substitution_nodes,
                s.face_nodes,
                s.arena_bytes
            );
        }
    }
}
