use kamo::{CheckedProgram, Options};

fn nf(source: &str, name: &str) -> String {
    CheckedProgram::check(source)
        .unwrap()
        .normalize(name)
        .unwrap()
        .text
}
fn rejects(source: &str, part: &str) {
    let e = CheckedProgram::check(source).unwrap_err();
    assert!(e.message.contains(part), "{e}");
}

#[test]
fn example_program() {
    let p = CheckedProgram::check(include_str!("../examples/core.kamo")).unwrap();
    for (name, expected) in [
        ("not-true", "false"),
        ("not-false", "true"),
        ("four", "(suc (suc (suc (suc zero))))"),
        ("unpack", "true"),
        ("endpoint", "true"),
        ("transport-bool", "true"),
        ("transport-pair", "(pair true false)"),
        ("transport-path", "(path i0 true)"),
        ("composed", "true"),
        ("split", "true"),
    ] {
        assert_eq!(p.normalize(name).unwrap().text, expected, "{name}");
    }
}
#[test]
fn universe_errors() {
    rejects("(def bad (U 0) (U 0))", "type mismatch");
    rejects("(def bad (U 1) Bool)", "type mismatch");
    rejects("(def bad (U 4294967295) Bool)", "overflow");
}

#[test]
fn yoneda_foundations_and_function_extensionality() {
    let source = format!(
        "{}\n{}",
        include_str!("../examples/foundations.kamo"),
        r#"
; These laws quantify over arbitrary dependent families and open paths.
(def funext-beta
  (Pi A (U 0) (Pi B (Pi x A (U 0))
    (Pi f (Pi x A (app B x)) (Pi g (Pi x A (app B x))
      (Pi h (Pi x A (Path i (app B x) (app f x) (app g x)))
        (Path j (Pi x A (Path i (app B x) (app f x) (app g x)))
          (app (app (app (app (app happly A) B) f) g)
            (app (app (app (app (app funext A) B) f) g) h)) h))))))
  (lam A (lam B (lam f (lam g (lam h (path j h)))))))
(def funext-eta
  (Pi A (U 0) (Pi B (Pi x A (U 0))
    (Pi f (Pi x A (app B x)) (Pi g (Pi x A (app B x))
      (Pi p (Path i (Pi x A (app B x)) f g)
        (Path j (Path i (Pi x A (app B x)) f g)
          (app (app (app (app (app funext A) B) f) g)
            (app (app (app (app (app happly A) B) f) g) p)) p))))))
  (lam A (lam B (lam f (lam g (lam p (path j p)))))))
(def reversed (Path i Nat zero zero)
  (app (app (app (app sym Nat) zero) zero) (path i zero)))
(def joined (Path i Nat zero zero)
  (app (app (app (app (app (app concat Nat) zero) zero) zero)
    reversed) (path i zero)))
(def mapped (Path i Nat (suc zero) (suc zero))
  (app (app (app (app (app (app cong Nat) Nat) (lam n (suc n)))
    zero) zero) joined))
(def mapped-left Nat (at mapped 0))
(def mapped-right Nat (at mapped 1))
"#
    );
    for optimized in [true, false] {
        let options = Options {
            optimized,
            ..Options::default()
        };
        let program = CheckedProgram::check_with(&source, options).unwrap();
        for name in ["mapped-left", "mapped-right"] {
            assert_eq!(
                program.normalize_with(name, options).unwrap().text,
                "(suc zero)",
                "{name}, optimized={optimized}"
            );
        }
        let invalid = format!(
            "{}\n(def bool-is-prop (app isProp Bool) (lam x (lam y (path i x))))",
            include_str!("../examples/foundations.kamo")
        );
        let error = CheckedProgram::check_with(&invalid, options).unwrap_err();
        assert!(error.message.contains("endpoint"), "{error}");
    }
}
#[test]
fn rejects_bad_endpoints() {
    rejects(
        "(def bad (Path i Bool true false) (path i true))",
        "endpoint",
    );
}
#[test]
fn rejects_composition_cap() {
    rejects("(def bad Bool (com i Bool 0 1 true ((top false))))", "cap");
}
#[test]
fn rejects_noncovering_system() {
    rejects(
        "(def bad (Path i Bool true true) (path i (system Bool (((or (= i 0) (= i 1)) true)))))",
        "cover",
    );
}
#[test]
fn rejects_overlapping_system() {
    rejects(
        "(def bad Bool (system Bool ((top true) (top false))))",
        "overlap",
    );
}
#[test]
fn no_postulates_or_general_recursion() {
    rejects("(def loop Bool loop)", "unknown name");
    rejects("(axiom ua (U 0))", "expected (def");
    rejects(
        "(def x (U 0) (Glue Bool ((top Bool true))))",
        "type mismatch",
    );
}
#[test]
fn higher_order_and_shadowing() {
    let s = "(def f (Pi A (U 0) (Pi x A (Pi y A A))) (lam A (lam x (lam y x))))
        (def x Bool (app (app (app f Bool) true) false))
        (def shadow (Pi x Bool (Pi x Bool Bool)) (lam x (lam x x)))";
    assert_eq!(nf(s, "x"), "true");
    assert_eq!(nf(s, "shadow"), "(lam x0 (lam x1 x1))");
}
#[test]
fn dependent_eliminators() {
    let s = "(def family (Pi b Bool (U 0)) (lam b (bool-elim (lam _ (U 0)) Nat Bool b)))
        (def f (Pi b Bool (app family b)) (lam b (bool-elim family zero false b)))
        (def a Nat (app f true)) (def b Bool (app f false))";
    assert_eq!(nf(s, "a"), "zero");
    assert_eq!(nf(s, "b"), "false");
}
#[test]
fn eta_functions_pairs_and_paths() {
    let s="(def fun (Pi f (Pi x Bool Bool) (Path i (Pi x Bool Bool) f (lam x (app f x)))) (lam f (path i f)))
    (def pair-eta (Pi p (Sigma x Bool Bool) (Path i (Sigma x Bool Bool) p (pair (fst p) (snd p)))) (lam p (path i p)))
    (def path-eta (Pi p (Path i Bool true true) (Path j (Path i Bool true true) p (path i (at p i)))) (lam p (path j p)))";
    CheckedProgram::check(s).unwrap();
}
#[test]
fn neutral_path_endpoint() {
    let s = "(def f (Pi p (Path i Bool true true) Bool) (lam p (at p 0)))";
    assert_eq!(nf(s, "f"), "(lam x0 true)");
}
#[test]
fn force_under_stronger_face() {
    // The open path is neutral globally, but its endpoints compute in each tube.
    let s = "(def f (Pi p (Path j Bool true false) (Path i Bool (at p 0) (at p 1)))
      (lam p (path i (com j Bool 0 1 (at p i) (((= i 0) true) ((= i 1) false))))))";
    CheckedProgram::check(s).unwrap();
}
#[test]
fn interval_shadowing() {
    let s="(def square (Path i (Path j Bool true true) (path j true) (path j true)) (path i (path i true)))
      (def b Bool (at (at square 0) 1))";
    assert_eq!(nf(s, "b"), "true");
}
#[test]
fn transport_dependent_pair() {
    let s = "(def p (Sigma A (U 0) A) (pair Bool true))
      (def q (Sigma A (U 0) A) (coe i (Sigma A (U 0) A) 0 0 p))
      (def x Bool (snd q))";
    assert_eq!(nf(s, "x"), "true");
}
#[test]
fn arena_sessions_are_independent() {
    let p = CheckedProgram::check(include_str!("../examples/core.kamo")).unwrap();
    for _ in 0..20 {
        assert_eq!(
            p.normalize("four").unwrap().text,
            "(suc (suc (suc (suc zero))))"
        );
        assert_eq!(p.normalize("unpack").unwrap().text, "true");
    }
}
#[test]
fn budgets_fail_explicitly() {
    let p = CheckedProgram::check("(def a Bool true)").unwrap();
    let e = p
        .normalize_with(
            "a",
            Options {
                fuel: 1,
                optimized: true,
                ..Options::default()
            },
        )
        .unwrap_err();
    assert!(e.message.contains("budget exhausted"));
}
#[test]
fn source_locations() {
    let s = "; comment\n(def x Bool mystery)";
    let e = CheckedProgram::check(s).unwrap_err();
    assert!(e.render("test.kamo", s).starts_with("test.kamo:2:13:"));
}
#[test]
fn optimized_and_reference_examples_agree() {
    let p = CheckedProgram::check(include_str!("../examples/core.kamo")).unwrap();
    for name in p.names() {
        let a = p.normalize(name).unwrap();
        let b = p
            .normalize_with(
                name,
                Options {
                    optimized: false,
                    ..Options::default()
                },
            )
            .unwrap();
        assert_eq!(a.text, b.text, "{name}");
    }
}
#[test]
fn generated_transport_chains_agree() {
    for depth in 0..24 {
        let mut term = "true".to_string();
        for _ in 0..depth {
            term = format!("(coe i Bool 0 1 {term})");
        }
        let src = format!("(def a Bool {term})");
        let p = CheckedProgram::check(&src).unwrap();
        for optimized in [false, true] {
            assert_eq!(
                p.normalize_with(
                    "a",
                    Options {
                        optimized,
                        ..Options::default()
                    }
                )
                .unwrap()
                .text,
                "true"
            );
        }
    }
}
#[test]
fn universe_computation_is_not_faked() {
    let p = CheckedProgram::check("(def a (U 0) (coe i (U 0) 0 1 Bool))").unwrap();
    assert_eq!(p.normalize("a").unwrap().text, "(Glue Bool ())");
}

const UNIVALENCE: &str = include_str!("../examples/univalence.kamo");
#[test]
fn full_univalence_theorem_is_checked() {
    let p = CheckedProgram::check(UNIVALENCE).unwrap();
    assert!(p.names().any(|n| n == "univalence"));
    for (name, expected) in [
        ("identity-transport", "true"),
        ("neg-true", "false"),
        ("neg-false", "true"),
        ("neg-inverse", "false"),
        ("neg-twice", "true"),
    ] {
        for optimized in [false, true] {
            assert_eq!(
                p.normalize_with(
                    name,
                    Options {
                        optimized,
                        ..Options::default()
                    }
                )
                .unwrap()
                .text,
                expected,
                "{name}, optimized={optimized}"
            );
        }
    }
}
#[test]
fn invalid_equivalence_is_rejected() {
    rejects(
        "(def bad (U 0) (Glue Bool ((top Bool (pair (lam x true) true)))))",
        "type mismatch",
    );
    let source = UNIVALENCE.replace("(def neg-equiv", "(def broken-neg-equiv");
    rejects(&source, "unknown name 'neg-equiv'");
    // A correctly typed forward function alone is insufficient: the fiber
    // center must have a path from its image to the supplied target.
    let source = format!(
        "{UNIVALENCE}\n(def bad (app (app Equiv Bool) Bool) (pair (lam x true) (lam b (pair (pair true (path i true)) (lam h (path i h))))))"
    );
    rejects(&source, "endpoint");
}
#[test]
fn glue_introduction_boundaries() {
    let prefix = include_str!("../examples/prelude.kamo");
    let bad = format!(
        "{prefix}\n(def bad Bool (glue (Glue Bool ((top Bool (app id-equiv Bool)))) true ((top false))))"
    );
    rejects(&bad, "image disagrees");
    let bad = format!(
        "{prefix}\n(def bad Bool (glue (Glue Bool ((top Bool (app id-equiv Bool)))) true ()))"
    );
    rejects(&bad, "do not cover");
    let good =
        format!("{prefix}\n(def good Bool (unglue (Glue Bool ()) (glue (Glue Bool ()) true ())))");
    assert_eq!(nf(&good, "good"), "true");
}
#[test]
fn universe_composition_and_nested_glue() {
    let s = "(def G (U 0) (coe i (U 0) 0 1 Bool))
      (def a G (glue G true ()))
      (def b Bool (unglue G (coe i G 0 1 a)))
      (def H (U 0) (Glue G ()))
      (def c H (glue H a ()))
      (def d Bool (unglue G (unglue H (coe i H 0 1 c))))";
    assert_eq!(nf(s, "b"), "true");
    assert_eq!(nf(s, "d"), "true");
}

#[test]
fn computed_glue_annotations_survive_endpoint_restriction() {
    let source = "(def p (Path i Bool true true)
      (path i (unglue (coe k (U 0) 0 i Bool)
        (glue (coe k (U 0) 0 i Bool) true (((= i 0) true))))))
      (def left Bool (at p 0)) (def right Bool (at p 1))";
    let p = CheckedProgram::check(source).unwrap();
    for name in ["left", "right"] {
        for optimized in [false, true] {
            assert_eq!(
                p.normalize_with(
                    name,
                    Options {
                        optimized,
                        ..Options::default()
                    }
                )
                .unwrap()
                .text,
                "true"
            );
        }
    }
}
#[test]
fn dependent_function_and_pair_transport() {
    let extra = "
      (def moved-f (Pi b Bool (Sigma y Bool (Path j Bool y y)))
        (coe i (Pi b Bool (Sigma y (at neg-path i) (Path j (at neg-path i) y y)))
          0 1 (lam b (pair b (path j b)))))
      (def result-f Bool (fst (app moved-f true)))
      (def moved-p (Sigma y Bool (Path j Bool y y))
        (coe i (Sigma y (at neg-path i) (Path j (at neg-path i) y y))
          0 1 (pair true (path j true))))
      (def result-p Bool (fst moved-p))";
    let p = CheckedProgram::check(&format!("{UNIVALENCE}{extra}")).unwrap();
    for name in ["result-f", "result-p"] {
        for optimized in [true, false] {
            assert_eq!(
                p.normalize_with(
                    name,
                    Options {
                        optimized,
                        ..Options::default()
                    }
                )
                .unwrap()
                .text,
                "false"
            );
        }
    }
}
#[test]
fn node_budget_is_reported_as_resource_exhaustion() {
    let error = CheckedProgram::check_with(
        "(def id (Pi b Bool Bool) (lam b b))",
        Options {
            max_nodes: 4,
            ..Options::default()
        },
    )
    .unwrap_err();
    assert!(error.message.contains("node budget exhausted"), "{error}");
    let p = CheckedProgram::check("(def id (Pi b Bool Bool) (lam b b))").unwrap();
    assert!(
        p.normalize_with(
            "id",
            Options {
                max_nodes: 4,
                ..Options::default()
            }
        )
        .is_err()
    );
}
#[test]
fn generated_boolean_programs_match_an_independent_oracle() {
    let mut src = UNIVALENCE.to_owned();
    let mut expected = true;
    for n in 0..24 {
        let prev = if n == 0 {
            "true".into()
        } else {
            format!("v{}", n - 1)
        };
        let body = match n % 4 {
            0 => {
                expected = !expected;
                format!("(coe i (at neg-path i) 0 1 {prev})")
            }
            1 => {
                expected = !expected;
                format!("(app not {prev})")
            }
            2 => format!("(coe i Bool 0 1 {prev})"),
            _ => {
                expected = !expected;
                format!("(bool-elim (lam b Bool) false true {prev})")
            }
        };
        src.push_str(&format!("\n(def v{n} Bool {body})"));
        let p = CheckedProgram::check(&src).unwrap();
        for optimized in [false, true] {
            assert_eq!(
                p.normalize_with(
                    &format!("v{n}"),
                    Options {
                        optimized,
                        ..Options::default()
                    }
                )
                .unwrap()
                .text,
                expected.to_string()
            );
        }
    }
}

#[test]
fn deep_natural_quotation_uses_a_bounded_stack() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let mut source = String::from("(def n0 Nat zero)\n");
            for i in 1..=30_000 {
                source.push_str(&format!("(def n{i} Nat (suc n{}))\n", i - 1));
            }
            let p = CheckedProgram::check(&source).unwrap();
            let expected = format!("{}zero{}", "(suc ".repeat(30_000), ")".repeat(30_000));
            for optimized in [false, true] {
                assert_eq!(
                    p.normalize_with(
                        "n30000",
                        Options {
                            optimized,
                            ..Options::default()
                        }
                    )
                    .unwrap()
                    .text,
                    expected
                );
            }
            assert_eq!(p.normalize("n0").unwrap().text, "zero");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn deep_structural_quotation_returns_a_resource_error() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let mut source = String::from("(def T0 (U 0) Bool)\n(def v0 T0 true)\n");
            for i in 1..=100 {
                source.push_str(&format!(
                    "(def T{i} (U 0) (Sigma x Bool T{}))\n(def v{i} T{i} (pair true v{}))\n",
                    i - 1,
                    i - 1
                ));
            }
            let p = CheckedProgram::check(&source).unwrap();
            for optimized in [false, true] {
                let error = p
                    .normalize_with(
                        "v100",
                        Options {
                            optimized,
                            ..Options::default()
                        },
                    )
                    .unwrap_err();
                assert!(
                    error.message.contains("quotation depth budget exhausted"),
                    "{error}"
                );
            }
            assert_eq!(p.normalize("v0").unwrap().text, "true");
        })
        .unwrap()
        .join()
        .unwrap();
}
