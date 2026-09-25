use kamo::{CheckedProgram, Options};

fn category_source() -> String {
    format!(
        "{}\n{}",
        include_str!("../examples/foundations.kamo"),
        include_str!("../examples/category.kamo")
    )
}

#[test]
fn small_categories_check_and_compose_in_order() {
    let source = format!(
        "{}\n{}",
        category_source(),
        r#"
; For any small set A, endomorphisms compose as g(f(x)).
; This checks the projected operation against an independently stated equation.
(def endomorphisms (Pi A (U 0) (Pi set-A (app isSet A) Category))
  (lam A (lam set-A
    (app (app (app function-category Unit) (lam u A)) (lam u set-A)))))
(def composition-order
  (Pi A (U 0) (Pi set-A (app isSet A)
    (Pi f (Pi x A A) (Pi g (Pi x A A)
      (Path i (Pi x A A)
        (app (app (app (app (app (app cat-compose
          (app (app endomorphisms A) set-A)) unit) unit) unit) f) g)
        (lam x (app g (app f x))))))))
  (lam A (lam set-A (lam f (lam g (path i (lam x (app g (app f x)))))))))
; Exercise both unit-law projections and the associativity projection.
(def left-unit-proof
  (Path i Unit
    (app (app (app (app (app (app cat-compose two-object-category)
      true) false) false) example-arrow) (app (app cat-id two-object-category) false))
    example-arrow)
  (app (app (app (app cat-id-left two-object-category) true) false) example-arrow))
(def right-unit-proof
  (Path i Unit
    (app (app (app (app (app (app cat-compose two-object-category)
      true) true) false) (app (app cat-id two-object-category) true)) example-arrow)
    example-arrow)
  (app (app (app (app cat-id-right two-object-category) true) false) example-arrow))
(def associativity-proof (Path i Unit unit unit)
  (app (app (app (app (app (app (app (app cat-assoc two-object-category)
    true) false) true) false) unit) unit) unit))
(def left-start Bool (fst (at left-unit-proof 0)))
(def left-end Bool (fst (at left-unit-proof 1)))
(def right-start Bool (fst (at right-unit-proof 0)))
(def right-end Bool (fst (at right-unit-proof 1)))
(def assoc-start Bool (fst (at associativity-proof 0)))
(def assoc-end Bool (fst (at associativity-proof 1)))
"#
    );
    for optimized in [true, false] {
        let options = Options {
            optimized,
            ..Options::default()
        };
        let program = CheckedProgram::check_with(&source, options).unwrap();
        for name in [
            "example-result",
            "left-start",
            "left-end",
            "right-start",
            "right-end",
            "assoc-start",
            "assoc-end",
        ] {
            assert_eq!(
                program.normalize_with(name, options).unwrap().text,
                "true",
                "{name}, optimized={optimized}"
            );
        }
    }
}

#[test]
fn categories_reject_incompatible_arrows_and_invalid_unit_laws() {
    let incompatible = format!(
        "{}\n{}",
        category_source(),
        r#"
(def incompatible
  (Pi C Category
    (Pi a (app cat-objects C) (Pi b (app cat-objects C)
      (Pi c (app cat-objects C) (Pi d (app cat-objects C)
        (Pi f (app (app (app cat-hom C) a) b)
          (Pi g (app (app (app cat-hom C) c) d)
            (app (app (app cat-hom C) a) d))))))))
  (lam C (lam a (lam b (lam c (lam d (lam f (lam g
    (app (app (app (app (app (app cat-compose C) a) b) d) f) g)))))))))
"#
    );
    // Dropping g still gives a well-typed function, but breaks the right unit law.
    let invalid_units = format!(
        "{}\n{}",
        category_source(),
        r#"
(def invalid-units (Pi A (U 0) (Pi set-A (app isSet A) Category))
  (lam A (lam set-A
    (app
      (app
        (app
          (app
            (app
              (app
                (app (app make-category Unit) (lam a (lam b (Pi x A A))))
                (lam a (lam x x)))
              (lam a (lam b (lam c (lam f (lam g f))))))
            (lam a (lam b (app (app (app isSetPi A) (lam x A)) (lam x set-A)))))
          (lam a (lam b (lam f (path i f)))))
        (lam a (lam b (lam f (path i f)))))
      (lam a (lam b (lam c (lam d (lam f (lam g (lam h (path i f))))))))))))
"#
    );
    for optimized in [true, false] {
        let options = Options {
            optimized,
            ..Options::default()
        };
        let error = CheckedProgram::check_with(&incompatible, options).unwrap_err();
        assert!(error.message.contains("type mismatch"), "{error}");
        let error = CheckedProgram::check_with(&invalid_units, options).unwrap_err();
        assert!(error.message.contains("endpoint"), "{error}");
    }
}
