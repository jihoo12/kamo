use kamo::{CheckedProgram, Options};

fn functor_source() -> String {
    format!(
        "{}\n{}\n{}",
        include_str!("../examples/foundations.kamo"),
        include_str!("../examples/category.kamo"),
        include_str!("../examples/functor.kamo")
    )
}

#[test]
fn set_functors_compute_and_preserve_category_laws() {
    let source = format!(
        "{}\n{}",
        functor_source(),
        r#"
(def mapped-id-proof
  (Path
    i
    Unit
    (app
      (app
        (app (app (app (app functor-map two-object-category) representable-example) false) false)
        (app (app cat-id two-object-category) false))
      unit)
    unit)
  (app (app (app (app functor-id two-object-category) representable-example) false) unit))

(def mapped-compose-proof
  (Path
    i
    Unit
    (app
      (app
        (app (app (app (app functor-map two-object-category) representable-example) true) true)
        (app
          (app (app (app (app (app cat-compose two-object-category) true) false) true) unit)
          unit))
      unit)
    (app
      (app
        (app (app (app (app functor-map two-object-category) representable-example) false) true)
        unit)
      (app
        (app
          (app (app (app (app functor-map two-object-category) representable-example) true) false)
          unit)
        unit)))
  (app
    (app
      (app
        (app
          (app
            (app (app (app functor-compose two-object-category) representable-example) true)
            false)
          true)
        unit)
      unit)
    unit))

(def mapped-id-0 Bool (fst (at mapped-id-proof 0)))

(def mapped-id-1 Bool (fst (at mapped-id-proof 1)))

(def mapped-compose-0 Bool (fst (at mapped-compose-proof 0)))

(def mapped-compose-1 Bool (fst (at mapped-compose-proof 1)))

(def underlying-action
  (Pi O (U 0)
    (Pi values (Pi a O (U 0))
      (Pi sets (Pi a O (app isSet (app values a)))
        (Pi a O
          (Pi b O
            (Pi f (Pi x (app values a) (app values b))
              (Pi x (app values a)
                (Path
                  i
                  (app values b)
                  (app
                    (app
                      (app
                        (app
                          (app
                            (app functor-map (app (app (app function-category O) values) sets))
                            (app (app (app underlying-set-functor O) values) sets))
                          a)
                        b)
                      f)
                    x)
                  (app f x)))))))))
  (lam O (lam values (lam sets (lam a (lam b (lam f (lam x (path i (app f x))))))))))

(def representable-at-identity
  (Pi C Category
    (Pi r (app cat-objects C)
      (Pi a (app cat-objects C)
        (Pi f (app (app (app cat-hom C) r) a)
          (Path
            i
            (app (app (app cat-hom C) r) a)
            (app
              (app (app (app (app (app functor-map C) (app (app representable C) r)) r) a) f)
              (app (app cat-id C) r))
            f)))))
  (lam C (lam r (lam a (lam f (app (app (app (app cat-id-right C) r) a) f))))))
"#
    );
    for optimized in [true, false] {
        let options = Options {
            optimized,
            ..Options::default()
        };
        let program = CheckedProgram::check_with(&source, options).unwrap();
        for name in [
            "representable-result",
            "constant-result",
            "mapped-id-0",
            "mapped-id-1",
            "mapped-compose-0",
            "mapped-compose-1",
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
fn set_functors_reject_invalid_laws_and_set_proofs() {
    let cases = [
        (
            "bad-identity",
            r#"
(def bad-identity
  (Pi C Category (Pi A (U 0) (Pi set-A (app isSet A) (Pi center A (app SetFunctor C)))))
  (lam C
    (lam A
      (lam set-A
        (lam center
          (app
            (app
              (app
                (app (app (app make-set-functor C) (lam a A)) (lam a set-A))
                (lam a (lam b (lam f (lam x center)))))
              (lam a (lam x (path i x))))
            (lam a (lam b (lam c (lam f (lam g (lam x (path i center)))))))))))))
"#,
            "endpoint",
        ),
        (
            "bad-composition",
            r#"
(def bad-composition
  (Pi A (U 0)
    (Pi set-A (app isSet A)
      (app SetFunctor (app (app (app function-category Unit) (lam u A)) (lam u set-A)))))
  (lam A
    (lam set-A
      (app
        (app
          (app
            (app
              (app
                (app
                  make-set-functor
                  (app (app (app function-category Unit) (lam u A)) (lam u set-A)))
                (lam a A))
              (lam a set-A))
            (lam a (lam b (lam f (lam x (app f (app f x)))))))
          (lam a (lam x (path i x))))
        (lam a (lam b (lam c (lam f (lam g (lam x (path i (app g (app g (app f (app f x)))))))))))))))
"#,
            "endpoint",
        ),
        (
            "bad-set-proof",
            r#"
(def bad-set-proof
  (app SetFunctor two-object-category)
  (app
    (app
      (app
        (app (app (app make-set-functor two-object-category) (lam a Unit)) (lam a true))
        (lam a (lam b (lam f (lam x x)))))
      (lam a (lam x (path i x))))
    (lam a (lam b (lam c (lam f (lam g (lam x (path i x)))))))))
"#,
            "type mismatch",
        ),
    ];
    for optimized in [true, false] {
        let options = Options {
            optimized,
            ..Options::default()
        };
        for (name, invalid, expected) in cases {
            let source = format!("{}\n{invalid}", functor_source());
            let error = CheckedProgram::check_with(&source, options).unwrap_err();
            assert!(
                error.message.contains(name) && error.message.contains(expected),
                "{name}, optimized={optimized}: {error}"
            );
        }
    }
}
