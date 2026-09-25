use kamo::{CheckedProgram, Options};

fn natural_source() -> String {
    format!(
        "{}\n{}\n{}\n{}",
        include_str!("../examples/foundations.kamo"),
        include_str!("../examples/category.kamo"),
        include_str!("../examples/functor.kamo"),
        include_str!("../examples/natural.kamo")
    )
}

// Reference evaluation expands the dependent-pair path proof without sharing.
// Raise only its node limit; optimized checks keep all default budgets.
fn natural_options(optimized: bool) -> Options {
    let mut options = Options {
        optimized,
        ..Options::default()
    };
    if !optimized {
        options.max_nodes = 1_000_000;
    }
    options
}

#[test]
fn natural_transformations_compose_and_lift_component_paths() {
    let source = format!(
        "{}\n{}",
        natural_source(),
        r#"
(def ext-preserves-components
  (Pi C Category
    (Pi F (app SetFunctor C)
      (Pi G (app SetFunctor C)
        (Pi alpha (app (app (app NatTrans C) F) G)
          (Pi beta (app (app (app NatTrans C) F) G)
            (Pi h
              (Pi a (app cat-objects C)
                (Pi x (app (app (app functor-objects C) F) a)
                  (Path
                    i
                    (app (app (app functor-objects C) G) a)
                    (app (app (app (app (app (app nat-component C) F) G) alpha) a) x)
                    (app (app (app (app (app (app nat-component C) F) G) beta) a) x))))
              (Pi a (app cat-objects C)
                (Pi x (app (app (app functor-objects C) F) a)
                  (Path
                    j
                    (Path
                      i
                      (app (app (app functor-objects C) G) a)
                      (app (app (app (app (app (app nat-component C) F) G) alpha) a) x)
                      (app (app (app (app (app (app nat-component C) F) G) beta) a) x))
                    (path i
                      (app
                        (app
                          (app
                            (app (app (app nat-component C) F) G)
                            (at (app (app (app (app (app (app nat-ext C) F) G) alpha) beta) h) i))
                          a)
                        x))
                    (app (app h a) x))))))))))
  (lam C (lam F (lam G (lam alpha (lam beta (lam h (lam a (lam x (path j (app (app h a) x)))))))))))

(def example-ext
  (Path
    i
    (app (app (app NatTrans two-object-category) constant-example) constant-example)
    natural-example
    (app (app nat-id two-object-category) constant-example))
  (app
    (app
      (app
        (app (app (app nat-ext two-object-category) constant-example) constant-example)
        natural-example)
      (app (app nat-id two-object-category) constant-example))
    (lam a (lam x (app unit-contract x)))))

(def example-left-unit
  (Path
    i
    (app (app (app NatTrans two-object-category) constant-example) constant-example)
    natural-composite
    natural-example)
  (app
    (app (app (app nat-id-left two-object-category) constant-example) constant-example)
    natural-example))

(def example-right-unit
  (Path
    i
    (app (app (app NatTrans two-object-category) constant-example) constant-example)
    (app
      (app
        (app
          (app (app (app nat-compose two-object-category) constant-example) constant-example)
          constant-example)
        (app (app nat-id two-object-category) constant-example))
      natural-example)
    natural-example)
  (app
    (app (app (app nat-id-right two-object-category) constant-example) constant-example)
    natural-example))

(def example-assoc
  (Path
    i
    (app (app (app NatTrans two-object-category) constant-example) constant-example)
    (app
      (app
        (app
          (app (app (app nat-compose two-object-category) constant-example) constant-example)
          constant-example)
        (app
          (app
            (app
              (app (app (app nat-compose two-object-category) constant-example) constant-example)
              constant-example)
            natural-example)
          natural-example))
      natural-example)
    (app
      (app
        (app
          (app (app (app nat-compose two-object-category) constant-example) constant-example)
          constant-example)
        natural-example)
      (app
        (app
          (app
            (app (app (app nat-compose two-object-category) constant-example) constant-example)
            constant-example)
          natural-example)
        natural-example)))
  (app
    (app
      (app
        (app
          (app
            (app (app (app nat-assoc two-object-category) constant-example) constant-example)
            constant-example)
          constant-example)
        natural-example)
      natural-example)
    natural-example))

(def example-ext-0
  Bool
  (fst
    (app
      (app
        (app
          (app (app (app nat-component two-object-category) constant-example) constant-example)
          (at example-ext 0))
        true)
      unit)))

(def example-ext-1
  Bool
  (fst
    (app
      (app
        (app
          (app (app (app nat-component two-object-category) constant-example) constant-example)
          (at example-ext 1))
        true)
      unit)))

(def example-left-unit-0
  Bool
  (fst
    (app
      (app
        (app
          (app (app (app nat-component two-object-category) constant-example) constant-example)
          (at example-left-unit 0))
        true)
      unit)))

(def example-left-unit-1
  Bool
  (fst
    (app
      (app
        (app
          (app (app (app nat-component two-object-category) constant-example) constant-example)
          (at example-left-unit 1))
        true)
      unit)))

(def example-right-unit-0
  Bool
  (fst
    (app
      (app
        (app
          (app (app (app nat-component two-object-category) constant-example) constant-example)
          (at example-right-unit 0))
        true)
      unit)))

(def example-right-unit-1
  Bool
  (fst
    (app
      (app
        (app
          (app (app (app nat-component two-object-category) constant-example) constant-example)
          (at example-right-unit 1))
        true)
      unit)))

(def example-assoc-0
  Bool
  (fst
    (app
      (app
        (app
          (app (app (app nat-component two-object-category) constant-example) constant-example)
          (at example-assoc 0))
        true)
      unit)))

(def example-assoc-1
  Bool
  (fst
    (app
      (app
        (app
          (app (app (app nat-component two-object-category) constant-example) constant-example)
          (at example-assoc 1))
        true)
      unit)))

(def vertical-composition-order
  (Pi A (U 0)
    (Pi set-A (app isSet A)
      (Pi f (Pi x A A)
        (Pi g (Pi x A A)
          (Pi x A
            (Path
              i
              A
              (app
                (app
                  (app
                    (app
                      (app
                        (app nat-component two-object-category)
                        (app (app (app constant-set-functor two-object-category) A) set-A))
                      (app (app (app constant-set-functor two-object-category) A) set-A))
                    (app
                      (app
                        (app
                          (app
                            (app
                              (app nat-compose two-object-category)
                              (app (app (app constant-set-functor two-object-category) A) set-A))
                            (app (app (app constant-set-functor two-object-category) A) set-A))
                          (app (app (app constant-set-functor two-object-category) A) set-A))
                        (app
                          (app
                            (app (app (app (app constant-nat two-object-category) A) A) set-A)
                            set-A)
                          f))
                      (app
                        (app
                          (app (app (app (app constant-nat two-object-category) A) A) set-A)
                          set-A)
                        g)))
                  false)
                x)
              (app g (app f x))))))))
  (lam A (lam set-A (lam f (lam g (lam x (path i (app g (app f x)))))))))
"#
    );
    for optimized in [true, false] {
        let options = natural_options(optimized);
        let program = CheckedProgram::check_with(&source, options).unwrap();
        for name in [
            "natural-result",
            "example-ext-0",
            "example-ext-1",
            "example-left-unit-0",
            "example-left-unit-1",
            "example-right-unit-0",
            "example-right-unit-1",
            "example-assoc-0",
            "example-assoc-1",
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
fn natural_transformations_require_naturality_and_component_equality() {
    let cases = [
        (
            "bad-naturality",
            r#"
(def bad-naturality
  (Pi A (U 0)
    (Pi set-A (app isSet A)
      (Pi x A
        (Pi y A
          (app
            (app
              (app NatTrans two-object-category)
              (app (app (app constant-set-functor two-object-category) A) set-A))
            (app (app (app constant-set-functor two-object-category) A) set-A))))))
  (lam A
    (lam set-A
      (lam x
        (lam y
          (app
            (app
              (app
                (app
                  (app make-nat-trans two-object-category)
                  (app (app (app constant-set-functor two-object-category) A) set-A))
                (app (app (app constant-set-functor two-object-category) A) set-A))
              (lam a (lam z (bool-elim (lam b A) x y a))))
            (lam a (lam b (lam f (lam z (path i (bool-elim (lam b A) x y b))))))))))))
"#,
        ),
        (
            "bad-extensionality",
            r#"
(def bad-extensionality
  (Pi C Category
    (Pi F (app SetFunctor C)
      (Pi G (app SetFunctor C)
        (Pi alpha (app (app (app NatTrans C) F) G)
          (Pi beta (app (app (app NatTrans C) F) G)
            (Path i (app (app (app NatTrans C) F) G) alpha beta))))))
  (lam C
    (lam F
      (lam G
        (lam alpha
          (lam beta
            (app
              (app (app (app (app (app nat-ext C) F) G) alpha) beta)
              (lam a
                (lam x (path i (app (app (app (app (app (app nat-component C) F) G) alpha) a) x)))))))))))
"#,
        ),
    ];
    for optimized in [true, false] {
        let options = natural_options(optimized);
        for (name, invalid) in cases {
            let source = format!("{}\n{invalid}", natural_source());
            let error = CheckedProgram::check_with(&source, options).unwrap_err();
            assert!(
                error.message.contains(name) && error.message.contains("endpoint"),
                "{name}, optimized={optimized}: {error}"
            );
        }
    }
}
