use kamo::{CheckedProgram,Options};

fn nf(source:&str,name:&str)->String {CheckedProgram::check(source).unwrap().normalize(name).unwrap().text}
fn rejects(source:&str,part:&str) {let e=CheckedProgram::check(source).unwrap_err();assert!(e.message.contains(part),"{e}");}

#[test] fn example_program() {
    let p=CheckedProgram::check(include_str!("../examples/core.kamo")).unwrap();
    for (name,expected) in [("not-true","false"),("not-false","true"),("four","(suc (suc (suc (suc zero))))"),("unpack","true"),("endpoint","true"),("transport-bool","true"),("transport-pair","(pair true false)"),("transport-path","(path i0 true)"),("composed","true"),("split","true")] {
        assert_eq!(p.normalize(name).unwrap().text,expected,"{name}");
    }
}
#[test] fn universe_errors() {
    rejects("(def bad (U 0) (U 0))","type mismatch");
    rejects("(def bad (U 1) Bool)","type mismatch");
    rejects("(def bad (U 4294967295) Bool)","overflow");
}
#[test] fn rejects_bad_endpoints() {rejects("(def bad (Path i Bool true false) (path i true))","endpoint");}
#[test] fn rejects_composition_cap() {rejects("(def bad Bool (com i Bool 0 1 true ((top false))))","cap");}
#[test] fn rejects_noncovering_system() {
    rejects("(def bad (Path i Bool true true) (path i (system Bool (((or (= i 0) (= i 1)) true)))))","cover");
}
#[test] fn rejects_overlapping_system() {rejects("(def bad Bool (system Bool ((top true) (top false))))","overlap");}
#[test] fn no_postulates_or_general_recursion() {
    rejects("(def loop Bool loop)","unknown name");rejects("(axiom ua (U 0))","expected (def");
    rejects("(def x (U 0) (Glue Bool ((top Bool true))))","type mismatch");
}
#[test] fn higher_order_and_shadowing() {
    let s="(def f (Pi A (U 0) (Pi x A (Pi y A A))) (lam A (lam x (lam y x))))
        (def x Bool (app (app (app f Bool) true) false))
        (def shadow (Pi x Bool (Pi x Bool Bool)) (lam x (lam x x)))";
    assert_eq!(nf(s,"x"),"true");assert_eq!(nf(s,"shadow"),"(lam x0 (lam x1 x1))");
}
#[test] fn dependent_eliminators() {
    let s="(def family (Pi b Bool (U 0)) (lam b (bool-elim (lam _ (U 0)) Nat Bool b)))
        (def f (Pi b Bool (app family b)) (lam b (bool-elim family zero false b)))
        (def a Nat (app f true)) (def b Bool (app f false))";
    assert_eq!(nf(s,"a"),"zero");assert_eq!(nf(s,"b"),"false");
}
#[test] fn eta_functions_pairs_and_paths() {
    let s="(def fun (Pi f (Pi x Bool Bool) (Path i (Pi x Bool Bool) f (lam x (app f x)))) (lam f (path i f)))
    (def pair-eta (Pi p (Sigma x Bool Bool) (Path i (Sigma x Bool Bool) p (pair (fst p) (snd p)))) (lam p (path i p)))
    (def path-eta (Pi p (Path i Bool true true) (Path j (Path i Bool true true) p (path i (at p i)))) (lam p (path j p)))";
    CheckedProgram::check(s).unwrap();
}
#[test] fn neutral_path_endpoint() {
    let s="(def f (Pi p (Path i Bool true true) Bool) (lam p (at p 0)))";
    assert_eq!(nf(s,"f"),"(lam x0 true)");
}
#[test] fn force_under_stronger_face() {
    // The open path is neutral globally, but its endpoints compute in each tube.
    let s="(def f (Pi p (Path j Bool true false) (Path i Bool (at p 0) (at p 1)))
      (lam p (path i (com j Bool 0 1 (at p i) (((= i 0) true) ((= i 1) false))))))";
    CheckedProgram::check(s).unwrap();
}
#[test] fn interval_shadowing() {
    let s="(def square (Path i (Path j Bool true true) (path j true) (path j true)) (path i (path i true)))
      (def b Bool (at (at square 0) 1))";assert_eq!(nf(s,"b"),"true");
}
#[test] fn transport_dependent_pair() {
    let s="(def p (Sigma A (U 0) A) (pair Bool true))
      (def q (Sigma A (U 0) A) (coe i (Sigma A (U 0) A) 0 0 p))
      (def x Bool (snd q))";assert_eq!(nf(s,"x"),"true");
}
#[test] fn arena_sessions_are_independent() {
    let p=CheckedProgram::check(include_str!("../examples/core.kamo")).unwrap();
    for _ in 0..20 {assert_eq!(p.normalize("four").unwrap().text,"(suc (suc (suc (suc zero))))");assert_eq!(p.normalize("unpack").unwrap().text,"true");}
}
#[test] fn budgets_fail_explicitly() {
    let p=CheckedProgram::check("(def a Bool true)").unwrap();
    let e=p.normalize_with("a",Options{fuel:1,optimized:true,..Options::default()}).unwrap_err();assert!(e.message.contains("budget exhausted"));
}
#[test] fn source_locations() {
    let s="; comment\n(def x Bool mystery)";let e=CheckedProgram::check(s).unwrap_err();assert!(e.render("test.kamo",s).starts_with("test.kamo:2:13:"));
}
#[test] fn optimized_and_reference_examples_agree() {
    let p=CheckedProgram::check(include_str!("../examples/core.kamo")).unwrap();
    for name in p.names(){let a=p.normalize(name).unwrap();let b=p.normalize_with(name,Options{optimized:false,..Options::default()}).unwrap();assert_eq!(a.text,b.text,"{name}");}
}
#[test] fn generated_transport_chains_agree() {
    for depth in 0..24 {
        let mut term="true".to_string();for _ in 0..depth{term=format!("(coe i Bool 0 1 {term})");}
        let src=format!("(def a Bool {term})");let p=CheckedProgram::check(&src).unwrap();
        for optimized in [false,true]{assert_eq!(p.normalize_with("a",Options{optimized,..Options::default()}).unwrap().text,"true");}
    }
}
#[test] fn universe_computation_is_not_faked() {
    let p=CheckedProgram::check("(def a (U 0) (coe i (U 0) 0 1 Bool))").unwrap();
    assert_eq!(p.normalize("a").unwrap().text,"(Glue Bool ())");
}
