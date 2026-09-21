// Appended to a temporary copy of src/face.rs by run-internal.sh.
#[cfg(test)]
mod audit_face_oracle {
    use super::*;
    fn eval(f: &Faces, id: FaceId, assignment: &[u8; 4]) -> bool {
        let dim = |d: Dim| match d {
            Dim::Zero => 0,
            Dim::One => 1,
            Dim::Var(i) => assignment[i as usize],
        };
        match f.nodes.get(id) {
            Face::Top => true,
            Face::Bot => false,
            Face::Eq(a, b) => dim(*a) == dim(*b),
            Face::And(a, b) => eval(f, *a, assignment) && eval(f, *b, assignment),
            Face::Or(a, b) => eval(f, *a, assignment) || eval(f, *b, assignment),
        }
    }
    #[test]
    fn entailment_and_quantification_match_finite_partition_oracle() {
        // Six colors enumerate every equality partition of four dimensions and
        // two distinct endpoints, including a fresh generic value for forall.
        let mut f = Faces::default();
        let dims = [
            Dim::Zero,
            Dim::One,
            Dim::Var(0),
            Dim::Var(1),
            Dim::Var(2),
            Dim::Var(3),
        ];
        let mut formulas = vec![f.top(), f.bot()];
        for i in 0..dims.len() {
            for j in i + 1..dims.len() {
                formulas.push(f.eq(dims[i], dims[j]));
            }
        }
        let mut seed = 17usize;
        for i in 0..80 {
            seed = seed.wrapping_mul(1664525).wrapping_add(1013904223);
            let a = formulas[seed % formulas.len()];
            seed = seed.wrapping_mul(1664525).wrapping_add(1013904223);
            let b = formulas[seed % formulas.len()];
            formulas.push(if i % 2 == 0 { f.and(a, b) } else { f.or(a, b) });
        }
        let assignments: Vec<_> = (0..1296)
            .map(|mut n| {
                let mut a = [0; 4];
                for x in &mut a {
                    *x = (n % 6) as u8;
                    n /= 6;
                }
                a
            })
            .collect();
        let tables: Vec<Vec<_>> = formulas
            .iter()
            .map(|id| assignments.iter().map(|a| eval(&f, *id, a)).collect())
            .collect();
        for (i, a) in formulas.iter().enumerate() {
            for (j, b) in formulas.iter().enumerate() {
                let expected = tables[i].iter().zip(&tables[j]).all(|(a, b)| !a || *b);
                assert_eq!(
                    f.entails(*a, *b).unwrap(),
                    expected,
                    "formula pair {i}, {j}"
                );
            }
        }
        for id in formulas {
            let quantified = f.forall(0, id).unwrap();
            for assignment in &assignments {
                let expected = (0..6).all(|value| {
                    let mut a = *assignment;
                    a[0] = value;
                    eval(&f, id, &a)
                });
                assert_eq!(eval(&f, quantified, assignment), expected);
            }
        }
    }
}
