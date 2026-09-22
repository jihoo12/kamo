//! Stop-the-world compaction at quotation task boundaries. All semantic roots
//! are explicit there. Syntax and dimension/term levels are never remapped.
use super::*;
#[derive(Clone, Copy)]
enum Root {
    Value(ValId),
    Env(EnvId),
    Sub(SubId),
}
impl Engine<'_> {
    pub fn should_collect(&self) -> bool {
        self.optimized
            && self.values.len() + self.envs.len() + self.subs.len() + self.faces.len()
                > self.collection_at
    }
    pub fn collect_quote(&mut self, roots: &mut [ValId], face_roots: &mut [FaceId]) {
        self.observe_arena_peak();
        let mut vs = vec![false; self.values.len()];
        let mut es = vec![false; self.envs.len()];
        let mut ss = vec![false; self.subs.len()];
        let mut work: Vec<_> = roots.iter().copied().map(Root::Value).collect();
        while let Some(r) = work.pop() {
            match r {
                Root::Value(v) => {
                    if std::mem::replace(&mut vs[v.index()], true) {
                        continue;
                    }
                    let mut vals = Vec::new();
                    match self.values.get(v) {
                        Val::Susp(_, e) => work.push(Root::Env(*e)),
                        Val::Sub(v, s) => {
                            vals.push(*v);
                            work.push(Root::Sub(*s));
                        }
                        Val::Var(_, t) => vals.extend(t),
                        Val::Pi(a, b) | Val::Sigma(a, b) => vals.extend([*a, b.body]),
                        Val::Lam(b) | Val::PLam(b) => vals.push(b.body),
                        Val::Path(b, l, r) => vals.extend([b.body, *l, *r]),
                        Val::App(a, b) | Val::Pair(a, b) | Val::Unglue(a, b) => {
                            vals.extend([*a, *b])
                        }
                        Val::Fst(v) | Val::Snd(v) | Val::Suc(v) | Val::PApp(v, _) => vals.push(*v),
                        Val::If(p, a, b, c) | Val::NatElim(p, a, b, c) => {
                            vals.extend([*p, *a, *b, *c])
                        }
                        Val::Com(c) => {
                            vals.extend([c.family, c.cap]);
                            vals.extend(c.tubes.iter().map(|(_, v)| *v));
                        }
                        Val::System(a, bs) | Val::GlueIntro(a, bs) => {
                            vals.push(*a);
                            vals.extend(bs.iter().map(|(_, v)| *v));
                        }
                        Val::Glue(a, bs) => {
                            vals.push(*a);
                            for (_, t, e) in bs {
                                vals.extend([*t, *e]);
                            }
                        }
                        _ => {}
                    }
                    work.extend(vals.into_iter().map(Root::Value));
                }
                Root::Env(e) => {
                    if std::mem::replace(&mut es[e.index()], true) {
                        continue;
                    }
                    work.extend(self.envs.get(e).terms.iter().copied().map(Root::Value));
                }
                Root::Sub(s) => {
                    if std::mem::replace(&mut ss[s.index()], true) {
                        continue;
                    }
                    let s = self.subs.get(s);
                    work.extend(s.terms.iter().map(|(_, v)| Root::Value(*v)));
                    if let Some((a, b)) = s.compose {
                        work.extend([Root::Sub(a), Root::Sub(b)]);
                    }
                }
            }
        }
        let old_faces = self.faces.len();
        let mut all_faces = face_roots.to_vec();
        for (i, yes) in vs.iter().enumerate() {
            if !yes {
                continue;
            }
            match self.values.get(ValId::new(i)) {
                Val::Com(c) => all_faces.extend(c.tubes.iter().map(|(f, _)| *f)),
                Val::System(_, bs) | Val::GlueIntro(_, bs) => {
                    all_faces.extend(bs.iter().map(|(f, _)| *f))
                }
                Val::Glue(_, bs) => all_faces.extend(bs.iter().map(|(f, _, _)| *f)),
                _ => {}
            }
        }
        let fm = self.faces.compact(&mut all_faces);
        face_roots.copy_from_slice(&all_faces[..face_roots.len()]);
        let face_id = |f: FaceId| FaceId::new(fm[f.index()]);
        self.reclaimed_nodes += old_faces - self.faces.len();
        fn numbering(mark: &[bool]) -> Vec<usize> {
            let mut n = 0;
            mark.iter()
                .map(|live| {
                    if *live {
                        let i = n;
                        n += 1;
                        i
                    } else {
                        usize::MAX
                    }
                })
                .collect()
        }
        let vm = numbering(&vs);
        let em = numbering(&es);
        let sm = numbering(&ss);
        let v = |id: ValId| {
            let mapped = vm[id.index()];
            assert_ne!(
                mapped,
                usize::MAX,
                "unmarked value during collection: {id:?}"
            );
            ValId::new(mapped)
        };
        let e = |id: EnvId| {
            let mapped = em[id.index()];
            assert_ne!(
                mapped,
                usize::MAX,
                "unmarked environment during collection: {id:?}"
            );
            EnvId::new(mapped)
        };
        let s = |id: SubId| {
            let mapped = sm[id.index()];
            assert_ne!(
                mapped,
                usize::MAX,
                "unmarked substitution during collection: {id:?}"
            );
            SubId::new(mapped)
        };
        let mut values = Arena::default();
        let mut envs = Arena::default();
        let mut subs = Arena::default();
        for (i, live) in vs.iter().enumerate() {
            if !live {
                continue;
            }
            let old = self.values.get(ValId::new(i));
            let binder = |b: &Binder| Binder {
                var: b.var,
                body: v(b.body),
            };
            let new = match old {
                Val::Susp(t, a) => Val::Susp(*t, e(*a)),
                Val::Sub(a, b) => Val::Sub(v(*a), s(*b)),
                Val::Var(x, t) => Val::Var(*x, t.map(v)),
                Val::Pi(a, b) => Val::Pi(v(*a), binder(b)),
                Val::Sigma(a, b) => Val::Sigma(v(*a), binder(b)),
                Val::Lam(b) => Val::Lam(binder(b)),
                Val::PLam(b) => Val::PLam(binder(b)),
                Val::Path(b, l, r) => Val::Path(binder(b), v(*l), v(*r)),
                Val::App(a, b) => Val::App(v(*a), v(*b)),
                Val::Pair(a, b) => Val::Pair(v(*a), v(*b)),
                Val::Unglue(a, b) => Val::Unglue(v(*a), v(*b)),
                Val::Fst(a) => Val::Fst(v(*a)),
                Val::Snd(a) => Val::Snd(v(*a)),
                Val::Suc(a) => Val::Suc(v(*a)),
                Val::PApp(a, d) => Val::PApp(v(*a), *d),
                Val::If(p, a, b, c) => Val::If(v(*p), v(*a), v(*b), v(*c)),
                Val::NatElim(p, a, b, c) => Val::NatElim(v(*p), v(*a), v(*b), v(*c)),
                Val::Com(c) => Val::Com(Composition {
                    family: v(c.family),
                    cap: v(c.cap),
                    tubes: c.tubes.iter().map(|(f, a)| (face_id(*f), v(*a))).collect(),
                    ..c.clone()
                }),
                Val::System(a, bs) => Val::System(
                    v(*a),
                    bs.iter().map(|(f, a)| (face_id(*f), v(*a))).collect(),
                ),
                Val::GlueIntro(a, bs) => Val::GlueIntro(
                    v(*a),
                    bs.iter().map(|(f, a)| (face_id(*f), v(*a))).collect(),
                ),
                Val::Glue(a, bs) => Val::Glue(
                    v(*a),
                    bs.iter()
                        .map(|(f, a, b)| (face_id(*f), v(*a), v(*b)))
                        .collect(),
                ),
                _ => old.clone(),
            };
            values.alloc(new);
        }
        for (i, live) in es.iter().enumerate() {
            if *live {
                let old = self.envs.get(EnvId::new(i));
                envs.alloc(Env {
                    terms: old.terms.iter().copied().map(v).collect(),
                    dims: old.dims.clone(),
                });
            }
        }
        for (i, live) in ss.iter().enumerate() {
            if *live {
                let old = self.subs.get(SubId::new(i));
                subs.alloc(Sub {
                    terms: old.terms.iter().map(|(x, a)| (*x, v(*a))).collect(),
                    dims: old.dims.clone(),
                    compose: old.compose.map(|(a, b)| (s(a), s(b))),
                });
            }
        }
        for root in roots {
            *root = v(*root);
        }
        self.reclaimed_nodes += self.values.len() + self.envs.len() + self.subs.len()
            - values.len()
            - envs.len()
            - subs.len();
        self.collections += 1;
        self.collection_at = ((values.len() + envs.len() + subs.len() + self.faces.len()) * 2)
            .max((self.max_nodes / 2).clamp(1, 250_000));
        self.cache = self
            .cache
            .iter()
            .filter(|((a, f, _), b)| vs[a.index()] && vs[b.index()] && fm[f.index()] != usize::MAX)
            .map(|((a, f, g), b)| ((v(*a), face_id(*f), *g), v(*b)))
            .collect();
        self.globals = self
            .globals
            .iter()
            .filter(|(_, a)| vs[a.index()])
            .map(|(i, a)| (*i, v(*a)))
            .collect();
        self.sub_cache = self
            .sub_cache
            .iter()
            .filter(|((a, b), c)| vs[a.index()] && ss[b.index()] && vs[c.index()])
            .map(|((a, b), c)| ((v(*a), s(*b)), v(*c)))
            .collect();
        self.push_cache = self
            .push_cache
            .iter()
            .filter(|((a, b), c)| vs[a.index()] && ss[b.index()] && vs[c.index()])
            .map(|((a, b), c)| ((v(*a), s(*b)), v(*c)))
            .collect();
        self.unfold_cache = self
            .unfold_cache
            .iter()
            .filter(|((_, a), b)| es[a.index()] && vs[b.index()])
            .map(|((t, a), b)| ((*t, e(*a)), v(*b)))
            .collect();

        self.identity_cache = self
            .identity_cache
            .iter()
            .filter(|(a, b)| vs[a.index()] && vs[b.index()])
            .map(|(a, b)| (v(*a), v(*b)))
            .collect();
        self.contr_cache = self
            .contr_cache
            .iter()
            .filter(|(a, b)| vs[a.index()] && vs[b.index()])
            .map(|(a, b)| (v(*a), v(*b)))
            .collect();
        self.equiv_cache = self
            .equiv_cache
            .iter()
            .filter(|((a, b), c)| vs[a.index()] && vs[b.index()] && vs[c.index()])
            .map(|((a, b), c)| ((v(*a), v(*b)), v(*c)))
            .collect();
        self.isequiv_cache = self
            .isequiv_cache
            .iter()
            .filter(|((a, b, c), d)| {
                vs[a.index()] && vs[b.index()] && vs[c.index()] && vs[d.index()]
            })
            .map(|((a, b, c), d)| ((v(*a), v(*b), v(*c)), v(*d)))
            .collect();
        self.fiber_cache = self
            .fiber_cache
            .iter()
            .filter(|((a, b, c, d), e)| {
                vs[a.index()] && vs[b.index()] && vs[c.index()] && vs[d.index()] && vs[e.index()]
            })
            .map(|((a, b, c, d), e)| ((v(*a), v(*b), v(*c), v(*d)), v(*e)))
            .collect();
        self.values = values;
        self.envs = envs;
        self.subs = subs;
        self.support_cache = self
            .support_cache
            .iter()
            .filter(|(a, _)| vs[a.index()])
            .map(|(a, support)| (v(*a), support.clone()))
            .collect();
        self.value_intern.clear();
        self.env_intern.clear();
        self.sub_intern.clear();
        for i in 0..self.values.len() {
            let id = ValId::new(i);
            self.value_intern.insert(self.get(id), id);
        }
        for i in 0..self.envs.len() {
            let id = EnvId::new(i);
            self.env_intern.insert(self.environment(id), id);
        }
        for i in 0..self.subs.len() {
            let id = SubId::new(i);
            self.sub_intern.insert(self.subs.get(id).clone(), id);
        }
    }
}
