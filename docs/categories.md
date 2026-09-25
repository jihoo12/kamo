# Small categories for Yoneda

`examples/category.kamo` depends on `examples/foundations.kamo`. Concatenate
the files in that order before checking, as shown in the README. All definitions
are ordinary checked library terms; there are no new kernel primitives or axioms.

## Representation and universes

`Category : U 1` packages the following fields with nested dependent pairs:

| Projection | Meaning |
| --- | --- |
| `cat-objects C` | Object type in `U 0` |
| `cat-hom C a b` | Type of arrows from `a` to `b`, in `U 0` |
| `cat-id C a` | Identity arrow at `a` |
| `cat-compose C a b c f g` | Composite `g ∘ f`, for `f : a → b`, `g : b → c` |
| `cat-hom-set C a b` | Proof of `isSet (cat-hom C a b)` |
| `cat-id-left C a b f` | Path from `id_b ∘ f` to `f` |
| `cat-id-right C a b f` | Path from `f ∘ id_a` to `f` |
| `cat-assoc C a b c d f g h` | Path from `h ∘ (g ∘ f)` to `(h ∘ g) ∘ f` |

Applications in this table use mathematical shorthand; source terms use nested
`app`. All object arguments are explicit. “Left” and “right” refer to the usual
`g ∘ f` notation, not the order of arguments to `cat-compose`.

`make-category` takes these eight fields in table order, with each later field's
type depending on earlier fields. It packages them as nested pairs. The final
field is the associativity proof itself, so no extra record terminator is needed.

The object type is not required to be a set, and equality of objects is not
required to coincide with isomorphism. In terminology that reserves “category”
for univalent categories, this structure is a small precategory with hom-sets.
The set-valued Yoneda lemma does not require adding category univalence.

## Checked examples

`Unit` is encoded as `Sigma b Bool (Path i Bool b true)`. Its chosen point is
`unit = (pair true (path i true))`. `unit-contract` constructs a path from this
point to every inhabitant using composition. From it, `unit-isProp` and
`unit-isSet` establish the uniqueness properties needed below.

`indiscrete-category O` has object type `O` and `Unit` as every hom type.
Identities and compositions return `unit`. The unit laws use `unit-contract`
because an arbitrary arrow need not be definitionally equal to `unit`.
`two-object-category` instantiates `O` with `Bool`. Its example composes an
arrow `true → false` with one `false → true`; `example-result` observes the
Boolean component of the resulting arrow and normalizes to `true`.

`function-category O F sets` takes a small object type `O`, a family
`F : O → U 0`, and proofs `sets : Π a, isSet (F a)`. Its arrows from `a` to `b`
are functions `F a → F b`. Composition computes to `λ x, g (f x)`; the category
laws follow by function beta/eta, and hom-set proofs use `isSetPi`.
This is an indexed family of small sets, not the category of all small sets:
the latter has an object type in `U 1` and lies outside this first universe scope.

## Small-set-valued functors

Append `examples/functor.kamo` after the foundations and category files.
`SetFunctor C : U 1` packages a covariant functor from `C` to small sets directly;
it does not require constructing a larger category of all sets.

| Projection | Meaning |
| --- | --- |
| `functor-objects C F a` | The type `F(a) : U 0` |
| `functor-sets C F a` | Proof that `F(a)` is a set |
| `functor-map C F a b f x` | `F(f)(x) : F(b)`, for `f : a → b`, `x : F(a)` |
| `functor-id C F a x` | Path from `F(id_a)(x)` to `x` |
| `functor-compose C F a b c f g x` | Path from `F(g ∘ f)(x)` to `F(g)(F(f)(x))` |

`make-set-functor` takes `C` followed by these five fields in table order.
The laws are pointwise paths, so they are immediately usable for elementwise
equational reasoning; function extensionality can turn them into function paths.
The final field is the composition proof itself.

`representable C r` implements `C(r, -)`. Its object value at `a` is `C(r, a)`;
an arrow `f : a → b` sends `h : r → a` to `f ∘ h`. Hom-set proofs come from
`cat-hom-set`. Identity preservation uses `cat-id-left`. Composition preservation
uses the reverse of `cat-assoc`, because the functor law starts at
`(g ∘ f) ∘ h`, whereas the category's associativity proof starts at `g ∘ (f ∘ h)`.
The library's `sym` reverses the path using Cartesian composition.

`constant-set-functor C A set-A` assigns `A` to every object and the identity
function to every arrow. `underlying-set-functor O values sets` acts on
`function-category O values sets`: it assigns `values a` to `a` and evaluates
each supplied function on its argument. Both prove their laws with constant paths.
The concrete `representable-result` and `constant-result` examples normalize
to `true` in the two-object category.

## Natural transformations

Append `examples/natural.kamo` after the functor file. For `F, G : SetFunctor C`,
`NatComponents C F G` is the type of families `α_a : F(a) → G(a)`.
`Naturality C F G α` states, for every `f : a → b` and `x : F(a)`,

```text
α_b(F(f)(x)) = G(f)(α_a(x)).
```

`NatTrans C F G : U 0` pairs the component family with this naturality proof.
`make-nat-trans` requires both fields; `nat-component` and `nat-naturality`
project them. All three operations take `C`, `F`, and `G` explicitly.
Although the type of functors lives in `U 1`, the transformation type between
two fixed functors lives in `U 0`.

`naturality-isProp` proves uniqueness of the naturality witness for fixed
components using the sethood of each `G(b)`. This is a local proof of uniqueness,
not a global proof-irrelevance rule.

`nat-ext C F G α β h` takes paths `h a x : α_a(x) = β_a(x)` and returns a path
from `α` to `β`. Its component path is pointwise `h`. To connect the naturality
witnesses along the changing components, it uses two foundation lemmas:

- `prop-family-path` connects specified endpoints in a proposition-valued
  family along a base path, using transport and composition.
- `sigma-path-prop` lifts a path between first components to a path between
  dependent pairs when each second-component type is a proposition.

`nat-id` is the identity transformation. `nat-compose C F G H α β` means `β`
after `α`; its naturality proof applies congruence to the first square and then
concatenates the second square. `nat-id-left`, `nat-id-right`, and `nat-assoc`
lift the component equations with `nat-ext`, proving equality of complete
transformations. `constant-nat` turns any function between small sets into a
transformation of their constant functors. The concrete `natural-result` example
normalizes to `true`.

The optimized evaluator checks this library with default budgets. Reference
evaluation reaches the default node limit while checking `nat-ext`; use
`--reference --max-nodes 1000000`. The reference tests use that node budget,
retaining the default fuel limit. A resource-limit failure is inconclusive.

## Validation and next steps

`tests/category.rs` checks both constructions in optimized and reference modes.
It verifies the composition equation for endomorphisms of an arbitrary small
set, evaluates endpoints of the projected laws, rejects arrows with incompatible
intermediate objects, and rejects a well-typed composition operation that drops
its second arrow and violates the right unit law.

`tests/functor.rs` checks all three functor constructions in both execution modes.
It checks the underlying functor's action for arbitrary indexed families and
the equation `C(r, -)(f)(id_r) = f` for an arbitrary category. It also evaluates
both endpoints of the representable functor's laws in the concrete example.
Negative tests reject a constant arrow action that violates identity preservation,
squaring endomorphisms (which preserves identity but fails composition), and
an invalid set proof.

`tests/natural.rs` checks that `nat-ext` preserves an arbitrary supplied component
path and that composition acts as `g(f(x))` for arbitrary functions between
constant functors. It evaluates endpoints of extensionality, unit, and
associativity proofs in the concrete example, and rejects both a component
family that is not natural and an attempt to identify arbitrary transformations
without valid component equalities. Both execution modes are exercised.

Next comes the Yoneda correspondence itself: evaluate a transformation
`C(r, -) → F` at `id_r`, construct a transformation from `x : F(r)` using
`f ↦ F(f)(x)`, and prove the two inverse laws. `nat-ext` supplies the final step
from pointwise equality to equality of transformations.
