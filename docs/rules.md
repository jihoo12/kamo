# Rule correspondence and implementation boundary

Specification: Angiuli, Brunerie, Coquand, Harper, Hou (Favonia), and Licata,
[Syntax and Models of Cartesian Cubical Type Theory](https://www.cs.cmu.edu/~rwh/papers/ccctt/preprint.pdf).
Section numbers below refer to that manuscript.

| Reference | Implementation |
| --- | --- |
| §§2.2–2.6: contexts, faces, substitution, equality | Separate term/interval environments and face assumptions; de Bruijn indices in syntax; unique semantic levels; exact positive equality reasoning subject to explicit resource limits |
| §2.7: composition and filling | `com`, with source/target equality and tube boundary reductions; `coe` is empty-tube composition; fillers compose to a fresh dimension |
| §2.8: dependent pairs | Dependent formation, beta/eta; composition transports the second component over the filler of the first |
| §2.9: dependent functions | Dependent formation, beta/eta; composition uses a backward filler for arguments |
| §2.10: dependent paths | Endpoint checking and reduction, path eta, composition with the two endpoint faces added |
| §2.11: Glue | Contractible-fiber equivalences, checked introduction boundaries and overlaps, unglue beta, Glue eta, weak introduction and extension of partial fiber data, followed by alignment using universally quantified faces |
| §2.12: universes | Numeric Russell universes, Glue-based universe composition, identity fiber contraction, and equivalence witnesses obtained by transporting identity-equivalence proofs |
| §§2.13–2.14: strict data | Booleans/naturals and dependent eliminators; constructor-directed composition, using the decidable-checking alternative described for Booleans, extended recursively to naturals |

We do **not** implement Boolean or natural-number equality reflection. Empty
Glue is not definitionally collapsed to its base type, and transport in an
arbitrary constant type is not given an extra regularity rule. These shortcuts
would change the specified judgmental equality. Composition across neutral
types can remain blocked until substitution or stronger face assumptions expose
a reducible head.

## Computational univalence

The library uses the ordinary definition

```
Fiber f b = Sigma a A (Path i B (f a) b)
Contr A   = Sigma center A (Pi point A (Path i A center point))
Equiv A B = Sigma f (Pi a A B) (Pi b B (Contr (Fiber f b)))
```

`ua` is a Glue path with the supplied equivalence at the first endpoint and
the identity equivalence at the second. It is an ordinary definition, not a
kernel primitive. Boolean negation's equivalence witness is proved by filling
its fibers using the two involution homotopies.

The full theorem proceeds by proving contractibility of `Sigma A (U 0)
(Equiv A B)`, using the equivalence of `unglue`. It obtains a decoding path,
proves a section by dependent composition, and proves a retraction by singleton
path induction. The checked isomorphism-to-equivalence lemma then constructs a
contractible-fiber witness for the canonical map.

Two formulations are named explicitly:

- `transport-equiv`: its forward function is transport along a universe path.
- `path-to-equiv`: the canonical map defined by transporting the identity
  equivalence backwards in the domain family `Equiv (p i) B`.

`univalence` proves that **`path-to-equiv` is an equivalence**, with domain
`Path i (U 0) A B` and codomain `Equiv A B`. This domain is in `U 1`, which is why
the explicit library has a mixed-level `Equiv10` definition. The implementation
does not silently equate universe levels.

The geometric isomorphism and equivalence-extension constructions also follow
the standard methods illustrated in the Cubical Agda library's
[Isomorphism](https://github.com/agda/cubical/blob/master/Cubical/Foundations/Isomorphism.agda)
and [Univalence](https://github.com/agda/cubical/blob/master/Cubical/Foundations/Univalence.agda)
modules. Kamo's terms use Cartesian composition with explicit source/target
dimensions; they do not import Agda's De Morgan connections or interval reversal.

## Evaluation and allocation

The kernel uses a graph-based form of normalization by evaluation: syntax
suspensions carry explicit environments, and semantic binders carry unique
levels and delayed substitutions. Beta reduction instantiates binders without
substituting through source syntax. Values, environments, substitutions, and
faces have separate typed arena IDs. Public checked programs retain only syntax.

Optimized substitution composition builds a graph; it does not eagerly copy
the images of every earlier substitution. Forcing pushes substitutions only as
needed. Interning and unfolding caches preserve sharing. A bounded congruence
check exposes ordinary beta redexes before expanding Kan operations, avoiding
large expansions when the same computation occurs on both sides of an equality.
Failure of that shortcut falls through to typed conversion.

Reduction caches are keyed by value, face context, and whether the caller needs
the underlying Glue data. Glue composition retains its exposed type data:
re-evaluating the original type after substitution could otherwise lose that
data by reducing to a boundary type. Caches and semantic arenas are discarded
between declarations and between normalization calls.

Face nodes are shared. Entailment compares normalized disjunctions of equality
partitions, checking transitivity and the inconsistency of `0 = 1`. A generic
fresh dimension, rather than endpoint enumeration, implements universal face
quantification. Intermediate expansion and solver caches are bounded.

The performance-oriented [cctt notes](https://github.com/AndrasKovacs/cctt)
motivated delayed substitution and demand-driven computation. Kamo does not
adopt its restriction on disjunctive systems or its closed-evaluation shortcuts
that require a different canonicity invariant.

## What the checks establish

Tests validate the complete library theorem, concrete transports, invalid
boundaries/equivalences/universes, capture avoidance, substitution composition,
context-sensitive cache behavior, arena disposal, and resource errors. Generated
Boolean computations are also compared with an independent Boolean oracle.
Optimized and reference execution are compared on computation examples.

The two execution modes share the mathematical reduction code. Their agreement
does not independently validate those rules. Native semantic expansions of
derived constructions remain part of the trusted implementation; the identity
fiber construction is additionally compared against its checked library term.
Passing the library is evidence about this implementation, not a mechanized
proof of kernel soundness or normalization. Resource-bounded conversion may
report an inconclusive result for a valid term.
