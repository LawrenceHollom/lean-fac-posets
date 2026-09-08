# Consolidation endpoint and representative obstructions

This note records the obstructions found after Phase D and S3.E.1--S3.E.8.
Work has resumed using the principal-cut construction in
[CONSOLIDATION_LIMIT_REPAIR.md](CONSOLIDATION_LIMIT_REPAIR.md). That note also
shows why genuine global cofinality cannot be added, gives a mathematical
sequential upper-bound proof with whole-chain local-cofinality witnesses, and
identifies the remaining Lean obligations. The counterexamples below remain
valid; the new construction avoids the assertions they refute.

## The incompatible requirements

The normalized completion follows `def:h-p`: the formal top is distinct from
every genuine increasing germ, including the germ of an entire chain without
a greatest element. The formal top belongs to `N+`; the formal bottom belongs
to `N-`. They have no representative chains.

The consolidation definition (`def:cofinal-comparability` in `vacillating.tex`)
asks that a non-atomic increasing source admit a continuous, direction-preserving
order embedding `f : N(C) -> N(D)` with cofinal image, satisfying the base
consolidation relation at atomic source germs. Its claimed consequence
`lem:consolidation-is-cofinal` (S3.I.8) is

    for every y in D there is x in C with y < x.

However, any map taking the formal top to the formal top already has cofinal
image in `N(D)`. This does not control genuine germs below that formal endpoint.
The dual issue occurs for coinitial image and the formal bottom.

`Completion/CompletionAPI.lean` checks this observation directly on the public
API (`nonprincipal_cofinal_of_top`). It also checks that every admissible
completion inclusion automatically has cofinal and coinitial image, regardless
of the cofinality of the original inclusion.

## Counterexample to the claimed cofinality consequence

Take the ambient well-order

    P = D = omega^2 + omega,

and let `C` be its initial segment of type `omega^2`. These are saturated chains;
both have no greatest element. The cofinality lemma applies to saturated
representatives/germs; it does not require `C` to be maximal in `P`.
The ambient poset is countable, scattered, FAC,
and vacillating. The source germ is non-atomic: every final segment of `C`
contains `omega + 1`.

Write `a_n` for the increasing germ at the end of the nth omega-block of `C`,
and `a_infty` for the germ at the end of all of `C`. Then

    N(C): bottom < a_1 < a_2 < ... < a_infty < formal_top.

In `N(D)` there is precisely one additional genuine nonprincipal point `b`,
the increasing germ of the final omega-block (equivalently, of all of `D`):

    N(D): bottom < a_1 < a_2 < ... < a_infty < b < formal_top.

The natural inclusion sends every `a_n` and `a_infty` to itself, and sends both
formal endpoints to their corresponding formal endpoints. This map satisfies
all the stated witness conditions, when atomicity is applied to genuine
representative chains:

* It is a strict order embedding and preserves direction.
* It preserves **all** suprema and infima, which is stronger than preserving
  only nonempty bounded ones. A set containing the formal top has that maximum;
  otherwise its supremum is computed in the common initial segment ending at
  `a_infty`. Every nonempty set has a least element, so its infimum is preserved.
  Empty-set bounds are the formal endpoints and are preserved too.
* Its image is cofinal because it contains the formal top, and coinitial because
  it contains the formal bottom.
* The genuine atomic source germs are exactly the `a_n`. Each maps to itself,
  so the atomic cofinal-above clause holds by reflexivity.

But no point of `C` lies above the first point of the final omega-block of `D`.
Thus the asserted underlying cofinality fails.

There is also a failure of **representative invariance** (S3.I.7). Replace `D`
by its final omega-block `D'`, which represents exactly the same increasing germ.
Now `N(D')` has just three points: its formal bottom, its genuine increasing germ,
and its formal top. There cannot be an injective map from the infinite `N(C)`
to this three-point set. The source is still non-atomic, so the alternative
atomic-source clause cannot supply a witness. The stated raw-chain relation
therefore holds with representative `D` but fails with the equivalent `D'`.

The order-type and atomicity analysis in this section is a mathematical
counterexample, not a completed Lean formalization of atomic consolidation.
The endpoint-vacuity lemmas and all Phase D/E code already completed are checked
by Lean without additional mathematical axioms or `sorry`s.

## Where the manuscript proof fails

The proof of `lem:consolidation-is-cofinal` uses cofinal image to choose an image
point `Y > y`, then approximates its preimage by genuine atomic points. For a
point `y` in the added omega-block in this example, the only suitable image point
is the **formal top**. That point has no representative chain, and is not a
supremum of the genuine atomic source germs: their supremum is `a_infty`, which
is strictly smaller than the formal top.

## Required design decision

A possible repair is to require cofinality after deleting the formal endpoints,
or explicitly require the genuine upper germ of an increasing source to map to
the genuine upper germ of the target (and dually at a lower end). This would
exclude the counterexample. It strengthens the consolidation relation, so its
availability in the later replacement and limit constructions must be checked
before implementing it. Treating the formal top as the genuine upper germ would
instead change the completion already specified by the roadmap and manuscript.

Neither repair has been silently adopted. E.9--E.11 and the later phases remain
unchecked pending this decision. The separate intrinsic/ambient convention for
the quasifounded partition is recorded in ROADMAP.md and is not this blocker.

## Follow-up: localizing to germs does not give the required partial order

Requiring genuine cofinality is necessary, but the proposed further repair of
allowing consolidation on suitable final segments has a separate obstruction.
The following example satisfies even genuine-endpoint preservation and shows
that this localized relation is not antisymmetric on the existing germs.

For each natural number `n`, let `B_n` be the disjoint union of two copies of
`omega`, denoted `C_n` and `D_n`, with every point of `C_n` incomparable with every
point of `D_n`. Let

    P = B_0 + B_1 + B_2 + ...,

where every point of an earlier block is below every point of a later block.
This poset is countable, wellfounded, scattered, vacillating, and of width two,
hence FAC. Put

    C = C_0 + C_1 + C_2 + ...,
    D = D_0 + D_1 + D_2 + ... .

These are saturated maximal chains of type `omega^2`. Write `c_n`, `d_n` for
their genuine increasing germs at the ends of individual blocks, and `c_inf`,
`d_inf` for their genuine upper endpoints. Their endpoint-deleted nonprincipal
orders are respectively

    c_0 < c_1 < ... < c_inf,
    d_0 < d_1 < ... < d_inf.

Let `C_tail = C_1 + C_2 + ...`. The map

    c_(n+1) |-> d_n,     c_inf |-> d_inf

extends by fixing the formal endpoints to a consolidation witness from
`C_tail` to `D`, even with the strengthened endpoint requirements:

* It is a direction-preserving order isomorphism on the nonprincipal orders,
  both with and without the formal endpoints. It therefore preserves all their
  existing suprema and infima and has genuinely cofinal and coinitial image.
* It maps the genuine upper endpoint to the genuine upper endpoint.
* The atomic germs are exactly the individual block ends. Every point of
  `C_(n+1)` is above every point of `D_n`, so each atomic consolidation clause
  holds.
* Both the source and target chains have no greatest element. Their upper
  endpoints are non-atomic, so the general-witness clause applies.

Symmetrically, `D_tail = D_1 + D_2 + ...` consolidates to `C` by
`d_(n+1) |-> c_n`, with `d_inf |-> c_inf`.

Consequently, a germ relation admitting these witnesses after passage to final
segments has both

    [C]_+ consolidates to [D]_+,
    [D]_+ consolidates to [C]_+.

Nevertheless `[C]_+` and `[D]_+` are distinct. Any pair of final segments of
`C` and `D` contains both complete sides of every sufficiently late block.
Each point on either side of such a block has infinitely many incomparable
points on the other side. Thus no pair of final segments has mutually finite
incomparability.

This is also a new counterexample to raw representative invariance after the
endpoint repair: `C_tail` consolidates to `D`, but `C` does not consolidate to
`D`. The first atomic germ `c_0` has no possible atomic-clause-compatible image
in `N(D)`.

In particular, **no partial order on the existing increasing germs can both
respect all these strengthened raw witnesses and retain the existing germ
equality**. Merely defining the relation existentially over representatives
makes representative independence automatic, but loses S3.I.11--S3.I.12.

### Why the antisymmetry argument no longer applies

The manuscript iterates a composite self-embedding of one fixed `N(C)` to
produce a forbidden infinite descent. Here the composite is only defined on a
tail: after deleting two initial blocks it sends `c_(n+2)` to `c_n`. A fixed
block-end point can only be iterated finitely many times before leaving that
domain. There is no infinite descent and no contradiction with vacillation.

### Additional endpoint qualification

For a relation on arbitrary whole chains, cofinality in
`N(D) \ {formal_bottom, formal_top}` still does not by itself guarantee
cofinality towards the actual end of `D`. For example, the inclusion from
`C = omega^2` into `D = omega^2 + 1` induces an isomorphism of these
nonprincipal orders, but the last principal point of `D` is above the entire
image. This example is about saturated chains, not maximal source chains.

When the source has no greatest element, a sufficient precise condition is
that the target also has no greatest element and that the map preserve their
genuine upper endpoints; use the dual condition below. Equivalently in this
setting, require that for every principal point `d` of `D` some genuine
increasing image point lies strictly above `d`. The condition should remain
conditional on the source lacking the corresponding endpoint: finite-to-
infinite replacements used later must not be excluded automatically.

### Consequences for a repair

The endpoint correction remains appropriate. The germ-localization proposal
does **not** suffice to recover all the later machinery as currently stated.
A more promising design is to retain witnesses on the entire nonprincipal
orders of actual chains for candidate consolidation, and reserve germ-level
relations for the local properties that are needed there (in particular the
atomic base relation and directional cofinality). A candidate order may need
to quotient by equality of its full ambient nonprincipal profile; this is
different from quotienting a chain by its upper germ.

With fixed whole-chain domains, the particular iteration obstruction above
disappears. This is a proposed design, not a proved repair: antisymmetry on the
chosen candidate objects, genuine cofinality of the stable-limit witnesses,
and the final replacement witnesses still need verification. The examples and
arguments in this follow-up are mathematical proofs, not new Lean theorems.

## Whole-chain follow-up: stable germs need not survive the limit chain

Keeping whole-chain witnesses avoids the preceding tail-shift counterexample
to antisymmetry. However, a further check of S3.J.6--S3.J.11 finds a false
claim in the proposed stable-limit construction. This is a strictly increasing
sequence of candidate profiles, so quotienting away repeated profiles does not
remove the example.

For each `i : Nat`, form a block `B_i` consisting of a singleton `s_i` and a
chain `W_i` of type `omega`, with `s_i` incomparable with every point of `W_i`.
Let `P = B_0 + B_1 + ...`. Thus all points in different blocks are ordered by
their block indices. Again `P` is countable, wellfounded, scattered,
quasifounded, vacillating, out-wellfounded, and of width two. Its maximal chains
choose either the singleton or the entire omega-chain in each block.

Define maximal chains

    C_n = W_0 + ... + W_(n-1) + {s_n} + {s_(n+1)} + ...,
    E   = W_0 + W_1 + W_2 + ... .

Let `u` be the increasing germ of `{s_0 < s_1 < ...}`, and `w_i` that of `W_i`.
Every `C_n` has the same genuine upper germ `u`, because its final singleton
tail agrees with that representative of `u`. All these germs are atomic, and

    N_genuine(C_n) = {w_0 < ... < w_(n-1) < u}.

For every `n`, inclusion of these finite orders gives a whole-chain witness
from `C_n` to `C_(n+1)`: fix each existing `w_i`, fix `u`, and fix the formal
endpoints. The maps preserve direction and all existing suprema/infima (the
domains are finite), have genuine cofinal image, and preserve the genuine
upper endpoints. Every atomic clause is reflexivity. Taking `C_0` as the
starting chain, all `C_n` are candidates for the strengthened whole-chain
relation. They are alternating maximal: in this wellfounded poset every
infinite maximal chain has exactly one alternation class, and there is no
nontrivial alternating replacement of such a chain. The profiles strictly
increase, acquiring `w_n` at stage `n+1`.

The liminf of the carriers is exactly `E`: each point of `W_i` belongs to all
`C_n` for `n > i`, while `s_i` belongs to only finitely many `C_n`. Moreover,
`E` is already maximal, so there is no choice of maximal extension that can
change the outcome.

Nevertheless **`u` does not occur in `N(E)`**. Every final segment of its
singleton representative contains some `s_i` whose incomparability trace on
any sufficiently long final segment of `E` contains the infinite chain `W_i`.
The genuine upper germ `v` of `E`, of type `omega^2`, is different from `u`.
The other genuine points of `N(E)` are precisely the `w_i`.

In the manuscript's atomic transition graph, `(u,n)` lies on the constant
path `u,u,u,...`, hence is a stabilization point at every stage. Each `w_i`
also stabilizes once it appears. For the initial atomic source `u`, therefore,

    S(u) = {w_i | i : Nat} union {u}.

Since every `w_i < u` in the ambient completion, this set has maximum `u`.
The proposed formula `f(u) = sup S(u)` returns `u`, which is not a point of
`N(E)`. Thus the claim that every stabilized atomic germ belongs to the limit
chain is false, and the proposed limit map is not defined into its claimed
codomain. Interpreting the supremum intrinsically in `H(E)` does not solve this:
the summand `u` is not in that completion's ambient image in the first place.

This failure cannot be removed by selecting different representatives for the
same finite-stage profiles. In this poset those profiles determine `C_n`
uniquely: using `W_i` introduces `w_i`, while using `s_i` does not. Nor is there
any maximal chain simultaneously realizing all `w_i` and `u`.

### What the example does and does not disprove

The sequential upper-bound statement itself is not refuted by this example.
There are valid whole-chain witnesses `C_n -> E` fixing `w_i` for `i < n` and
mapping `u` to `v`. The atomic clause at `u` holds because every point of
`W_i` is below `s_(i+1)`. These witnesses have genuinely cofinal image and
preserve the relevant suprema/infima.

Thus the upper-bound witnesses must be allowed to change a germ which every
finite-stage transition fixes, and an atomic source may acquire a non-atomic
limit image. Stabilization of a germ is weaker than stabilization of its
representing intervals. The latter intervals can shrink away entirely.

One possible direction is to construct the limit images from limits of
principal cuts/representing intervals, allowing a new boundary germ to arise,
rather than from a union of all constant germ descendants. A general proof
would still have to establish simultaneous realization, strict ordering,
directional cofinality, continuity, and the atomic cofinal-above clauses. The
current argument does not provide those facts. This is a substantial missing
limit argument, not merely a choice of quotient or formal-endpoint convention.

Accordingly the whole-chain design has not been certified as a complete
repair, and implementation remains paused at the Phase E checkpoint. No new
roadmap item is marked complete on the strength of this analysis. This example
is a mathematical verification of the obstruction, not a Lean formalization.
