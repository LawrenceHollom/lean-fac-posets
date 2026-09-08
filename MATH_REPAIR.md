# Repair of Lemma 3.5 (chain equivalence)

The classwise mutual-maximality assertion in the existing proof is unnecessary.
In particular, the sentence treating finite corresponding classes must not be used
to establish maximality. Prove finite incomparability and maximality separately,
as follows. This argument uses the manuscript's definition of saturation: a point
between two chain points belongs to the chain **if it is comparable with the whole
chain**. It does not assume ambient order-convexity.

The equivalence lemma is understood on saturated chains, as required by the
subsequent definition of F(P). Its unqualified wording must not be read as a
claim about all nonsaturated chains: for example, the even natural numbers in
the usual order on N have no final segment maximal in its own convex hull, so
the stated relation is not even reflexive on that chain. Endpoint-bearing
chains are handled separately by equality of their endpoints.

## Finite-trace transfer

Suppose D and E have mutually finite incomparability. Let x be an ambient point
whose incomparability trace I on D is finite, and suppose x belongs to D or is
incomparable with some point of D. Then x is incomparable with only finitely many
points of E.

If x belongs to D this is part of the hypothesis. Otherwise I is nonempty; let
a = min I and b = max I. Every point of D below a is strictly below x, and every
point above b is strictly above x. Also [a,b] in D is contained in I.

Enlarge I by the immediate predecessor of a and the immediate successor of b,
when these exist, obtaining a finite set K. For d in K, the set of E-points equal
or incomparable to d is finite. We claim that their union contains the entire
E-incomparability trace of x.

Take e in E incomparable with x. If e belongs to D it belongs to I. Otherwise
its nonempty finite incomparability trace J on D exists by maximality of D in
Conv(D union E). If e is incomparable with any element of I, the claim already
holds. In the remaining case e is comparable with every element of I. There are
three possibilities:

* If e < a, put d = max J. Necessarily d < a. For any t in D with d < t < a,
  maximality of d in J implies e < t: t is comparable with e and t <= e would
  imply d < e. Minimality of a in I similarly implies t < x. Consequently
  e < t < x, a contradiction. Thus d is the immediate predecessor of a, and
  e is in its incomparability trace.
* If b < e, the order-dual argument makes min J the immediate successor of b.
* Otherwise a <= e <= b. Every point of J must then lie in [a,b] in D, hence
  in I, contradicting the assumption that e is comparable with all of I.

This proves the claim. It covers absent neighbors and finite boundary classes
without any classwise maximality assertion. It requires no countability, FAC,
scattering, or vacillation assumption.

## Aligning the middle segments

Write C', D1, D2, E' for witnesses to C ~+ D ~+ E. Choose a point d0 in
D1 intersection D2; two nonempty final segments of a chain always intersect.
Mutually finite-incomparable chains without greatest points are mutually cofinal:
given a point in one, pass above its finite incomparability trace and an equal or
incomparable representative in the other.

Choose c0 in C' and e0 in E' strictly above d0. Restrict provisionally to the
tails A = C'[>= c0] and B = E'[>= e0]. For x in A, every point of D2
incomparable with x belongs to D1: a point outside the final segment D1 is below
d0 < x. Thus the D2-trace is finite. An equal or incomparable D1-representative
of x also lies above d0, hence belongs to D2. Apply finite-trace transfer to
D2, E'. This proves finiteness of the B-trace of x. Interchanging the two
original witnesses proves finiteness of the A-trace of every point of B.

The tails A and B are mutually cofinal. To go from A to B, pass first to a
larger point of D1, which lies in D2 since it is above d0, then to a larger
point of E', and finally farther up E' if necessary to enter B. The reverse
argument is identical.

## Normalize just the two starting points

For any two mutually cofinal saturated chains A and B without greatest points,
there are equal or incomparable points a in A and b in B. Indeed, choose
a0 < b < a1 with a0,a1 in A and b in B. If b belongs to A, use the common
point. Otherwise saturation supplies a point of A incomparable with b.

Take the final tails A* = A[>= a] and B* = B[>= b]. They retain finite
incomparability and mutual cofinality, and are saturated. They are maximal
chains in Conv(A* union B*): let z in this hull be comparable with all of A*.
It has an upper bound in A* by mutual cofinality. Also a <= z. Otherwise
comparability gives z < a; a lower hull witness from A* contradicts this
directly, and one from B* gives b <= z < a, contradicting equality or
incomparability of a and b. Saturation between a and the upper bound now
puts z in A*. The argument for B* is symmetric.

Thus A* and B* witness C ~+ E. Reflexivity follows from saturation and
symmetry is immediate. Order duality proves the decreasing result; the case
of chains with greatest/least points remains equality of those endpoints.

This replaces the transitivity proof in full, so the quotient constructions
need neither a strengthened relation nor its equivalence closure. The earlier
finite-distance class isomorphism and its endpoint properties remain available
unchanged. No LaTeX file has been edited.

## Formalisation fidelity

The existing Lean definition `IsSaturatedChain C := IsChain C and C.OrdConnected`
is stronger than the manuscript's definition (a maximal chain through a diamond
is a basic counterexample). It must be corrected before claiming a formal proof
of the manuscript. In a linear ambient order the two definitions coincide; thus
the isolated Hausdorff input keeps the same mathematical content.

## Checked implementation

* `Completion/TraceTransfer.lean`: `MutuallyFiniteIncomparability.transfer_finite_trace`.
* `Completion/ChainTransitivity.lean`: `normalize_finite_cofinal`,
  `IncreasingEquivalent.trans`, and `DecreasingEquivalent.trans`.
* `Completion/Germs.lean`: private quotient implementation, exact equality
  criteria, representatives, invariant unary/binary lifts, and duality.
* `Completion/GermAPI.lean`: independent public-API examples and axiom audit.
* `Completion/SaturationExamples.lean`: a saturated but nonconvex diamond chain.

The full `lake build` and both test-module builds pass. The audited repair and
germ equality theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound`; they have no `sorry` or external mathematical assumption.
This completes roadmap Phase C. Later Stage 3 phases remain open, including the
pre-existing `sorry` in `Final/TubeFromChain.lean`.
