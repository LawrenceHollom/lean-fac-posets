# Frozen completion interface (Phase E)

Later phases import `AharoniKorman.Completion`. The public-API gate is
`AharoniKorman.Completion.CompletionAPI`; concrete regression examples are in
`AharoniKorman.Completion.AccumulationExamples`. Both import only the aggregate
interface. No later proof should unfold germ setoids, quotient constructors,
`H.StrictLT`, or representative-level domination. Use the comparison and
representative lemmas below instead.

## Objects and endpoint conventions

`SaturatedChain`, `IncreasingChain`, and `DecreasingChain` are nonempty bundled
chains. An increasing chain has no greatest point; the decreasing definition
is dual. `IncreasingGerm` and `DecreasingGerm` are their normalized germ types.
Use `ofChain`, `inductionOn`, `Represents`, `representative_spec`, and
`ofChain_eq_iff` from the public germ API to introduce or change representatives.

`H α` has five distinct constructors: `principal`, `increasing`, `decreasing`,
`bottom`, and `top`. `H.N α` includes the formal bottom and top; they have signs
but no representing chains. A genuine boundary is an `increasing g` or
`decreasing g`. In particular, the upper germ of an unbounded chain is strictly
below the formal top.

## Main interfaces

| Operation | Public declarations | Assumptions |
| --- | --- | --- |
| Principal inclusion | `H.principalEmbedding`, `principal_lt_principal`, `principal_le_principal` | Partial order |
| Representative comparisons | `H.principal_lt_increasing_ofChain`, `increasing_ofChain_lt_principal`, and the six other constructor comparison formulas | Partial order |
| Duality | `H.dualOrderIso`, `dual_lt_dual`, `direction_dual` | Partial order |
| Admissible sub-completions | `SaturationPreserving`, `H.mapEmbedding`, `H.Represents.map` | Inclusion preserves saturation; proved for convex subsets and saturated chains |
| Completeness | `CompleteLinearOrder (H α)`, `H.isLUB_supChain`, `sSup_eq_supChain` | Linear original order |
| Non-attained bounds | `H.sSup_eq_increasing_of_not_mem`, `sInf_eq_decreasing_of_not_mem`, direction and sequence variants | Nonempty set in a chain completion |
| Continuous embeddings | `SupInfEmbedding`, `refl`, `comp`, `dual`, `codRestrict`, `restrictDomain` | Existing nonempty suprema/infima; source restriction is convex in a linear order |
| Global cofinality | `SupInfEmbedding.HasCofinalRange`, `HasCoinitialRange`, composition and restriction equivalences | Separate from continuity and local germ cofinality |
| Local cofinality | `IncreasingGerm.lowerProfile`, `CofinalAbove`; dual `upperProfile`, `CoinitialBelow` | Genuine germs in any partial order |
| Bicomparability | `IncreasingGerm.Bicomparable`, `DecreasingGerm.Bicomparable`, equivalence laws and `bicomparable_ofChain_iff` | Same-direction genuine germs |
| Cofinal representative sequences | `IncreasingChain.exists_cofinal_sequence`, `DecreasingChain.exists_coinitial_sequence` | Countable original poset |
| Sequential bicomparability | `IncreasingChain.bicomparable_iff_sequences`, decreasing counterpart | Chosen cofinal/coinitial sequences; no additional countability needed |
| Accumulation and isolation | `H.IsAccumulation`, `IsIsolated`, constructor and duality lemmas | Partial order; relative to `N(α)` |
| Isolated boundaries | `H.isIsolated_increasing_iff`, `isIsolated_decreasing_iff` | A cover in the nonprincipal subtype, not in the full completion |
| Cofinal/bound characterizations | `H.accumulatesBelow_iff_cofinal`, `accumulatesBelow_iff_isLUB`, dual coinitial/infimum theorems | Linear original order; exclude the endpoint opposite to the direction of approach |
| Sequential accumulation | `H.isAccumulation_increasing_iff_sequence`, `isAccumulation_decreasing_iff_sequence` | Countable original linear order |
| Principal-cut realization | `H.principalInterpolationBelow_of_maxChain`, its dual, `exists_principalTrace_extension`, `realizeMaxChainIncreasing_lt`, `realizeIncreasing_strict_of_principal_bound` | Scattered original poset, maximal completion chain; trace extension requires a nonempty original poset |

The generic sequence theorem `H.exists_strictMono_isLUB` applies to any nonempty
set without a greatest member in a countable chain's completion. It obtains a
countable cofinal family using principal points. It does **not** assume the
completion itself is countable; the rational-chain examples exercise this case.

## Accumulation and bicomparability

Increasing accumulation means that every smaller nonprincipal point has a
nonprincipal point strictly between it and the boundary. Decreasing
accumulation reverses both inequalities. These definitions are ambient-order
relative: accumulation in `H(C)` is not automatically accumulation in `H(P)`
for a chain `C` contained in `P`.

In a chain completion, accumulation is equivalent to cofinal approximation by
nonprincipal points in the full completion. For countable original chains it
is equivalent to a strictly monotone nonprincipal sequence with that supremum
(or a strictly antitone sequence with that infimum). Formal endpoints are
isolated, including when the original chain is empty. Principal points are
neither accumulation points nor isolated nonprincipal points.

Bicomparability is equality of lower profiles for increasing germs, or upper
profiles for decreasing germs. It is symmetric and transitive, but does not
identify germs. Given cofinal sequences in representatives, it is equivalent
to each sequence eventually reaching above every term of the other (dually,
below). The existing germ equivalence remains unchanged.

## Trust and scope

The Phase E audits use only `propext`, `Classical.choice`, and `Quot.sound`, or
subsets of those axioms. No Phase E theorem depends on `sorryAx`, Hausdorff,
Zaguia, or another mathematical axiom.

The consolidation repair in `CONSOLIDATION_LIMIT_REPAIR.md` uses the checked
principal-cut tools, but its full sequential witness, atomic/hull prerequisites,
and arbitrary-chain upper-bound argument belong to later phases. Completing
this interface does not discharge those obligations.

Run the gate and examples with:

```text
lake build AharoniKorman.Completion.CompletionAPI AharoniKorman.Completion.AccumulationExamples
```
