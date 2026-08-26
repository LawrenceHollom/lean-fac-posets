# Formalisation roadmap

## Design principles

The project follows mathematical dependency rather than the paper's presentation order.  In
particular, the tube reduction is independent of the chain completion and can be completed first.
Paper labels are recorded beside theorem declarations so that changes to the manuscript can be
tracked without encoding section numbers into Lean names.

Sets in an ambient partial order are used throughout.  A chain is `IsChain (· ≤ ·) C`, an
antichain is `IsAntichain (· ≤ ·) A`, and convexity is mathlib's `Set.OrdConnected`.  A spine is
represented canonically by a chain-indexed antichain partition: every block contains its indexing
chain point.  This removes an irrelevant quotient/reindexing problem from later proofs.

The completion `H(P)` is deliberately isolated.  Later files should use its public order,
principal embedding, nonprincipal increasing/decreasing points, representatives, completeness,
and embedding lemmas; they should not unfold its nested quotients.

## Dependency graph

```text
Preliminaries
  |-- Tube ------------------------------- Stage 1
  |-- Structural ------------------------- Stage 2
  `-- Completion
        `-- Illfounded
              `-- Alternating
                    `-- Consolidation
                          `-- Final/TubeFromChain

Tube + Structural + Final/TubeFromChain
  `-- Final/Main ------------------------- Stage 3
```

## File map

### Project surface

- `AharoniKorman.lean`: public umbrella import.
- `AharoniKorman/Final/Main.lean`: final theorem and the short assembly proof.
- `README.md`: project entry point and build instructions.
- `ROADMAP.md`: this dependency and theorem map.

### Shared preliminaries

- `Preliminaries/Relations.lean`: comparability, incomparability sets, and strict comparison of
  sets.
- `Preliminaries/Chains.lean`: maximal/saturated chains, initial and final segments, cofinality,
  coinitiality, and duality lemmas.
- `Preliminaries/Intervals.lean`: nonempty convex intervals, convex hulls, and endpoint-free
  intervals used by replacement witnesses.
- `Preliminaries/FAC.lean`: FAC, inheritance by induced subposets/order duals, and the infinite
  chain/Ramsey lemma (`fact:infinite-chain`).
- `Preliminaries/Scattered.lean`: scattered posets as those admitting no order embedding of
  `ℚ`, inheritance, and the cover lemma (`fact:covers`).
- `Preliminaries/Vacillating.lean`: omega-sums of infinite co-wellfounded blocks and vacillation,
  including inheritance by convex induced subposets.
- `Preliminaries/Spine.lean`: canonical chain-indexed antichain partitions, spines, and restriction
  and reindexing lemmas.

### Imported mathematical results

- `External/Zaguia.lean`: the locally finite incomparability graph/tube theorem used as a black
  box in Stage 1 (`thm:zaguia-spine-reformed`).  This theorem must ultimately be proved locally or
  explicitly retained as an assumption in the trusted theorem statement.
- `External/Hausdorff.lean`: the precise Hausdorff classification lemma needed to extract atomic
  chains from scattered linear orders (`thm:hausdorff-classification`).

### Stage 1: maximal tubes imply spines (paper Section 4)

- `Tube/Defs.lean`: tubes, maximal tubes, basic closure facts, and the outside-point
  characterization of maximality.
- `Tube/PartitionExtension.lean`: the infinite supply lemma
  `outside_incomparable_blocks` (`lem:extend-spine-partition`) and the countable fresh-block
  recursion assigning each outside point to a distinct compatible block.
- `Tube/MaximalImpliesSpine.lean`: `maximalTube_hasSpine`
  (`prop:maximal-tube-suffices`), combining Zaguia's theorem with partition extension.

This stage is largely elementary.  Its only substantial library work is a clean countable
enumeration/recursive-choice lemma.  It should be the first fully sorry-free milestone.

### Stage 2: reduction to scattered posets (paper Section 5)

- `Structural/EtaChains.lean`: copies of `η`, eta-maximal chains, eta intervals, and the fact that
  a rational sum of singleton/eta orders again has type eta (`lem:eta-nesting`).
- `Structural/EtaReplacement.lean`: eta-replacement witnesses, triviality, transitivity,
  antisymmetry, the partial order, countable-chain upper bounds, and exclusion of uncountable
  strict replacement chains.
- `Structural/Decomposition.lean`: eta-strongly maximal chains, the extended-real pieces `A_r`,
  the five fields of `ScatteredDecomposition`, and `structural_decomposition`
  (`thm:structural`, Theorem 1.4).
- `Structural/Reduction.lean`: union of maximal tubes in the scattered pieces and
  `maximalTube_reduction_to_scattered` (`cor:scattered-reduction`).

The delicate point is the Zorn step.  It should be expressed once as an abstract lemma saying
that countable cofinal replacement chains suffice; ordinal/cofinality bookkeeping should not be
repeated in each later replacement construction.

### Stage 3 foundation: the chain extension H(P) (paper Section 3)

- `Completion/FiniteDistance.lean`: finite-distance classes on saturated chains and their order.
- `Completion/ChainEquivalence.lean`: mutually finite incomparability, increasing/decreasing chain
  equivalence, equivalence-relation proofs, and the quotient-class isomorphism.
- `Completion/Construction.lean`: increasing and decreasing quotient points, gluing principal
  points, adjoining top/bottom, representative APIs, and the principal embedding `P -> H(P)`.
- `Completion/Order.lean`: domination, well-definedness on quotients, the partial order, scattering
  of `H(P)`, and the fact that `H(C)` is a chain.
- `Completion/Completeness.lean`: completeness of `H(C)`, sup/inf representation lemmas, natural
  embeddings `H(Q) -> H(P)`, accumulation points, and bicomparability.

### Stage 3 reductions and maximal chains (paper Sections 6--8)

- `Illfounded/Limits.lean`: illfounded limit points, quasifounded intervals, the quasifounded
  equivalence relation and partition.
- `Illfounded/Replacement.lean`: illfounded replacements, their partial order, forest limits,
  countable upper bounds, and stabilization below `omega_1`.
- `Illfounded/Reduction.lean`: existence of an illfounded-maximal chain and gluing maximal tubes
  across quasifounded intervals (`lem:quasifounded-suffices`).
- `Alternating/Classes.lean`: out-wellfounded posets, alternating equivalence/classes, and basic
  interval structure.
- `Alternating/Replacement.lean`: alternating replacements, order preservation, preorder/quotient
  partial order, forest upper bounds, and preservation of illfounded endpoints.
- `Alternating/Maximal.lean`: existence of alternating-maximal chains and the out-wellfounded
  convex-hull lemma.

### Stage 3 consolidation and conclusion (paper Sections 9--10)

- `Consolidation/Atomic.lean`: atomic increasing/decreasing chains and their existence via
  Hausdorff classification.
- `Consolidation/Relation.lean`: consolidation witnesses, transitivity, strong bicomparability,
  antisymmetry under vacillation, and domination/comparability lemmas.
- `Consolidation/Maximal.lean`: candidate chains, sequential upper bounds, exclusion of uncountable
  strict chains, preservation of illfounded endpoints, and existence of a consolidated chain.
- `Final/TubeFromChain.lean`: the finite-incomparability thickening of a consolidated chain is a
  maximal tube (`lem:f-finite-incomparability`), followed by `exists_maximalTube`.
- `Final/Main.lean`: combine `exists_maximalTube` with Stage 1 to obtain the main spine theorem
  (`thm:main`, hence the first-page formulation/Theorem 1.11).

## Risk assessment

No component appears intrinsically unformalizable, but three parts are high risk.

1. **The nested quotient construction of H(P).**  The manuscript freely identifies chains,
   equivalence classes, principal points, and embedded sub-completions.  Lean will not.  The
   construction needs a carefully designed representative API and many well-definedness proofs.
   This is likely the single largest engineering task.
2. **Upper bounds for replacement chains.**  All three replacement orders build forests and then
   appeal to countability, transfinite stabilization, and Zorn.  Informal phrases such as
   "arbitrarily extend to a maximal chain" must be made compatible with the witness maps.  Reusing
   a generic maximality/cofinality framework is important.
3. **Classical scattered-order input.**  Mathlib does not currently expose the paper's needed
   Hausdorff classification under the same notion of scattered order.  Proving the exact
   classification is a major independent project.  The recommended route is first to isolate and
   prove only the corollary actually used (`exists_atomic`), retaining the full classification in
   `External/Hausdorff.lean` only if necessary.

There are also several proof-level ambiguities worth resolving early: whether every use of
"saturated" means order-convex in the ambient poset; exact endpoint behavior in `H(Q) -> H(P)`;
and the manuscript's occasional identification of a finite incomparability set with its minimum
and maximum when it may be empty.  These look repairable, but the Lean statements should make the
edge cases explicit before long proofs are attempted.

## Suggested execution order

1. Finish all preliminaries needed by `Tube/*`, then make Stage 1 sorry-free.
2. Finish `EtaChains`, formalize eta replacement, and complete Stage 2.
3. Freeze the public API of `Completion/*` after proving its order and completeness theorems.
4. Implement the illfounded and alternating replacement frameworks.
5. Implement consolidation, construct the maximal tube, and close the final two-line theorem.
