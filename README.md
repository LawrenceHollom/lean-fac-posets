# Aharoni--Korman in Lean

This project formalises the structural theory of countable posets satisfying the finite
antichain condition (FAC) and the resulting Aharoni--Korman theorem.

The formalisation is divided into the same three milestones as the project:

1. reduce the existence of a spine to the existence of a maximal tube;
2. prove the structural decomposition into scattered pieces and reduce maximal-tube existence
   to scattered posets;
3. construct a maximal tube in a countable vacillating scattered FAC poset and deduce the main
   theorem.

See [ROADMAP.md](ROADMAP.md) for the module map, dependency graph, theorem correspondence, and
risk assessment.

Stages 1 and 2 are implemented and checked by Lean.  Stage 1 is relative to Zaguia's published
tube theorem, kept as an explicit external assumption in `External/Zaguia.lean`.  Stage 2 includes
the eta-replacement upper-bound theorem, the structural decomposition (Theorem 1.4), and the
reduction to scattered posets; it has no remaining `sorry` declarations.  See `ROADMAP.md` for the
proof architecture and the remaining Stage 3 work.

Stage 3 phases A–C are complete. The mathematical repair of chain-equivalence
transitivity is recorded in [MATH_REPAIR.md](MATH_REPAIR.md). Saturation now uses
the manuscript's insertability condition. The increasing/decreasing germ APIs
and their transitivity proofs have no `sorry` or external mathematical assumption.
Phase D is also complete: the normalized completion has a partial order, an order embedding
of the original poset, an order-duality isomorphism, representative comparison formulas, and
a proof that completion preserves scatteredness. The Phase D axiom audit uses only standard
Lean axioms. Phase E is complete: admissible completion embeddings, linearity,
suprema/infima, non-attained bounds, continuity, local germ cofinality, bicomparability,
and accumulation/isolated points. Cofinal and sequential characterizations are checked
in both directions, with countability required only of the original chain. Formal
endpoints are isolated in chain completions, including the empty-chain case.
The frozen interface is `AharoniKorman.Completion`; see
[COMPLETION_API.md](COMPLETION_API.md) for its declarations and assumptions. Its gate
and rational-chain regression examples have no `sorry`s or external mathematical axioms.

Formalisation has resumed using the sequential construction in
[CONSOLIDATION_LIMIT_REPAIR.md](CONSOLIDATION_LIMIT_REPAIR.md). It uses a maximal chain in
the completion, its principal trace, and new cuts in a maximal chain of the original poset.
Stable germs may change, including from atomic to nonatomic. Principal interpolation,
nonemptiness of the trace, the increasing cut construction, and the strict-separation
safeguard are checked in Lean without new axioms or `sorry`s. The complete sequential
theorem and its scheduled atomic/hull prerequisites have not yet been formalized; the
arbitrary-chain upper-bound argument remains a separate obligation.

The construction uses local cofinality at genuine image points. Requiring genuine global
cofinality at ordinary endpoints is incompatible with sequential upper bounds; the new
proof note gives a counterexample. Earlier counterexamples to germ-level antisymmetry and
unchanged stable-germ realization remain in [PHASE_E_BLOCKER.md](PHASE_E_BLOCKER.md).
The remaining phases, including the maximal-tube endpoint, remain to be implemented.

Build with:

```text
lake build
```

Check the Phase C public API, axiom audit, and saturation regression example with:

```text
lake build AharoniKorman.Completion.GermAPI AharoniKorman.Completion.SaturationExamples
```

Check the Phase D public API, finite-chain and infinite-chain examples, and axiom audit with:

```text
lake build AharoniKorman.Completion.OrderAPI
```

Check the Phase E interface, axiom audit, and accumulation examples with:

```text
lake build AharoniKorman.Completion.CompletionAPI AharoniKorman.Completion.AccumulationExamples
```
