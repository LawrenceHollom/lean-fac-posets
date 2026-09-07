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

Build with:

```text
lake build
```
