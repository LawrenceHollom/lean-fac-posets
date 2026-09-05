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

Stage 1 is implemented and checked by Lean, relative to Zaguia's published tube theorem, which is
kept as an explicit external assumption in `External/Zaguia.lean`. Later-stage interfaces still
contain `sorry` at their planned milestone boundaries.

Build with:

```text
lake build
```
