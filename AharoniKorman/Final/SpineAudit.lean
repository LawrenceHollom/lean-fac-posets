import AharoniKorman.Final.Main
import AharoniKorman.Final.AtomicHull
import Mathlib.Util.AssertNoSorry

/-!
The Hausdorff induction principle and the spine proof use only Lean's standard logical axioms.
-/

open AharoniKorman AharoniKorman.Consolidation

assert_no_sorry External.scattered_well_sum_induction
assert_no_sorry IsQuasifounded.isVacillating
assert_no_sorry IsVacillating.isQuasifounded_of_no_internal_increasing
assert_no_sorry exists_ordered_open_chains
assert_no_sorry hasSaturatedZeta_of_open_saturated
assert_no_sorry exists_open_quasifounded_in_convex
assert_no_sorry exists_separatingTube_of_not_quasifounded
assert_no_sorry maximalTube_reduction_to_quasifounded
assert_no_sorry IsMaximalTubeIn.isSeparatingTube
assert_no_sorry exists_isMaximalTube_of_convex_regions
assert_no_sorry finiteIncomparabilityHull_trace_ordConnected
assert_no_sorry exists_atomicallyConsolidated
assert_no_sorry atomicallyConsolidated_hull_maximalTube
assert_no_sorry exists_maximalTube_of_scattered
assert_no_sorry exists_maximalTube
assert_no_sorry IsTube.hasSpine_univ
assert_no_sorry main_theorem

run_cmd do
  let logical : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Lean.Name := #[
    ``External.scattered_well_sum_induction, ``IsQuasifounded.isVacillating,
    ``IsVacillating.isQuasifounded_of_no_internal_increasing,
    ``exists_ordered_open_chains, ``hasSaturatedZeta_of_open_saturated,
    ``exists_open_quasifounded_in_convex, ``exists_separatingTube_of_not_quasifounded,
    ``maximalTube_reduction_to_quasifounded, ``finiteIncomparabilityHull_trace_ordConnected,
    ``IsMaximalTubeIn.isSeparatingTube, ``exists_isMaximalTube_of_convex_regions,
    ``IsTube.hasSpine_univ, ``exists_atomicallyConsolidated,
    ``atomicallyConsolidated_hull_maximalTube, ``exists_maximalTube_of_scattered,
    ``exists_maximalTube, ``main_theorem]
  for declaration in checked do
    for axiomName in (← Lean.collectAxioms declaration) do
      unless logical.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"

#print axioms External.scattered_well_sum_induction
#print axioms maximalTube_reduction_to_quasifounded
#print axioms atomicallyConsolidated_hull_maximalTube
#print axioms exists_maximalTube
#print axioms main_theorem
