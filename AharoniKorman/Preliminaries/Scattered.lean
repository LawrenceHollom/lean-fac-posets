import AharoniKorman.Preliminaries.Chains
import Mathlib.Data.Rat.Defs

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- A poset is scattered when it contains no order-embedded copy of the rationals. -/
def IsScattered (α : Type*) [PartialOrder α] : Prop := ¬ Nonempty (ℚ ↪o α)

/-- Scatteredness is inherited by induced subposets. -/
theorem IsScattered.subtype (h : IsScattered α) (S : Set α) : IsScattered S := by
  sorry

/-- Paper fact `fact:covers`. -/
theorem IsScattered.exists_covBy_between (h : IsScattered α) {x y : α} (hxy : x < y) :
    ∃ u v, x ≤ u ∧ u < v ∧ v ≤ y ∧ u ⋖ v := by
  sorry

end AharoniKorman
