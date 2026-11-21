import AharoniKorman.Final.ScatteredTube
import AharoniKorman.Structural.Reduction

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- Paper `prop:exists-maximal-tube`. -/
theorem exists_maximalTube [Countable α] (hfac : IsFAC α) (hvac : IsVacillating α) :
    ∃ T : Set α, IsMaximalTube T := by
  apply maximalTube_reduction_to_scattered hfac hvac
  intro β _ _ hβfac hβvac hβscattered
  exact exists_maximalTube_of_scattered hβfac hβscattered hβvac

end AharoniKorman
