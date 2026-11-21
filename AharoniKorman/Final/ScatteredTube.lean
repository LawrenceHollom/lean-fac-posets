import AharoniKorman.Final.QuasifoundedTube
import AharoniKorman.Tube.QuasifoundedReduction

namespace AharoniKorman

variable {α : Type*} [PartialOrder α]

/-- The scattered case of paper `prop:exists-maximal-tube`. -/
theorem exists_maximalTube_of_scattered [Countable α]
    (hfac : IsFAC α) (hscattered : IsScattered α) (hvac : IsVacillating α) :
    ∃ T : Set α, IsMaximalTube T := by
  apply maximalTube_reduction_to_quasifounded hfac hscattered hvac
  intro β _ _ hβfac hβsc hβqf
  exact exists_maximalTube_of_quasifounded hβfac hβsc hβqf

end AharoniKorman
