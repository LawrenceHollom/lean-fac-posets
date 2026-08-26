import AharoniKorman.Structural.Decomposition
import AharoniKorman.Preliminaries.Vacillating
import AharoniKorman.Tube.Defs

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- Paper Corollary `cor:scattered-reduction` (the second Stage 2 target). -/
theorem maximalTube_reduction_to_scattered [Countable α]
    (hfac : IsFAC α) (hvac : IsVacillating α)
    (scattered_case : ∀ (β : Type*) [PartialOrder β] [Countable β],
      IsFAC β → IsVacillating β → IsScattered β → ∃ T : Set β, IsMaximalTube T) :
    ∃ T : Set α, IsMaximalTube T := by
  sorry

end AharoniKorman
