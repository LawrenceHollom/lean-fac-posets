import AharoniKorman.Consolidation.Maximal
import AharoniKorman.Structural.Reduction

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- Stage 3's structural endpoint: every countable vacillating FAC poset has a maximal tube
(`prop:exists-maximal-tube`). -/
theorem exists_maximalTube [Countable α] (hfac : IsFAC α) (hvac : IsVacillating α) :
    ∃ T : Set α, IsMaximalTube T := by
  sorry

end AharoniKorman
