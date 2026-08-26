import AharoniKorman.Final.TubeFromChain
import AharoniKorman.Tube.MaximalImpliesSpine

namespace AharoniKorman

variable {α : Type*} [PartialOrder α]

/-- Paper `thm:main` / Theorem 1.11: every countable vacillating FAC poset has a spine. -/
theorem main_theorem [Countable α] (hfac : IsFAC α) (hvac : IsVacillating α) : HasSpine α := by
  obtain ⟨T, hT⟩ := exists_maximalTube hfac hvac
  exact maximalTube_hasSpine hfac hT

end AharoniKorman
