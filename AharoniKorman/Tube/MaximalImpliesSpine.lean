import AharoniKorman.Tube.PartitionExtension

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- Paper Proposition `prop:maximal-tube-suffices` (Stage 1 target). -/
theorem maximalTube_hasSpine [Countable α] (hfac : IsFAC α)
    {T : Set α} (hT : IsMaximalTube T) : HasSpine α := by
  sorry

end AharoniKorman
