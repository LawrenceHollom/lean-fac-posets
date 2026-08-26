import AharoniKorman.Tube.Defs

/-! The external theorem of Zaguia used in paper Section 4. -/

namespace AharoniKorman.External

open Set
open AharoniKorman

variable {α : Type*} [PartialOrder α]

/-- Zaguia, Theorem 6, rephrased: every tube has a spine in its induced order. -/
theorem tube_hasSpine (T : Set α) (hT : IsTube T) : HasSpineOn T := by
  sorry

end AharoniKorman.External
