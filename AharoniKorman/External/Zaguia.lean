import AharoniKorman.Tube.Defs

/-! The external theorem of Zaguia used in paper Section 4. -/

namespace AharoniKorman.External

open Set
open AharoniKorman

variable {α : Type*} [PartialOrder α]

/-- **External input (Zaguia, Theorem 6).** Every tube has a spine in its induced order.

This is the sole Zaguia result used by the formalisation and is intentionally exposed as an exact
axiom rather than hidden behind a `sorry`. -/
axiom tube_hasSpine (T : Set α) (hT : IsTube T) : HasSpineOn T

end AharoniKorman.External
