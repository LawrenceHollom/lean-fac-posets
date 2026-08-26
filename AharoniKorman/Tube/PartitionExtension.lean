import AharoniKorman.External.Zaguia

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- Paper Lemma `lem:extend-spine-partition`: every outside point has infinitely many compatible
blocks in any spine partition of a maximal tube. -/
theorem outside_incomparable_blocks [Countable α] (hfac : IsFAC α)
    {T C : Set α} (hT : IsMaximalTube T) (S : SpineData T C) {y : α} (hy : y ∉ T) :
    {x : C | ∀ z ∈ S.block x, Incomparable y z}.Infinite := by
  sorry

/-- Countably assign outside points to distinct compatible blocks and extend the partition. -/
theorem extend_spineData [Countable α] (hfac : IsFAC α)
    {T C : Set α} (hT : IsMaximalTube T) (S : SpineData T C) :
    Nonempty (SpineData (Set.univ : Set α) C) := by
  sorry

end AharoniKorman
