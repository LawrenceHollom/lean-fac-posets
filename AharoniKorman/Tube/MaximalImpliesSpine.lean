import AharoniKorman.Tube.PartitionExtension
import AharoniKorman.Tube.Spine

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- Paper `prop:maximal-tube-suffices`. The resulting spine lies inside the maximal tube. -/
theorem maximalTube_hasSpine_inside [Countable α] (hfac : IsFAC α)
    {T : Set α} (hT : IsMaximalTube T) :
    ∃ C : Set α, C ⊆ T ∧ Nonempty (SpineData (Set.univ : Set α) C) := by
  obtain ⟨C, ⟨S⟩⟩ := hT.1.hasSpine
  exact ⟨C, S.chain_subset, extend_spineData hfac hT S⟩

/-- A countable FAC poset with a maximal tube has a spine. -/
theorem maximalTube_hasSpine [Countable α] (hfac : IsFAC α)
    {T : Set α} (hT : IsMaximalTube T) : HasSpine α := by
  obtain ⟨C, _, hC⟩ := maximalTube_hasSpine_inside hfac hT
  exact ⟨C, hC⟩

end AharoniKorman
