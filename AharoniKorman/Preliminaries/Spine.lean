import AharoniKorman.Preliminaries.FAC

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- A canonical antichain partition of `P`, indexed by the points of a chain `C`.

This is equivalent to the paper's formulation because an antichain meets a chain in at most one
point. -/
structure SpineData (P C : Set α) where
  chain : IsChain (· ≤ ·) C
  chain_subset : C ⊆ P
  block : C → Set α
  block_antichain : ∀ x, IsAntichain (· ≤ ·) (block x)
  mem_block : ∀ x, x.1 ∈ block x
  blocks_disjoint : ∀ x y, x ≠ y → Disjoint (block x) (block y)
  iUnion_blocks : (⋃ x, block x) = P

theorem SpineData.block_subset {P C : Set α} (S : SpineData P C) (x : C) :
    S.block x ⊆ P := by
  intro z hz
  rw [← S.iUnion_blocks]
  exact Set.mem_iUnion_of_mem x hz

/-- `P` has a spine contained in `P`. -/
def HasSpineOn (P : Set α) : Prop := ∃ C : Set α, Nonempty (SpineData P C)

/-- The whole ambient poset has a spine. -/
abbrev HasSpine (α : Type*) [PartialOrder α] : Prop := HasSpineOn (Set.univ : Set α)

end AharoniKorman
