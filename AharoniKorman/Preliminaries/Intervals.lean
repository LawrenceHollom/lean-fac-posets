import AharoniKorman.Preliminaries.Chains

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- A nonempty convex subset, used as the codomain object of replacement witnesses. -/
structure NonemptyInterval (α : Type*) [PartialOrder α] where
  carrier : Set α
  nonempty : carrier.Nonempty
  ordConnected : carrier.OrdConnected

instance : SetLike (NonemptyInterval α) α where
  coe I := I.carrier
  coe_injective := by intro I J h; cases I; cases J; cases h; rfl

/-- Convex hull in a partial order, following the manuscript's definition. -/
def convexHull (S : Set α) : Set α := {x | ∃ y ∈ S, ∃ z ∈ S, y ≤ x ∧ x ≤ z}

end AharoniKorman
