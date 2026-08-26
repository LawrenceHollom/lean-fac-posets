import AharoniKorman.Preliminaries.Relations
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Preorder.Chain

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- A chain which is order-convex in the ambient poset. -/
def IsSaturatedChain (C : Set α) : Prop := IsChain (· ≤ ·) C ∧ C.OrdConnected

/-- An inclusion-maximal chain. -/
abbrev IsMaximalChain (C : Set α) : Prop := IsMaxChain (· ≤ ·) C

def IsFinalSegment (C D : Set α) : Prop :=
  C ⊆ D ∧ ∀ ⦃x y⦄, x ∈ C → y ∈ D → x ≤ y → y ∈ C

def IsInitialSegment (C D : Set α) : Prop :=
  C ⊆ D ∧ ∀ ⦃x y⦄, x ∈ C → y ∈ D → y ≤ x → y ∈ C

def IsCofinalIn (C D : Set α) : Prop :=
  C ⊆ D ∧ ∀ ⦃y⦄, y ∈ D → ∃ x ∈ C, y ≤ x

def IsCoinitialIn (C D : Set α) : Prop :=
  C ⊆ D ∧ ∀ ⦃y⦄, y ∈ D → ∃ x ∈ C, x ≤ y

theorem isSaturatedChain_iff (C : Set α) :
    IsSaturatedChain C ↔ IsChain (· ≤ ·) C ∧ C.OrdConnected := Iff.rfl

end AharoniKorman
