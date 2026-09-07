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

/-- The two order directions used throughout the completion and replacement constructions. -/
inductive OrderDirection
  | increasing
  | decreasing
  deriving DecidableEq

namespace OrderDirection

/-- Reverse an order direction. -/
def dual : OrderDirection → OrderDirection
  | increasing => decreasing
  | decreasing => increasing

@[simp] theorem dual_increasing : dual increasing = decreasing := rfl

@[simp] theorem dual_decreasing : dual decreasing = increasing := rfl

@[simp] theorem dual_dual (d : OrderDirection) : dual (dual d) = d := by
  cases d <;> rfl

end OrderDirection

/-- A final segment in the increasing direction and an initial segment in the decreasing one. -/
def IsDirectionalSegment (d : OrderDirection) (C D : Set α) : Prop :=
  match d with
  | .increasing => IsFinalSegment C D
  | .decreasing => IsInitialSegment C D

/-- Cofinality in the increasing direction and coinitiality in the decreasing one. -/
def IsDirectionalCofinalIn (d : OrderDirection) (C D : Set α) : Prop :=
  match d with
  | .increasing => IsCofinalIn C D
  | .decreasing => IsCoinitialIn C D

@[simp] theorem isDirectionalSegment_increasing (C D : Set α) :
    IsDirectionalSegment .increasing C D ↔ IsFinalSegment C D := Iff.rfl

@[simp] theorem isDirectionalSegment_decreasing (C D : Set α) :
    IsDirectionalSegment .decreasing C D ↔ IsInitialSegment C D := Iff.rfl

@[simp] theorem isDirectionalCofinalIn_increasing (C D : Set α) :
    IsDirectionalCofinalIn .increasing C D ↔ IsCofinalIn C D := Iff.rfl

@[simp] theorem isDirectionalCofinalIn_decreasing (C D : Set α) :
    IsDirectionalCofinalIn .decreasing C D ↔ IsCoinitialIn C D := Iff.rfl

theorem isSaturatedChain_iff (C : Set α) :
    IsSaturatedChain C ↔ IsChain (· ≤ ·) C ∧ C.OrdConnected := Iff.rfl

end AharoniKorman
