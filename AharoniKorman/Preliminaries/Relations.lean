import Mathlib.Order.Comparable
import Mathlib.Order.SetNotation

/-! Basic comparison notation for the paper. -/

namespace AharoniKorman

open Relation Set

variable {α : Type*} [PartialOrder α]

/-- Two elements are comparable in the ambient partial order. -/
abbrev Comparable (x y : α) : Prop := Relation.SymmGen (· ≤ ·) x y

/-- Two elements are incomparable in the ambient partial order. -/
abbrev Incomparable (x y : α) : Prop := IncompRel (· ≤ ·) x y

/-- The elements comparable with `x`. -/
def comparableSet (x : α) : Set α := {y | Comparable x y}

/-- The elements incomparable with `x`. -/
def incomparableSet (x : α) : Set α := {y | Incomparable x y}

/-- Every element of `S` is strictly below every element of `T`. -/
def SetStrictLT (S T : Set α) : Prop := ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ T → x < y

@[simp] theorem mem_comparableSet {x y : α} : y ∈ comparableSet x ↔ Comparable x y := Iff.rfl

@[simp] theorem mem_incomparableSet {x y : α} : y ∈ incomparableSet x ↔ Incomparable x y := Iff.rfl

theorem incomparable_comm (x y : α) : Incomparable x y ↔ Incomparable y x := incompRel_comm

end AharoniKorman
