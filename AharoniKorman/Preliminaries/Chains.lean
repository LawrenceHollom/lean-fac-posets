import AharoniKorman.Preliminaries.Relations
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Preorder.Chain

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- A chain with no insertable point between two of its points (the manuscript's
definition). Ambient points incomparable with the chain need not belong to it. -/
def IsSaturatedChain (C : Set α) : Prop :=
  IsChain (· ≤ ·) C ∧ ∀ ⦃a b x⦄, a ∈ C → b ∈ C → a ≤ x → x ≤ b →
    (∀ c ∈ C, x ≤ c ∨ c ≤ x) → x ∈ C

theorem IsSaturatedChain.of_ordConnected {C : Set α}
    (hc : IsChain (· ≤ ·) C) (ho : C.OrdConnected) : IsSaturatedChain C :=
  ⟨hc, fun _ _ _ ha hb hax hxb _ => ho.out ha hb ⟨hax, hxb⟩⟩

theorem IsSaturatedChain.dual {C : Set α} (h : IsSaturatedChain C) :
    @IsSaturatedChain αᵒᵈ inferInstance C :=
  ⟨h.1.symm, fun _ _ _ ha hb hax hxb hc =>
    h.2 hb ha hxb hax (fun c hcC => (hc c hcC).symm)⟩

/-- An interval of a saturated chain is saturated in the ambient poset. -/
theorem IsSaturatedChain.restrict {C S : Set α} (h : IsSaturatedChain C)
    (hsub : S ⊆ C)
    (hconv : ∀ ⦃a b c⦄, a ∈ S → b ∈ S → c ∈ C → a ≤ c → c ≤ b → c ∈ S) :
    IsSaturatedChain S := by
  refine ⟨h.1.mono hsub, ?_⟩
  intro a b x ha hb hax hxb hx
  have hxC : x ∈ C := h.2 (hsub ha) (hsub hb) hax hxb (by
    intro c hc
    by_cases hca : c ≤ a
    · exact Or.inr (hca.trans hax)
    by_cases hbc : b ≤ c
    · exact Or.inl (hxb.trans hbc)
    have hac := (h.1.total (hsub ha) hc).resolve_right hca
    have hcb := (h.1.total hc (hsub hb)).resolve_right hbc
    exact hx c (hconv ha hb hc hac hcb))
  exact hconv ha hb hxC hax hxb

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

theorem isSaturatedChain_iff {β : Type*} [LinearOrder β] (C : Set β) :
    IsSaturatedChain C ↔ C.OrdConnected := by
  constructor
  · intro h
    exact ⟨fun _ ha _ hb _ hx => h.2 ha hb hx.1 hx.2 (fun c _ => le_total _ c)⟩
  · intro h
    exact IsSaturatedChain.of_ordConnected (isChain_of_trichotomous C) h

end AharoniKorman
