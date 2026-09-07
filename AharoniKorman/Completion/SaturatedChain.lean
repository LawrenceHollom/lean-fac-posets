import AharoniKorman.Preliminaries.Intervals

/-! Bundled nonempty saturated chains and their basic maximality API. -/

namespace AharoniKorman.Completion

open _root_.AharoniKorman Set
open AharoniKorman

variable {α : Type*} [PartialOrder α]

/-- A nonempty saturated chain, bundled so its invariants travel with its carrier. -/
structure SaturatedChain (α : Type*) [PartialOrder α] where
  carrier : Set α
  nonempty : carrier.Nonempty
  saturated : IsSaturatedChain carrier

instance : SetLike (SaturatedChain α) α where
  coe C := C.carrier
  coe_injective := by
    intro C D h
    cases C
    cases D
    cases h
    rfl

@[simp] theorem SaturatedChain.mem_carrier (C : SaturatedChain α) (x : α) :
    x ∈ C.carrier ↔ x ∈ C := Iff.rfl

theorem SaturatedChain.isChain (C : SaturatedChain α) : IsChain (· ≤ ·) (C : Set α) :=
  C.saturated.1

theorem SaturatedChain.ordConnected (C : SaturatedChain α) : (C : Set α).OrdConnected :=
  C.saturated.2

noncomputable instance SaturatedChain.instLinearOrder (C : SaturatedChain α) : LinearOrder C := by
  classical
  exact C.isChain.linearOrder

/-- Restrict a saturated chain to a nonempty direction-indexed segment. -/
def SaturatedChain.restrict (C : SaturatedChain α) (d : OrderDirection) (S : Set α)
    (hS : IsDirectionalSegment d S C) (hne : S.Nonempty) : SaturatedChain α := by
  cases d with
  | increasing =>
      exact
        { carrier := S
          nonempty := hne
          saturated := by
            constructor
            · exact C.isChain.mono hS.1
            · constructor
              intro x hx y hy z hz
              have hzC : z ∈ C := C.ordConnected.out (hS.1 hx) (hS.1 hy) hz
              exact hS.2 hx hzC hz.1 }
  | decreasing =>
      exact
        { carrier := S
          nonempty := hne
          saturated := by
            constructor
            · exact C.isChain.mono hS.1
            · constructor
              intro x hx y hy z hz
              have hzC : z ∈ C := C.ordConnected.out (hS.1 hx) (hS.1 hy) hz
              exact hS.2 hy hzC hz.2 }

/-- Reverse the ambient order of a bundled saturated chain. -/
def SaturatedChain.dual (C : SaturatedChain α) : SaturatedChain αᵒᵈ where
  carrier := fun x : αᵒᵈ => x ∈ C.carrier
  nonempty := C.nonempty
  saturated := ⟨C.isChain.symm, C.ordConnected.dual⟩

@[simp] theorem SaturatedChain.mem_dual (C : SaturatedChain α) (x : α) :
    (show αᵒᵈ from x) ∈ C.dual ↔ x ∈ C := Iff.rfl

@[simp] theorem SaturatedChain.dual_dual (C : SaturatedChain α) : C.dual.dual = C := by
  apply SetLike.ext
  intro x
  rfl

namespace SaturatedChain

/-- The bundled chain has a greatest point. -/
def HasTop (C : SaturatedChain α) : Prop := ∃ m : C, ∀ x : C, x ≤ m

/-- The bundled chain has a least point. -/
def HasBottom (C : SaturatedChain α) : Prop := ∃ m : C, ∀ x : C, m ≤ x

def NoTop (C : SaturatedChain α) : Prop := ¬C.HasTop

def NoBottom (C : SaturatedChain α) : Prop := ¬C.HasBottom

theorem top_unique {C : SaturatedChain α} {m n : C}
    (hm : ∀ x : C, x ≤ m) (hn : ∀ x : C, x ≤ n) : m = n :=
  le_antisymm (hn m) (hm n)

theorem bottom_unique {C : SaturatedChain α} {m n : C}
    (hm : ∀ x : C, m ≤ x) (hn : ∀ x : C, n ≤ x) : m = n :=
  le_antisymm (hm n) (hn m)

@[simp] theorem dual_hasTop_iff (C : SaturatedChain α) : C.dual.HasTop ↔ C.HasBottom := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨⟨m.1, m.2⟩, fun x => hm ⟨x.1, x.2⟩⟩
  · rintro ⟨m, hm⟩
    exact ⟨⟨m.1, m.2⟩, fun x => hm ⟨x.1, x.2⟩⟩

@[simp] theorem dual_hasBottom_iff (C : SaturatedChain α) : C.dual.HasBottom ↔ C.HasTop := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨⟨m.1, m.2⟩, fun x => hm ⟨x.1, x.2⟩⟩
  · rintro ⟨m, hm⟩
    exact ⟨⟨m.1, m.2⟩, fun x => hm ⟨x.1, x.2⟩⟩

@[simp] theorem dual_noTop_iff (C : SaturatedChain α) : C.dual.NoTop ↔ C.NoBottom := by
  simp only [NoTop, NoBottom, dual_hasTop_iff]

@[simp] theorem dual_noBottom_iff (C : SaturatedChain α) : C.dual.NoBottom ↔ C.NoTop := by
  simp only [NoTop, NoBottom, dual_hasBottom_iff]

end SaturatedChain

/-- Maximality of a chain among chains contained in an induced subposet. -/
structure IsMaximalChainIn (C H : Set α) : Prop where
  subset : C ⊆ H
  isChain : IsChain (· ≤ ·) C
  maximal : ∀ {D : Set α}, IsChain (· ≤ ·) D → D ⊆ H → C ⊆ D → C = D

/-- Two bundled chains are both maximal in the convex hull of their union. -/
structure MutuallyMaximalInConvexHull (C D : SaturatedChain α) : Prop where
  left : IsMaximalChainIn C (convexHull ((C : Set α) ∪ D))
  right : IsMaximalChainIn D (convexHull ((C : Set α) ∪ D))

theorem IsMaximalChainIn.exists_incomparable {C H : Set α} (h : IsMaximalChainIn C H)
    {x : α} (hxH : x ∈ H) (hxC : x ∉ C) : ∃ y ∈ C, Incomparable x y := by
  classical
  by_contra hnone
  push_neg at hnone
  have hcomp : ∀ y ∈ C, x ≠ y → x ≤ y ∨ y ≤ x := by
    intro y hy hxy
    exact (not_incompRel_iff_symmGen.mp (hnone y hy)).casesOn Or.inl Or.inr
  have hins : IsChain (· ≤ ·) (insert x C) := h.isChain.insert hcomp
  have hsub : insert x C ⊆ H := by
    intro z hz
    rcases hz with rfl | hz
    · exact hxH
    · exact h.subset hz
  have heq : C = insert x C := h.maximal hins hsub (Set.subset_insert x C)
  exact hxC (heq ▸ Set.mem_insert x C)

theorem MutuallyMaximalInConvexHull.left_incomparable
    {C D : SaturatedChain α} (h : MutuallyMaximalInConvexHull C D)
    {x : α} (hx : x ∈ convexHull ((C : Set α) ∪ D)) (hxC : x ∉ C) :
    ∃ y ∈ C, Incomparable x y :=
  h.left.exists_incomparable hx hxC

theorem MutuallyMaximalInConvexHull.right_incomparable
    {C D : SaturatedChain α} (h : MutuallyMaximalInConvexHull C D)
    {x : α} (hx : x ∈ convexHull ((C : Set α) ∪ D)) (hxD : x ∉ D) :
    ∃ y ∈ D, Incomparable x y :=
  h.right.exists_incomparable hx hxD

end AharoniKorman.Completion
