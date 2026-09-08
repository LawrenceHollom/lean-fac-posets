import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Interval.Set.OrdConnected

/-! Order embeddings preserving existing nonempty suprema and infima.

Cofinality is a separate property, not part of the witness structure. In particular,
restricting the codomain to genuine points does not confer cofinality automatically.
-/

namespace AharoniKorman.Completion

open Set

variable {α β γ : Type*} [PartialOrder α] [PartialOrder β] [PartialOrder γ]

structure SupInfEmbedding (α β : Type*) [PartialOrder α] [PartialOrder β] where
  toOrderEmbedding : α ↪o β
  map_isLUB : ∀ {s : Set α} {x : α}, s.Nonempty → IsLUB s x →
    IsLUB (toOrderEmbedding '' s) (toOrderEmbedding x)
  map_isGLB : ∀ {s : Set α} {x : α}, s.Nonempty → IsGLB s x →
    IsGLB (toOrderEmbedding '' s) (toOrderEmbedding x)

instance : CoeFun (SupInfEmbedding α β) (fun _ => α → β) :=
  ⟨fun f => f.toOrderEmbedding⟩

namespace SupInfEmbedding

def ofOrderIso (e : α ≃o β) : SupInfEmbedding α β where
  toOrderEmbedding := e.toOrderEmbedding
  map_isLUB _ h := e.isLUB_image'.2 h
  map_isGLB _ h := e.isGLB_image'.2 h

def refl (α : Type*) [PartialOrder α] : SupInfEmbedding α α := ofOrderIso (OrderIso.refl α)

@[simp] theorem refl_apply (x : α) : refl α x = x := rfl

def comp (g : SupInfEmbedding β γ) (f : SupInfEmbedding α β) : SupInfEmbedding α γ where
  toOrderEmbedding := f.toOrderEmbedding.trans g.toOrderEmbedding
  map_isLUB hs h := by
    have h' := g.map_isLUB (hs.image f) (f.map_isLUB hs h)
    simpa only [Set.image_image, RelEmbedding.coe_trans, Function.comp_apply] using h'
  map_isGLB hs h := by
    have h' := g.map_isGLB (hs.image f) (f.map_isGLB hs h)
    simpa only [Set.image_image, RelEmbedding.coe_trans, Function.comp_apply] using h'

@[simp] theorem comp_apply (g : SupInfEmbedding β γ) (f : SupInfEmbedding α β) (x : α) :
    g.comp f x = g (f x) := rfl

def dual (f : SupInfEmbedding α β) : SupInfEmbedding αᵒᵈ βᵒᵈ where
  toOrderEmbedding := f.toOrderEmbedding.dual
  map_isLUB := f.map_isGLB
  map_isGLB := f.map_isLUB

@[simp] theorem dual_apply (f : SupInfEmbedding α β) (x : αᵒᵈ) : f.dual x = f x := rfl

/-- Restricting the target retains any bound already proved in the whole target. -/
def codRestrict (f : SupInfEmbedding α β) (T : Set β) (hf : ∀ x, f x ∈ T) :
    SupInfEmbedding α T where
  toOrderEmbedding := OrderEmbedding.ofMapLEIff (fun x => (⟨f x, hf x⟩ : T))
    (by intro x y; exact f.toOrderEmbedding.le_iff_le)
  map_isLUB hs h := by
    have h' := f.map_isLUB hs h
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      exact h'.1 ⟨x, hx, rfl⟩
    · intro z hz
      apply h'.2
      rintro _ ⟨x, hx, rfl⟩
      exact hz ⟨x, hx, rfl⟩
  map_isGLB hs h := by
    have h' := f.map_isGLB hs h
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      exact h'.1 ⟨x, hx, rfl⟩
    · intro z hz
      apply h'.2
      rintro _ ⟨x, hx, rfl⟩
      exact hz ⟨x, hx, rfl⟩

@[simp] theorem codRestrict_apply (f : SupInfEmbedding α β) (T : Set β)
    (hf : ∀ x, f x ∈ T) (x : α) : (f.codRestrict T hf x).1 = f x := rfl

def HasCofinalRange (f : SupInfEmbedding α β) : Prop := ∀ y : β, ∃ x : α, y ≤ f x

def HasCoinitialRange (f : SupInfEmbedding α β) : Prop := ∀ y : β, ∃ x : α, f x ≤ y

theorem HasCofinalRange.comp {g : SupInfEmbedding β γ} {f : SupInfEmbedding α β}
    (hg : g.HasCofinalRange) (hf : f.HasCofinalRange) : (g.comp f).HasCofinalRange := by
  intro z
  obtain ⟨y, hzy⟩ := hg z
  obtain ⟨x, hyx⟩ := hf y
  exact ⟨x, hzy.trans (g.toOrderEmbedding.monotone hyx)⟩

theorem HasCoinitialRange.comp {g : SupInfEmbedding β γ} {f : SupInfEmbedding α β}
    (hg : g.HasCoinitialRange) (hf : f.HasCoinitialRange) : (g.comp f).HasCoinitialRange :=
  HasCofinalRange.comp (g := g.dual) (f := f.dual) hg hf

theorem codRestrict_cofinal_iff (f : SupInfEmbedding α β) (T : Set β)
    (hf : ∀ x, f x ∈ T) :
    (f.codRestrict T hf).HasCofinalRange ↔ ∀ y ∈ T, ∃ x : α, y ≤ f x := by
  exact ⟨fun h y hy => h ⟨y, hy⟩, fun h y => h y.1 y.2⟩

theorem codRestrict_coinitial_iff (f : SupInfEmbedding α β) (T : Set β)
    (hf : ∀ x, f x ∈ T) :
    (f.codRestrict T hf).HasCoinitialRange ↔ ∀ y ∈ T, ∃ x : α, f x ≤ y := by
  exact ⟨fun h y hy => h ⟨y, hy⟩, fun h y => h y.1 y.2⟩

end SupInfEmbedding

section Restriction

variable {δ : Type*} [LinearOrder δ]

private theorem isLUB_image_subtype_of_ordConnected {S : Set δ} (hS : S.OrdConnected)
    {s : Set S} {x : S} (hs : s.Nonempty) (h : IsLUB s x) :
    IsLUB (Subtype.val '' s) x.1 := by
  constructor
  · rintro _ ⟨y, hy, rfl⟩
    exact h.1 hy
  · intro z hz
    by_contra hxz
    have hzx : z < x.1 := lt_of_not_ge hxz
    obtain ⟨a, ha⟩ := hs
    have haz : a.1 ≤ z := hz ⟨a, ha, rfl⟩
    have hzS : z ∈ S := hS.out a.2 x.2 ⟨haz, hzx.le⟩
    have hbound : (⟨z, hzS⟩ : S) ∈ upperBounds s := by
      intro y hy
      exact hz ⟨y, hy, rfl⟩
    exact hzx.not_ge (h.2 hbound)

/-- A convex source restriction preserves all its nonempty existing bounds. -/
def SupInfEmbedding.restrictDomain (f : SupInfEmbedding δ β) (S : Set δ)
    (hS : S.OrdConnected) : SupInfEmbedding S β where
  toOrderEmbedding := (OrderEmbedding.subtype S).trans f.toOrderEmbedding
  map_isLUB {s} {x} hs h := by
    have h' := f.map_isLUB (hs.image Subtype.val)
      (isLUB_image_subtype_of_ordConnected hS hs h)
    change IsLUB ((fun a : S => f a.1) '' s) (f x.1)
    simpa only [Set.image_image] using h'
  map_isGLB {s} {x} hs h := by
    have h' := f.map_isGLB (hs.image Subtype.val)
      (isLUB_image_subtype_of_ordConnected (δ := δᵒᵈ) hS.dual hs h)
    change IsGLB ((fun a : S => f a.1) '' s) (f x.1)
    simpa only [Set.image_image] using h'

@[simp] theorem SupInfEmbedding.restrictDomain_apply (f : SupInfEmbedding δ β)
    (S : Set δ) (hS : S.OrdConnected) (x : S) : f.restrictDomain S hS x = f x.1 := rfl

end Restriction

section Complete

variable {δ ε : Type*} [CompleteLinearOrder δ] [CompleteLinearOrder ε]

theorem SupInfEmbedding.map_sSup (f : SupInfEmbedding δ ε) {s : Set δ} (hs : s.Nonempty) :
    f (sSup s) = sSup (f '' s) :=
  (f.map_isLUB hs (isLUB_sSup s)).unique (isLUB_sSup _)

theorem SupInfEmbedding.map_sInf (f : SupInfEmbedding δ ε) {s : Set δ} (hs : s.Nonempty) :
    f (sInf s) = sInf (f '' s) :=
  (f.map_isGLB hs (isGLB_sInf s)).unique (isGLB_sInf _)

end Complete

end AharoniKorman.Completion
