import AharoniKorman.Preliminaries.Chains
import Mathlib.Order.Cofinal
import Mathlib.SetTheory.Cardinal.Order

namespace AharoniKorman.External

open Set

universe u

variable {α : Type u} [LinearOrder α]

/-- Closure under convex well-ordered and reverse well-ordered sums. -/
def WellSumClosed (Q : Set α → Prop) : Prop :=
  ∀ (ι : Type u) [LinearOrder ι],
    (WellFounded ((· < ·) : ι → ι → Prop) ∨ WellFounded ((· > ·) : ι → ι → Prop)) →
    ∀ B : ι → Set α, (∀ i, (B i).Nonempty) → (∀ i, (B i).OrdConnected) →
      (⋃ i, B i).OrdConnected → (∀ ⦃i j⦄, i < j → SetStrictLT (B i) (B j)) →
      (∀ i, Q (B i)) → Q (⋃ i, B i)

/-- The ordered union of two convex pieces is a sum with at most two summands. -/
theorem WellSumClosed.union {Q : Set α → Prop} (sum : WellSumClosed Q)
    {A B : Set α} (hA : A.OrdConnected) (hB : B.OrdConnected)
    (hAB : (A ∪ B).OrdConnected) (hord : SetStrictLT A B) (hQA : Q A) (hQB : Q B) :
    Q (A ∪ B) := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | hneA
  · simpa using hQB
  rcases B.eq_empty_or_nonempty with rfl | hneB
  · simpa using hQA
  let I := ULift.{u} (Fin 2)
  let D (i : I) := if i.down = 0 then A else B
  have heq : (⋃ i, D i) = A ∪ B := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      by_cases h : i.down = 0
      · exact Or.inl (by simpa [D, h] using hi)
      · exact Or.inr (by simpa [D, h] using hi)
    · intro hx
      rcases hx with ha | hb
      · exact mem_iUnion.mpr ⟨⟨0⟩, by simpa [D] using ha⟩
      · exact mem_iUnion.mpr ⟨⟨1⟩, by simpa [D] using hb⟩
  rw [← heq]
  refine sum I (Or.inl wellFounded_lt) D ?_ ?_ (heq.symm ▸ hAB) ?_ ?_
  · intro i
    by_cases h : i.down = 0 <;> simp [D, h, hneA, hneB]
  · intro i
    by_cases h : i.down = 0 <;> simp [D, h, hA, hB]
  · intro i j hij x hx y hy
    change i.down < j.down at hij
    have hi : i.down = 0 := Fin.eq_of_val_eq (by omega)
    have hj : j.down ≠ 0 := by omega
    exact hord (by simpa [D, hi] using hx) (by simpa [D, hj] using hy)
  · intro i
    by_cases h : i.down = 0 <;> simp [D, h, hQA, hQB]

private theorem WellSumClosed.dual {Q : Set α → Prop} (sum : WellSumClosed Q) :
    WellSumClosed (α := αᵒᵈ) Q := by
  intro ι _ hw B hne hconv hUnion hordered hQ
  have hrev : WellFounded ((· < ·) : ιᵒᵈ → ιᵒᵈ → Prop) ∨
      WellFounded ((· > ·) : ιᵒᵈ → ιᵒᵈ → Prop) := hw.symm
  refine sum ιᵒᵈ hrev (fun i => B i) (fun i => hne i) (fun i => (hconv i).dual)
    hUnion.dual ?_ hQ
  intro i j hij x hx y hy
  exact hordered hij hy hx

private theorem boundedBelow_of_bounded_convex {Q : Set α → Prop} (sum : WellSumClosed Q)
    {S : Set α} (hS : S.OrdConnected) {a : α} (ha : ∀ x ∈ S, a ≤ x)
    (hlocal : ∀ T : Set α, T ⊆ S → T.OrdConnected → ∀ b ∈ S, T ⊆ Icc a b → Q T) :
    Q S := by
  classical
  let R : Set S := {i | ∀ j : S, WellOrderingRel j i → j < i}
  have hcofinal : IsCofinal R := isCofinal_setOfPred_imp_lt WellOrderingRel
  have hw : WellFounded ((· < ·) : R → R → Prop) := by
    refine (InvImage.wf (fun i : R => i.val) WellOrderingRel.isWellOrder.wf).mono ?_
    intro i j hij
    rcases trichotomous_of (α := S) WellOrderingRel i.val j.val with h | h | h
    · exact h
    · exact ((show i.val < j.val from hij).ne h).elim
    · exact ((show i.val < j.val from hij).not_gt (i.property _ h)).elim
  let B (i : R) : Set α := {x ∈ S | x ≤ i.val.val ∧ ∀ j : R, j < i → j.val.val < x}
  have hne (i : R) : (B i).Nonempty :=
    ⟨i.val.val, i.val.property, le_rfl, fun _ hij => hij⟩
  have hconv (i : R) : (B i).OrdConnected := by
    refine ⟨?_⟩
    intro x hx y hy z hz
    exact ⟨hS.out hx.1 hy.1 hz, hz.2.trans hy.2.1,
      fun j hj => (hx.2.2 j hj).trans_le hz.1⟩
  have hordered {i j : R} (hij : i < j) : SetStrictLT (B i) (B j) :=
    fun _ hx _ hy => hx.2.1.trans_lt (hy.2.2 i hij)
  have heq : (⋃ i, B i) = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨_, hx⟩ := mem_iUnion.mp hx
      exact hx.1
    · intro hx
      obtain ⟨i, hi, hle⟩ := hcofinal ⟨x, hx⟩
      let T : Set R := {j | x ≤ j.val.val}
      obtain ⟨j, hj, hmin⟩ := hw.has_min T ⟨⟨i, hi⟩, hle⟩
      exact mem_iUnion.mpr ⟨j, hx, hj, fun k hk => lt_of_not_ge fun hge => hmin k hge hk⟩
  have hQ (i : R) : Q (B i) := hlocal (B i) (fun _ hx => hx.1) (hconv i)
    i.val.val i.val.property (fun x hx => ⟨ha x hx.1, hx.2.1⟩)
  rw [← heq]
  exact sum R (Or.inl hw) B hne hconv (heq.symm ▸ hS) (fun {_ _} hij => hordered hij) hQ

/-- If every bounded convex part of a convex set belongs to a sum-closed class, the set does too.
Split at a point and partition each half into the convex slices of a cofinal well-order. -/
theorem convex_of_bounded_convex (Q : Set α → Prop) (hEmpty : Q ∅) (sum : WellSumClosed Q)
    {S : Set α} (hS : S.OrdConnected)
    (hlocal : ∀ T : Set α, T ⊆ S → T.OrdConnected →
      (∃ a ∈ S, ∃ b ∈ S, T ⊆ Icc a b) → Q T) : Q S := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact hEmpty
  let L := S ∩ Iio a
  let R := S ∩ Ici a
  have hL : L.OrdConnected := hS.inter inferInstance
  have hR : R.OrdConnected := hS.inter inferInstance
  have hQL : Q L := by
    refine boundedBelow_of_bounded_convex (α := αᵒᵈ) (a := OrderDual.toDual a)
      sum.dual hL.dual ?_ ?_
    · exact fun _ hx => hx.2.le
    · intro T hT hconv b hb hTbound
      exact hlocal T (fun _ hx => (hT hx).1) hconv.dual
        ⟨b, hb.1, a, ha, fun _ hx => ⟨(hTbound hx).2, (hTbound hx).1⟩⟩
  have hQR : Q R := by
    refine boundedBelow_of_bounded_convex (a := a) sum hR (fun _ hx => hx.2) ?_
    intro T hT hconv b hb hTbound
    exact hlocal T (fun _ hx => (hT hx).1) hconv ⟨a, ha, b, hb.1, hTbound⟩
  have heq : L ∪ R = S := by
    ext x
    constructor
    · rintro (hx | hx) <;> exact hx.1
    · intro hx
      rcases lt_or_ge x a with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  rw [← heq]
  exact sum.union hL hR (heq.symm ▸ hS) (fun _ hx _ hy => hx.2.trans_le hy.2) hQL hQR

end AharoniKorman.External
