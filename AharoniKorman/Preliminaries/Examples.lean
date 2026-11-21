import AharoniKorman.Preliminaries.Spine
import AharoniKorman.Preliminaries.Vacillating
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Prod.Lex
import Mathlib.Order.WellQuasiOrder

namespace AharoniKorman

open Set

theorem natGrid_isFAC : IsFAC (ℕ × ℕ) :=
  fun _ h => WellQuasiOrderedLE.finite_of_isAntichain h

/-- The example in the introduction, with spine the vertical axis and antichains the diagonals. -/
theorem natGrid_hasSpine : HasSpine (ℕ × ℕ) := by
  let C : Set (ℕ × ℕ) := {x | x.1 = 0}
  let block (c : C) : Set (ℕ × ℕ) := {x | x.1 + x.2 = c.1.2}
  refine ⟨C, ⟨⟨?_, subset_univ _, block, ?_, ?_, ?_, ?_⟩⟩⟩
  · intro x hx y hy _
    have hx' : x.1 = 0 := hx
    have hy' : y.1 = 0 := hy
    rcases le_total x.2 y.2 with h | h
    · exact Or.inl ⟨by simp [hx', hy'], h⟩
    · exact Or.inr ⟨by simp [hx', hy'], h⟩
  · intro c x hx y hy hne hle
    have h1 : x.1 ≤ y.1 := hle.1
    have h2 : x.2 ≤ y.2 := hle.2
    have hx' : x.1 + x.2 = c.1.2 := hx
    have hy' : y.1 + y.2 = c.1.2 := hy
    exact hne (Prod.ext (by omega) (by omega))
  · intro c
    have h : c.1.1 = 0 := c.2
    change c.1.1 + c.1.2 = c.1.2
    simp [h]
  · intro c d hne
    apply disjoint_left.mpr
    intro x hx hy
    apply hne
    apply Subtype.ext
    exact Prod.ext (c.2.trans (Eq.symm d.2)) ((show x.1 + x.2 = c.1.2 from hx).symm.trans hy)
  · apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨⟨(0, x.1 + x.2), rfl⟩, rfl⟩

/-- The Cartesian product example following `def:vacillating`. -/
theorem natGrid_orderDual_isVacillating : IsVacillating (ℕ × ℕᵒᵈ) := by
  apply isVacillating_of_finite_Icc
  intro x y
  apply ((Set.finite_Iic y.1).prod (Set.finite_Iic (show ℕ from x.2))).subset
  intro z hz
  exact ⟨hz.2.1, hz.1.2⟩

/-- The lexicographic product example following `def:vacillating`. -/
theorem natLex_orderDual_not_isVacillating : ¬ IsVacillating (ℕ ×ₗ ℕᵒᵈ) := by
  intro hv
  let B (n : ℕ) : Set (ℕ ×ₗ ℕᵒᵈ) := {x | (ofLex x).1 = n}
  have huniv : (univ : Set (ℕ ×ₗ ℕᵒᵈ)) = ⋃ n, B n := by
    ext x
    simp only [mem_univ, true_iff, mem_iUnion]
    exact ⟨(ofLex x).1, rfl⟩
  apply (hv univ (.of_ordConnected (isChain_of_trichotomous _) ordConnected_univ)).1
  refine ⟨B, huniv, ?_, ?_, ?_⟩
  · intro n
    let f (m : ℕ) : B n := ⟨toLex (n, OrderDual.toDual m), rfl⟩
    have hf : Function.Injective f := fun _ _ h => congrArg (fun x : B n => (ofLex x.1).2) h
    exact Set.infinite_coe_iff.mp (Infinite.of_injective f hf)
  · intro n
    refine (InvImage.wf (fun x : B n => (show ℕ from (ofLex x.1).2)) Nat.lt_wfRel.wf).mono ?_
    intro x y hxy
    rcases Prod.Lex.lt_iff.mp hxy with h | h
    · exact (h.ne ((show (ofLex y.1).1 = n from y.2).trans (Eq.symm x.2))).elim
    · exact h.2
  · intro i j hij x hx y hy
    exact Prod.Lex.lt_iff.mpr (Or.inl (by simpa only [show (ofLex x).1 = i from hx,
      show (ofLex y).1 = j from hy] using hij))

end AharoniKorman
