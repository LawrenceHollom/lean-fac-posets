import AharoniKorman.Preliminaries.FACCore
import Mathlib.Data.Set.Card

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

private theorem finite_upperLevel (hfac : IsFAC α) (hinterval : ∀ a b : α, (Icc a b).Finite)
    (a : α) (k : ℕ) : {x | a ≤ x ∧ (Icc a x).ncard = k}.Finite := by
  apply hfac.antichain_finite
  intro x hx y hy hne hxy
  have hlt := lt_of_le_of_ne hxy hne
  have hx' : a ≤ x ∧ (Icc a x).ncard = k := hx
  have hy' : a ≤ y ∧ (Icc a y).ncard = k := hy
  have hsub : Icc a x ⊂ Icc a y := by
    refine ssubset_iff_subset_ne.mpr ⟨fun z hz => ⟨hz.1, hz.2.trans hxy⟩, ?_⟩
    intro he
    have hmem : y ∈ Icc a x := he ▸ (show y ∈ Icc a y from ⟨hy'.1, le_rfl⟩)
    exact hlt.not_ge hmem.2
  exact (Set.ncard_lt_ncard hsub (hinterval a y)).ne (hx'.2.trans hy'.2.symm)

/-- The bounded levels around a finite maximal antichain exhaust a locally finite FAC poset.
Interval cardinality is strictly monotone in each of the two directions from the antichain. -/
theorem IsFAC.exists_finite_exhaustion (hfac : IsFAC α)
    (hinterval : ∀ a b : α, (Icc a b).Finite) :
    ∃ S : ℕ → Finset α, Monotone S ∧ ∀ x : α, ∃ n, x ∈ S n := by
  classical
  obtain ⟨A, _, hAfin, _, hmax⟩ := hfac.exists_commonIncomparables_core (fun _ => True) trivial
  have hcover (x : α) : ∃ a ∈ A, Comparable a x := by
    by_contra h
    have hx : x ∈ commonIncomparables A := by
      intro a ha
      exact not_symmGen_iff.mp fun hc => h ⟨a, ha, hc⟩
    exact hmax x hx trivial
  let upper (a : α) (k : ℕ) : Set α := {x | a ≤ x ∧ (Icc a x).ncard = k}
  let lower (a : α) (k : ℕ) : Set α := {x | x ≤ a ∧ (Icc x a).ncard = k}
  have interval_dual (b c : αᵒᵈ) : Icc b c = (Icc (show α from c) (show α from b)) := by
    ext z
    exact and_comm
  have finite_lower (a : α) (k : ℕ) : (lower a k).Finite := by
    have h := finite_upperLevel (α := αᵒᵈ) hfac.orderDual
      (fun b c => interval_dual b c ▸ hinterval c b) a k
    have heq : lower a k = {x : αᵒᵈ | @LE.le αᵒᵈ _ a x ∧ (@Icc αᵒᵈ _ a x).ncard = k} := by
      ext x
      have hcard : (@Icc αᵒᵈ _ (OrderDual.toDual a) (OrderDual.toDual x)).ncard =
          (Icc x a).ncard := congrArg Set.ncard (interval_dual (OrderDual.toDual a) (OrderDual.toDual x))
      exact and_congr_right fun _ => ⟨hcard.trans, hcard.symm.trans⟩
    rw [heq]
    exact h
  let box (n : ℕ) : Set α :=
    ⋃ a ∈ A, ⋃ k ∈ (↑(Finset.range (n + 1)) : Set ℕ), upper a k ∪ lower a k
  have hbox (n : ℕ) : (box n).Finite := hAfin.biUnion fun a _ =>
    (Finset.range (n + 1)).finite_toSet.biUnion fun k _ =>
      (finite_upperLevel hfac hinterval a k).union (finite_lower a k)
  refine ⟨fun n => (hbox n).toFinset, ?_, ?_⟩
  · intro m n hmn x hx
    obtain ⟨a, ha, k, hk, hxk⟩ := by
      simpa only [hbox, Set.Finite.mem_toFinset, box, mem_iUnion, exists_prop] using hx
    refine (hbox n).mem_toFinset.mpr ?_
    exact mem_iUnion₂.mpr ⟨a, ha, mem_iUnion₂.mpr ⟨k,
      Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le (Nat.succ_le_succ hmn)), hxk⟩⟩
  · intro x
    obtain ⟨a, ha, hax | hxa⟩ := hcover x
    · refine ⟨(Icc a x).ncard, (hbox _).mem_toFinset.mpr ?_⟩
      exact mem_iUnion₂.mpr ⟨a, ha, mem_iUnion₂.mpr ⟨_,
        Finset.mem_range.mpr (Nat.lt_succ_self _), Or.inl ⟨hax, rfl⟩⟩⟩
    · refine ⟨(Icc x a).ncard, (hbox _).mem_toFinset.mpr ?_⟩
      exact mem_iUnion₂.mpr ⟨a, ha, mem_iUnion₂.mpr ⟨_,
        Finset.mem_range.mpr (Nat.lt_succ_self _), Or.inr ⟨hxa, rfl⟩⟩⟩

/-- The countability observation following `thm:main` in the introduction. -/
theorem IsFAC.countable_of_finite_Icc (hfac : IsFAC α)
    (hinterval : ∀ a b : α, (Icc a b).Finite) : Countable α := by
  obtain ⟨S, _, hS⟩ := hfac.exists_finite_exhaustion hinterval
  have huniv : (⋃ n, (↑(S n) : Set α)) = univ :=
    eq_univ_of_forall fun x => mem_iUnion.mpr (hS x)
  have hcount : (univ : Set α).Countable := huniv ▸
    countable_iUnion (fun n => (S n).finite_toSet.countable)
  exact countable_univ_iff.mp hcount

end AharoniKorman
