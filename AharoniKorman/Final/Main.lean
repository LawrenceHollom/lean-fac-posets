import AharoniKorman.Final.TubeFromChain
import AharoniKorman.Tube.MaximalImpliesSpine
import AharoniKorman.Preliminaries.FiniteIntervals
import Mathlib.SetTheory.Cardinal.Order

namespace AharoniKorman

variable {α : Type*} [PartialOrder α]

/-- Paper `thm:main` and `thm:main-on-first-page`, using the definition of vacillation. -/
theorem main_theorem [Countable α] (hfac : IsFAC α) (hvac : IsVacillating α) : HasSpine α := by
  obtain ⟨T, hT⟩ := exists_maximalTube hfac hvac
  exact maximalTube_hasSpine hfac hT

/-- `thm:no-infinite-interval`, deduced from the main theorem as in the introduction. -/
theorem hasSpine_of_finite_intervals (hfac : IsFAC α)
    (hfin : ∀ a b : α, (Set.Icc a b).Finite) : HasSpine α := by
  let := hfac.countable_of_finite_Icc hfin
  exact main_theorem hfac (isVacillating_of_finite_Icc hfin)

/-- The difference outside a strongly maximal chain is no larger than the difference inside it. -/
def IsStronglyMaximalChain (C : Set α) : Prop :=
  IsChain (· ≤ ·) C ∧ ∀ D : Set α, IsChain (· ≤ ·) D →
    Cardinal.mk (↥(D \ C)) ≤ Cardinal.mk (↥(C \ D))

theorem IsStronglyMaximalChain.isMaxChain {C : Set α} (h : IsStronglyMaximalChain C) :
    IsMaxChain (· ≤ ·) C := by
  refine ⟨h.1, fun D hD hCD => Set.Subset.antisymm hCD ?_⟩
  have hcard := h.2 D hD
  have hdiff : C \ D = ∅ := Set.sdiff_eq_empty.mpr hCD
  rw [hdiff, Cardinal.mk_eq_zero ↥(∅ : Set α)] at hcard
  have hemp := Cardinal.mk_set_eq_zero_iff.mp (nonpos_iff_eq_zero.mp hcard)
  exact Set.sdiff_eq_empty.mp hemp

/-- The observation in the concluding section: send a point of `D \ C` to the point of `C`
in its antichain. No two points of `D` lie in the same antichain. -/
theorem SpineData.isStronglyMaximalChain {C : Set α}
    (S : SpineData (Set.univ : Set α) C) : IsStronglyMaximalChain C := by
  classical
  refine ⟨S.chain, fun D hD => ?_⟩
  have belongs (x : ↥(D \ C)) : ∃ c : C, x.1 ∈ S.block c := by
    apply Set.mem_iUnion.mp
    rw [S.iUnion_blocks]
    exact Set.mem_univ _
  choose rep hrep using belongs
  have incomp (x : ↥(D \ C)) : Incomparable x.1 (rep x).1 := by
    have hne : x.1 ≠ (rep x).1 := fun h => x.2.2 (h.symm ▸ (rep x).2)
    exact ⟨S.block_antichain _ (hrep x) (S.mem_block _) hne,
      S.block_antichain _ (S.mem_block _) (hrep x) hne.symm⟩
  let f (x : ↥(D \ C)) : ↥(C \ D) :=
    ⟨(rep x).1, (rep x).2, fun h => (not_symmGen_iff.mpr (incomp x)) (hD.total x.2.1 h)⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro x y hxy
  by_contra hne
  have hrep_eq : rep x = rep y :=
    Subtype.ext (congrArg (fun p : ↥(C \ D) => p.1) hxy)
  have hval : x.1 ≠ y.1 := fun h => hne (Subtype.ext h)
  have hy := hrep_eq.symm ▸ hrep y
  rcases hD x.2.1 y.2.1 hval with h | h
  · exact S.block_antichain _ (hrep x) hy hval h
  · exact S.block_antichain _ hy (hrep x) hval.symm h

/-- The strongly maximal chain consequence in the concluding section. -/
theorem exists_stronglyMaximalChain [Countable α] (hfac : IsFAC α)
    (hvac : IsVacillating α) : ∃ C : Set α, IsStronglyMaximalChain C := by
  obtain ⟨C, ⟨S⟩⟩ := main_theorem hfac hvac
  exact ⟨C, S.isStronglyMaximalChain⟩

end AharoniKorman
