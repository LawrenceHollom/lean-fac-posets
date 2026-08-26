import AharoniKorman.Preliminaries.Spine
import AharoniKorman.Preliminaries.Relations

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- Every point of `T` is incomparable with only finitely many points of `T`. -/
def IsTube (T : Set α) : Prop :=
  ∀ x ∈ T, (T ∩ incomparableSet x).Finite

/-- Inclusion-maximality among tubes, written in the one-point form used in the paper. -/
def IsMaximalTube (T : Set α) : Prop :=
  IsTube T ∧ ∀ x ∉ T, ¬ IsTube (insert x T)

theorem IsTube.mono {S T : Set α} (hT : IsTube T) (hST : S ⊆ T) : IsTube S := by
  intro x hx
  exact (hT x (hST hx)).subset (inter_subset_inter_left _ hST)

/-- Every chain is a tube. -/
theorem IsChain.isTube {C : Set α} (hC : IsChain (· ≤ ·) C) : IsTube C := by
  intro x hx
  have hEmpty : C ∩ incomparableSet x = ∅ := by
    ext y
    constructor
    · rintro ⟨hy, hinc⟩
      have hne : y ≠ x := (show Incomparable x y from hinc).symm.ne
      rcases hC hx hy hne.symm with hxy | hyx
      · exact False.elim ((show Incomparable x y from hinc).not_le hxy)
      · exact False.elim ((show Incomparable x y from hinc).not_ge hyx)
    · simp
  rw [hEmpty]
  exact Set.finite_empty

/-- The useful outside-point characterization of maximal tubes. -/
theorem isMaximalTube_iff (T : Set α) :
    IsMaximalTube T ↔ IsTube T ∧ ∀ x ∉ T, (T ∩ incomparableSet x).Infinite := by
  sorry

end AharoniKorman
