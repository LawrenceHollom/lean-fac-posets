import AharoniKorman.Consolidation.LocalDual

namespace AharoniKorman.Consolidation

open Set Completion

variable {α : Type*} [PartialOrder α]

theorem boundaries_eq_empty_of_finite {C : Set α} (hC : C.Finite) : boundaries C = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  rintro X (⟨A, hAC, _⟩ | ⟨A, hAC, _⟩)
  · exact increasingChain_infinite A (hC.subset hAC)
  · exact decreasingChain_infinite A (hC.subset hAC)

theorem increasingGerm_tail_eq (A : IncreasingChain α) (a : A.1) :
    IncreasingGerm.ofChain (⟨A.1.tail a, A.1.tail_noTop a A.2⟩ : IncreasingChain α) =
      IncreasingGerm.ofChain A := by
  apply IncreasingGerm.ofChain_eq_iff.2
  exact ⟨A.1.tail a, A.1.tail a,
    ⟨Subset.rfl, fun _ _ _ hy _ => hy⟩, A.1.tail_final a, MutuallyFiniteIncomparability.refl _⟩

theorem positive_boundary_ordered_union {L R : Set α} (hLR : SetStrictLT L R)
    {g : IncreasingGerm α} (hg : H.increasing g ∈ boundaries (L ∪ R)) :
    H.increasing g ∈ boundaries L ∨ H.increasing g ∈ boundaries R := by
  classical
  obtain ⟨A, hAC, rfl⟩ := increasingGerm_mem_boundaries hg
  by_cases hmeet : ∃ a : A.1, a.1 ∈ R
  · obtain ⟨a, haR⟩ := hmeet
    let T : IncreasingChain α := ⟨A.1.tail a, A.1.tail_noTop a A.2⟩
    have hTR : (T.1 : Set α) ⊆ R := by
      rintro x ⟨hxA, hax⟩
      rcases hAC hxA with hxL | hxR
      · exact False.elim ((hLR hxL haR).not_ge hax)
      · exact hxR
    exact Or.inr (Or.inl ⟨T, hTR, congrArg H.increasing (increasingGerm_tail_eq A a).symm⟩)
  · refine Or.inl (Or.inl ⟨A, fun x hx => ?_, rfl⟩)
    exact (hAC hx).resolve_right (fun hxR => hmeet ⟨⟨x, hx⟩, hxR⟩)

theorem negative_boundary_ordered_union {L R : Set α} (hLR : SetStrictLT L R)
    {g : DecreasingGerm α} (hg : H.decreasing g ∈ boundaries (L ∪ R)) :
    H.decreasing g ∈ boundaries L ∨ H.decreasing g ∈ boundaries R := by
  have hRL : SetStrictLT (α := αᵒᵈ) R L := fun _ hr _ hl => hLR hl hr
  have hd : H.increasing g.toDual ∈ boundaries (α := αᵒᵈ) (R ∪ L) := by
    exact (Set.union_comm L R) ▸ (boundary_dual_mem (α := α) hg)
  rcases positive_boundary_ordered_union hRL hd with hR | hL
  · exact Or.inr (boundary_dual_mem (α := αᵒᵈ) hR)
  · exact Or.inl (boundary_dual_mem (α := αᵒᵈ) hL)

theorem boundaries_ordered_union {L R : Set α} (hLR : SetStrictLT L R) :
    boundaries (L ∪ R) = boundaries L ∪ boundaries R := by
  apply Subset.antisymm
  · intro X hX
    obtain ⟨A, hAC, hA⟩ | ⟨A, hAC, hA⟩ := hX
    · rw [hA]; exact positive_boundary_ordered_union hLR (Or.inl ⟨A, hAC, rfl⟩)
    · rw [hA]; exact negative_boundary_ordered_union hLR (Or.inr ⟨A, hAC, rfl⟩)
  · exact union_subset (boundaries_mono subset_union_left) (boundaries_mono subset_union_right)

end AharoniKorman.Consolidation
