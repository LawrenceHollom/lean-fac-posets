import AharoniKorman.Consolidation.Genuine
import AharoniKorman.Completion.ChainSuborder

/-! Genuine boundary orders of saturated subchains. The formal endpoints of
the ambient completion are never elements of these boundary orders. -/

namespace AharoniKorman.Consolidation

open Set Completion

variable {α : Type*} [PartialOrder α]

theorem MaximalChains.isSaturated (C : MaximalChains α) : IsSaturatedChain C.carrier := by
  refine ⟨C.isMaximal.1, ?_⟩
  intro a b x _ _ _ _ hx
  have hchain := C.isMaximal.1.insert (fun y hy _ => hx y hy)
  have heq := C.isMaximal.2 hchain (Set.subset_insert x C.carrier)
  exact heq.symm ▸ Set.mem_insert x C.carrier

theorem boundary_dual_mem {C : Set α} {X : H α} (hX : X ∈ boundaries C) :
    X.dual ∈ boundaries (α := αᵒᵈ) C := by
  obtain ⟨A, hAC, rfl⟩ | ⟨A, hAC, rfl⟩ := hX
  · refine Or.inr ⟨A.toDual, hAC, ?_⟩
    simp only [H.dual, IncreasingGerm.toDual_ofChain]
  · exact Or.inl ⟨A.toDual, hAC, rfl⟩

theorem boundary_has_preimage {C : Set α} (hC : IsSaturatedChain C)
    {X : H α} (hX : X ∈ boundaries C) :
    ∃ Y : H C, H.map (OrderEmbedding.subtype C)
      (saturationPreserving_subtype_of_saturated hC) Y = X := by
  obtain ⟨A, hAC, rfl⟩ | ⟨A, hAC, rfl⟩ := hX
  · refine ⟨H.increasing (IncreasingGerm.ofChain (A.within hAC)), ?_⟩
    simp only [H.map, IncreasingGerm.map_ofChain, IncreasingChain.map_within]
  · refine ⟨H.decreasing (DecreasingGerm.ofChain (A.within hAC)), ?_⟩
    simp only [H.map, DecreasingGerm.map_ofChain, DecreasingChain.map_within]

theorem boundaries_isChain {C : Set α} (hC : IsSaturatedChain C) :
    IsChain (· ≤ ·) (boundaries C) := by
  classical
  let : LinearOrder C := hC.1.linearOrder
  intro X hX Y hY _
  obtain ⟨X', rfl⟩ := boundary_has_preimage hC hX
  obtain ⟨Y', rfl⟩ := boundary_has_preimage hC hY
  exact (le_total X' Y').imp (fun h => (H.map_le_map _ _ _ _).2 h)
    (fun h => (H.map_le_map _ _ _ _).2 h)

theorem boundary_comparable_principal {C : Set α} (hC : IsSaturatedChain C)
    {X : H α} (hX : X ∈ boundaries C) {p : α} (hp : p ∈ C) :
    X ≤ H.principal p ∨ H.principal p ≤ X := by
  classical
  let : LinearOrder C := hC.1.linearOrder
  obtain ⟨X', rfl⟩ := boundary_has_preimage hC hX
  let e := H.mapEmbedding (α := C) (β := α) (OrderEmbedding.subtype C)
    (saturationPreserving_subtype_of_saturated hC)
  rcases le_total X' (H.principal (⟨p, hp⟩ : C)) with h | h
  · exact Or.inl (e.monotone h)
  · exact Or.inr (e.monotone h)

theorem positive_profile_subset_iff {C : Set α} (hC : IsSaturatedChain C)
    {g h : IncreasingGerm α}
    (hg : H.increasing g ∈ boundaries C) (hh : H.increasing h ∈ boundaries C) :
    g.lowerProfile ⊆ h.lowerProfile ↔ H.increasing g ≤ H.increasing h := by
  constructor
  · intro hprofile
    rcases (boundaries_isChain hC).total hg hh with hle | hle
    · exact hle
    by_contra hnot
    have hlt : H.increasing h < H.increasing g := lt_iff_le_not_ge.2 ⟨hle, hnot⟩
    obtain ⟨p, hhp, hpg⟩ := H.exists_principal_between_increasing hlt
    exact (hhp.trans (hprofile hpg)).false
  · intro hle p hp
    exact (show H.principal p < H.increasing g from hp).trans_le hle

theorem negative_profile_subset_iff {C : Set α} (hC : IsSaturatedChain C)
    {g h : DecreasingGerm α}
    (hg : H.decreasing g ∈ boundaries C) (hh : H.decreasing h ∈ boundaries C) :
    g.upperProfile ⊆ h.upperProfile ↔ H.decreasing h ≤ H.decreasing g := by
  have hdual := positive_profile_subset_iff hC.dual (boundary_dual_mem hg) (boundary_dual_mem hh)
  exact hdual.trans (H.dual_le_dual (H.decreasing g) (H.decreasing h))

theorem increasingChain_infinite (A : IncreasingChain α) : (A.1 : Set α).Infinite := by
  intro hfin
  obtain ⟨m, hm, hmax⟩ := hfin.exists_maximal A.1.nonempty
  obtain ⟨n, hmn⟩ := A.2.exists_gt ⟨m, hm⟩
  exact hmn.not_ge (hmax n.2 hmn.le)

theorem decreasingChain_infinite (A : DecreasingChain α) : (A.1 : Set α).Infinite :=
  increasingChain_infinite A.toDual

theorem increasingGerm_mem_boundaries {C : Set α} {g : IncreasingGerm α}
    (hg : H.increasing g ∈ boundaries C) :
    ∃ A : IncreasingChain α, (A.1 : Set α) ⊆ C ∧ IncreasingGerm.ofChain A = g := by
  obtain ⟨A, hAC, h⟩ | ⟨A, _, h⟩ := hg
  · exact ⟨A, hAC, (H.increasing.inj h).symm⟩
  · cases h

theorem boundary_incomparable_principal {J : Set α} {p : α}
    (hJ : J ⊆ incomparableSet p) {X : H α} (hX : X ∈ boundaries J) :
    Incomparable X (H.principal p) := by
  obtain ⟨B, hBJ, rfl⟩ | ⟨B, hBJ, rfl⟩ := hX
  · constructor
    · intro hle
      rcases le_iff_eq_or_lt.1 hle with heq | hlt
      · cases heq
      · obtain ⟨b, hb⟩ := B.1.nonempty
        exact (hJ (hBJ hb)).not_ge ((H.increasing_ofChain_lt_principal B p).1 hlt ⟨b, hb⟩).le
    · intro hle
      rcases le_iff_eq_or_lt.1 hle with heq | hlt
      · cases heq
      · obtain ⟨b, hpb⟩ := (H.principal_lt_increasing_ofChain p B).1 hlt
        exact (hJ (hBJ b.2)).not_le hpb.le
  · constructor
    · intro hle
      rcases le_iff_eq_or_lt.1 hle with heq | hlt
      · cases heq
      · obtain ⟨b, hbp⟩ := (H.decreasing_ofChain_lt_principal B p).1 hlt
        exact (hJ (hBJ b.2)).not_ge hbp.le
    · intro hle
      rcases le_iff_eq_or_lt.1 hle with heq | hlt
      · cases heq
      · obtain ⟨b, hb⟩ := B.1.nonempty
        exact (hJ (hBJ hb)).not_le ((H.principal_lt_decreasing_ofChain p B).1 hlt ⟨b, hb⟩).le

end AharoniKorman.Consolidation
