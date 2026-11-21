import AharoniKorman.Consolidation.AtomicRepresentatives
import AharoniKorman.Consolidation.BoundaryOrder

/-! Principal separators isolating atomic germs in a fixed chain. -/

namespace AharoniKorman.Consolidation

open Set Completion

variable {α : Type*} [PartialOrder α]

theorem finite_interval_in_omega_subchain {C : Set α} (hC : IsChain (· ≤ ·) C)
    (A : IncreasingChain α) (hA : IsOmegaRepresentative A) (hAC : (A.1 : Set α) ⊆ C)
    (a b : A.1) : {x : α | x ∈ C ∧ a.1 ≤ x ∧ x ≤ b.1}.Finite := by
  apply ((hA b).image Subtype.val).subset
  intro x hx
  have hxA : x ∈ A.1 := A.1.saturated.2 a.2 b.2 hx.2.1 hx.2.2
    (fun y hy => hC.total hx.1 (hAC hy))
  exact ⟨⟨x, hxA⟩, hx.2.2, rfl⟩

theorem no_boundary_between_omega_point_and_end {C : Set α}
    (hC : IsChain (· ≤ ·) C) (A : IncreasingChain α) (hA : IsOmegaRepresentative A)
    (hAC : (A.1 : Set α) ⊆ C) (a : A.1) {Y : H α} (hYC : Y ∈ boundaries C) :
    ¬(H.principal a.1 < Y ∧ Y < H.increasing (IncreasingGerm.ofChain A)) := by
  rintro ⟨haY, hYA⟩
  obtain ⟨B, hBC, rfl⟩ | ⟨B, hBC, rfl⟩ := hYC
  · obtain ⟨q, haq⟩ := (H.principal_lt_increasing_ofChain a.1 B).1 haY
    obtain ⟨b, hb⟩ := (H.increasing_ofChain_lt_increasing_ofChain B A).1 hYA
    let T : IncreasingChain α := ⟨B.1.tail q, B.1.tail_noTop q B.2⟩
    apply increasingChain_infinite T
    apply (finite_interval_in_omega_subchain hC A hA hAC a b).subset
    intro x hx
    exact ⟨hBC hx.1, haq.le.trans hx.2, (hb ⟨x, hx.1⟩).le⟩
  · have haB := (H.principal_lt_decreasing_ofChain a.1 B).1 haY
    obtain ⟨q, b, hqb⟩ := (H.decreasing_ofChain_lt_increasing_ofChain B A).1 hYA
    let I : Set α := {x | x ∈ B.1 ∧ x ≤ q.1}
    have hI : IsInitialSegment I B.1 :=
      ⟨fun _ hx => hx.1, fun {_ _} hx hy hyx => ⟨hy, hyx.trans hx.2⟩⟩
    let T₀ := B.1.restrict .decreasing I hI ⟨q.1, q.2, le_rfl⟩
    let T : DecreasingChain α := ⟨T₀, B.initialSegment_noBottom T₀ hI⟩
    apply decreasingChain_infinite T
    apply (finite_interval_in_omega_subchain hC A hA hAC a b).subset
    intro x hx
    exact ⟨hBC hx.1, (haB ⟨x, hx.1⟩).le, hx.2.trans hqb.le⟩

/-- A principal point of the original chain separates an atom from all earlier limits. -/
theorem positiveAtom_isolated {C : Set α} (hC : IsSaturatedChain C)
    {g : IncreasingGerm α} (hg : IsPositiveAtom g)
    (hgC : H.increasing g ∈ boundaries C) :
    ∃ p ∈ C, H.principal p < H.increasing g ∧
      ∀ Y ∈ boundaries C, Y < H.increasing g → Y < H.principal p := by
  obtain ⟨B, hBC, hBg⟩ := increasingGerm_mem_boundaries hgC
  obtain ⟨A, hAB, hAomega, hAg⟩ := hg.exists_omega_finalSegment B hBg
  change IncreasingGerm.ofChain A = g at hAg
  have hAC := hAB.1.trans hBC
  obtain ⟨p, hp⟩ := A.1.nonempty
  have hpg : H.principal p < H.increasing g := by
    rw [← hAg]
    exact IncreasingGerm.representative_mem_lowerProfile A ⟨p, hp⟩
  refine ⟨p, hAC hp, hpg, fun Y hYC hYg => ?_⟩
  have hne : Y ≠ H.principal p := by
    intro heq
    exact principal_not_mem_boundaries C p (heq ▸ hYC)
  rcases boundary_comparable_principal hC hYC (hAC hp) with hYp | hpY
  · exact lt_of_le_of_ne hYp hne
  · exfalso
    apply no_boundary_between_omega_point_and_end hC.1 A hAomega hAC ⟨p, hp⟩ hYC
    exact ⟨lt_of_le_of_ne hpY hne.symm, by simpa only [hAg] using hYg⟩

theorem negativeAtom_isolated {C : Set α} (hC : IsSaturatedChain C)
    {g : DecreasingGerm α} (hg : IsNegativeAtom g)
    (hgC : H.decreasing g ∈ boundaries C) :
    ∃ p ∈ C, H.decreasing g < H.principal p ∧
      ∀ Y ∈ boundaries C, H.decreasing g < Y → H.principal p < Y := by
  obtain ⟨p, hp, hpg, hsep⟩ :=
    positiveAtom_isolated hC.dual hg (boundary_dual_mem hgC)
  refine ⟨p, hp, (H.dual_lt_dual (H.principal (α := α) p) (H.decreasing g)).1 hpg,
    fun Y hYC hgY => ?_⟩
  exact (H.dual_lt_dual Y (H.principal p)).1
    (hsep Y.dual (boundary_dual_mem hYC) ((H.dual_lt_dual Y (H.decreasing g)).2 hgY))

end AharoniKorman.Consolidation
