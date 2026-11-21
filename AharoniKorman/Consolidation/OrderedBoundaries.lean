import AharoniKorman.Consolidation.BoundarySplitting
import AharoniKorman.Consolidation.AtomicGerms

namespace AharoniKorman.Consolidation

open Set Completion

variable {α : Type*} [PartialOrder α]

theorem boundary_lt_principal_of_set_lt {C : Set α} {p : α} (hCp : ∀ x ∈ C, x < p)
    {X : H α} (hX : X ∈ boundaries C) : X < H.principal p := by
  obtain ⟨A, hAC, rfl⟩ | ⟨A, hAC, rfl⟩ := hX
  · exact (H.increasing_ofChain_lt_principal A p).2 (fun a => hCp a.1 (hAC a.2))
  · obtain ⟨a, ha⟩ := A.1.nonempty
    exact (H.decreasing_ofChain_lt_principal A p).2 ⟨⟨a, ha⟩, hCp a (hAC ha)⟩

theorem principal_lt_boundary_of_lt_set {C : Set α} {p : α} (hpC : ∀ x ∈ C, p < x)
    {X : H α} (hX : X ∈ boundaries C) : H.principal p < X := by
  obtain ⟨A, hAC, rfl⟩ | ⟨A, hAC, rfl⟩ := hX
  · obtain ⟨a, ha⟩ := A.1.nonempty
    exact (H.principal_lt_increasing_ofChain p A).2 ⟨⟨a, ha⟩, hpC a (hAC ha)⟩
  · exact (H.principal_lt_decreasing_ofChain p A).2 (fun a => hpC a.1 (hAC a.2))

theorem boundaries_strictLT {L R : Set α} (hLR : SetStrictLT L R) :
    SetStrictLT (boundaries L) (boundaries R) := by
  rintro X hX Y hY
  obtain ⟨A, hAL, rfl⟩ | ⟨A, hAL, rfl⟩ := hX <;>
    obtain ⟨B, hBR, rfl⟩ | ⟨B, hBR, rfl⟩ := hY
  · obtain ⟨b, hb⟩ := B.1.nonempty
    exact ((H.increasing_ofChain_lt_principal A b).2 (fun a => hLR (hAL a.2) (hBR hb))).trans
      ((H.principal_lt_increasing_ofChain b B).2 (B.2.exists_gt ⟨b, hb⟩))
  · exact (H.increasing_ofChain_lt_decreasing_ofChain A B).2 (fun a b => hLR (hAL a.2) (hBR b.2))
  · obtain ⟨a, ha⟩ := A.1.nonempty
    obtain ⟨b, hb⟩ := B.1.nonempty
    exact (H.decreasing_ofChain_lt_increasing_ofChain A B).2 ⟨⟨a, ha⟩, ⟨b, hb⟩, hLR (hAL ha) (hBR hb)⟩
  · obtain ⟨a, ha⟩ := A.1.nonempty
    exact ((H.decreasing_ofChain_lt_principal A a).2 (A.2.exists_lt ⟨a, ha⟩)).trans
      ((H.principal_lt_decreasing_ofChain a B).2 (fun b => hLR (hAL ha) (hBR b.2)))

/-- Local finiteness is stated in ambient coordinates for replacement intervals. -/
def FiniteInitialIntervals (J : Set α) : Prop := ∀ p ∈ J, (J ∩ Iic p).Finite

theorem FiniteInitialIntervals.omega {J : SaturatedChain α} (hJ : FiniteInitialIntervals (J : Set α))
    (hinf : (J : Set α).Infinite) : ∃ htop : J.NoTop, IsOmegaRepresentative ⟨J, htop⟩ := by
  have htop : J.NoTop := by
    rintro ⟨m, hm⟩
    exact hinf ((hJ m.1 m.2).subset (fun x hx => ⟨hx, hm ⟨x, hx⟩⟩))
  refine ⟨htop, fun j => ?_⟩
  exact ((hJ j.1 j.2).preimage Subtype.val_injective.injOn).subset (fun x hx => ⟨x.2, hx⟩)

theorem FiniteInitialIntervals.no_decreasing {J : Set α} (hJ : FiniteInitialIntervals J)
    (A : DecreasingChain α) (hAJ : (A.1 : Set α) ⊆ J) : False := by
  obtain ⟨a, ha⟩ := A.1.nonempty
  let T : IncreasingChain αᵒᵈ := ⟨A.1.dual.tail ⟨a, ha⟩, A.1.dual.tail_noTop ⟨a, ha⟩ A.2⟩
  exact increasingChain_infinite T ((hJ a (hAJ ha)).subset (fun x hx => ⟨hAJ hx.1, hx.2⟩))

theorem FiniteInitialIntervals.cofinal {J : Set α} (hJ : FiniteInitialIntervals J)
    (hc : IsChain (· ≤ ·) J) (A : IncreasingChain α) (hAJ : (A.1 : Set α) ⊆ J)
    {p : α} (hp : p ∈ J) : ∃ a : A.1, p < a.1 := by
  by_contra hno
  apply increasingChain_infinite A
  apply (hJ p hp).subset
  intro a ha
  refine ⟨hAJ ha, ?_⟩
  rcases hc.total (hAJ ha) hp with h | h
  · exact h
  · exact (lt_or_eq_of_le h).elim (fun hlt => False.elim (hno ⟨⟨a, ha⟩, hlt⟩)) (fun h => h.symm.le)

theorem omega_boundaries_singleton (A : IncreasingChain α)
    (hA : FiniteInitialIntervals (A.1 : Set α)) :
    boundaries (A.1 : Set α) = {H.increasing (IncreasingGerm.ofChain A)} := by
  apply Subset.antisymm
  · intro X hX
    obtain ⟨B, hBA, rfl⟩ | ⟨B, hBA, rfl⟩ := hX
    · apply Set.mem_singleton_iff.2
      apply congrArg H.increasing
      apply H.increasing.inj
      have hAA : H.increasing (IncreasingGerm.ofChain A) ∈ boundaries (A.1 : Set α) := Or.inl ⟨A, Subset.rfl, rfl⟩
      have hBB : H.increasing (IncreasingGerm.ofChain B) ∈ boundaries (A.1 : Set α) := Or.inl ⟨B, hBA, rfl⟩
      apply le_antisymm
      · apply (positive_profile_subset_iff A.1.saturated hBB hAA).1
        intro p hp
        obtain ⟨b, hpb⟩ := (IncreasingGerm.mem_lowerProfile_ofChain B p).1 hp
        exact (IncreasingGerm.mem_lowerProfile_ofChain A p).2 ⟨⟨b.1, hBA b.2⟩, hpb⟩
      · apply (positive_profile_subset_iff A.1.saturated hAA hBB).1
        intro p hp
        obtain ⟨a, hpa⟩ := (IncreasingGerm.mem_lowerProfile_ofChain A p).1 hp
        obtain ⟨b, hab⟩ := hA.cofinal A.1.isChain B hBA a.2
        exact (IncreasingGerm.mem_lowerProfile_ofChain B p).2 ⟨b, hpa.trans hab⟩
    · exact False.elim (hA.no_decreasing B hBA)
  · rintro X rfl
    exact Or.inl ⟨A, Subset.rfl, rfl⟩

end AharoniKorman.Consolidation
