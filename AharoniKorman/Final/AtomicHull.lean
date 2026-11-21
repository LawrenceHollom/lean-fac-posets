import AharoniKorman.Consolidation.AtomicOrder
import AharoniKorman.Consolidation.ReplacementGeometry
import AharoniKorman.Final.HullTransfer

namespace AharoniKorman.Consolidation

open Set Completion

variable {α : Type*} [PartialOrder α]

private theorem atomicallyConsolidated_dual {C : Set α} (hC : IsAtomicallyConsolidated C) :
    IsAtomicallyConsolidated (α := αᵒᵈ) C := by
  rintro D hD ⟨f⟩
  have heq := hC D hD.dual ⟨f.dual⟩
  ext X
  constructor
  · intro hX
    have h := AtomicWitness.atomic_dual_mem (α := αᵒᵈ) hX
    have h' : X.dual ∈ atomicBoundaries (α := α) C := heq ▸ h
    exact (H.dual_dual (α := αᵒᵈ) X) ▸ AtomicWitness.atomic_dual_mem (α := α) h'
  · intro hX
    have h := AtomicWitness.atomic_dual_mem (α := αᵒᵈ) hX
    have h' : X.dual ∈ atomicBoundaries (α := α) D := heq.symm ▸ h
    exact (H.dual_dual (α := αᵒᵈ) X) ▸ AtomicWitness.atomic_dual_mem (α := α) h'

private theorem LocalReplacement.not_atomicallyConsolidated_of_omega {C : MaximalChains α}
    (Q : LocalReplacement C) (homega : IsOmegaRepresentative Q.replacement) :
    ¬IsAtomicallyConsolidated C.carrier := by
  classical
  have hnew : IsAtomicGerm Q.newBoundary.1 := ⟨Q.replacement, rfl, homega⟩
  let f (X : AtomProfile C.carrier) : AtomProfile Q.target.carrier := by
    let Y := Q.mapBoundary ⟨X.1, X.2.1⟩
    refine ⟨Y.1, Y.2, ?_⟩
    by_cases hx : X.1 ∈ boundaries (Q.middle : Set α)
    · change IsAtomicGerm (Q.mapBoundary ⟨X.1, X.2.1⟩).1
      rw [Q.mapBoundary_eq_new hx]
      exact hnew
    · change IsAtomicGerm (Q.mapBoundary ⟨X.1, X.2.1⟩).1
      rw [Q.mapBoundary_eq_self hx]
      exact X.2.2
  have hf : ∀ X : AtomProfile C.carrier, GermImproves (f X).1 X.1 := by
    intro X
    change GermImproves (Q.mapBoundary ⟨X.1, X.2.1⟩).1 X.1
    by_cases hx : X.1 ∈ boundaries (Q.middle : Set α)
    · rw [Q.mapBoundary_eq_new hx]
      exact Q.middle_properties.2.2 _ hx
    · rw [Q.mapBoundary_eq_self hx]
      exact GermImproves.refl _
  let : LinearOrder (AtomProfile C.carrier) :=
    ((boundaries_isChain C.isSaturated).mono inter_subset_left).linearOrder
  have hstrict : StrictMono f := by
    intro X Y hXY
    exact Q.mapBoundary_strict (a := ⟨X.1, X.2.1⟩) (b := ⟨Y.1, Y.2.1⟩) hXY
  let witness : AtomicWitness C.carrier Q.target.carrier :=
    ⟨OrderEmbedding.ofStrictMono f hstrict, fun X => (hf X).1, fun X => (hf X).2⟩
  intro hC
  have hEq := hC Q.target.carrier Q.target.isSaturated ⟨witness⟩
  have hmem : Q.newBoundary.1 ∈ atomicBoundaries Q.target.carrier := ⟨Q.newBoundary.2, hnew⟩
  have hmem' : Q.newBoundary.1 ∈ atomicBoundaries C.carrier := hEq ▸ hmem
  exact Q.newBoundary_not_old hmem'.1

private theorem IncreasingFan.not_atomicallyConsolidated
    (hsc : IsScattered α) (hvac : IsVacillating α) {C : MaximalChains α}
    (G : IncreasingFan C) : ¬IsAtomicallyConsolidated C.carrier := by
  obtain ⟨Q⟩ := G.exists_replacement
  let : Nonempty Q.replacement.1 := Q.replacement.1.nonempty.to_subtype
  let : NoMaxOrder Q.replacement.1 := ⟨Q.replacement.2.exists_gt⟩
  obtain ⟨f, hf⟩ := Nat.exists_strictMono Q.replacement.1
  obtain ⟨B, hB, homega⟩ := exists_omega_subchain_of_embedding hsc hvac Q.replacement.1
    ⟨OrderEmbedding.ofStrictMono f hf⟩
  let R : LocalReplacement C := {
    Q with
    replacement := B
    left_replacement := fun _ hl _ hb => Q.left_replacement hl (hB hb)
    replacement_right := fun _ hb _ hr => Q.replacement_right (hB hb) hr
    replacement_target := hB.trans Q.replacement_target
    profile_control := fun hi y hy => Q.profile_control hi y (hB hy)
    separating_point := by
      obtain ⟨k, hk, hi⟩ := Q.separating_point
      exact ⟨k, hk, hB.trans hi⟩ }
  exact R.not_atomicallyConsolidated_of_omega homega

private theorem atomic_consolidated_point_trace_finite (hfac : IsFAC α)
    (hsc : IsScattered α) (hvac : IsVacillating α) (C : MaximalChains α)
    (hC : IsAtomicallyConsolidated C.carrier) (k : α) (hk : k ∈ C.carrier) :
    (finiteIncomparabilityHull C.carrier ∩ incomparableSet k).Finite := by
  by_contra hinf
  obtain ⟨y, hmono | hanti⟩ := hfac.exists_strictMono_or_strictAnti_sequence_in hinf
  · let G : IncreasingFan C := {
      point := k
      point_mem := hk
      seq := fun n => (y n).1
      strict := fun _ _ h => hmono h
      incomparable := fun n => (y n).2.2.symm
      finite_trace := fun n => (y n).2.1 }
    exact G.not_atomicallyConsolidated hsc hvac hC
  · let G : IncreasingFan C.dual := {
      point := k
      point_mem := hk
      seq := fun n => (y n).1
      strict := fun _ _ h => hanti h
      incomparable := fun n => (y n).2.2
      finite_trace := fun n => (trace_dual_eq C.carrier (y n).1).symm ▸ (y n).2.1 }
    exact IncreasingFan.not_atomicallyConsolidated (α := αᵒᵈ)
      (IsScattered.orderDual (α := α) hsc) (IsVacillating.orderDual (α := α) hvac) G
      (atomicallyConsolidated_dual (α := α) hC)

/-- Paper `lem:find-maximal-tube`, using the finite-trace replacement geometry
on the signed atomic profile. -/
theorem atomicallyConsolidated_hull_maximalTube (hfac : IsFAC α)
    (hsc : IsScattered α) (hvac : IsVacillating α) (C : MaximalChains α)
    (hC : IsAtomicallyConsolidated C.carrier) :
    C.carrier ⊆ finiteIncomparabilityHull C.carrier ∧
      IsMaximalTube (finiteIncomparabilityHull C.carrier) :=
  ⟨subset_finiteIncomparabilityHull C.isMaximal.1, hull_maximal_of_isTube C.isMaximal.1
    (hull_isTube_of_chain_traces_finite C (atomic_consolidated_point_trace_finite hfac hsc hvac C hC))⟩

end AharoniKorman.Consolidation
