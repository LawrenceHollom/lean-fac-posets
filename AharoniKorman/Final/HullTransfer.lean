import AharoniKorman.Completion.TraceTransfer
import AharoniKorman.Consolidation.BoundaryOrder
import AharoniKorman.Final.HullConvexity

namespace AharoniKorman.Consolidation

open Set Completion

variable {α : Type*} [PartialOrder α]

theorem trace_dual_eq (C : Set α) (x : α) :
    C ∩ incomparableSet (α := αᵒᵈ) x = C ∩ incomparableSet (α := α) x := by
  ext y
  exact ⟨fun ⟨hy, h⟩ => ⟨hy, h.symm⟩, fun ⟨hy, h⟩ => ⟨hy, h.symm⟩⟩

theorem maximal_chain_contact (C : MaximalChains α) (x : α) :
    ∃ k ∈ C.carrier, x = k ∨ Incomparable x k := by
  classical
  by_cases hx : x ∈ C.carrier
  · exact ⟨x, hx, Or.inl rfl⟩
  have hmax : IsMaximalChainIn C.carrier (univ : Set α) :=
    ⟨subset_univ _, C.isMaximal.1, fun h _ hs => C.isMaximal.2 h hs⟩
  obtain ⟨k, hk, hxk⟩ := hmax.exists_incomparable (Set.mem_univ x) hx
  exact ⟨k, hk, Or.inr hxk⟩

theorem hull_isTube_of_chain_traces_finite (C : MaximalChains α)
    (hfinite : ∀ k ∈ C.carrier, (finiteIncomparabilityHull C.carrier ∩ incomparableSet k).Finite) :
    IsTube (finiteIncomparabilityHull C.carrier) := by
  intro x hx
  classical
  have hne : C.carrier.Nonempty := C.isMaximal.nonempty_iff.1 ⟨x⟩
  let D : SaturatedChain α := ⟨C.carrier, hne, C.isSaturated⟩
  have htrace (y : α) (hy : y ∈ finiteIncomparabilityHull C.carrier) :
      (incomparabilityTrace D y).Finite := by
    have hf : (C.carrier ∩ incomparableSet y).Finite := hy
    exact (hf.preimage Subtype.val_injective.injOn).subset (fun c hc => ⟨c.2, hc.symm⟩)
  have hcontact (y : α) : ∃ d : D, y = d.1 ∨ Incomparable y d.1 := by
    obtain ⟨k, hk, h⟩ := maximal_chain_contact C y
    exact ⟨⟨k, hk⟩, h⟩
  obtain ⟨K, hK, hcontrol⟩ := exists_finite_trace_control D (htrace x hx) (hcontact x)
  let F : D → Set α := fun d => {d.1} ∪ (finiteIncomparabilityHull C.carrier ∩ incomparableSet d.1)
  have hF (d : D) : (F d).Finite := (Set.finite_singleton d.1).union
    (hfinite d.1 d.2)
  apply (hK.biUnion (fun d _ => hF d)).subset
  rintro y ⟨hyHull, hyx⟩
  obtain ⟨d, hd, hyd | hyd⟩ := hcontrol y hyx.symm (htrace y hyHull) (hcontact y)
  · exact Set.mem_biUnion hd (Or.inl (Set.mem_singleton_iff.2 hyd))
  · exact Set.mem_biUnion hd (Or.inr ⟨hyHull, hyd.symm⟩)

end AharoniKorman.Consolidation
