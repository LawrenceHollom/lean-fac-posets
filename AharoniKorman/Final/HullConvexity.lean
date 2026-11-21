import AharoniKorman.Tube.Defs
import Mathlib.Order.Interval.Set.OrdConnected

namespace AharoniKorman.Consolidation

open Set

variable {α : Type*} [PartialOrder α]

def finiteIncomparabilityHull (C : Set α) : Set α :=
  {x | (C ∩ incomparableSet x).Finite}

theorem subset_finiteIncomparabilityHull {C : Set α} (hC : IsChain (· ≤ ·) C) :
    C ⊆ finiteIncomparabilityHull C := fun x hx => IsChain.isTube hC x hx

theorem hull_maximal_of_isTube {C : Set α} (hC : IsChain (· ≤ ·) C)
    (hT : IsTube (finiteIncomparabilityHull C)) :
    IsMaximalTube (finiteIncomparabilityHull C) := by
  apply (isMaximalTube_iff _).2
  refine ⟨hT, ?_⟩
  intro x hx hfinite
  apply hx
  exact hfinite.subset (Set.inter_subset_inter_left _ (subset_finiteIncomparabilityHull hC))

/-- Paper `claim:q-convex`: incomparability with a point of the finite-trace
hull cuts out an order-convex subset of the ambient poset. -/
theorem finiteIncomparabilityHull_trace_ordConnected {C : Set α} {x : α}
    (hx : x ∈ finiteIncomparabilityHull C) :
    (finiteIncomparabilityHull C ∩ incomparableSet x).OrdConnected := by
  refine ⟨?_⟩
  intro y hy z hz w hw
  have hw_incomp : Incomparable x w :=
    ⟨fun hxw => hz.2.not_le (hxw.trans hw.2),
      fun hwx => hy.2.not_ge (hw.1.trans hwx)⟩
  refine ⟨?_, hw_incomp⟩
  change (C ∩ incomparableSet w).Finite
  apply (hx.union (hy.1.union hz.1)).subset
  rintro c ⟨hc, hwc⟩
  by_cases hyc : Incomparable y c
  · exact Or.inr (Or.inl ⟨hc, hyc⟩)
  by_cases hzc : Incomparable z c
  · exact Or.inr (Or.inr ⟨hc, hzc⟩)
  have hyc' : y ≤ c := by
    rcases not_incompRel_iff_symmGen.1 hyc with h | h
    · exact h
    · exact (hwc.not_ge (h.trans hw.1)).elim
  have hcz : c ≤ z := by
    rcases not_incompRel_iff_symmGen.1 hzc with h | h
    · exact (hwc.not_le (hw.2.trans h)).elim
    · exact h
  exact Or.inl ⟨hc, ⟨fun h => hz.2.not_le (h.trans hcz),
    fun h => hy.2.not_ge (hyc'.trans h)⟩⟩

end AharoniKorman.Consolidation
