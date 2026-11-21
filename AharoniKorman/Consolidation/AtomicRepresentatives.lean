import AharoniKorman.Consolidation.AtomicGerms

/-! Atomicity is independent of the chosen saturated representative. -/

namespace AharoniKorman.Consolidation

open Set Completion

variable {α : Type*} [PartialOrder α]

/-- Finite principal initial segments pass to subchains. -/
theorem finite_Iic_of_subset {C D : SaturatedChain α} (hCD : (C : Set α) ⊆ D)
    (hD : ∀ d : D, (Iic d).Finite) (c : C) : (Iic c).Finite := by
  let inc : C → D := fun x => ⟨x.1, hCD x.2⟩
  have hi : Function.Injective inc :=
    fun x y h => Subtype.ext (congrArg (fun z : D => z.1) h)
  exact (hD (inc c)).preimage hi.injOn

/-- Under mutually finite incomparability, an omega representative transfers
finite initial segments to the other representative. -/
theorem finite_Iic_of_mutuallyFinite {C D : SaturatedChain α}
    (h : MutuallyFiniteIncomparability C D) (hDtop : D.NoTop)
    (hD : ∀ d : D, (Iic d).Finite) (c : C) : (Iic c).Finite := by
  classical
  obtain ⟨d, hcd⟩ := h.exists_right_gt hDtop c
  have hfiber (y : D) : {x : C | CrossRelated x y}.Finite := by
    have heq : {x : C | x.1 = y.1}.Subsingleton := by
      intro a ha b hb
      exact Subtype.ext (ha.trans hb.symm)
    exact heq.finite.union (h.left_finite y)
  apply ((hD d).biUnion (fun y _ => hfiber y)).subset
  intro x hx
  obtain ⟨y, hxy⟩ := h.exists_crossRelated_right x
  have hyd : y ≤ d := by
    by_contra hyd
    have hdy : d < y := lt_of_not_ge hyd
    have hxylt : x.1 < y.1 := (show x.1 ≤ c.1 from hx).trans_lt (hcd.trans hdy)
    rcases hxy with heq | hinc
    · exact hxylt.ne heq
    · exact hinc.not_le hxylt.le
  exact Set.mem_biUnion hyd hxy

/-- Every representative of an atomic positive germ has a final omega segment.
This proves the representative-independence assertion needed for isolation. -/
theorem IsPositiveAtom.exists_omega_finalSegment {g : IncreasingGerm α}
    (hg : IsPositiveAtom g) (C : IncreasingChain α) (hC : g.Represents C) :
    ∃ A : IncreasingChain α,
      IsFinalSegment (A.1 : Set α) C.1 ∧ IsOmegaRepresentative A ∧ g.Represents A := by
  obtain ⟨D, hD, hDomega⟩ := hg
  have heq : IncreasingEquivalent C D :=
    IncreasingGerm.ofChain_eq_iff.1 (hC.trans hD.symm)
  obtain ⟨S, T, hS, hT, hST⟩ := heq
  let A : IncreasingChain α := ⟨S, C.finalSegment_noTop S hS⟩
  have hSomega : IsOmegaRepresentative A :=
    finite_Iic_of_mutuallyFinite hST (D.finalSegment_noTop T hT)
      (finite_Iic_of_subset hT.1 hDomega)
  refine ⟨A, hS, hSomega, ?_⟩
  apply Eq.trans _ hC
  apply IncreasingGerm.ofChain_eq_iff.2
  exact ⟨S, S, ⟨Subset.rfl, fun {_ _} _ hy _ => hy⟩, hS,
    MutuallyFiniteIncomparability.refl S⟩

end AharoniKorman.Consolidation
