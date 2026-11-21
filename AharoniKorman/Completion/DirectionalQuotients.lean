import AharoniKorman.Completion.Completeness
import Mathlib.Data.Setoid.Basic

/-! The paper's directional equivalences, including saturated chains with endpoints. -/

namespace AharoniKorman.Completion

open Set

variable {α : Type*} [PartialOrder α]

/-- Paper `def:equivalence`: equal greatest points, or equivalent increasing tails. -/
def IncreasingEquivalentOnSaturated (C D : SaturatedChain α) : Prop :=
  (∃ x : α, IsGreatest (C : Set α) x ∧ IsGreatest (D : Set α) x) ∨
    ∃ hC : C.NoTop, ∃ hD : D.NoTop, IncreasingEquivalent ⟨C, hC⟩ ⟨D, hD⟩

/-- Paper `def:equivalence`, with least points and decreasing tails. -/
def DecreasingEquivalentOnSaturated (C D : SaturatedChain α) : Prop :=
  IncreasingEquivalentOnSaturated C.dual D.dual

private theorem hasTop_of_isGreatest {C : SaturatedChain α} {x : α}
    (hx : IsGreatest (C : Set α) x) : C.HasTop := ⟨⟨x, hx.1⟩, fun c => hx.2 c.2⟩

/-- Paper `lem:equivalence`: transitivity uses the paper's common-endpoint case
and the finite-trace argument on endpoint-free representatives. -/
theorem increasingEquivalentOnSaturated_equivalence :
    Equivalence (IncreasingEquivalentOnSaturated (α := α)) where
  refl C := by
    by_cases hc : C.HasTop
    · obtain ⟨c, hmax⟩ := hc
      have hc' : IsGreatest (C : Set α) c.1 := ⟨c.2, fun _ hd => hmax ⟨_, hd⟩⟩
      exact Or.inl ⟨c.1, hc', hc'⟩
    · exact Or.inr ⟨hc, hc, IncreasingEquivalent.refl _⟩
  symm := by
    rintro C D (⟨x, hxC, hxD⟩ | ⟨hC, hD, h⟩)
    · exact Or.inl ⟨x, hxD, hxC⟩
    · exact Or.inr ⟨hD, hC, h.symm⟩
  trans := by
    rintro C D E (⟨x, hxC, hxD⟩ | ⟨hC, hD, h⟩) (⟨y, hyD, hyE⟩ | ⟨hD', hE, h'⟩)
    · have hxy := le_antisymm (hyD.2 hxD.1) (hxD.2 hyD.1)
      exact Or.inl ⟨x, hxC, hxy.symm ▸ hyE⟩
    · exact (hD' (hasTop_of_isGreatest hxD)).elim
    · exact (hD (hasTop_of_isGreatest hyD)).elim
    · exact Or.inr ⟨hC, hE, h.trans h'⟩

/-- Paper `lem:equivalence`, by reversing the order. -/
theorem decreasingEquivalentOnSaturated_equivalence :
    Equivalence (DecreasingEquivalentOnSaturated (α := α)) where
  refl C := increasingEquivalentOnSaturated_equivalence.refl C.dual
  symm h := increasingEquivalentOnSaturated_equivalence.symm h
  trans h h' := increasingEquivalentOnSaturated_equivalence.trans h h'

/-- The equivalence-class space `G_+(P)` from `def:increasing-and-decreasing`. -/
abbrev IncreasingQuotient (α : Type*) [PartialOrder α] :=
  Quotient (⟨IncreasingEquivalentOnSaturated, increasingEquivalentOnSaturated_equivalence⟩ :
    Setoid (SaturatedChain α))

/-- The equivalence-class space `G_-(P)` from `def:increasing-and-decreasing`. -/
abbrev DecreasingQuotient (α : Type*) [PartialOrder α] :=
  Quotient (⟨DecreasingEquivalentOnSaturated, decreasingEquivalentOnSaturated_equivalence⟩ :
    Setoid (SaturatedChain α))

private def singletonChain (x : α) : SaturatedChain α :=
  ⟨{x}, singleton_nonempty _, IsSaturatedChain.of_ordConnected IsChain.singleton
    ordConnected_singleton⟩

private theorem greatest_top {C : SaturatedChain α} (h : C.HasTop) :
    IsGreatest (C : Set α) (Classical.choose h).1 :=
  ⟨(Classical.choose h).2, fun _ hx => Classical.choose_spec h ⟨_, hx⟩⟩

private noncomputable def increasingLabel (C : SaturatedChain α) : α ⊕ IncreasingGerm α := by
  classical
  exact if h : C.HasTop then Sum.inl (Classical.choose h).1
    else Sum.inr (IncreasingGerm.ofChain ⟨C, h⟩)

private theorem increasingLabel_eq_iff (C D : SaturatedChain α) :
    increasingLabel C = increasingLabel D ↔ IncreasingEquivalentOnSaturated C D := by
  classical
  by_cases hC : C.HasTop <;> by_cases hD : D.HasTop
  · rw [increasingLabel, increasingLabel, dif_pos hC, dif_pos hD, Sum.inl.injEq]
    constructor
    · intro h
      exact Or.inl ⟨(Classical.choose hC).1, greatest_top hC, h.symm ▸ greatest_top hD⟩
    · rintro (⟨x, hxC, hxD⟩ | ⟨hnC, _, _⟩)
      · exact ((greatest_top hC).unique hxC).trans (hxD.unique (greatest_top hD))
      · exact (hnC hC).elim
  · rw [increasingLabel, increasingLabel, dif_pos hC, dif_neg hD]
    constructor
    · intro h
      cases h
    · rintro (⟨_, _, hxD⟩ | ⟨hnC, _, _⟩)
      · exact (hD (hasTop_of_isGreatest hxD)).elim
      · exact (hnC hC).elim
  · rw [increasingLabel, increasingLabel, dif_neg hC, dif_pos hD]
    constructor
    · intro h
      cases h
    · rintro (⟨_, hxC, _⟩ | ⟨_, hnD, _⟩)
      · exact (hC (hasTop_of_isGreatest hxC)).elim
      · exact (hnD hD).elim
  · rw [increasingLabel, increasingLabel, dif_neg hC, dif_neg hD, Sum.inr.injEq]
    constructor
    · exact fun h => Or.inr ⟨hC, hD, IncreasingGerm.ofChain_eq_iff.mp h⟩
    · rintro (⟨_, hxC, _⟩ | ⟨_, _, h⟩)
      · exact (hC (hasTop_of_isGreatest hxC)).elim
      · exact IncreasingGerm.ofChain_eq_iff.mpr h

/-- The principal classes of `G₊(P)` correspond to their greatest points. The
remaining classes are the representatives of genuine increasing germs. -/
noncomputable def increasingQuotientEquiv : IncreasingQuotient α ≃ α ⊕ IncreasingGerm α := by
  classical
  let f : IncreasingQuotient α → α ⊕ IncreasingGerm α :=
    Quotient.lift increasingLabel fun C D h => (increasingLabel_eq_iff C D).mpr h
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro C D
    induction C using Quotient.inductionOn with
    | _ C =>
      induction D using Quotient.inductionOn with
      | _ D => exact fun h => Quotient.sound ((increasingLabel_eq_iff C D).mp h)
  · rintro (x | g)
    · let C := singletonChain x
      have hx : IsGreatest (C : Set α) x := by
        refine ⟨mem_singleton _, ?_⟩
        intro a ha
        exact le_of_eq (mem_singleton_iff.mp ha)
      have hC := hasTop_of_isGreatest hx
      refine ⟨Quotient.mk _ C, ?_⟩
      change increasingLabel C = Sum.inl x
      rw [increasingLabel, dif_pos hC, (greatest_top hC).unique hx]
    · obtain ⟨C, hC⟩ := g.exists_representative
      refine ⟨Quotient.mk _ C.1, ?_⟩
      change increasingLabel C.1 = Sum.inr g
      rw [increasingLabel, dif_neg C.2]
      exact congrArg Sum.inr hC

/-- The dual normalization identifies principal classes with their least points. -/
noncomputable def decreasingQuotientEquiv : DecreasingQuotient α ≃ α ⊕ DecreasingGerm α := by
  let reverse : SaturatedChain α ≃ SaturatedChain αᵒᵈ :=
    ⟨SaturatedChain.dual, SaturatedChain.dual, SaturatedChain.dual_dual, SaturatedChain.dual_dual⟩
  let e : DecreasingQuotient α ≃ IncreasingQuotient αᵒᵈ :=
    Quotient.congr reverse (fun _ _ => Iff.rfl)
  exact e.trans (increasingQuotientEquiv (α := αᵒᵈ))

/-- The points of `H` after omitting its internal formal endpoints. -/
abbrev EndpointFreeExtension (α : Type*) [PartialOrder α] :=
  {X : H α // X ≠ ⊥ ∧ X ≠ ⊤}

private noncomputable def glueLabel : IncreasingQuotient α ⊕ DecreasingQuotient α →
    EndpointFreeExtension α
  | Sum.inl X => match increasingQuotientEquiv X with
    | Sum.inl x => ⟨H.principal x, H.principal_ne_bot x, H.principal_ne_top x⟩
    | Sum.inr g => ⟨H.increasing g, H.increasing_ne_bot g, H.increasing_ne_top g⟩
  | Sum.inr X => match decreasingQuotientEquiv X with
    | Sum.inl x => ⟨H.principal x, H.principal_ne_bot x, H.principal_ne_top x⟩
    | Sum.inr g => ⟨H.decreasing g, H.decreasing_ne_bot g, H.decreasing_ne_top g⟩

/-- Paper `def:h-p`: glue the two directional quotients along their principal classes. -/
def PaperChainExtension (α : Type*) [PartialOrder α] := Quotient (Setoid.ker (glueLabel (α := α)))

namespace PaperChainExtension

noncomputable def ofIncreasingClass (X : IncreasingQuotient α) : PaperChainExtension α :=
  Quotient.mk _ (Sum.inl X)

noncomputable def ofDecreasingClass (X : DecreasingQuotient α) : PaperChainExtension α :=
  Quotient.mk _ (Sum.inr X)

/-- Classes of opposite signs are identified precisely when they have the same
principal point. -/
theorem ofIncreasingClass_eq_ofDecreasingClass (X : IncreasingQuotient α)
    (Y : DecreasingQuotient α) :
    ofIncreasingClass X = ofDecreasingClass Y ↔
      ∃ x : α, increasingQuotientEquiv X = Sum.inl x ∧ decreasingQuotientEquiv Y = Sum.inl x := by
  change Quotient.mk (Setoid.ker (glueLabel (α := α))) (Sum.inl X) = Quotient.mk _ (Sum.inr Y) ↔ _
  rw [Quotient.eq_iff_equiv]
  change glueLabel (Sum.inl X) = glueLabel (Sum.inr Y) ↔ _
  cases hx : increasingQuotientEquiv X <;> cases hy : decreasingQuotientEquiv Y
  all_goals simp [glueLabel, hx, hy, Subtype.ext_iff]
  exact eq_comm

private theorem glueLabel_surjective : Function.Surjective (glueLabel (α := α)) := by
  rintro ⟨Z, hb, ht⟩
  cases Z with
  | principal x =>
      refine ⟨Sum.inl (increasingQuotientEquiv.symm (Sum.inl x)), Subtype.ext ?_⟩
      simp [glueLabel]
  | increasing g =>
      refine ⟨Sum.inl (increasingQuotientEquiv.symm (Sum.inr g)), Subtype.ext ?_⟩
      simp [glueLabel]
  | decreasing g =>
      refine ⟨Sum.inr (decreasingQuotientEquiv.symm (Sum.inr g)), Subtype.ext ?_⟩
      simp [glueLabel]
  | bottom => exact (hb rfl).elim
  | top => exact (ht rfl).elim

private noncomputable def normalize : PaperChainExtension α ≃ EndpointFreeExtension α :=
  Setoid.quotientKerEquivOfSurjective glueLabel glueLabel_surjective

noncomputable instance : PartialOrder (PaperChainExtension α) :=
  PartialOrder.lift normalize normalize.injective

/-- The nested quotient in the paper and the endpoint-free part of `H` have the
same points and domination order. -/
noncomputable def normalizeOrderIso : PaperChainExtension α ≃o EndpointFreeExtension α where
  toEquiv := normalize
  map_rel_iff' := Iff.rfl

end PaperChainExtension

namespace PaperChainExtension

variable {β : Type*} [LinearOrder β]

noncomputable instance : LinearOrder (PaperChainExtension β) :=
  LinearOrder.lift' normalize normalize.injective

/-- `lem:h-complete` on the paper's quotient. The principal-cut construction produces an
element of the quotient for every nonempty set, with positive sign if the bound is unattained. -/
theorem exists_isLUB_nonempty (D : Set (PaperChainExtension β)) (hD : D.Nonempty) :
    ∃ X, IsLUB D X ∧ (X ∉ D → ∃ g, (normalizeOrderIso X).1 = H.increasing g) := by
  classical
  let e : PaperChainExtension β ↪o H β := normalizeOrderIso.toOrderEmbedding.trans
    (OrderEmbedding.subtype fun Y : H β => Y ≠ ⊥ ∧ Y ≠ ⊤)
  let U := e '' D
  let Y := sSup U
  have hY : IsLUB U Y := isLUB_sSup U
  have hYend : Y ≠ ⊥ ∧ Y ≠ ⊤ := by
    by_cases hy : Y ∈ U
    · obtain ⟨x, _, hx⟩ := hy
      exact hx ▸ (normalizeOrderIso x).2
    · obtain ⟨g, hg⟩ := H.sSup_eq_increasing_of_not_mem (hD.image e) hy
      change Y = H.increasing g at hg
      rw [hg]
      exact ⟨H.increasing_ne_bot _, H.increasing_ne_top _⟩
  let X := normalizeOrderIso.symm ⟨Y, hYend⟩
  have heX : e X = Y := congrArg Subtype.val (normalizeOrderIso.apply_symm_apply ⟨Y, hYend⟩)
  refine ⟨X, ⟨?_, ?_⟩, ?_⟩
  · intro d hd
    apply e.le_iff_le.mp
    rw [heX]
    exact hY.1 ⟨d, hd, rfl⟩
  · intro z hz
    apply e.le_iff_le.mp
    rw [heX]
    apply hY.2
    rintro _ ⟨d, hd, rfl⟩
    exact e.monotone (hz hd)
  · intro hx
    have hy : Y ∉ U := by
      rintro ⟨x, hxD, hxe⟩
      exact hx (e.injective (hxe.trans heX.symm) ▸ hxD)
    obtain ⟨g, hg⟩ := H.sSup_eq_increasing_of_not_mem (hD.image e) hy
    exact ⟨g, heX.trans hg⟩

end PaperChainExtension

end AharoniKorman.Completion
