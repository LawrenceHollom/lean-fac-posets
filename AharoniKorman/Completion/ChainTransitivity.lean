import AharoniKorman.Completion.TraceTransfer

/-! Transitivity by aligned tails, canonical class maps and endpoint normalization. -/

namespace AharoniKorman.Completion

open Set

variable {α : Type*} [PartialOrder α]

theorem isFinalSegment_trans {A B C : Set α}
    (hAB : IsFinalSegment A B) (hBC : IsFinalSegment B C) : IsFinalSegment A C :=
  ⟨hAB.1.trans hBC.1, fun _ _ ha hc hac =>
    hAB.2 ha (hBC.2 (hAB.1 ha) hc hac) hac⟩

/-- The closed final tail at a chosen chain point. -/
def SaturatedChain.tail (C : SaturatedChain α) (a : C) : SaturatedChain α :=
  C.restrict .increasing {x | x ∈ C ∧ a.1 ≤ x}
    ⟨fun _ h => h.1, fun _ _ hx hy hxy => ⟨hy, hx.2.trans hxy⟩⟩
    ⟨a.1, a.2, le_rfl⟩

@[simp] theorem SaturatedChain.mem_tail (C : SaturatedChain α) (a : C) (x : α) :
    x ∈ C.tail a ↔ x ∈ C ∧ a.1 ≤ x := Iff.rfl

theorem SaturatedChain.tail_final (C : SaturatedChain α) (a : C) :
    IsFinalSegment (C.tail a : Set α) C :=
  ⟨fun _ h => h.1, fun _ _ hx hy hxy => ⟨hy, hx.2.trans hxy⟩⟩

theorem SaturatedChain.tail_noTop (C : SaturatedChain α) (a : C) (h : C.NoTop) :
    (C.tail a).NoTop := IncreasingChain.finalSegment_noTop ⟨C, h⟩ _ (C.tail_final a)

/-- Transfer finiteness along an inclusion of incomparability traces. -/
theorem finite_trace_of_trace_subset {C D : SaturatedChain α} {x : α}
    (hD : (incomparabilityTrace D x).Finite)
    (hsub : ∀ c ∈ incomparabilityTrace C x, c.1 ∈ D) :
    (incomparabilityTrace C x).Finite := by
  have himage := hD.image (fun d : D => d.1)
  have hpre := himage.preimage (f := fun c : C => c.1) Subtype.val_injective.injOn
  apply hpre.subset
  intro c hc
  exact ⟨⟨c.1, hsub c hc⟩, hc, rfl⟩

theorem finite_trace_of_subset {C D : SaturatedChain α} (hCD : (C : Set α) ⊆ D)
    {x : α} (hD : (incomparabilityTrace D x).Finite) :
    (incomparabilityTrace C x).Finite :=
  finite_trace_of_trace_subset hD (fun c _ => hCD c.2)

private theorem tail_crossRelated {C D : SaturatedChain α}
    (h : MutuallyFiniteIncomparability C D) {c : C} {d : D} (hcd : CrossRelated c d)
    (x : C.tail c) : ∃ y : D.tail d, CrossRelated x y := by
  let d' : D.tail d := ⟨d.1, d.2, le_rfl⟩
  by_cases hxd : CrossRelated x d'
  · exact ⟨d', hxd⟩
  have hdx : d.1 ≤ x.1 := by
    rcases not_incompRel_iff_symmGen.mp (fun hi => hxd (Or.inr hi)) with hle | hge
    · rcases hcd with he | hinc
      · have hge : d.1 ≤ x.1 := he ▸ x.2.2
        exact False.elim (hxd (Or.inl (le_antisymm hle hge)))
      · exact False.elim (hinc.not_le (x.2.2.trans hle))
    · exact hge
  obtain ⟨y, hxy⟩ := h.exists_crossRelated_right ⟨x.1, x.2.1⟩
  have hdy : d ≤ y := by
    apply le_of_not_gt
    intro hyd
    have hyx : y.1 < x.1 := (show y.1 < d.1 from hyd).trans_le hdx
    exact hxy.elim (fun he => hyx.ne he.symm) (fun hi => hi.not_ge hyx.le)
  exact ⟨⟨y.1, y.2, hdy⟩, hxy⟩

private theorem mfi_aligned_tails {C D : SaturatedChain α}
    (h : MutuallyFiniteIncomparability C D) {c : C} {d : D} (hcd : CrossRelated c d) :
    MutuallyFiniteIncomparability (C.tail c) (D.tail d) := by
  apply MutuallyFiniteIncomparability.of_finite_crossRelated
  · intro y
    exact finite_trace_of_subset (C.tail_final c).1 (h.left_finite ⟨y.1, y.2.1⟩)
  · intro x
    exact finite_trace_of_subset (D.tail_final d).1 (h.right_finite ⟨x.1, x.2.1⟩)
  · intro y
    obtain ⟨x, hxy⟩ := tail_crossRelated h.symm hcd.symm y
    exact ⟨x, hxy.symm⟩
  · exact tail_crossRelated h hcd

private theorem aligned_finite_trace {A M B : SaturatedChain α}
    (hAM : MutuallyFiniteIncomparability A M) (hMB : MutuallyFiniteIncomparability M B)
    (x : A) : (incomparabilityTrace B x.1).Finite ∧
      ∀ b : B, b ∈ incomparabilityTrace B x.1 →
        FiniteDistanceClass.mk b = (hMB.classOrderIso ∘ hAM.classOrderIso) (FiniteDistanceClass.mk x) := by
  obtain ⟨m, hxm⟩ := hAM.exists_crossRelated_right x
  obtain ⟨hfin, hclass⟩ := hMB.transfer_finite_trace_class (hAM.right_finite x) hxm
  refine ⟨hfin.subset (fun _ hi => Or.inr hi.symm), ?_⟩
  intro b hb
  exact (hclass b (Or.inr hb.symm)).trans (congrArg hMB.classOrderIso
    (hAM.classOrderIso_mk_of_crossRelated hxm).symm)

private theorem cofinal_tail_right {C D : SaturatedChain α}
    (h : ∀ c : C, ∃ d : D, c.1 < d.1) (b : D) :
    ∀ c : C, ∃ d : D.tail b, c.1 < d.1 := by
  intro c
  obtain ⟨d, hcd⟩ := h c
  exact ⟨⟨(max d b).1, (max d b).2, le_max_right d b⟩,
    hcd.trans_le (show d.1 ≤ (max d b).1 from le_max_left d b)⟩

/-- Cofinality and equal/incomparable least points give common-hull maximality.
Only saturation, not ambient convexity, is used. -/
private theorem maximal_of_crossRelated_bottom {C D : SaturatedChain α}
    (a : C) (b : D) (ha : ∀ c : C, a ≤ c) (hb : ∀ d : D, b ≤ d)
    (hab : CrossRelated a b) (hcof : ∀ d : D, ∃ c : C, d.1 < c.1) :
    IsMaximalChainIn C (convexHull ((C : Set α) ∪ D)) := by
  refine ⟨fun x hx => ⟨x, Or.inl hx, x, Or.inl hx, le_rfl, le_rfl⟩, C.isChain, ?_⟩
  intro S hS hsub hCS
  apply Set.Subset.antisymm hCS
  intro z hz
  obtain ⟨p, hp, q, hq, hpz, hzq⟩ := hsub hz
  have haz : a.1 ≤ z := by
    rcases hS.total (hCS a.2) hz with haz | hza
    · exact haz
    rcases hp with hp | hp
    · exact (show a.1 ≤ p from ha ⟨p, hp⟩).trans hpz
    · have hbz : b.1 ≤ z := (show b.1 ≤ p from hb ⟨p, hp⟩).trans hpz
      exact hab.elim (fun heq => heq ▸ hbz)
        (fun hi => False.elim (hi.not_ge (hbz.trans hza)))
  have hupper : ∃ c : C, z ≤ c.1 := by
    rcases hq with hq | hq
    · exact ⟨⟨q, hq⟩, hzq⟩
    · obtain ⟨c, hqc⟩ := hcof ⟨q, hq⟩
      exact ⟨c, hzq.trans hqc.le⟩
  obtain ⟨c, hzc⟩ := hupper
  exact C.mem_of_between a.2 c.2 haz hzc (fun t ht => hS.total hz (hCS ht))

/-- Normalize two mutually cofinal chains with finite cross traces by choosing
equal or incomparable starting points. -/
theorem normalize_finite_cofinal {C D : SaturatedChain α}
    (hCD : ∀ c : C, ∃ d : D, c.1 < d.1)
    (hDC : ∀ d : D, ∃ c : C, d.1 < c.1)
    (hleft : ∀ d : D, (incomparabilityTrace C d.1).Finite)
    (hright : ∀ c : C, (incomparabilityTrace D c.1).Finite) :
    ∃ C' D' : SaturatedChain α, IsFinalSegment (C' : Set α) C ∧
      IsFinalSegment (D' : Set α) D ∧ MutuallyFiniteIncomparability C' D' := by
  obtain ⟨c0, hc0⟩ := C.nonempty
  obtain ⟨b, hc0b⟩ := hCD ⟨c0, hc0⟩
  obtain ⟨c1, hbc1⟩ := hDC b
  have hcontact : ∃ a : C, CrossRelated a b := by
    by_cases hbC : b.1 ∈ C
    · exact ⟨⟨b.1, hbC⟩, Or.inl rfl⟩
    obtain ⟨a, ha, hba⟩ := C.maximalIn_convexHull.exists_incomparable
      ⟨c0, hc0, c1.1, c1.2, hc0b.le, hbc1.le⟩ hbC
    exact ⟨⟨a, ha⟩, Or.inr hba.symm⟩
  obtain ⟨a, hab⟩ := hcontact
  let A := C.tail a
  let B := D.tail b
  let a' : A := ⟨a.1, a.2, le_rfl⟩
  let b' : B := ⟨b.1, b.2, le_rfl⟩
  have hAB : ∀ x : A, ∃ y : B, x.1 < y.1 :=
    fun x => cofinal_tail_right hCD b ⟨x.1, x.2.1⟩
  have hBA : ∀ y : B, ∃ x : A, y.1 < x.1 :=
    fun y => cofinal_tail_right hDC a ⟨y.1, y.2.1⟩
  refine ⟨A, B, C.tail_final a, D.tail_final b, ?_⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact maximal_of_crossRelated_bottom a' b' (fun x => x.2.2) (fun y => y.2.2) hab hBA
  · simpa only [Set.union_comm] using
      maximal_of_crossRelated_bottom b' a' (fun y => y.2.2) (fun x => x.2.2) hab.symm hAB
  · intro y
    exact finite_trace_of_subset (C.tail_final a).1 (hleft ⟨y.1, y.2.1⟩)
  · intro x
    exact finite_trace_of_subset (D.tail_final b).1 (hright ⟨x.1, x.2.1⟩)

/-- Paper `lem:equivalence`: align the two middle tails, transfer finite traces
through the composed canonical isomorphism, and normalize the outer endpoints. -/
theorem IncreasingEquivalent.trans {C D E : IncreasingChain α}
    (hCD : IncreasingEquivalent C D) (hDE : IncreasingEquivalent D E) :
    IncreasingEquivalent C E := by
  obtain ⟨C', D₁, hC', hD₁, hCD⟩ := hCD
  obtain ⟨D₂, E', hD₂, hE', hDE⟩ := hDE
  have hcommon : ((D₁ : Set α) ∩ D₂).Nonempty := by
    rcases finalSegments_comparable hD₁ hD₂ with h12 | h21
    · obtain ⟨d, hd⟩ := D₁.nonempty
      exact ⟨d, hd, h12 hd⟩
    · obtain ⟨d, hd⟩ := D₂.nonempty
      exact ⟨d, h21 hd, hd⟩
  obtain ⟨d, hd₁, hd₂⟩ := hcommon
  obtain ⟨c, hcd⟩ := hCD.exists_crossRelated_left ⟨d, hd₁⟩
  obtain ⟨e, hde⟩ := hDE.exists_crossRelated_right ⟨d, hd₂⟩
  let d₁ : D₁ := ⟨d, hd₁⟩
  let d₂ : D₂ := ⟨d, hd₂⟩
  let A := C'.tail c
  let M := D₁.tail d₁
  let B := E'.tail e
  have heq : M = D₂.tail d₂ := by
    apply SetLike.ext
    intro x
    change (x ∈ D₁ ∧ d ≤ x) ↔ (x ∈ D₂ ∧ d ≤ x)
    exact ⟨fun hx => ⟨hD₂.2 hd₂ (hD₁.1 hx.1) hx.2, hx.2⟩,
      fun hx => ⟨hD₁.2 hd₁ (hD₂.1 hx.1) hx.2, hx.2⟩⟩
  have hAM : MutuallyFiniteIncomparability A M := mfi_aligned_tails hCD hcd
  have hMB : MutuallyFiniteIncomparability M B := by
    rw [heq]
    exact mfi_aligned_tails hDE hde
  have hnA : A.NoTop := C'.tail_noTop c (C.finalSegment_noTop C' hC')
  have hnM : M.NoTop := D₁.tail_noTop d₁ (D.finalSegment_noTop D₁ hD₁)
  have hnB : B.NoTop := E'.tail_noTop e (E.finalSegment_noTop E' hE')
  have hAB (x : A) : ∃ y : B, x.1 < y.1 := by
    obtain ⟨m, hxm⟩ := hAM.exists_right_gt hnM x
    obtain ⟨y, hmy⟩ := hMB.exists_right_gt hnB m
    exact ⟨y, hxm.trans hmy⟩
  have hBA (y : B) : ∃ x : A, y.1 < x.1 := by
    obtain ⟨m, hym⟩ := hMB.exists_left_gt hnM y
    obtain ⟨x, hmx⟩ := hAM.exists_left_gt hnA m
    exact ⟨x, hym.trans hmx⟩
  obtain ⟨A', B', hA', hB', hmfi⟩ := normalize_finite_cofinal hAB hBA
    (fun y => (aligned_finite_trace hMB.symm hAM.symm y).1)
    (fun x => (aligned_finite_trace hAM hMB x).1)
  exact ⟨A', B', isFinalSegment_trans hA' (isFinalSegment_trans (C'.tail_final c) hC'),
    isFinalSegment_trans hB' (isFinalSegment_trans (E'.tail_final e) hE'), hmfi⟩

theorem DecreasingEquivalent.trans {C D E : DecreasingChain α}
    (hCD : DecreasingEquivalent C D) (hDE : DecreasingEquivalent D E) :
    DecreasingEquivalent C E := IncreasingEquivalent.trans hCD hDE

/-- Equivalent increasing representatives are mutually cofinal in the ambient order. -/
theorem IncreasingEquivalent.exists_right_gt {C D : IncreasingChain α}
    (h : IncreasingEquivalent C D) (x : C.1) : ∃ y : D.1, x.1 < y.1 := by
  obtain ⟨C', D', hC', hD', hCD⟩ := h
  obtain ⟨c0, hc0⟩ := C'.nonempty
  have hcx : ∃ c : C', x.1 ≤ c.1 := by
    rcases C.1.isChain.total x.2 (hC'.1 hc0) with hxc | hcx
    · exact ⟨⟨c0, hc0⟩, hxc⟩
    · exact ⟨⟨x.1, hC'.2 hc0 x.2 hcx⟩, le_rfl⟩
  obtain ⟨c, hxc⟩ := hcx
  obtain ⟨d, hcd⟩ := hCD.exists_right_gt (D.finalSegment_noTop D' hD') c
  exact ⟨⟨d.1, hD'.1 d.2⟩, hxc.trans_lt hcd⟩

theorem IncreasingEquivalent.exists_left_gt {C D : IncreasingChain α}
    (h : IncreasingEquivalent C D) (y : D.1) : ∃ x : C.1, y.1 < x.1 :=
  h.symm.exists_right_gt y

/-- Upper bounds are independent of the increasing representative. -/
theorem IncreasingEquivalent.upperBounds_iff {C D : IncreasingChain α}
    (h : IncreasingEquivalent C D) (p : α) :
    (∀ x : C.1, x.1 ≤ p) ↔ ∀ y : D.1, y.1 ≤ p := by
  constructor
  · intro hp y
    obtain ⟨x, hyx⟩ := h.exists_left_gt y
    exact hyx.le.trans (hp x)
  · intro hp x
    obtain ⟨y, hxy⟩ := h.exists_right_gt x
    exact hxy.le.trans (hp y)

end AharoniKorman.Completion
