import AharoniKorman.Completion.TraceTransfer

/-! Transitivity by finite-trace transfer and normalization of two starting points.
The finite-distance class quotient is not needed for this argument. -/

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

/-- Equal or incomparable points cannot lie below a strict lower bound. -/
private theorem contact_mem_final {D : SaturatedChain α} {S : Set α}
    (hS : IsFinalSegment S D) {d0 x y : α} (hd0 : d0 ∈ S)
    (hdx : d0 < x) (hy : y ∈ D) (hxy : x = y ∨ Incomparable x y) : y ∈ S := by
  have hdy : d0 ≤ y := by
    rcases D.isChain.total (hS.1 hd0) hy with hdy | hyd
    · exact hdy
    · exact False.elim (hxy.elim
        (fun heq => hdx.not_ge (heq ▸ hyd))
        (fun hinc => hinc.not_ge (hyd.trans hdx.le)))
  exact hS.2 hd0 hy hdy

/-- Pointwise bridge across two final segments of the same middle chain. -/
private theorem bridge_point {C D1 D2 E D : SaturatedChain α}
    (hCD : MutuallyFiniteIncomparability C D1)
    (hDE : MutuallyFiniteIncomparability D2 E)
    (hD1 : IsFinalSegment (D1 : Set α) D)
    (hD2 : IsFinalSegment (D2 : Set α) D)
    {d0 : α} (hd1 : d0 ∈ D1) (hd2 : d0 ∈ D2)
    (hnD1 : D1.NoTop) (hnE : E.NoTop) (x : C) (hdx : d0 < x.1) :
    (incomparabilityTrace E x.1).Finite ∧ ∃ e : E, x.1 < e.1 := by
  have htrace : (incomparabilityTrace D2 x.1).Finite :=
    finite_trace_of_trace_subset (hCD.right_finite x) (by
      intro d hd
      exact contact_mem_final hD1 hd1 hdx (hD2.1 d.2) (Or.inr hd.symm))
  have hcontact : ∃ d : D2, x.1 = d.1 ∨ Incomparable x.1 d.1 := by
    obtain ⟨d, hd⟩ := hCD.exists_crossRelated_right x
    exact ⟨⟨d.1, contact_mem_final hD2 hd2 hdx (hD1.1 d.2) hd⟩, hd⟩
  refine ⟨hDE.transfer_finite_trace htrace hcontact, ?_⟩
  obtain ⟨d, hxd⟩ := hCD.exists_right_gt hnD1 x
  have hdD2 : d.1 ∈ D2 := hD2.2 hd2 (hD1.1 d.2) (hdx.trans hxd).le
  obtain ⟨e, hde⟩ := hDE.exists_right_gt hnE ⟨d.1, hdD2⟩
  exact ⟨e, hxd.trans hde⟩

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

/-- Transitivity of the direct manuscript relation. No equivalence closure or
extra mathematical assumption is introduced. -/
theorem IncreasingEquivalent.trans {C D E : IncreasingChain α}
    (hCD : IncreasingEquivalent C D) (hDE : IncreasingEquivalent D E) :
    IncreasingEquivalent C E := by
  obtain ⟨C', D1, hC', hD1, hCD⟩ := hCD
  obtain ⟨D2, E', hD2, hE', hDE⟩ := hDE
  have hnC := C.finalSegment_noTop C' hC'
  have hnD1 := D.finalSegment_noTop D1 hD1
  have hnD2 := D.finalSegment_noTop D2 hD2
  have hnE := E.finalSegment_noTop E' hE'
  have hcommon : ((D1 : Set α) ∩ D2).Nonempty := by
    rcases finalSegments_comparable hD1 hD2 with h12 | h21
    · obtain ⟨d, hd⟩ := D1.nonempty
      exact ⟨d, hd, h12 hd⟩
    · obtain ⟨d, hd⟩ := D2.nonempty
      exact ⟨d, h21 hd, hd⟩
  obtain ⟨d0, hd1, hd2⟩ := hcommon
  obtain ⟨c0, hdc⟩ := hCD.exists_left_gt hnC ⟨d0, hd1⟩
  obtain ⟨e0, hde⟩ := hDE.exists_right_gt hnE ⟨d0, hd2⟩
  let A := C'.tail c0
  let B := E'.tail e0
  have hforward (x : A) : (incomparabilityTrace E' x.1).Finite ∧
      ∃ e : E', x.1 < e.1 :=
    bridge_point hCD hDE hD1 hD2 hd1 hd2 hnD1 hnE ⟨x.1, x.2.1⟩
      (hdc.trans_le x.2.2)
  have hbackward (y : B) : (incomparabilityTrace C' y.1).Finite ∧
      ∃ c : C', y.1 < c.1 :=
    bridge_point hDE.symm hCD.symm hD2 hD1 hd2 hd1 hnD2 hnC ⟨y.1, y.2.1⟩
      (hde.trans_le y.2.2)
  obtain ⟨A', B', hA', hB', hAB⟩ := normalize_finite_cofinal
    (cofinal_tail_right (fun x => (hforward x).2) e0)
    (cofinal_tail_right (fun y => (hbackward y).2) c0)
    (fun y => finite_trace_of_subset (C'.tail_final c0).1 (hbackward y).1)
    (fun x => finite_trace_of_subset (E'.tail_final e0).1 (hforward x).1)
  exact ⟨A', B', isFinalSegment_trans hA' (isFinalSegment_trans (C'.tail_final c0) hC'),
    isFinalSegment_trans hB' (isFinalSegment_trans (E'.tail_final e0) hE'), hAB⟩

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
