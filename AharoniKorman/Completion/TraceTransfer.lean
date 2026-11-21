import AharoniKorman.Completion.ChainEquivalence
import Mathlib.Order.Cover

/-! Finite traces transfer to the class selected by the canonical isomorphism. -/

namespace AharoniKorman.Completion

open Set

variable {α : Type*} [PartialOrder α]

private theorem trace_lower_boundary (D : SaturatedChain α) {x e : α} {a : D}
    (ha : a ∈ incomparabilityTrace D x)
    (hmin : ∀ t ∈ incomparabilityTrace D x, a ≤ t)
    (hJ : (incomparabilityTrace D e).Finite)
    (hne : (incomparabilityTrace D e).Nonempty)
    (hea : e < a.1) (hex : Incomparable e x) :
    ∃ d : D, d ⋖ a ∧ Incomparable d.1 e := by
  obtain ⟨d, hd, hdmax⟩ := hJ.exists_maximal hne
  have hda : d < a := by
    apply lt_of_not_ge
    intro had
    exact hd.not_ge (hea.le.trans (show a.1 ≤ d.1 from had))
  refine ⟨d, ⟨hda, ?_⟩, hd⟩
  intro t hdt hta
  have htJ : t ∉ incomparabilityTrace D e := by
    intro ht
    exact hdt.not_ge (hdmax ht hdt.le)
  have het : e ≤ t.1 := by
    rcases not_incompRel_iff_symmGen.mp htJ with hte | het
    · exact False.elim (hd.not_le ((show d.1 ≤ t.1 from hdt.le).trans hte))
    · exact het
  have htI : t ∉ incomparabilityTrace D x := fun ht => hta.not_ge (hmin t ht)
  have htx : t.1 ≤ x := by
    rcases not_incompRel_iff_symmGen.mp htI with htx | hxt
    · exact htx
    · exact False.elim (ha.not_ge (hxt.trans (show t.1 ≤ a.1 from hta.le)))
  exact hex.not_le (het.trans htx)

private theorem trace_upper_boundary (D : SaturatedChain α) {x e : α} {b : D}
    (hb : b ∈ incomparabilityTrace D x)
    (hmax : ∀ t ∈ incomparabilityTrace D x, t ≤ b)
    (hJ : (incomparabilityTrace D e).Finite)
    (hne : (incomparabilityTrace D e).Nonempty)
    (hbe : b.1 < e) (hex : Incomparable e x) :
    ∃ d : D, b ⋖ d ∧ Incomparable d.1 e := by
  obtain ⟨d, hd, hdmin⟩ := hJ.exists_minimal hne
  have hbd : b < d := by
    apply lt_of_not_ge
    intro hdb
    exact hd.not_le ((show d.1 ≤ b.1 from hdb).trans hbe.le)
  refine ⟨d, ⟨hbd, ?_⟩, hd⟩
  intro t hbt htd
  have htJ : t ∉ incomparabilityTrace D e := by
    intro ht
    exact htd.not_ge (hdmin ht htd.le)
  have hte : t.1 ≤ e := by
    rcases not_incompRel_iff_symmGen.mp htJ with hte | het
    · exact hte
    · exact False.elim (hd.not_ge (het.trans (show t.1 ≤ d.1 from htd.le)))
  have htI : t ∉ incomparabilityTrace D x := fun ht => hbt.not_ge (hmax t ht)
  have hxt : x ≤ t.1 := by
    rcases not_incompRel_iff_symmGen.mp htI with htx | hxt
    · exact False.elim (hb.not_le ((show b.1 ≤ t.1 from hbt.le).trans htx))
    · exact hxt
  exact hex.not_ge (hxt.trans hte)

/-- Transfer an ambient point's finite trace, provided it has an equal or
incomparable representative on the intermediate chain. No maximality involving
the ambient point or its own chain is assumed. -/
theorem MutuallyFiniteIncomparability.transfer_finite_trace
    {D E : SaturatedChain α} (h : MutuallyFiniteIncomparability D E) {x : α}
    (hI : (incomparabilityTrace D x).Finite)
    (hcontact : ∃ d : D, x = d.1 ∨ Incomparable x d.1) :
    (incomparabilityTrace E x).Finite := by
  classical
  by_cases hxD : x ∈ D
  · exact h.right_finite ⟨x, hxD⟩
  have hIne : (incomparabilityTrace D x).Nonempty := by
    obtain ⟨d, hd | hd⟩ := hcontact
    · exact False.elim (hxD (hd ▸ d.2))
    · exact ⟨d, hd.symm⟩
  obtain ⟨a, ha, hamin⟩ := hI.exists_minimal hIne
  obtain ⟨b, hb, hbmax⟩ := hI.exists_maximal hIne
  have hmin : ∀ t ∈ incomparabilityTrace D x, a ≤ t := by
    intro t ht
    exact (le_total a t).elim id (fun hta => hamin ht hta)
  have hmax : ∀ t ∈ incomparabilityTrace D x, t ≤ b := by
    intro t ht
    exact (le_total t b).elim id (fun hbt => hbmax ht hbt)
  let K : Set D := incomparabilityTrace D x ∪ {d | d ⋖ a} ∪ {d | b ⋖ d}
  have hpred : ({d : D | d ⋖ a} : Set D).Finite :=
    Set.Subsingleton.finite (fun _ hd _ hd' => hd.unique_left hd')
  have hsucc : ({d : D | b ⋖ d} : Set D).Finite :=
    Set.Subsingleton.finite (fun _ hd _ hd' => hd.unique_right hd')
  have hK : K.Finite := (hI.union hpred).union hsucc
  let F : D → Set E := fun d => {e | e.1 = d.1} ∪ incomparabilityTrace E d.1
  have hF : ∀ d, (F d).Finite := by
    intro d
    have heq : ({e : E | e.1 = d.1} : Set E).Finite :=
      Set.Subsingleton.finite (fun _ he _ he' => Subtype.ext (he.trans he'.symm))
    exact heq.union (h.right_finite d)
  apply (hK.biUnion (fun d _ => hF d)).subset
  intro e hex
  suffices ∃ d ∈ K, e ∈ F d by
    obtain ⟨d, hd, he⟩ := this
    exact Set.mem_iUnion_of_mem d (Set.mem_iUnion_of_mem hd he)
  by_cases heD : e.1 ∈ D
  · exact ⟨⟨e.1, heD⟩, Or.inl (Or.inl hex), Or.inl rfl⟩
  have hJne : (incomparabilityTrace D e.1).Nonempty := by
    obtain ⟨d, hd | hd⟩ := h.exists_crossRelated_left e
    · exact False.elim (heD (hd ▸ d.2))
    · exact ⟨d, hd⟩
  by_cases hmeet : ∃ d ∈ incomparabilityTrace D x, Incomparable d.1 e.1
  · obtain ⟨d, hd, hde⟩ := hmeet
    exact ⟨d, Or.inl (Or.inl hd), Or.inr hde.symm⟩
  have hcomp : ∀ d ∈ incomparabilityTrace D x, d.1 ≤ e.1 ∨ e.1 ≤ d.1 := by
    intro d hd
    exact not_incompRel_iff_symmGen.mp (fun hde => hmeet ⟨d, hd, hde⟩)
  by_cases hea : e.1 < a.1
  · obtain ⟨d, hda, hde⟩ := trace_lower_boundary D ha hmin (h.left_finite e) hJne hea hex
    exact ⟨d, Or.inl (Or.inr hda), Or.inr hde.symm⟩
  by_cases hbe : b.1 < e.1
  · obtain ⟨d, hbd, hde⟩ := trace_upper_boundary D hb hmax (h.left_finite e) hJne hbe hex
    exact ⟨d, Or.inr hbd, Or.inr hde.symm⟩
  have hae : a.1 ≤ e.1 := (hcomp a ha).elim id
    (fun hea' => le_of_eq ((lt_or_eq_of_le hea').resolve_left hea).symm)
  have heb : e.1 ≤ b.1 := (hcomp b hb).elim
    (fun hbe' => le_of_eq ((lt_or_eq_of_le hbe').resolve_left hbe).symm) id
  obtain ⟨d, hd⟩ := hJne
  have had : a ≤ d := by
    apply le_of_not_gt
    intro hda
    exact hd.not_le ((show d.1 ≤ a.1 from hda.le).trans hae)
  have hdb : d ≤ b := by
    apply le_of_not_gt
    intro hbd
    exact hd.not_ge (heb.trans (show b.1 ≤ d.1 from hbd.le))
  exact False.elim (hmeet ⟨d, (incomparabilityTrace_ordConnected D x).out ha hb ⟨had, hdb⟩, hd⟩)

private theorem finiteDistance_of_covBy {D : SaturatedChain α} {a b : D} (hab : a ⋖ b) :
    FiniteDistance D a b := by
  apply Set.finite_empty.subset
  intro c hc
  rw [uIoo_of_lt hab.lt] at hc
  exact (hab.2 hc.1 hc.2).elim

private theorem exists_finite_trace_class_control (D : SaturatedChain α) {x : α} {s : D}
    (hI : (incomparabilityTrace D x).Finite)
    (hcontact : x = s.1 ∨ Incomparable x s.1) :
    ∃ K : Set D, K.Finite ∧ K ⊆ finiteDistanceClassSet D s ∧ ∀ e : α, Incomparable e x →
      (incomparabilityTrace D e).Finite →
      (∃ d : D, e = d.1 ∨ Incomparable e d.1) →
      ∃ d ∈ K, e = d.1 ∨ Incomparable e d.1 := by
  classical
  by_cases hxD : x ∈ D
  · have hs : (⟨x, hxD⟩ : D) = s := by
      apply Subtype.ext
      exact hcontact.resolve_right (fun hi => (D.isChain.total hxD s.2).elim hi.not_le hi.not_ge)
    refine ⟨{⟨x, hxD⟩}, Set.finite_singleton _, ?_, ?_⟩
    · intro a ha
      rw [mem_singleton_iff] at ha
      exact (ha.trans hs) ▸ FiniteDistance.refl D s
    · intro e hex _ _
      exact ⟨⟨x, hxD⟩, Set.mem_singleton _, Or.inr hex⟩
  have hs : s ∈ incomparabilityTrace D x :=
    (hcontact.resolve_left fun he => hxD (he ▸ s.2)).symm
  have hIne : (incomparabilityTrace D x).Nonempty := ⟨s, hs⟩
  obtain ⟨a, ha, hamin⟩ := hI.exists_minimal hIne
  obtain ⟨b, hb, hbmax⟩ := hI.exists_maximal hIne
  have hmin : ∀ t ∈ incomparabilityTrace D x, a ≤ t := by
    intro t ht
    exact (le_total a t).elim id (fun hta => hamin ht hta)
  have hmax : ∀ t ∈ incomparabilityTrace D x, t ≤ b := by
    intro t ht
    exact (le_total t b).elim id (fun hbt => hbmax ht hbt)
  let K : Set D := incomparabilityTrace D x ∪ {d | d ⋖ a} ∪ {d | b ⋖ d}
  have hpred : ({d : D | d ⋖ a} : Set D).Finite :=
    Set.Subsingleton.finite (fun _ hd _ hd' => hd.unique_left hd')
  have hsucc : ({d : D | b ⋖ d} : Set D).Finite :=
    Set.Subsingleton.finite (fun _ hd _ hd' => hd.unique_right hd')
  have hclass {d : D} (hd : d ∈ incomparabilityTrace D x) : FiniteDistance D s d := by
    apply hI.subset
    intro c hc
    rcases mem_uIcc.mp (uIoo_subset_uIcc_self hc) with h | h
    · exact (incomparabilityTrace_ordConnected D x).out hs hd h
    · exact (incomparabilityTrace_ordConnected D x).out hd hs h
  refine ⟨K, (hI.union hpred).union hsucc, ?_, ?_⟩
  · rintro d ((hd | hd) | hd)
    · exact hclass hd
    · exact (hclass ha).trans (finiteDistance_of_covBy hd).symm
    · exact (hclass hb).trans (finiteDistance_of_covBy hd)
  intro e hex hJ hecontact
  by_cases heD : e ∈ D
  · exact ⟨⟨e, heD⟩, Or.inl (Or.inl hex), Or.inl rfl⟩
  have hJne : (incomparabilityTrace D e).Nonempty := by
    obtain ⟨d, hd | hd⟩ := hecontact
    · exact False.elim (heD (hd ▸ d.2))
    · exact ⟨d, hd.symm⟩
  by_cases hmeet : ∃ d ∈ incomparabilityTrace D x, Incomparable d.1 e
  · obtain ⟨d, hd, hde⟩ := hmeet
    exact ⟨d, Or.inl (Or.inl hd), Or.inr hde.symm⟩
  have hcomp : ∀ d ∈ incomparabilityTrace D x, d.1 ≤ e ∨ e ≤ d.1 := by
    intro d hd
    exact not_incompRel_iff_symmGen.mp (fun hde => hmeet ⟨d, hd, hde⟩)
  by_cases hea : e < a.1
  · obtain ⟨d, hda, hde⟩ := trace_lower_boundary D ha hmin hJ hJne hea hex
    exact ⟨d, Or.inl (Or.inr hda), Or.inr hde.symm⟩
  by_cases hbe : b.1 < e
  · obtain ⟨d, hbd, hde⟩ := trace_upper_boundary D hb hmax hJ hJne hbe hex
    exact ⟨d, Or.inr hbd, Or.inr hde.symm⟩
  have hae : a.1 ≤ e := (hcomp a ha).elim id
    (fun hea' => le_of_eq ((lt_or_eq_of_le hea').resolve_left hea).symm)
  have heb : e ≤ b.1 := (hcomp b hb).elim
    (fun hbe' => le_of_eq ((lt_or_eq_of_le hbe').resolve_left hbe).symm) id
  obtain ⟨d, hd⟩ := hJne
  have had : a ≤ d := by
    apply le_of_not_gt
    intro hda
    exact hd.not_le ((show d.1 ≤ a.1 from hda.le).trans hae)
  have hdb : d ≤ b := by
    apply le_of_not_gt
    intro hbd
    exact hd.not_ge (heb.trans (show b.1 ≤ d.1 from hbd.le))
  exact False.elim (hmeet ⟨d, (incomparabilityTrace_ordConnected D x).out ha hb ⟨had, hdb⟩, hd⟩)

/-- Every point incomparable with `x` that has a finite trace and a contact
with `D` is equal or incomparable to one of finitely many controlling points. -/
theorem exists_finite_trace_control (D : SaturatedChain α) {x : α}
    (hI : (incomparabilityTrace D x).Finite)
    (hcontact : ∃ d : D, x = d.1 ∨ Incomparable x d.1) :
    ∃ K : Set D, K.Finite ∧ ∀ e : α, Incomparable e x →
      (incomparabilityTrace D e).Finite →
      (∃ d : D, e = d.1 ∨ Incomparable e d.1) →
      ∃ d ∈ K, e = d.1 ∨ Incomparable e d.1 := by
  obtain ⟨s, hs⟩ := hcontact
  obtain ⟨K, hK, _, hc⟩ := exists_finite_trace_class_control D hI hs
  exact ⟨K, hK, hc⟩

/-- Paper `lem:mfi-with-arbitrary`: a finite trace with a contact stays finite
and in the corresponding class under the canonical isomorphism. -/
theorem MutuallyFiniteIncomparability.transfer_finite_trace_class
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D) {x : α} {s : C}
    (hI : (incomparabilityTrace C x).Finite) (hs : x = s.1 ∨ Incomparable x s.1) :
    ({d : D | x = d.1 ∨ Incomparable x d.1} : Set D).Finite ∧
      ∀ d : D, x = d.1 ∨ Incomparable x d.1 →
        FiniteDistanceClass.mk d = h.classOrderIso (FiniteDistanceClass.mk s) := by
  have heq : ({d : D | x = d.1} : Set D).Finite :=
    Set.Subsingleton.finite (fun _ hd _ hd' => Subtype.ext (hd.symm.trans hd'))
  have hfinite := h.transfer_finite_trace hI ⟨s, hs⟩
  refine ⟨(heq.union hfinite).subset (fun d hd => hd.elim Or.inl (fun hi => Or.inr hi.symm)), ?_⟩
  obtain ⟨K, _, hK, hc⟩ := exists_finite_trace_class_control C hI hs
  intro d hd
  have related {c : C} (hc : FiniteDistance C s c) (hr : CrossRelated c d) :
      FiniteDistanceClass.mk d = h.classOrderIso (FiniteDistanceClass.mk s) := by
    rw [(h.classOrderIso_mk_of_crossRelated hr).symm, FiniteDistanceClass.mk_eq_mk.mpr hc]
  rcases hd with he | hi
  · apply related (FiniteDistance.refl C s)
    exact hs.elim (fun hx => Or.inl (hx.symm.trans he)) (fun hx => Or.inr (he ▸ hx.symm))
  · have hdcontact : ∃ c : C, d.1 = c.1 ∨ Incomparable d.1 c.1 := by
      obtain ⟨c, hd'⟩ := h.exists_crossRelated_left d
      exact ⟨c, hd'.elim (fun he => Or.inl he.symm) (fun hi => Or.inr hi.symm)⟩
    obtain ⟨c, hcK, hcd⟩ := hc d.1 hi.symm (h.left_finite d) hdcontact
    exact related (hK hcK) (hcd.elim (fun he => Or.inl he.symm) (fun hi => Or.inr hi.symm))

end AharoniKorman.Completion
