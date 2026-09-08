import AharoniKorman.Completion.ChainEquivalence
import Mathlib.Order.Cover

/-! Finite incomparability transfers without any classwise maximality assumption.
See `MATH_REPAIR.md` for the mathematical argument. -/

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

end AharoniKorman.Completion
