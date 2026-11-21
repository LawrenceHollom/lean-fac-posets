import AharoniKorman.External.HausdorffLocal
import AharoniKorman.External.HausdorffQuotient

/-! Hausdorff induction by merging convex classes. -/

namespace AharoniKorman.External

open Set

variable {α : Type*} [LinearOrder α]

/-- Every convex subset of `S` has the inductive property. -/
private def HereditaryOn (Q : Set α → Prop) (S : Set α) : Prop :=
  ∀ ⦃T : Set α⦄, T ⊆ S → T.OrdConnected → Q T

private theorem HereditaryOn.mono {Q : Set α → Prop} {S T : Set α}
    (hT : HereditaryOn Q T) (hST : S ⊆ T) : HereditaryOn Q S := by
  intro U hU hconv
  exact hT (hU.trans hST) hconv

private theorem HereditaryOn.union {Q : Set α → Prop} (sum : WellSumClosed Q)
    {A B : Set α} (hA : A.OrdConnected) (hB : B.OrdConnected) (hord : SetStrictLT A B)
    (hQA : HereditaryOn Q A) (hQB : HereditaryOn Q B) : HereditaryOn Q (A ∪ B) := by
  intro T hT hconv
  have heq : (T ∩ A) ∪ (T ∩ B) = T := by
    rw [← inter_union_distrib_left, inter_eq_left.mpr hT]
  have hUnion : ((T ∩ A) ∪ (T ∩ B)).OrdConnected := heq.symm ▸ hconv
  exact heq ▸ sum.union (hconv.inter hA) (hconv.inter hB) hUnion
    (fun _ hx _ hy => hord hx.2 hy.2) (hQA inter_subset_right (hconv.inter hA))
    (hQB inter_subset_right (hconv.inter hB))

private theorem hereditary_interval_forward {Q : Set α → Prop} (sum : WellSumClosed Q)
    {a b c : α} (hac : a ≤ c) (hab : HereditaryOn Q (uIcc a b)) (hbc : HereditaryOn Q (uIcc b c)) :
    HereditaryOn Q (uIcc a c) := by
  rw [uIcc_of_le hac]
  by_cases hba : b ≤ a
  · rw [uIcc_of_le (hba.trans hac)] at hbc
    exact hbc.mono (Icc_subset_Icc_left hba)
  by_cases hcb : c ≤ b
  · rw [uIcc_of_le (hac.trans hcb)] at hab
    exact hab.mono (Icc_subset_Icc_right hcb)
  have h₁ : a ≤ b := (lt_of_not_ge hba).le
  have h₂ : b ≤ c := (lt_of_not_ge hcb).le
  rw [uIcc_of_le h₁] at hab
  rw [uIcc_of_le h₂] at hbc
  rw [← Icc_union_Ioc_eq_Icc h₁ h₂]
  exact HereditaryOn.union sum ordConnected_Icc ordConnected_Ioc
    (fun _ hx _ hy => hx.2.trans_lt hy.1) hab (hbc.mono Ioc_subset_Icc_self)

/-- The induction direction of Hausdorff's classification for scattered linear orders.
The equivalence classes of points joined by a hereditarily good interval are themselves
hereditarily good. A cover in the quotient could be merged, so the scattered quotient has
at most one point. -/
theorem scattered_well_sum_induction (hsc : IsScattered α) (Q : Set α → Prop)
    (base : ∀ S : Set α, S.OrdConnected →
      (WellFounded ((· < ·) : S → S → Prop) ∨ WellFounded ((· > ·) : S → S → Prop)) → Q S)
    (sum : WellSumClosed Q) : Q univ := by
  classical
  have hEmpty : Q (∅ : Set α) := base ∅ ordConnected_empty (Or.inl (wellFounded_of_isEmpty _))
  let s : Setoid α := {
    r a b := HereditaryOn Q (uIcc a b)
    iseqv := {
      refl := fun a => by
        rw [uIcc_self]
        intro T hT hconv
        refine base T hconv (Or.inl ⟨fun x => Acc.intro x fun y hyx => ?_⟩)
        have hx : x.val = a := mem_singleton_iff.mp (hT x.property)
        have hy : y.val = a := mem_singleton_iff.mp (hT y.property)
        exact (hyx.ne (Subtype.ext (hy.trans hx.symm))).elim
      symm := fun {a b} h => by simpa only [uIcc_comm b a] using h
      trans := fun {a b c} hab hbc => by
        rcases le_total a c with hac | hca
        · exact hereditary_interval_forward sum hac hab hbc
        · rw [uIcc_comm a c]
          exact hereditary_interval_forward sum hca (uIcc_comm b c ▸ hbc) (uIcc_comm a b ▸ hab) } }
  let classOf (c : Quotient s) := Quotient.mk s ⁻¹' {c}
  have hclass (c : Quotient s) : (classOf c).OrdConnected := by
    constructor
    intro a ha b hb z hz
    have hab : s.r a b := Quotient.exact ((show Quotient.mk s a = c from ha).trans
      (show Quotient.mk s b = c from hb).symm)
    have haz : s.r a z := HereditaryOn.mono hab <| by
      rw [uIcc_of_le hz.1, uIcc_of_le (hz.1.trans hz.2)]
      exact Icc_subset_Icc_right hz.2
    exact (Quotient.sound haz).symm.trans ha
  let : ∀ c : Quotient s, (Quotient.mk s ⁻¹' {c}).OrdConnected := hclass
  have hgood (c : Quotient s) : HereditaryOn Q (classOf c) := by
    intro T hT hconv
    apply convex_of_bounded_convex Q hEmpty sum hconv
    rintro U _ hU ⟨a, ha, b, hb, hbound⟩
    have ha' : Quotient.mk s a = c := hT ha
    have hb' : Quotient.mk s b = c := hT hb
    have hab : s.r a b := Quotient.exact (ha'.trans hb'.symm)
    exact (show HereditaryOn Q (uIcc a b) from hab) (hbound.trans Icc_subset_uIcc) hU
  have noCover {c d : Quotient s} (hcd : c ⋖ d) : False := by
    have hUnion : classOf c ∪ classOf d = Quotient.mk s ⁻¹' Icc c d := by
      rw [hcd.Icc_eq]
      ext a
      simp [classOf]
    have hconv : (classOf c ∪ classOf d).OrdConnected := by
      rw [hUnion]
      exact ordConnected_Icc.preimage_mono Quotient.mk_monotone
    have hord : SetStrictLT (classOf c) (classOf d) := by
      intro a ha b hb
      exact Quotient.lt_of_mk_lt_mk (show Quotient.mk s a < Quotient.mk s b from
        (show Quotient.mk s a = c from ha).symm ▸ (show Quotient.mk s b = d from hb).symm ▸ hcd.lt)
    have hGoodUnion := HereditaryOn.union sum (hclass c) (hclass d) hord (hgood c) (hgood d)
    have hc : c.out ∈ classOf c := Quotient.out_eq c
    have hd : d.out ∈ classOf d := Quotient.out_eq d
    have hequiv : s.r c.out d.out := hGoodUnion.mono (hconv.uIcc_subset (Or.inl hc) (Or.inr hd))
    exact hcd.lt.ne ((Quotient.out_eq c).symm.trans ((Quotient.sound hequiv).trans (Quotient.out_eq d)))
  have hquot := hsc.quotient s
  let : Subsingleton (Quotient s) := ⟨fun c d => by
    rcases lt_trichotomy c d with h | h | h
    · obtain ⟨_, _, _, _, _, hcov⟩ := hquot.exists_covBy_between h
      exact (noCover hcov).elim
    · exact h
    · obtain ⟨_, _, _, _, _, hcov⟩ := hquot.exists_covBy_between h
      exact (noCover hcov).elim⟩
  by_cases hα : Nonempty α
  · obtain ⟨a⟩ := hα
    exact hgood (Quotient.mk s a) (fun _ _ => Subsingleton.elim _ _) ordConnected_univ
  · let : IsEmpty α := not_nonempty_iff.mp hα
    exact base univ ordConnected_univ (Or.inl (wellFounded_of_isEmpty _))

end AharoniKorman.External
