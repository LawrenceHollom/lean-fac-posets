import AharoniKorman.Consolidation.AtomicWellFounded

/-! The greedy positive sweep from `prop:consolidated-exists`. -/

namespace AharoniKorman.Consolidation

open Set Completion Completion.H

noncomputable section

variable {α : Type*} [PartialOrder α]

instance : PartialOrder (PositiveAtom α) :=
  PartialOrder.lift (fun a => H.increasing a.1)
    (fun _ _ heq => Subtype.ext (H.increasing.inj heq))

theorem positive_domination_wellFounded (hq : IsQuasifounded α) :
    WellFounded (LT.lt : PositiveAtom α → PositiveAtom α → Prop) :=
  InvImage.wf (fun a : PositiveAtom α => (⟨H.increasing a.1, rfl⟩ : NPlus α)) hq.1

theorem positive_profile_ssubset_of_lt {a b : PositiveAtom α} (hab : a < b) :
    a.1.lowerProfile ⊂ b.1.lowerProfile := by
  have hab' : H.increasing a.1 < H.increasing b.1 := hab
  obtain ⟨p, ha, hb⟩ := H.exists_principal_between_increasing hab'
  exact lt_iff_le_not_ge.2 ⟨IncreasingGerm.cofinalAbove_of_le hab'.le,
    fun h => (ha.trans (h hb)).false⟩

/-- A positive atom eligible to be chosen after the previously selected atoms. -/
def PositiveCandidate (Q : Set α) (S : Set (PositiveAtom α)) (a : PositiveAtom α) : Prop :=
  ∃ A : IncreasingChain α, a.1.Represents A ∧ (A.1 : Set α) ⊆ Q ∧
    ∀ s ∈ S, ∀ p : A.1, H.increasing s.1 < H.principal p.1

theorem PositiveCandidate.lt {Q : Set α} {S : Set (PositiveAtom α)} {a : PositiveAtom α}
    (ha : PositiveCandidate Q S a) {s : PositiveAtom α} (hs : s ∈ S) : s < a := by
  obtain ⟨A, hA, _, hAS⟩ := ha
  obtain ⟨p, hp⟩ := A.1.nonempty
  change H.increasing s.1 < H.increasing a.1
  rw [← hA]
  exact (hAS s hs ⟨p, hp⟩).trans (IncreasingGerm.representative_mem_lowerProfile A ⟨p, hp⟩)

theorem PositiveCandidate.mono {Q : Set α} {R S : Set (PositiveAtom α)} {a : PositiveAtom α}
    (ha : PositiveCandidate Q S a) (hRS : R ⊆ S) : PositiveCandidate Q R a := by
  obtain ⟨A, hA, hAQ, hAS⟩ := ha
  exact ⟨A, hA, hAQ, fun s hs p => hAS s (hRS hs) p⟩

private theorem previous_eq {D E : Set (PositiveAtom α)} (hDE : IsInitialSegment D E)
    {a : PositiveAtom α} (ha : a ∈ D) : E ∩ Iio a = D ∩ Iio a :=
  Set.Subset.antisymm (fun _ hx => ⟨hDE.2 ha hx.1 hx.2.le, hx.2⟩)
    (inter_subset_inter_left _ hDE.1)

/-- An initial portion of the greedy sweep, recording the minimality that
licensed each choice. -/
structure PositiveSweep (Q : Set α) where
  carrier : Set (PositiveAtom α)
  isChain : IsChain (· ≤ ·) carrier
  candidate : ∀ a ∈ carrier, PositiveCandidate Q (carrier ∩ Iio a) a
  minimal : ∀ a ∈ carrier, ∀ b, PositiveCandidate Q (carrier ∩ Iio a) b →
    ¬ b.1.lowerProfile ⊂ a.1.lowerProfile

namespace PositiveSweep

instance {Q : Set α} : PartialOrder (PositiveSweep Q) where
  le D E := IsInitialSegment D.carrier E.carrier
  le_refl _ := ⟨Subset.rfl, fun _ _ _ hy _ => hy⟩
  le_trans _ _ _ hDE hEF :=
    ⟨hDE.1.trans hEF.1, fun _ _ hx hy hyx => hDE.2 hx (hEF.2 (hDE.1 hx) hy hyx) hyx⟩
  le_antisymm D E hDE hED := by
    have h := Set.Subset.antisymm hDE.1 hED.1
    cases D
    cases E
    cases h
    rfl

private theorem bddAbove {Q : Set α} (F : Set (PositiveSweep Q))
    (hF : IsChain (· ≤ ·) F) : BddAbove F := by
  let U := ⋃ S ∈ F, PositiveSweep.carrier S
  have hSU {S : PositiveSweep Q} (hS : S ∈ F) : IsInitialSegment S.carrier U := by
    constructor
    · intro x hx
      exact mem_iUnion.2 ⟨S, mem_iUnion.2 ⟨hS, hx⟩⟩
    · intro x y hx hy hyx
      obtain ⟨T, hy⟩ := mem_iUnion.1 hy
      obtain ⟨hT, hy⟩ := mem_iUnion.1 hy
      rcases hF.total hS hT with hST | hTS
      · exact hST.2 hx hy hyx
      · exact hTS.1 hy
  have hUchain : IsChain (· ≤ ·) U := by
    intro x hx y hy hxy
    obtain ⟨S, hx⟩ := mem_iUnion.1 hx
    obtain ⟨hS, hx⟩ := mem_iUnion.1 hx
    obtain ⟨T, hy⟩ := mem_iUnion.1 hy
    obtain ⟨hT, hy⟩ := mem_iUnion.1 hy
    rcases hF.total hS hT with hST | hTS
    · exact T.isChain (hST.1 hx) hy hxy
    · exact S.isChain hx (hTS.1 hy) hxy
  have hC (a : PositiveAtom α) (ha : a ∈ U) : PositiveCandidate Q (U ∩ Iio a) a := by
    obtain ⟨S, ha⟩ := mem_iUnion.1 ha
    obtain ⟨hS, ha⟩ := mem_iUnion.1 ha
    exact (previous_eq (hSU hS) ha).symm ▸ S.candidate a ha
  have hM (a : PositiveAtom α) (ha : a ∈ U) (b : PositiveAtom α)
      (hb : PositiveCandidate Q (U ∩ Iio a) b) : ¬ b.1.lowerProfile ⊂ a.1.lowerProfile := by
    obtain ⟨S, ha⟩ := mem_iUnion.1 ha
    obtain ⟨hS, ha⟩ := mem_iUnion.1 ha
    exact S.minimal a ha b (previous_eq (hSU hS) ha ▸ hb)
  exact ⟨⟨U, hUchain, hC, hM⟩, fun _ hS => hSU hS⟩

/-- The paper's process continues until there is no atom admitting a ray
above all chosen atoms. Compatible initial portions have a union, which
packages the successor and limit stages of the transfinite construction. -/
theorem exists_exhausted (Q : Set α)
    (hwf : WellFounded (fun g h : PositiveAtom α => g.1.lowerProfile ⊂ h.1.lowerProfile)) :
    ∃ D : PositiveSweep Q, ∀ a, ¬ PositiveCandidate Q D.carrier a := by
  classical
  obtain ⟨D, hD⟩ := zorn_le (α := PositiveSweep Q) bddAbove
  refine ⟨D, fun a ha => ?_⟩
  let S := {b : PositiveAtom α | PositiveCandidate Q D.carrier b}
  let b := hwf.min S ⟨a, ha⟩
  have hb : PositiveCandidate Q D.carrier b := hwf.min_mem S ⟨a, ha⟩
  have hbmin (c : PositiveAtom α) (hc : PositiveCandidate Q D.carrier c) :
      ¬ c.1.lowerProfile ⊂ b.1.lowerProfile := hwf.not_lt_min S hc
  have hbnot : b ∉ D.carrier := fun h => (hb.lt h).false
  let E := insert b D.carrier
  have hDE : IsInitialSegment D.carrier E := by
    refine ⟨subset_insert _ _, fun x y hx hy hyx => ?_⟩
    rcases mem_insert_iff.1 hy with rfl | hy
    · exact ((hb.lt hx).not_ge hyx).elim
    · exact hy
  have hEchain : IsChain (· ≤ ·) E :=
    D.isChain.insert (fun _ hx _ => Or.inr (hb.lt hx).le)
  have hbelow : E ∩ Iio b = D.carrier := by
    ext x
    constructor
    · rintro ⟨hx, hxb⟩
      exact (mem_insert_iff.1 hx).resolve_left (ne_of_lt hxb)
    · intro hx
      exact ⟨mem_insert_of_mem _ hx, hb.lt hx⟩
  have hCandidate (x : PositiveAtom α) (hx : x ∈ E) : PositiveCandidate Q (E ∩ Iio x) x := by
    rcases mem_insert_iff.1 hx with rfl | hx
    · exact hbelow.symm ▸ hb
    · exact (previous_eq hDE hx).symm ▸ D.candidate x hx
  have hMinimal (x : PositiveAtom α) (hx : x ∈ E) (c : PositiveAtom α)
      (hc : PositiveCandidate Q (E ∩ Iio x) c) : ¬ c.1.lowerProfile ⊂ x.1.lowerProfile := by
    rcases mem_insert_iff.1 hx with rfl | hx
    · exact hbmin c (hbelow ▸ hc)
    · exact D.minimal x hx c (previous_eq hDE hx ▸ hc)
  let bigger : PositiveSweep Q := ⟨E, hEchain, hCandidate, hMinimal⟩
  have hh : bigger ≤ D := hD (show D ≤ bigger from hDE)
  exact hbnot (hh.1 (mem_insert _ _))

/-- The positive version of `claim:no-extra-atomics`, using the first chosen
atom strictly above a proposed additional atom. -/
theorem mem_of_can_insert {Q : Set α} (D : PositiveSweep Q)
    (hEx : ∀ a, ¬ PositiveCandidate Q D.carrier a)
    (hwf : WellFounded (LT.lt : PositiveAtom α → PositiveAtom α → Prop))
    (a : PositiveAtom α) (hcomp : ∀ b ∈ D.carrier, b ≤ a ∨ a ≤ b)
    (ha : PositiveCandidate Q (D.carrier ∩ Iio a) a) : a ∈ D.carrier := by
  classical
  by_contra hanot
  let U := D.carrier ∩ Ioi a
  by_cases hUne : U.Nonempty
  · let b := hwf.min U hUne
    have hb : b ∈ U := hwf.min_mem U hUne
    have hsub : D.carrier ∩ Iio b ⊆ D.carrier ∩ Iio a := by
      rintro x ⟨hx, hxb⟩
      refine ⟨hx, ?_⟩
      rcases hcomp x hx with hxa | hax
      · exact lt_of_le_of_ne hxa (fun heq => hanot (heq ▸ hx))
      · have hax' : a < x := lt_of_le_of_ne hax (fun heq => hanot (heq.symm ▸ hx))
        exact (hwf.not_lt_min U (show x ∈ U from ⟨hx, hax'⟩) hxb).elim
    exact D.minimal b hb.1 a (ha.mono hsub) (positive_profile_ssubset_of_lt hb.2)
  · have hsub : D.carrier ⊆ D.carrier ∩ Iio a := by
      intro x hx
      refine ⟨hx, ?_⟩
      rcases hcomp x hx with hxa | hax
      · exact lt_of_le_of_ne hxa (fun heq => hanot (heq ▸ hx))
      · have hax' : a < x := lt_of_le_of_ne hax (fun heq => hanot (heq.symm ▸ hx))
        exact (hUne ⟨x, hx, hax'⟩).elim
    exact hEx a (ha.mono hsub)

/-- Taking a final segment keeps the increasing germ represented. -/
theorem tail_represents {g : IncreasingGerm α} {A : IncreasingChain α}
    (hA : g.Represents A) (a : A.1) :
    g.Represents (⟨A.1.tail a, A.1.tail_noTop a A.2⟩ : IncreasingChain α) := by
  apply Eq.trans _ hA
  apply IncreasingGerm.ofChain_eq_iff.2
  exact ⟨A.1.tail a, A.1.tail a,
    ⟨Subset.rfl, fun _ _ _ hy _ => hy⟩, A.1.tail_final a, MutuallyFiniteIncomparability.refl _⟩

/-- Realize all choices on one chain. If the chosen set is nonempty, its first
atom supplies a principal lower bound after trimming its representative. -/
theorem exists_chain_bounded_below {Q : Set α} (D : PositiveSweep Q)
    (hwf : WellFounded (LT.lt : PositiveAtom α → PositiveAtom α → Prop)) :
    ∃ S : Set α, IsChain (· ≤ ·) S ∧ S ⊆ Q ∧
      (∀ a ∈ D.carrier, H.increasing a.1 ∈ boundaries S) ∧
      (S = ∅ ∨ ∃ p ∈ Q, ∀ x ∈ S, p ≤ x) := by
  classical
  by_cases hne : D.carrier.Nonempty
  · let b := hwf.min D.carrier hne
    have hb : b ∈ D.carrier := hwf.min_mem D.carrier hne
    let t (a : D.carrier) := D.candidate a.1 a.2
    choose A hA hAQ hAlt using t
    let b' : D.carrier := ⟨b, hb⟩
    obtain ⟨p, hp⟩ := (A b').1.nonempty
    let p' : (A b').1 := ⟨p, hp⟩
    have hbRays (a : D.carrier) : ∃ B : IncreasingChain α,
        a.1.1.Represents B ∧ B.1.carrier ⊆ (A a).1.carrier ∧
        (∀ x ∈ B.1.carrier, p ≤ x) := by
      by_cases ha : a = b'
      · subst a
        let B : IncreasingChain α := ⟨(A b').1.tail p', (A b').1.tail_noTop p' (A b').2⟩
        exact ⟨B, tail_represents (hA b') p', fun _ hx => hx.1, fun _ hx => hx.2⟩
      · have hba : b < a.1 := by
          rcases D.isChain.total hb a.2 with hba | hab
          · exact lt_of_le_of_ne hba (fun heq => ha (Subtype.ext heq.symm))
          · have hab' : a.1 < b := lt_of_le_of_ne hab (fun heq => ha (Subtype.ext heq))
            exact (hwf.not_lt_min D.carrier a.2 hab').elim
        have hpLt : H.principal p < H.increasing b.1 := by
          rw [← hA b']
          exact IncreasingGerm.representative_mem_lowerProfile (A b') p'
        exact ⟨A a, hA a, Subset.rfl, fun x hx => ((H.principal_lt_principal p x).1
          (hpLt.trans (hAlt a b ⟨hb, hba⟩ ⟨x, hx⟩))).le⟩
    choose B hBg hBA hBp using hbRays
    let S := ⋃ a : D.carrier, (B a).1.carrier
    have hSp (x : α) (hx : x ∈ S) : p ≤ x := by
      obtain ⟨a, hxa⟩ := mem_iUnion.1 hx
      exact hBp a x hxa
    have horder {a b : D.carrier} (hab : a.1 < b.1) :
        SetStrictLT (B a).1.carrier (B b).1.carrier := by
      intro x hx y hy
      have hx' : H.principal x < H.increasing a.1.1 := by
        rw [← hA a]
        exact IncreasingGerm.representative_mem_lowerProfile (A a) ⟨x, hBA a hx⟩
      exact (H.principal_lt_principal x y).1
        (hx'.trans (hAlt b a.1 ⟨a.2, hab⟩ ⟨y, hBA b hy⟩))
    have hchain : IsChain (· ≤ ·) S := by
      intro x hx y hy hxy
      obtain ⟨a, hxa⟩ := mem_iUnion.1 hx
      obtain ⟨b, hyb⟩ := mem_iUnion.1 hy
      rcases D.isChain.total a.2 b.2 with hab | hba
      · rcases lt_or_eq_of_le hab with hab | hab
        · exact Or.inl ((horder hab hxa hyb).le)
        · have heq : a = b := Subtype.ext hab
          exact (B a).1.isChain hxa (heq.symm ▸ hyb) hxy
      · rcases lt_or_eq_of_le hba with hba | hba
        · exact Or.inr ((horder hba hyb hxa).le)
        · have heq : b = a := Subtype.ext hba
          exact (B a).1.isChain hxa (heq ▸ hyb) hxy
    refine ⟨S, hchain, ?_, ?_, Or.inr ⟨p, hAQ b' hp, hSp⟩⟩
    · intro x hx
      obtain ⟨a, ha⟩ := mem_iUnion.1 hx
      exact hAQ a (hBA a ha)
    · intro a ha
      let a' : D.carrier := ⟨a, ha⟩
      exact Or.inl ⟨B a', (fun _ hx => mem_iUnion.2 ⟨a', hx⟩),
        congrArg H.increasing (hBg a').symm⟩
  · exact ⟨∅, by intro x hx; exact hx.elim, empty_subset _,
      fun a ha => (hne ⟨a, ha⟩).elim, Or.inl rfl⟩

end PositiveSweep

end

end AharoniKorman.Consolidation
