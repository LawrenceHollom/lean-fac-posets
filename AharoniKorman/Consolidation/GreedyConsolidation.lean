import AharoniKorman.Consolidation.GreedySweep
import AharoniKorman.Consolidation.AtomicOrder
import AharoniKorman.Consolidation.AtomicIsolation

/-! The positive sweep, the dual sweeps in its gaps, and their simultaneous realization. -/

namespace AharoniKorman.Consolidation

open Set Completion

noncomputable section

variable {α : Type*} [PartialOrder α]

private abbrev pos (a : PositiveAtom α) : H α := H.increasing a.1
private abbrev neg (b : PositiveAtom αᵒᵈ) : H α := H.decreasing b.1

private abbrev PositiveCuts (D : PositiveSweep (univ : Set α)) :=
  {I : Set (PositiveAtom α) // IsInitialSegment I D.carrier}

private def gap {D : PositiveSweep (univ : Set α)} (I : PositiveCuts D) : Set α :=
  {p | (∀ x ∈ I.1, pos x < H.principal p) ∧
    (∀ x ∈ D.carrier \ I.1, H.principal p < pos x)}

private theorem candidate_of_chain {C Q : Set α} (hC : IsSaturatedChain C)
    {a : PositiveAtom α} (ha : pos a ∈ boundaries C)
    {S : Set (PositiveAtom α)} (hS : ∀ b ∈ S, pos b ∈ boundaries C ∧ b < a)
    (hQ : ∀ x ∈ C, H.principal x < pos a →
      (∀ Y ∈ boundaries C, Y < pos a → Y < H.principal x) → x ∈ Q) :
    PositiveCandidate Q S a := by
  obtain ⟨p, hpC, hp, hsep⟩ := positiveAtom_isolated hC a.2 ha
  obtain ⟨A, hAC, hA⟩ := increasingGerm_mem_boundaries ha
  have hpA : H.principal p < H.increasing (IncreasingGerm.ofChain A) := by rwa [hA]
  obtain ⟨u, hu⟩ := (H.principal_lt_increasing_ofChain p A).1 hpA
  let B : IncreasingChain α := ⟨A.1.tail u, A.1.tail_noTop u A.2⟩
  have hBg : IncreasingGerm.ofChain B = a.1 := PositiveSweep.tail_represents hA u
  have hBound (x : B.1) : H.principal x.1 < pos a := by
    change H.principal x.1 < H.increasing a.1
    rw [← hBg]
    exact IncreasingGerm.representative_mem_lowerProfile B x
  have hAbove (x : B.1) (Y : H α) (hY : Y ∈ boundaries C) (hYa : Y < pos a) :
      Y < H.principal x.1 :=
    (hsep Y hY hYa).trans ((H.principal_lt_principal p x.1).2 (hu.trans_le x.2.2))
  exact ⟨B, hBg, fun x hx => hQ x (hAC hx.1) (hBound ⟨x, hx⟩) (hAbove ⟨x, hx⟩),
    fun b hb x => hAbove x (pos b) (hS b hb).1 (hS b hb).2⟩

private theorem positive_comparable {C : Set α} (hC : IsSaturatedChain C)
    {a b : PositiveAtom α} (ha : pos a ∈ boundaries C) (hb : pos b ∈ boundaries C) :
    a ≤ b ∨ b ≤ a := (boundaries_isChain hC).total ha hb

private def cutBefore {D : PositiveSweep (univ : Set α)} (a : D.carrier) : PositiveCuts D :=
  ⟨D.carrier ∩ Iio a.1,
    inter_subset_left, fun _ _ hx hy hyx => ⟨hy, hyx.trans_lt hx.2⟩⟩

private def cutAt {D : PositiveSweep (univ : Set α)} (z : H α) : PositiveCuts D :=
  ⟨{a ∈ D.carrier | pos a < z},
    fun _ ha => ha.1, fun x y hx hy hle => ⟨hy, (show pos y ≤ pos x from hle).trans_lt hx.2⟩⟩

private theorem gap_posRays {D : PositiveSweep (univ : Set α)} (a : D.carrier)
    {A : IncreasingChain α} (hA : a.1.1.Represents A)
    (hbelow : ∀ s ∈ D.carrier ∩ Iio a.1, ∀ x : A.1, pos s < H.principal x.1) :
    (A.1 : Set α) ⊆ gap (cutBefore a) := by
  intro p hp
  refine ⟨fun b hb => hbelow b hb ⟨p, hp⟩, fun b hb => ?_⟩
  have h : H.principal p < pos a.1 := by
    change H.principal p < H.increasing a.1.1
    rw [← hA]
    exact IncreasingGerm.representative_mem_lowerProfile A ⟨p, hp⟩
  have hab : a.1 ≤ b := by
    rcases D.isChain.total a.2 hb.1 with hab | hba
    · exact hab
    · exact le_of_eq (eq_of_le_of_not_lt hba (fun h => hb.2 ⟨hb.1, h⟩)).symm
  exact h.trans_le hab

private theorem gap_ordered {D : PositiveSweep (univ : Set α)} {I J : PositiveCuts D}
    {a : PositiveAtom α} (haI : a ∈ I.1) (haJ : a ∉ J.1) :
    SetStrictLT (gap J) (gap I) := by
  intro x hx y hy
  exact (H.principal_lt_principal x y).1
    ((hx.2 a ⟨I.2.1 haI, haJ⟩).trans (hy.1 a haI))

private theorem gaps_comparable {D : PositiveSweep (univ : Set α)} (I J : PositiveCuts D) :
    I = J ∨ SetStrictLT (gap I) (gap J) ∨ SetStrictLT (gap J) (gap I) := by
  classical
  by_cases hIJ : I.1 ⊆ J.1
  · by_cases hJI : J.1 ⊆ I.1
    · exact Or.inl (Subtype.ext (Set.Subset.antisymm hIJ hJI))
    · obtain ⟨a, haJ, haI⟩ := Set.not_subset.1 hJI
      exact Or.inr (Or.inl (gap_ordered haJ haI))
  · obtain ⟨a, haI, haJ⟩ := Set.not_subset.1 hIJ
    exact Or.inr (Or.inr (gap_ordered haI haJ))

private theorem negative_candidate_in_cut {D : PositiveSweep (univ : Set α)}
    {C : Set α} (hC : IsSaturatedChain C)
    (hD : ∀ a ∈ D.carrier, pos a ∈ boundaries C)
    (I : PositiveCuts D) {b : PositiveAtom αᵒᵈ} (hb : neg b ∈ boundaries C)
    (hcut : I = cutAt (neg b))
    {S : Set (PositiveAtom αᵒᵈ)} (hS : ∀ g ∈ S, neg g ∈ boundaries C ∧ g < b) :
    PositiveCandidate (α := αᵒᵈ) (gap (α := α) I) S b := by
  apply candidate_of_chain (α := αᵒᵈ) hC.dual (boundary_dual_mem (α := α) hb)
  · intro g hg
    exact ⟨boundary_dual_mem (α := α) (hS g hg).1, (hS g hg).2⟩
  · intro x hx hxb hsep
    change H.principal (α := αᵒᵈ) x < (neg b).dual at hxb
    have hbx : neg b < H.principal (α := α) x :=
      (H.dual_lt_dual (H.principal (α := α) x) (neg b)).1 hxb
    refine ⟨?_, ?_⟩
    · intro a ha
      have ha' : a ∈ (cutAt (D := D) (neg b)).1 := hcut ▸ ha
      have hab : pos a < neg b := (show a ∈ D.carrier ∧ pos a < neg b from ha').2
      exact hab.trans hbx
    · intro a ha
      have hn : ¬ pos a < neg b := fun h => ha.2 (hcut.symm ▸
        (show a ∈ (cutAt (D := D) (neg b)).1 from ⟨ha.1, h⟩))
      have hba : neg b < pos a := by
        rcases (boundaries_isChain hC).total hb (hD a ha.1) with hle | hge
        · exact lt_of_le_of_ne hle (by intro h; cases h)
        · exact (hn (lt_of_le_of_ne hge (by intro h; cases h))).elim
      exact (H.dual_lt_dual (pos a) (H.principal (α := α) x)).1
        (hsep (pos a).dual (boundary_dual_mem (α := α) (hD a ha.1))
          ((H.dual_lt_dual (pos a) (neg b)).2 hba))

private theorem cutAt_eq_of_negative_ray_in_gap {D : PositiveSweep (univ : Set α)}
    (I : PositiveCuts D) {b : PositiveAtom αᵒᵈ} {S : Set α}
    (hS : S ⊆ gap I) (hb : neg b ∈ boundaries S) : cutAt (neg b) = I := by
  rcases hb with ⟨A, hAS, hA⟩ | ⟨A, hAS, hA⟩
  · cases hA
  apply Subtype.ext
  ext a
  change (a ∈ D.carrier ∧ pos a < neg b) ↔ a ∈ I.1
  constructor
  · intro ha
    by_contra hnot
    obtain ⟨p, hp⟩ := A.1.nonempty
    have hp' := (hS (hAS hp)).2 a ⟨ha.1, hnot⟩
    have hbp : neg b < H.principal p := by
      rw [hA]
      exact (H.decreasing_ofChain_lt_principal A p).2 (A.2.exists_lt ⟨p, hp⟩)
    exact (ha.2.trans (hbp.trans hp')).false
  · intro ha
    refine ⟨I.2.1 ha, ?_⟩
    change H.increasing a.1 < neg b
    rw [hA]
    have hbound (p : A.1) : H.increasing a.1 < H.principal p.1 :=
      (hS (hAS p.2)).1 a ha
    generalize hg : a.1 = g at hbound ⊢
    induction g using IncreasingGerm.inductionOn with
    | h B =>
      exact (H.increasing_ofChain_lt_decreasing_ofChain B A).2
        (fun q p => (H.increasing_ofChain_lt_principal B p.1).1 (hbound p) q)

private theorem cutBefore_injective {D : PositiveSweep (univ : Set α)} :
    Function.Injective (@cutBefore α _ D) := by
  intro a b h
  apply Subtype.ext
  by_contra hne
  rcases D.isChain.total a.2 b.2 with hab | hba
  · have hab' : a.1 < b.1 := lt_of_le_of_ne hab hne
    have hm : a.1 ∈ (cutBefore b).1 := ⟨a.2, hab'⟩
    exact (lt_irrefl a.1) (show a.1 ∈ (cutBefore a).1 from h.symm ▸ hm).2
  · have hba' : b.1 < a.1 := lt_of_le_of_ne hba (fun h => hne h.symm)
    have hm : b.1 ∈ (cutBefore a).1 := ⟨b.2, hba'⟩
    exact (lt_irrefl b.1) (show b.1 ∈ (cutBefore b).1 from h ▸ hm).2

private theorem exists_chain_realizing_sweeps (hq : IsQuasifounded α)
    (D : PositiveSweep (univ : Set α))
    (E : ∀ I : PositiveCuts D, PositiveSweep (α := αᵒᵈ) (gap (α := α) I)) :
    ∃ C : MaximalChains α,
      (∀ a ∈ D.carrier, pos a ∈ boundaries C.carrier) ∧
      (∀ (I : PositiveCuts D) (b : PositiveAtom αᵒᵈ), b ∈ (E I).carrier →
        neg b ∈ boundaries C.carrier ∧ cutAt (D := D) (neg b) = I) := by
  classical
  have hn (I : PositiveCuts D) :=
    (E I).exists_chain_bounded_below (positive_domination_wellFounded hq.orderDual)
  choose R hRchain hRgap hRg hRcap using hn
  have hA (a : D.carrier) : ∃ A : IncreasingChain α,
      a.1.1.Represents A ∧ (A.1 : Set α) ⊆ gap (cutBefore a) ∧
      SetStrictLT (α := α) (R (cutBefore a)) A.1.carrier := by
    obtain ⟨A, hA, _, hAlt⟩ := D.candidate a.1 a.2
    have hAgap := gap_posRays a hA hAlt
    rcases hRcap (cutBefore a) with hzero | ⟨p, hp, hcap⟩
    · exact ⟨A, hA, hAgap, fun _ hx => (Set.notMem_empty _ (hzero ▸ hx)).elim⟩
    · have hpA : H.principal (α := α) p < H.increasing (IncreasingGerm.ofChain A) := by
        rw [hA]
        exact hp.2 a.1 ⟨a.2, fun h => (lt_irrefl a.1) h.2⟩
      obtain ⟨t, ht⟩ := (H.principal_lt_increasing_ofChain (α := α) p A).1 hpA
      let B : IncreasingChain α := ⟨A.1.tail t, A.1.tail_noTop t A.2⟩
      refine ⟨B, PositiveSweep.tail_represents hA t, fun x hx => hAgap hx.1, ?_⟩
      intro x hx y hy
      exact @lt_of_le_of_lt α _ x p y (hcap x hx) (@lt_of_lt_of_le α _ p t.1 y ht hy.2)
  choose A hAg hAgap hAR using hA
  let U : Set α := (⋃ I, R I) ∪ ⋃ a, (A a).1.carrier
  have hchain : IsChain ((· ≤ ·) : α → α → Prop) U := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · obtain ⟨I, hx⟩ := mem_iUnion.1 hx
      obtain ⟨J, hy⟩ := mem_iUnion.1 hy
      rcases gaps_comparable I J with rfl | hIJ | hJI
      · exact ((hRchain I hx hy hxy).symm)
      · exact Or.inl (hIJ (hRgap I hx) (hRgap J hy)).le
      · exact Or.inr (hJI (hRgap J hy) (hRgap I hx)).le
    · obtain ⟨I, hx⟩ := mem_iUnion.1 hx
      obtain ⟨a, hy⟩ := mem_iUnion.1 hy
      rcases gaps_comparable I (cutBefore a) with hEq | hIJ | hJI
      · subst I
        exact Or.inl (hAR a hx hy).le
      · exact Or.inl (hIJ (hRgap I hx) (hAgap a hy)).le
      · exact Or.inr (hJI (hAgap a hy) (hRgap I hx)).le
    · obtain ⟨a, hx⟩ := mem_iUnion.1 hx
      obtain ⟨J, hy⟩ := mem_iUnion.1 hy
      rcases gaps_comparable (cutBefore a) J with hEq | hIJ | hJI
      · subst J
        exact Or.inr (hAR a hy hx).le
      · exact Or.inl (hIJ (hAgap a hx) (hRgap J hy)).le
      · exact Or.inr (hJI (hRgap J hy) (hAgap a hx)).le
    · obtain ⟨a, hx⟩ := mem_iUnion.1 hx
      obtain ⟨b, hy⟩ := mem_iUnion.1 hy
      rcases gaps_comparable (cutBefore a) (cutBefore b) with hEq | hIJ | hJI
      · have hab := cutBefore_injective hEq
        exact (A a).1.isChain hx (hab.symm ▸ hy) hxy
      · exact Or.inl (hIJ (hAgap a hx) (hAgap b hy)).le
      · exact Or.inr (hJI (hAgap b hy) (hAgap a hx)).le
  obtain ⟨C, hC, hUC⟩ := hchain.exists_maxChain
  refine ⟨⟨C, hC⟩, ?_, ?_⟩
  · intro a ha
    let a' : D.carrier := ⟨a, ha⟩
    exact Or.inl ⟨A a', fun p hp => hUC (Or.inr (mem_iUnion.2 ⟨a', hp⟩)),
      congrArg H.increasing (hAg a').symm⟩
  · intro I b hb
    have hR : neg b ∈ boundaries (α := α) (R I) := boundary_dual_mem (α := αᵒᵈ) (hRg I b hb)
    exact ⟨boundaries_mono (fun p hp => hUC (Or.inl (mem_iUnion.2 ⟨I, hp⟩))) hR,
      cutAt_eq_of_negative_ray_in_gap I (hRgap I) hR⟩

private def witnessedPositive {C : Set α} (a : PositiveAtom α)
    (ha : pos a ∈ boundaries C) : AtomProfile C := ⟨pos a, ha, a.2⟩

private def witnessedNegative {C : Set α} (b : PositiveAtom αᵒᵈ)
    (hb : neg b ∈ boundaries C) : AtomProfile C := ⟨neg b, hb, b.2⟩

private theorem fix_positive_sweep {Q C F : Set α} (D : PositiveSweep Q)
    (hwf : WellFounded (LT.lt : PositiveAtom α → PositiveAtom α → Prop))
    (f : AtomicWitness C F) (hD : ∀ a ∈ D.carrier, pos a ∈ boundaries C)
    (hCandidate : ∀ a (ha : a ∈ D.carrier) b,
      (f.embedding (witnessedPositive a (hD a ha))).1 = pos b →
      (∀ x ∈ D.carrier ∩ Iio a, pos x ∈ boundaries F ∧ x < b) →
      PositiveCandidate Q (D.carrier ∩ Iio a) b) :
    ∀ a (ha : a ∈ D.carrier), (f.embedding (witnessedPositive a (hD a ha))).1 = pos a := by
  intro a
  apply hwf.induction a
  intro a ih ha
  let X := witnessedPositive a (hD a ha)
  let Y := f.embedding X
  have hd : Y.1.direction = some .increasing := f.direction X
  rcases (H.direction_eq_increasing_iff _).1 hd with ⟨g, hg⟩ | ht
  · have hgAtom : IsAtomicGerm (H.increasing g) := hg ▸ Y.2.2
    let b : PositiveAtom α := ⟨g, hgAtom⟩
    change Y.1 = pos a
    by_contra hne
    have hb : Y.1 = pos b := hg
    have hEarlier (x : PositiveAtom α) (hx : x ∈ D.carrier ∩ Iio a) :
        pos x ∈ boundaries F ∧ x < b := by
      let Z := witnessedPositive x (hD x hx.1)
      have hZ : (f.embedding Z).1 = pos x := ih x hx.2 hx.1
      have hlt : (f.embedding Z).1 < Y.1 := f.embedding.strictMono hx.2
      refine ⟨hZ ▸ (f.embedding Z).2.1, ?_⟩
      change pos x < pos b
      rwa [hZ, hb] at hlt
    apply D.minimal a ha b (hCandidate a ha b hb hEarlier)
    apply lt_iff_le_not_ge.2
    have hp : b.1.lowerProfile ⊆ a.1.lowerProfile := by
      have hp := f.profile X
      change boundaryProfile Y.1 ⊆ a.1.lowerProfile at hp
      rwa [hb] at hp
    refine ⟨hp, fun hrev => hne ?_⟩
    have heq := positiveAtom_eq_of_lowerProfile_eq b.2 a.2 (Set.Subset.antisymm hp hrev)
    exact hb.trans (congrArg H.increasing heq)
  · exact (top_not_mem_boundaries F (ht ▸ Y.2.1)).elim

private theorem image_preserves_cut {D : PositiveSweep (univ : Set α)} {C F : Set α}
    (f : AtomicWitness C F) (hD : ∀ a ∈ D.carrier, pos a ∈ boundaries C)
    (hfix : ∀ a (ha : a ∈ D.carrier), (f.embedding (witnessedPositive a (hD a ha))).1 = pos a)
    (X : AtomProfile C) : cutAt (D := D) (f.embedding X).1 = cutAt X.1 := by
  apply Subtype.ext
  ext a
  change (a ∈ D.carrier ∧ pos a < (f.embedding X).1) ↔ (a ∈ D.carrier ∧ pos a < X.1)
  constructor
  · intro ha
    refine ⟨ha.1, ?_⟩
    let Z := witnessedPositive a (hD a ha.1)
    have hZ : (f.embedding Z).1 = pos a := hfix a ha.1
    have hlt : (f.embedding Z).1 < (f.embedding X).1 := by simpa only [hZ] using ha.2
    exact f.embedding.lt_iff_lt.1 hlt
  · intro ha
    refine ⟨ha.1, ?_⟩
    let Z := witnessedPositive a (hD a ha.1)
    have hlt : (f.embedding Z).1 < (f.embedding X).1 := f.embedding.strictMono ha.2
    have hZ : (f.embedding Z).1 = pos a := hfix a ha.1
    rwa [hZ] at hlt

private theorem no_extra_atom {D : PositiveSweep (univ : Set α)}
    (E : ∀ I : PositiveCuts D, PositiveSweep (α := αᵒᵈ) (gap (α := α) I))
    (hDEx : ∀ a, ¬ PositiveCandidate univ D.carrier a)
    (hEEx : ∀ I a, ¬ PositiveCandidate (α := αᵒᵈ) (gap (α := α) I) (E I).carrier a)
    (hq : IsQuasifounded α) {C : Set α} (hC : IsSaturatedChain C)
    (hD : ∀ a ∈ D.carrier, pos a ∈ boundaries C)
    (hE : ∀ (I : PositiveCuts D) b, b ∈ (E I).carrier → neg b ∈ boundaries C)
    {X : H α} (hX : X ∈ atomicBoundaries C) :
    (∃ a ∈ D.carrier, X = pos a) ∨
      (∃ (I : PositiveCuts D) (b : PositiveAtom αᵒᵈ), b ∈ (E I).carrier ∧ X = neg b) := by
  cases X with
  | increasing g =>
    let a : PositiveAtom α := ⟨g, hX.2⟩
    have ha : pos a ∈ boundaries C := hX.1
    have hcomp (b : PositiveAtom α) (hb : b ∈ D.carrier) : b ≤ a ∨ a ≤ b :=
      positive_comparable hC (hD b hb) ha
    have hCand : PositiveCandidate univ (D.carrier ∩ Iio a) a :=
      candidate_of_chain hC ha (fun x hx => ⟨hD x hx.1, hx.2⟩) (fun _ _ _ _ => trivial)
    exact Or.inl ⟨a, D.mem_of_can_insert hDEx (positive_domination_wellFounded hq) a hcomp hCand, rfl⟩
  | decreasing g =>
    let b : PositiveAtom αᵒᵈ := ⟨g.toDual, hX.2⟩
    let I := cutAt (D := D) (neg b)
    have hb : neg b ∈ boundaries C := hX.1
    have hcomp (c : PositiveAtom αᵒᵈ) (hc : c ∈ (E I).carrier) : c ≤ b ∨ b ≤ c :=
      positive_comparable (α := αᵒᵈ) hC.dual (boundary_dual_mem (α := α) (hE I c hc))
        (boundary_dual_mem (α := α) hb)
    have hCand : PositiveCandidate (α := αᵒᵈ) (gap (α := α) I) ((E I).carrier ∩ Iio b) b :=
      negative_candidate_in_cut hC hD I hb rfl (fun x hx => ⟨hE I x hx.1, hx.2⟩)
    exact Or.inr ⟨I, b, (E I).mem_of_can_insert (hEEx I)
      (positive_domination_wellFounded hq.orderDual) b hcomp hCand, rfl⟩
  | principal _ | bottom | top => exact hX.2.elim

/-- Paper `prop:consolidated-exists`, by the positive sweep and the dual sweep
in every gap of the positive sweep. -/
theorem exists_atomicallyConsolidated (hfac : IsFAC α) (hq : IsQuasifounded α) :
    ∃ C : MaximalChains α, IsAtomicallyConsolidated C.carrier := by
  classical
  obtain ⟨D, hDEx⟩ := PositiveSweep.exists_exhausted (univ : Set α)
    (positive_consolidation_wellFounded hfac hq)
  have hex (I : PositiveCuts D) := PositiveSweep.exists_exhausted (α := αᵒᵈ) (gap (α := α) I)
    (positive_consolidation_wellFounded hfac.orderDual hq.orderDual)
  choose E hEEx using hex
  obtain ⟨C, hCD, hCE⟩ := exists_chain_realizing_sweeps hq D E
  refine ⟨C, fun F hF ⟨f⟩ => ?_⟩
  have hfixPos := fix_positive_sweep D (positive_domination_wellFounded hq) f hCD
    (fun a ha b hb hPrev => by
      have hy : pos b ∈ boundaries F := hb ▸ (f.embedding (witnessedPositive a (hCD a ha))).2.1
      exact candidate_of_chain hF hy hPrev (fun _ _ _ _ => trivial))
  have hFD (a : PositiveAtom α) (ha : a ∈ D.carrier) : pos a ∈ boundaries F :=
    (hfixPos a ha) ▸ (f.embedding (witnessedPositive a (hCD a ha))).2.1
  have hfixNeg (I : PositiveCuts D) (b : PositiveAtom αᵒᵈ) (hb : b ∈ (E I).carrier) :
      (f.embedding (witnessedNegative b (hCE I b hb).1)).1 = neg b := by
    let hCD' (x : PositiveAtom αᵒᵈ) (hx : x ∈ (E I).carrier) : pos x ∈ boundaries (α := αᵒᵈ) C.carrier :=
      boundary_dual_mem (α := α) (hCE I x hx).1
    have hfix := fix_positive_sweep (E I) (positive_domination_wellFounded hq.orderDual)
      f.dual hCD' (fun a ha c hc hPrev => by
        let X := witnessedNegative a (hCE I a ha).1
        let Y := f.embedding X
        have hyd : (f.dual.embedding (witnessedPositive a (hCD' a ha))).1 = Y.1.dual := f.dual_apply X
        have hY : Y.1 = neg c := H.dual_injective (hyd.symm.trans hc)
        have hcut : I = cutAt (neg c) := by
          have hsame := image_preserves_cut f hCD hfixPos X
          change cutAt Y.1 = cutAt (neg a) at hsame
          rw [hY, (hCE I a ha).2] at hsame
          exact hsame.symm
        exact negative_candidate_in_cut hF hFD I (hY ▸ Y.2.1) hcut
          (fun x hx => ⟨boundary_dual_mem (α := αᵒᵈ) (hPrev x hx).1, (hPrev x hx).2⟩)) b hb
    exact H.dual_injective ((f.dual_apply (witnessedNegative b (hCE I b hb).1)).symm.trans hfix)
  have hFE (I : PositiveCuts D) (b : PositiveAtom αᵒᵈ) (hb : b ∈ (E I).carrier) :
      neg b ∈ boundaries F :=
    (hfixNeg I b hb) ▸ (f.embedding (witnessedNegative b (hCE I b hb).1)).2.1
  apply Set.Subset.antisymm
  · intro X hX
    rcases no_extra_atom E hDEx hEEx hq hF hFD hFE hX with ⟨a, ha, rfl⟩ | ⟨I, b, hb, rfl⟩
    · exact ⟨hCD a ha, a.2⟩
    · exact ⟨(hCE I b hb).1, b.2⟩
  · intro X hX
    rcases no_extra_atom E hDEx hEEx hq C.isSaturated hCD (fun I b hb => (hCE I b hb).1) hX with
      ⟨a, ha, rfl⟩ | ⟨I, b, hb, rfl⟩
    · exact ⟨hFD a ha, a.2⟩
    · exact ⟨hFE I b hb, b.2⟩

/-- The consolidated-chain theorem with atomicity defined by excluding `ω + 1` and its dual. -/
theorem exists_paperAtomicallyConsolidated (hfac : IsFAC α) (hq : IsQuasifounded α) :
    ∃ C : MaximalChains α, IsPaperAtomicallyConsolidated C.carrier := by
  obtain ⟨C, hC⟩ := exists_atomicallyConsolidated hfac hq
  exact ⟨C, (isPaperAtomicallyConsolidated_iff hq.isVacillating C.carrier).2 hC⟩

end

end AharoniKorman.Consolidation
