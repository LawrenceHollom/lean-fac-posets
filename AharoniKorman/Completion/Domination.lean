import AharoniKorman.Completion.Representatives

/-! Representative-level strict domination (paper `def:domination`).
The four formulas below are the quantifier normal forms of separation of
nonempty final/initial segments. Invariance is proved before any germ lift. -/

namespace AharoniKorman.Completion

variable {α : Type*} [PartialOrder α]

theorem IncreasingEquivalent.exists_iff {C D : IncreasingChain α}
    (h : IncreasingEquivalent C D) {P : α → Prop}
    (hP : ∀ a b, a ≤ b → P a → P b) :
    (∃ c : C.1, P c.1) ↔ ∃ d : D.1, P d.1 := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨d, hcd⟩ := h.exists_right_gt c
    exact ⟨d, hP _ _ hcd.le hc⟩
  · rintro ⟨d, hd⟩
    obtain ⟨c, hdc⟩ := h.exists_left_gt d
    exact ⟨c, hP _ _ hdc.le hd⟩

theorem IncreasingEquivalent.forall_iff {C D : IncreasingChain α}
    (h : IncreasingEquivalent C D) {P : α → Prop}
    (hP : ∀ a b, a ≤ b → P b → P a) :
    (∀ c : C.1, P c.1) ↔ ∀ d : D.1, P d.1 := by
  constructor
  · intro hc d
    obtain ⟨c, hdc⟩ := h.exists_left_gt d
    exact hP _ _ hdc.le (hc c)
  · intro hd c
    obtain ⟨d, hcd⟩ := h.exists_right_gt c
    exact hP _ _ hcd.le (hd d)

theorem DecreasingEquivalent.exists_iff {C D : DecreasingChain α}
    (h : DecreasingEquivalent C D) {P : α → Prop}
    (hP : ∀ a b, a ≤ b → P b → P a) :
    (∃ c : C.1, P c.1) ↔ ∃ d : D.1, P d.1 :=
  IncreasingEquivalent.exists_iff (α := αᵒᵈ) h (fun a b hab => hP b a hab)

theorem DecreasingEquivalent.forall_iff {C D : DecreasingChain α}
    (h : DecreasingEquivalent C D) {P : α → Prop}
    (hP : ∀ a b, a ≤ b → P a → P b) :
    (∀ c : C.1, P c.1) ↔ ∀ d : D.1, P d.1 :=
  IncreasingEquivalent.forall_iff (α := αᵒᵈ) h (fun a b hab => hP b a hab)

namespace Domination

def principalIncreasing (x : α) (D : IncreasingChain α) : Prop := ∃ d : D.1, x < d.1
def increasingPrincipal (C : IncreasingChain α) (y : α) : Prop := ∀ c : C.1, c.1 < y
def principalDecreasing (x : α) (D : DecreasingChain α) : Prop := ∀ d : D.1, x < d.1
def decreasingPrincipal (C : DecreasingChain α) (y : α) : Prop := ∃ c : C.1, c.1 < y
def increasingIncreasing (C D : IncreasingChain α) : Prop :=
  ∃ d : D.1, ∀ c : C.1, c.1 < d.1
def increasingDecreasing (C : IncreasingChain α) (D : DecreasingChain α) : Prop :=
  ∀ c : C.1, ∀ d : D.1, c.1 < d.1
def decreasingIncreasing (C : DecreasingChain α) (D : IncreasingChain α) : Prop :=
  ∃ c : C.1, ∃ d : D.1, c.1 < d.1
def decreasingDecreasing (C D : DecreasingChain α) : Prop :=
  ∃ c : C.1, ∀ d : D.1, c.1 < d.1

theorem principalIncreasing_congr (x : α) {C D : IncreasingChain α}
    (h : IncreasingEquivalent C D) : principalIncreasing x C ↔ principalIncreasing x D :=
  h.exists_iff (fun _ _ hab hxa => hxa.trans_le hab)

theorem increasingPrincipal_congr (x : α) {C D : IncreasingChain α}
    (h : IncreasingEquivalent C D) : increasingPrincipal C x ↔ increasingPrincipal D x :=
  h.forall_iff (fun _ _ hab hbx => hab.trans_lt hbx)

theorem principalDecreasing_congr (x : α) {C D : DecreasingChain α}
    (h : DecreasingEquivalent C D) : principalDecreasing x C ↔ principalDecreasing x D :=
  h.forall_iff (fun _ _ hab hxa => hxa.trans_le hab)

theorem decreasingPrincipal_congr (x : α) {C D : DecreasingChain α}
    (h : DecreasingEquivalent C D) : decreasingPrincipal C x ↔ decreasingPrincipal D x :=
  h.exists_iff (fun _ _ hab hbx => hab.trans_lt hbx)

theorem increasingIncreasing_congr {C C' D D' : IncreasingChain α}
    (hC : IncreasingEquivalent C C') (hD : IncreasingEquivalent D D') :
    increasingIncreasing C D ↔ increasingIncreasing C' D' := by
  change (∃ d : D.1, increasingPrincipal C d.1) ↔ ∃ d : D'.1, increasingPrincipal C' d.1
  simp_rw [increasingPrincipal_congr _ hC]
  exact hD.exists_iff (fun _ _ hab h c => (h c).trans_le hab)

theorem increasingDecreasing_congr {C C' : IncreasingChain α} {D D' : DecreasingChain α}
    (hC : IncreasingEquivalent C C') (hD : DecreasingEquivalent D D') :
    increasingDecreasing C D ↔ increasingDecreasing C' D' := by
  change (∀ c : C.1, principalDecreasing c.1 D) ↔ ∀ c : C'.1, principalDecreasing c.1 D'
  simp_rw [principalDecreasing_congr _ hD]
  exact hC.forall_iff (P := fun x => principalDecreasing x D')
    (fun _ _ hab h d => hab.trans_lt (h d))

theorem decreasingIncreasing_congr {C C' : DecreasingChain α} {D D' : IncreasingChain α}
    (hC : DecreasingEquivalent C C') (hD : IncreasingEquivalent D D') :
    decreasingIncreasing C D ↔ decreasingIncreasing C' D' := by
  change (∃ c : C.1, principalIncreasing c.1 D) ↔ ∃ c : C'.1, principalIncreasing c.1 D'
  simp_rw [principalIncreasing_congr _ hD]
  exact hC.exists_iff (P := fun x => principalIncreasing x D')
    (fun _ _ hab ⟨d, hbd⟩ => ⟨d, hab.trans_lt hbd⟩)

theorem decreasingDecreasing_congr {C C' D D' : DecreasingChain α}
    (hC : DecreasingEquivalent C C') (hD : DecreasingEquivalent D D') :
    decreasingDecreasing C D ↔ decreasingDecreasing C' D' := by
  change (∃ c : C.1, principalDecreasing c.1 D) ↔ ∃ c : C'.1, principalDecreasing c.1 D'
  simp_rw [principalDecreasing_congr _ hD]
  exact hC.exists_iff (P := fun x => principalDecreasing x D')
    (fun _ _ hab h d => hab.trans_lt (h d))

/-- The manuscript's separation condition before taking equivalence classes. -/
def SegmentLT (d e : OrderDirection) (C D : SaturatedChain α) : Prop :=
  ∃ S T : Set α, IsDirectionalSegment d S C ∧ S.Nonempty ∧
    IsDirectionalSegment e T D ∧ T.Nonempty ∧ SetStrictLT S T

theorem segmentLT_dual (d e : OrderDirection) (C D : SaturatedChain α) :
    SegmentLT d e C D ↔ SegmentLT e.dual d.dual D.dual C.dual := by
  cases d <;> cases e <;>
    simp only [SegmentLT, IsDirectionalSegment, OrderDirection.dual,
      IsFinalSegment, IsInitialSegment, SetStrictLT]
  all_goals
    constructor <;> rintro ⟨S, T, hS, hnS, hT, hnT, hST⟩
    · exact ⟨T, S, hT, hnT, hS, hnS, fun _ ht _ hs => hST hs ht⟩
    · exact ⟨T, S, hT, hnT, hS, hnS, fun _ ht _ hs => hST hs ht⟩

theorem segmentLT_increasingIncreasing (C D : IncreasingChain α) :
    SegmentLT .increasing .increasing C.1 D.1 ↔ increasingIncreasing C D := by
  constructor
  · rintro ⟨S, T, hS, ⟨s, hs⟩, hT, ⟨t, ht⟩, hST⟩
    refine ⟨⟨t, hT.1 ht⟩, ?_⟩
    intro c
    rcases C.1.isChain.total c.2 (hS.1 hs) with hcs | hsc
    · exact hcs.trans_lt (hST hs ht)
    · exact hST (hS.2 hs c.2 hsc) ht
  · rintro ⟨d, hd⟩
    refine ⟨C.1, D.1.tail d, ⟨Set.Subset.rfl, fun _ _ _ hy _ => hy⟩,
      C.1.nonempty, D.1.tail_final d, (D.1.tail d).nonempty, ?_⟩
    intro c hc t ht
    exact (hd ⟨c, hc⟩).trans_le ht.2

theorem segmentLT_increasingDecreasing (C : IncreasingChain α) (D : DecreasingChain α) :
    SegmentLT .increasing .decreasing C.1 D.1 ↔ increasingDecreasing C D := by
  constructor
  · rintro ⟨S, T, hS, ⟨s, hs⟩, hT, ⟨t, ht⟩, hST⟩ c d
    have hct : ∀ t ∈ T, c.1 < t := by
      intro t ht
      rcases C.1.isChain.total c.2 (hS.1 hs) with hcs | hsc
      · exact hcs.trans_lt (hST hs ht)
      · exact hST (hS.2 hs c.2 hsc) ht
    rcases D.1.isChain.total (hT.1 ht) d.2 with htd | hdt
    · exact (hct t ht).trans_le htd
    · exact hct d.1 (hT.2 ht d.2 hdt)
  · intro h
    exact ⟨C.1, D.1, ⟨Set.Subset.rfl, fun _ _ _ hy _ => hy⟩, C.1.nonempty,
      ⟨Set.Subset.rfl, fun _ _ _ hy _ => hy⟩, D.1.nonempty,
      fun _ hc _ hd => h ⟨_, hc⟩ ⟨_, hd⟩⟩

theorem segmentLT_decreasingIncreasing (C : DecreasingChain α) (D : IncreasingChain α) :
    SegmentLT .decreasing .increasing C.1 D.1 ↔ decreasingIncreasing C D := by
  constructor
  · rintro ⟨S, T, hS, ⟨s, hs⟩, hT, ⟨t, ht⟩, hST⟩
    exact ⟨⟨s, hS.1 hs⟩, ⟨t, hT.1 ht⟩, hST hs ht⟩
  · rintro ⟨c, d, hcd⟩
    refine ⟨{x | x ∈ C.1 ∧ x ≤ c.1}, D.1.tail d,
      ⟨fun _ h => h.1, fun _ _ hx hy hyx => ⟨hy, hyx.trans hx.2⟩⟩,
      ⟨c.1, c.2, le_rfl⟩, D.1.tail_final d, (D.1.tail d).nonempty, ?_⟩
    intro s hs t ht
    exact (hs.2.trans_lt hcd).trans_le ht.2

theorem segmentLT_decreasingDecreasing (C D : DecreasingChain α) :
    SegmentLT .decreasing .decreasing C.1 D.1 ↔ decreasingDecreasing C D := by
  rw [segmentLT_dual]
  exact segmentLT_increasingIncreasing D.toDual C.toDual

end Domination

end AharoniKorman.Completion
