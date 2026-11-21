import AharoniKorman.Completion.VacillationSuborder
import AharoniKorman.Preliminaries.InitialOmega

namespace AharoniKorman

open Set Completion Completion.H

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

/-- Paper `def:quasifdd`: the two signed parts of the completion are
well-founded in their respective directions. -/
def IsQuasifounded (α : Type*) [PartialOrder α] : Prop :=
  WellFounded (LT.lt : NPlus α → NPlus α → Prop) ∧
    WellFounded (GT.gt : NMinus α → NMinus α → Prop)

theorem IsQuasifounded.orderDual (h : IsQuasifounded α) : IsQuasifounded αᵒᵈ := by
  constructor
  · let f : NPlus αᵒᵈ → NMinus α := fun X =>
      ⟨X.1.dual, (H.direction_dual (α := αᵒᵈ) X.1).trans
        (congrArg (Option.map OrderDirection.dual) X.2)⟩
    exact (InvImage.wf f h.2).mono fun X Y hXY => (H.dual_lt_dual Y.1 X.1).2 hXY
  · let f : NMinus αᵒᵈ → NPlus α := fun X =>
      ⟨X.1.dual, (H.direction_dual (α := αᵒᵈ) X.1).trans
        (congrArg (Option.map OrderDirection.dual) X.2)⟩
    exact (InvImage.wf f h.1).mono fun X Y hXY => (H.dual_lt_dual X.1 Y.1).2 hXY

theorem IsQuasifounded.of_saturationPreserving (h : IsQuasifounded β)
    (e : α ↪o β) (he : SaturationPreserving e) : IsQuasifounded α := by
  constructor
  · let f : NPlus α → NPlus β := fun X => ⟨H.map e he X.1, (H.direction_map e he X.1).trans X.2⟩
    exact (InvImage.wf f h.1).mono fun _ _ hXY => (H.mapEmbedding e he).strictMono hXY
  · let f : NMinus α → NMinus β := fun X => ⟨H.map e he X.1, (H.direction_map e he X.1).trans X.2⟩
    exact (InvImage.wf f h.2).mono fun _ _ hXY => (H.mapEmbedding e he).strictMono hXY

theorem IsQuasifounded.ordConnected_subtype (h : IsQuasifounded α) {S : Set α}
    (hS : OrdConnected S) : IsQuasifounded S :=
  h.of_saturationPreserving (OrderEmbedding.subtype S)
    (saturationPreserving_subtype_of_ordConnected hS)

theorem exists_increasingGerm_descent (h : ¬WellFounded (LT.lt : NPlus α → NPlus α → Prop)) :
    ∃ f : ℕ → IncreasingGerm α, StrictAnti (fun n => H.increasing (f n)) := by
  classical
  rw [wellFounded_iff_isEmpty_descending_chain, not_isEmpty_iff] at h
  obtain ⟨f, hf⟩ := h
  have hex (n : ℕ) : ∃ g, (f (n + 1)).1 = H.increasing g := by
    refine ((H.direction_eq_increasing_iff _).1 (f (n + 1)).2).resolve_right ?_
    intro heq
    have hlt : (f (n + 1)).1 < (f n).1 := hf n
    exact (not_lt_of_ge le_top) (heq ▸ hlt)
  choose g hg using hex
  refine ⟨g, strictAnti_nat_of_succ_lt ?_⟩
  intro n
  have hlt : (f (n + 2)).1 < (f (n + 1)).1 := hf (n + 1)
  simpa only [hg] using hlt

theorem exists_decreasingGerm_ascent (h : ¬WellFounded (GT.gt : NMinus α → NMinus α → Prop)) :
    ∃ f : ℕ → DecreasingGerm α, StrictMono (fun n => H.decreasing (f n)) := by
  classical
  rw [wellFounded_iff_isEmpty_descending_chain, not_isEmpty_iff] at h
  obtain ⟨f, hf⟩ := h
  have hex (n : ℕ) : ∃ g, (f (n + 1)).1 = H.decreasing g := by
    refine ((H.direction_eq_decreasing_iff _).1 (f (n + 1)).2).resolve_right ?_
    intro heq
    have hlt : (f n).1 < (f (n + 1)).1 := hf n
    exact not_lt_bot (heq ▸ hlt)
  choose g hg using hex
  refine ⟨g, strictMono_nat_of_lt_succ ?_⟩
  intro n
  have hlt : (f (n + 1)).1 < (f (n + 2)).1 := hf (n + 1)
  simpa only [hg] using hlt

private theorem no_ordered_cowellFounded_blocks
    (h : WellFounded (GT.gt : NMinus α → NMinus α → Prop))
    (B : ℕ → Set α) (hBsat : ∀ n, IsSaturatedChain (B n))
    (hinf : ∀ n, (B n).Infinite) (hwf : ∀ n, WellFounded (fun x y : B n => x > y))
    (hB : ∀ ⦃i j : ℕ⦄, i < j → SetStrictLT (B i) (B j)) : False := by
  classical
  have hrep (n : ℕ) : ∃ D : DecreasingChain α, (D.1 : Set α) ⊆ B n := by
    let : LinearOrder (B n) := (hBsat n).1.linearOrder
    let : Infinite (B n)ᵒᵈ := (hinf n).to_subtype
    obtain ⟨e, he⟩ := exists_initial_natEmbedding (β := (B n)ᵒᵈ) (hwf n)
    let D : Set α := range (fun i : ℕ => (e i).1)
    have hDB : D ⊆ B n := by rintro _ ⟨i, rfl⟩; exact (e i).2
    have hDs : IsSaturatedChain D := by
      apply (hBsat n).restrict hDB
      rintro a b x ⟨i, rfl⟩ _ hx hax _
      obtain ⟨j, hj⟩ := he (show (B n)ᵒᵈ from ⟨x, hx⟩) i hax
      exact ⟨j, congrArg Subtype.val hj⟩
    let A : SaturatedChain α := ⟨D, ⟨(e 0).1, 0, rfl⟩, hDs⟩
    have hAn : A.NoBottom := by
      rintro ⟨⟨a, i, rfl⟩, ha⟩
      have hi : (e (i + 1)).1 < (e i).1 := e.strictMono (Nat.lt_succ_self i)
      exact hi.not_ge (ha ⟨(e (i + 1)).1, i + 1, rfl⟩)
    exact ⟨⟨A, hAn⟩, hDB⟩
  choose D hD using hrep
  let f : ℕ → NMinus α := fun n => ⟨H.decreasing (DecreasingGerm.ofChain (D n)), rfl⟩
  apply (wellFounded_iff_isEmpty_descending_chain.1 h).false
  refine ⟨f, fun n => ?_⟩
  change H.decreasing (DecreasingGerm.ofChain (D n)) <
    H.decreasing (DecreasingGerm.ofChain (D (n + 1)))
  obtain ⟨x, hx⟩ := (D n).1.nonempty
  exact (H.decreasing_ofChain_lt_decreasing_ofChain _ _).2
    ⟨⟨x, hx⟩, fun d => hB (Nat.lt_succ_self n) (hD n hx) (hD (n + 1) d.2)⟩

private theorem no_omegaSum_of_wellFounded_NMinus
    (h : WellFounded (GT.gt : NMinus α → NMinus α → Prop))
    {C : Set α} (hC : IsSaturatedChain C) : ¬IsOmegaSumOfInfiniteCowellfounded C := by
  rintro ⟨B, hCB, hinf, hwf, hB⟩
  have hsub (n : ℕ) : B n ⊆ C := by
    intro x hx
    rw [hCB]
    exact mem_iUnion.2 ⟨n, hx⟩
  apply no_ordered_cowellFounded_blocks h B ?_ hinf hwf hB
  intro n
  apply hC.restrict (hsub n)
  intro a b x ha hb hx hax hxb
  rw [hCB] at hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx
  rcases lt_trichotomy i n with hin | rfl | hni
  · exact ((hB hin hi ha).not_ge hax).elim
  · exact hi
  · exact ((hB hni hb hi).not_ge hxb).elim

/-- Paper `lem:quasifounded-implies-vacillating`: every block of a forbidden
sum witnesses a decreasing completion point, ordered by the block indices. -/
theorem IsQuasifounded.isVacillating (h : IsQuasifounded α) : IsVacillating α := by
  intro C hC
  exact ⟨no_omegaSum_of_wellFounded_NMinus h.2 hC,
    no_omegaSum_of_wellFounded_NMinus h.orderDual.2 hC.dual⟩

end AharoniKorman
