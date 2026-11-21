import AharoniKorman.Completion.Completeness
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order
import Mathlib.Order.Bounds.Basic

/-! The two lexicographic examples introducing chain equivalence. -/

namespace AharoniKorman.Completion

open Set

namespace H

variable {α : Type*} [PartialOrder α]

/-- An increasing representative's limit is a minimal upper bound of its principal points. -/
theorem increasing_ofChain_minimal_upperBound (C : IncreasingChain α) :
    increasing (IncreasingGerm.ofChain C) ∈ upperBounds (principal '' (C.1 : Set α)) ∧
      ∀ Y ∈ upperBounds (principal '' (C.1 : Set α)),
        ¬Y < increasing (IncreasingGerm.ofChain C) := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact ((principal_lt_increasing_ofChain x C).mpr (C.2.exists_gt ⟨x,hx⟩)).le
  · intro Y hY hYC
    suffices ∃ c : C.1, Y < principal c.1 by
      obtain ⟨c, hlt⟩ := this
      exact hlt.not_ge (hY ⟨c.1, c.2, rfl⟩)
    induction Y using inductionOnRepresentatives with
    | hp x =>
        obtain ⟨c, hc⟩ := (principal_lt_increasing_ofChain x C).mp hYC
        exact ⟨c, (principal_lt_principal x c.1).mpr hc⟩
    | hi D =>
        obtain ⟨c, hc⟩ := (increasing_ofChain_lt_increasing_ofChain D C).mp hYC
        exact ⟨c, (increasing_ofChain_lt_principal D c.1).mpr hc⟩
    | hd D =>
        obtain ⟨d, c, hc⟩ := (decreasing_ofChain_lt_increasing_ofChain D C).mp hYC
        exact ⟨c, (decreasing_ofChain_lt_principal D c.1).mpr ⟨d, hc⟩⟩
    | hb =>
        obtain ⟨c, hc⟩ := C.1.nonempty
        exact ⟨⟨c,hc⟩, bot_lt_iff_ne_bot.mpr (principal_ne_bot c)⟩
    | ht => exact (not_lt_of_ge le_top hYC).elim

end H

namespace GermExamples

variable {β : Type*} [PartialOrder β]

private theorem lex_lt_of_index_lt {x y : ℕ ×ₗ β} (h : (ofLex x).1 < (ofLex y).1) : x < y := by
  rw [← toLex_ofLex x, ← toLex_ofLex y, Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

private theorem lex_index_eq_of_incomparable {x y : ℕ ×ₗ β} (h : Incomparable x y) :
    (ofLex x).1 = (ofLex y).1 := by
  rcases lt_trichotomy (ofLex x).1 (ofLex y).1 with hlt | he | hgt
  · exact (h.not_le (lex_lt_of_index_lt hlt).le).elim
  · exact he
  · exact (h.not_ge (lex_lt_of_index_lt hgt).le).elim

private def lexChain (rows : ℕ → Set β) (hne : ∀ i, (rows i).Nonempty)
    (hchain : ∀ i, IsChain (· ≤ ·) (rows i))
    (hmax : ∀ i b, (∀ a ∈ rows i, b ≤ a ∨ a ≤ b) → b ∈ rows i) :
    IncreasingChain (ℕ ×ₗ β) := by
  let S : Set (ℕ ×ₗ β) := {x | (ofLex x).2 ∈ rows (ofLex x).1}
  have hS : IsSaturatedChain S := by
    constructor
    · intro x hx y hy _
      rcases lt_trichotomy (ofLex x).1 (ofLex y).1 with hlt | heq | hgt
      · exact Or.inl (lex_lt_of_index_lt hlt).le
      · change (ofLex x).2 ∈ rows (ofLex x).1 at hx
        change (ofLex y).2 ∈ rows (ofLex y).1 at hy
        rw [← heq] at hy
        have hcomp := (hchain _).total hx hy
        change x ≤ y ∨ y ≤ x
        rw [← toLex_ofLex x, ← toLex_ofLex y, Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_le_toLex]
        exact hcomp.elim (fun h => Or.inl (Or.inr ⟨heq, h⟩))
          (fun h => Or.inr (Or.inr ⟨heq.symm, h⟩))
      · exact Or.inr (lex_lt_of_index_lt hgt).le
    · intro _ _ x _ _ _ _ hx
      apply hmax
      intro a ha
      have hcomp := hx (toLex ((ofLex x).1, a)) ha
      rw [← toLex_ofLex x, Prod.Lex.toLex_le_toLex', Prod.Lex.toLex_le_toLex'] at hcomp
      exact hcomp.elim (fun h => Or.inl (h.2 rfl)) (fun h => Or.inr (h.2 rfl))
  have hSne : S.Nonempty := by
    obtain ⟨a, ha⟩ := hne 0
    exact ⟨toLex (0, a), ha⟩
  let C : SaturatedChain (ℕ ×ₗ β) := ⟨S, hSne, hS⟩
  refine ⟨C, ?_⟩
  rintro ⟨m, hM⟩
  obtain ⟨a, ha⟩ := hne ((ofLex m.1).1+1)
  let y : C := ⟨toLex ((ofLex m.1).1+1, a), ha⟩
  have hlt : m.1 < y.1 := lex_lt_of_index_lt (Nat.lt_succ_self _)
  exact hlt.not_ge (hM y)

/-- The two-point antichain, realized as the disjoint sum of two singleton orders. -/
abbrev Two := Unit ⊕ Unit

private theorem two_le_iff {a b : Two} : a ≤ b ↔ a = b := by
  cases a <;> cases b <;> simp

/-- The chains selecting one point in each level of the first example. -/
def selectorChain (s : ℕ → Two) : IncreasingChain (ℕ ×ₗ Two) :=
  lexChain (fun n => {s n}) (fun _ => Set.singleton_nonempty _)
    (fun _ => IsChain.singleton) (fun n b h => by
      rcases h (s n) (mem_singleton _) with hle | hge
      · exact mem_singleton_iff.mpr (two_le_iff.mp hle)
      · exact mem_singleton_iff.mpr (two_le_iff.mp hge).symm)

private theorem selector_coords {s : ℕ → Two} (x : (selectorChain s).1) :
    ofLex x.1 = ((ofLex x.1).1, s (ofLex x.1).1) := by
  apply Prod.ext
  · rfl
  · have h : (ofLex x.1).2 ∈ ({s (ofLex x.1).1} : Set Two) := x.2
    exact mem_singleton_iff.mp h

private theorem selector_trace_finite (s : ℕ → Two) (p : ℕ ×ₗ Two) :
    (incomparabilityTrace (selectorChain s).1 p).Finite := by
  apply Set.Subsingleton.finite
  intro x hx y hy
  apply Subtype.ext
  apply ofLex.injective
  have hxy := (lex_index_eq_of_incomparable hx).trans (lex_index_eq_of_incomparable hy).symm
  exact (selector_coords x).trans ((congrArg (fun n => (n, s n)) hxy).trans (selector_coords y).symm)

private theorem selector_contact (s : ℕ → Two) (p : ℕ ×ₗ Two) :
    ∃ q : (selectorChain s).1, p = q.1 ∨ Incomparable p q.1 := by
  let i := (ofLex p).1
  let q : (selectorChain s).1 := ⟨toLex (i, s i), mem_singleton _⟩
  refine ⟨q, ?_⟩
  by_cases he : p = q.1
  · exact Or.inl he
  · right
    have collapse (h : p ≤ q.1 ∨ q.1 ≤ p) : p = q.1 := by
      apply ofLex.injective
      have hf : (ofLex p).1 = (ofLex q.1).1 := rfl
      apply Prod.ext hf
      rw [← toLex_ofLex p, ← toLex_ofLex q.1, Prod.Lex.toLex_le_toLex', Prod.Lex.toLex_le_toLex'] at h
      exact h.elim (fun h => two_le_iff.mp (h.2 hf)) (fun h => (two_le_iff.mp (h.2 hf.symm)).symm)
    exact ⟨fun h => he (collapse (Or.inl h)), fun h => he (collapse (Or.inr h))⟩

/-- Paper `ex:n-cross-2`: all selections induce the same increasing germ. -/
theorem selector_germs_eq (s t : ℕ → Two) :
    IncreasingGerm.ofChain (selectorChain s) = IncreasingGerm.ofChain (selectorChain t) := by
  apply IncreasingGerm.ofChain_eq_iff.mpr
  refine ⟨_, _, ⟨Subset.rfl, fun _ _ _ hy _ => hy⟩,
    ⟨Subset.rfl, fun _ _ _ hy _ => hy⟩, ?_⟩
  apply MutuallyFiniteIncomparability.of_finite_crossRelated
  · intro y
    exact selector_trace_finite s y.1
  · intro x
    exact selector_trace_finite t x.1
  · intro y
    obtain ⟨x, hx | hx⟩ := selector_contact s y.1
    · exact ⟨x, Or.inl hx.symm⟩
    · exact ⟨x, Or.inr hx.symm⟩
  · intro x
    exact selector_contact t x.1

abbrev NatStar := ℕ ⊕ Unit

private def star : NatStar := Sum.inr ()

/-- The chain `C₀` in `ex:n-cross-n-star`. -/
def naturalRows : IncreasingChain (ℕ ×ₗ NatStar) :=
  lexChain (fun _ => range Sum.inl) (fun _ => range_nonempty Sum.inl)
    (fun _ => Sum.inl_mono.isChain_range) (fun _ b h => by
      cases b with
      | inl n => exact ⟨n, rfl⟩
      | inr s =>
          rcases h (Sum.inl 0) ⟨0, rfl⟩ with hle | hge
          · exact (Sum.not_inr_le_inl hle).elim
          · exact (Sum.not_inl_le_inr hge).elim)

/-- The chain `C₁` in `ex:n-cross-n-star`. -/
def starRows : IncreasingChain (ℕ ×ₗ NatStar) :=
  lexChain (fun _ => {star}) (fun _ => singleton_nonempty _) (fun _ => IsChain.singleton)
    (fun _ b h => by
      cases b with
      | inl n =>
          rcases h star (mem_singleton _) with hle | hge
          · exact (Sum.not_inl_le_inr hle).elim
          · exact (Sum.not_inr_le_inl hge).elim
      | inr s => cases s; exact mem_singleton _)

private theorem natural_star_incomparable (i j : ℕ) :
    Incomparable (toLex (i, (Sum.inl j : NatStar))) (toLex (i, star)) := by
  exact ⟨fun h => Sum.not_inl_le_inr ((Prod.Lex.toLex_le_toLex'.mp h).2 rfl),
    fun h => Sum.not_inr_le_inl ((Prod.Lex.toLex_le_toLex'.mp h).2 rfl)⟩

theorem natural_star_germs_ne :
    IncreasingGerm.ofChain naturalRows ≠ IncreasingGerm.ofChain starRows := by
  intro h
  obtain ⟨C, D, hC, hD, hCD⟩ := IncreasingGerm.ofChain_eq_iff.mp h
  obtain ⟨c, hc⟩ := C.nonempty
  obtain ⟨d, hd⟩ := D.nonempty
  let n := max (ofLex c).1 (ofLex d).1 + 1
  have hc' : (ofLex c).1 < n := Nat.lt_succ_of_le (le_max_left _ _)
  have hd' : (ofLex d).1 < n := Nat.lt_succ_of_le (le_max_right _ _)
  let y : D := ⟨toLex (n, star), hD.2 hd (mem_singleton _) (lex_lt_of_index_lt hd').le⟩
  let x (j : ℕ) : C := ⟨toLex (n, (Sum.inl j : NatStar)),
    hC.2 hc ⟨j, rfl⟩ (lex_lt_of_index_lt hc').le⟩
  let f (j : ℕ) : incomparabilityTrace C y.1 := ⟨x j, natural_star_incomparable n j⟩
  let := (hCD.left_finite y).to_subtype
  let : Finite ℕ := Finite.of_injective f (fun _ _ h => by
    have h' := congrArg (fun k => (ofLex k.1.1).2) h
    exact Sum.inl.inj h')
  exact not_finite ℕ

theorem natural_rows_cofinal (x : ℕ ×ₗ NatStar) : ∃ a : naturalRows.1, x < a.1 :=
  ⟨⟨toLex ((ofLex x).1+1, (Sum.inl 0 : NatStar)), ⟨0, rfl⟩⟩,
    lex_lt_of_index_lt (Nat.lt_succ_self _)⟩

theorem star_rows_cofinal (x : ℕ ×ₗ NatStar) : ∃ a : starRows.1, x < a.1 :=
  ⟨⟨toLex ((ofLex x).1+1, star), mem_singleton _⟩, lex_lt_of_index_lt (Nat.lt_succ_self _)⟩

private theorem cofinal_chain_upperBounds {α : Type*} [PartialOrder α] (C : IncreasingChain α)
    (hcofinal : ∀ x, ∃ c : C.1, x < c.1) :
    upperBounds (H.principal '' (C.1 : Set α)) = upperBounds (range H.principal) := by
  ext X
  constructor
  · rintro hX _ ⟨x, rfl⟩
    obtain ⟨c, hxc⟩ := hcofinal x
    exact ((H.principal_lt_principal x c.1).mpr hxc).le.trans (hX ⟨c.1, c.2, rfl⟩)
  · intro hX _ hx
    obtain ⟨x, _, rfl⟩ := hx
    exact hX ⟨x, rfl⟩

/-- Paper `ex:n-cross-n-star`: two cofinal chains have distinct germs, each a
minimal upper bound of the two chains. -/
theorem natural_star_distinct_minimal_upperBounds :
    ∃ X Y : H (ℕ ×ₗ NatStar), X ≠ Y ∧
      X ∈ upperBounds (range H.principal) ∧ Y ∈ upperBounds (range H.principal) ∧
      ∀ Z ∈ upperBounds (range H.principal), ¬Z < X ∧ ¬Z < Y := by
  have hn := H.increasing_ofChain_minimal_upperBound naturalRows
  have hs := H.increasing_ofChain_minimal_upperBound starRows
  rw [cofinal_chain_upperBounds _ natural_rows_cofinal] at hn
  rw [cofinal_chain_upperBounds _ star_rows_cofinal] at hs
  exact ⟨_, _, fun h => natural_star_germs_ne (H.increasing.inj h), hn.1, hs.1,
    fun Z hZ => ⟨hn.2 Z hZ, hs.2 Z hZ⟩⟩

/-- The cofinal chain `C₀` has no least upper bound in this chain extension. -/
theorem natural_rows_no_lub :
    ¬ ∃ X : H (ℕ ×ₗ NatStar), IsLUB (H.principal '' (naturalRows.1 : Set _)) X := by
  rintro ⟨U, hU⟩
  change IsLeast (upperBounds (H.principal '' (naturalRows.1 : Set _))) U at hU
  rw [cofinal_chain_upperBounds _ natural_rows_cofinal] at hU
  obtain ⟨X, Y, hne, hX, hY, hmin⟩ := natural_star_distinct_minimal_upperBounds
  have hx : U = X := (lt_or_eq_of_le (hU.2 hX)).resolve_left (hmin U hU.1).1
  have hy : U = Y := (lt_or_eq_of_le (hU.2 hY)).resolve_left (hmin U hU.1).2
  exact hne (hx.symm.trans hy)

/-- Completing the natural order twice introduces a new increasing point for
the original natural chain. -/
theorem natural_chain_second_extension :
    ∃ g : IncreasingGerm (H ℕ),
      IsLUB (range (fun n : ℕ => H.principal (H.principal n))) (H.increasing g) ∧
      ∀ X : H ℕ, H.increasing g ≠ H.principal X := by
  let f (n : ℕ) : H (H ℕ) := H.principal (H.principal n)
  have hf : StrictMono f := H.principalEmbedding.strictMono.comp H.principalEmbedding.strictMono
  have hnot : sSup (range f) ∉ range f := by
    rintro ⟨n, hn⟩
    have hle : f (n+1) ≤ sSup (range f) := le_sSup (mem_range_self (n+1))
    exact (hf (Nat.lt_succ_self n)).not_ge (hn.symm ▸ hle)
  obtain ⟨g, hg⟩ := H.sSup_eq_increasing_of_not_mem (range_nonempty f) hnot
  exact ⟨g, hg ▸ isLUB_sSup _, fun X h => H.principal_ne_increasing X g h.symm⟩

end GermExamples

end AharoniKorman.Completion
