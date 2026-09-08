import AharoniKorman.Completion.Embedding

/-! The completion of a linear order is linear (paper `lem:h-chain-is-chain`). -/

namespace AharoniKorman.Completion

variable {α : Type*} [LinearOrder α]

private theorem finite_trace (C : SaturatedChain α) (x : α) :
    (incomparabilityTrace C x).Finite := by
  apply Set.finite_empty.subset
  intro c hc
  exact False.elim ((le_total c.1 x).elim hc.not_le hc.not_ge)

theorem IncreasingEquivalent.of_mutually_cofinal (C D : IncreasingChain α)
    (hCD : ∀ c : C.1, ∃ d : D.1, c.1 < d.1)
    (hDC : ∀ d : D.1, ∃ c : C.1, d.1 < c.1) : IncreasingEquivalent C D := by
  obtain ⟨S, T, hS, hT, hST⟩ := normalize_finite_cofinal hCD hDC
    (fun d => finite_trace C.1 d.1) (fun c => finite_trace D.1 c.1)
  exact ⟨S, T, hS, hT, hST⟩

private theorem increasing_strict_bound (C : IncreasingChain α) (x : α)
    (h : ¬∃ c : C.1, x < c.1) : ∀ c : C.1, c.1 < x := by
  intro c
  obtain ⟨d, hcd⟩ := C.2.exists_gt c
  have hdx : d.1 ≤ x := le_of_not_gt (fun hxd => h ⟨d, hxd⟩)
  exact (show c.1 < d.1 from hcd).trans_le hdx

namespace H

private theorem principal_increasing_total (x : α) (C : IncreasingChain α) :
    principal x ≤ increasing (IncreasingGerm.ofChain C) ∨
      increasing (IncreasingGerm.ofChain C) ≤ principal x := by
  by_cases h : ∃ c : C.1, x < c.1
  · exact Or.inl ((principal_lt_increasing_ofChain x C).2 h).le
  · exact Or.inr ((increasing_ofChain_lt_principal C x).2 (increasing_strict_bound C x h)).le

private theorem principal_decreasing_total (x : α) (C : DecreasingChain α) :
    principal x ≤ decreasing (DecreasingGerm.ofChain C) ∨
      decreasing (DecreasingGerm.ofChain C) ≤ principal x := by
  by_cases h : ∃ c : C.1, c.1 < x
  · exact Or.inr ((decreasing_ofChain_lt_principal C x).2 h).le
  · apply Or.inl
    apply le_of_lt
    apply (principal_lt_decreasing_ofChain x C).2
    intro c
    obtain ⟨d, hdc⟩ := C.2.exists_lt c
    exact (le_of_not_gt (fun hdx => h ⟨d, hdx⟩)).trans_lt hdc

private theorem increasing_total (C D : IncreasingChain α) :
    increasing (IncreasingGerm.ofChain C) ≤ increasing (IncreasingGerm.ofChain D) ∨
      increasing (IncreasingGerm.ofChain D) ≤ increasing (IncreasingGerm.ofChain C) := by
  by_cases hCD : ∃ d : D.1, ∀ c : C.1, c.1 < d.1
  · exact Or.inl ((increasing_ofChain_lt_increasing_ofChain C D).2 hCD).le
  by_cases hDC : ∃ c : C.1, ∀ d : D.1, d.1 < c.1
  · exact Or.inr ((increasing_ofChain_lt_increasing_ofChain D C).2 hDC).le
  have heq : IncreasingEquivalent C D := IncreasingEquivalent.of_mutually_cofinal C D
    (by
      intro c
      by_contra h
      exact hDC ⟨c, increasing_strict_bound D c.1 h⟩)
    (by
      intro d
      by_contra h
      exact hCD ⟨d, increasing_strict_bound C d.1 h⟩)
  exact Or.inl (le_of_eq (congrArg increasing (IncreasingGerm.ofChain_eq_iff.2 heq)))

private theorem increasing_decreasing_total (C : IncreasingChain α) (D : DecreasingChain α) :
    increasing (IncreasingGerm.ofChain C) ≤ decreasing (DecreasingGerm.ofChain D) ∨
      decreasing (DecreasingGerm.ofChain D) ≤ increasing (IncreasingGerm.ofChain C) := by
  by_cases h : ∀ c : C.1, ∀ d : D.1, c.1 < d.1
  · exact Or.inl ((increasing_ofChain_lt_decreasing_ofChain C D).2 h).le
  push Not at h
  obtain ⟨c, d, hdc⟩ := h
  obtain ⟨c', hcc'⟩ := C.2.exists_gt c
  exact Or.inr ((decreasing_ofChain_lt_increasing_ofChain D C).2
    ⟨d, c', hdc.trans_lt hcc'⟩).le

/-- Paper `lem:h-chain-is-chain`, with formal endpoints included. -/
theorem total (X Y : H α) : X ≤ Y ∨ Y ≤ X := by
  induction X using inductionOnRepresentatives <;>
    induction Y using inductionOnRepresentatives
  case hp.hp x y =>
    exact (le_total x y).imp (principal_le_principal x y).2 (principal_le_principal y x).2
  case hp.hi x C => exact principal_increasing_total x C
  case hp.hd x C => exact principal_decreasing_total x C
  case hi.hp C x => exact (principal_increasing_total x C).symm
  case hd.hp C x => exact (principal_decreasing_total x C).symm
  case hi.hi C D => exact increasing_total C D
  case hi.hd C D => exact increasing_decreasing_total C D
  case hd.hi D C => exact (increasing_decreasing_total C D).symm
  case hd.hd C D =>
    have ht := increasing_total C.toDual D.toDual
    have hC : (decreasing (DecreasingGerm.ofChain C)).dual =
        increasing (IncreasingGerm.ofChain C.toDual) := rfl
    have hD : (decreasing (DecreasingGerm.ofChain D)).dual =
        increasing (IncreasingGerm.ofChain D.toDual) := rfl
    rw [← hC, ← hD, dual_le_dual, dual_le_dual] at ht
    exact ht.symm
  all_goals first | exact Or.inl bot_le | exact Or.inr bot_le |
    exact Or.inl le_top | exact Or.inr le_top

noncomputable instance : LinearOrder (H α) where
  le_total := total
  toDecidableLE := Classical.decRel _

end H

end AharoniKorman.Completion
