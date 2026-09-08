import AharoniKorman.Completion

/-! Phase E regression examples: genuine rational accumulation, its dual,
and isolated formal endpoints even for the empty original chain. -/

namespace AharoniKorman.Completion.AccumulationExamples

open Set

private def rationalChain : IncreasingChain ℚ := by
  refine ⟨⟨univ, univ_nonempty, IsSaturatedChain.of_ordConnected
    (isChain_of_trichotomous _) ordConnected_univ⟩, ?_⟩
  rintro ⟨m, hm⟩
  exact (lt_add_one m.1).not_ge (hm ⟨m.1 + 1, mem_univ _⟩)

private def rationalCut (q : ℚ) : IncreasingChain ℚ := by
  refine ⟨⟨Iio q, ⟨q - 1, sub_one_lt q⟩, IsSaturatedChain.of_ordConnected
    (isChain_of_trichotomous _) ordConnected_Iio⟩, ?_⟩
  rintro ⟨m, hm⟩
  obtain ⟨x, hmx, hxq⟩ := exists_between (show m.1 < q from m.2)
  exact hmx.not_ge (hm ⟨x, hxq⟩)

/-- The upper germ of the rationals is an accumulation point of the nonprincipal order. -/
theorem rational_upper_accumulates :
    (H.increasing (IncreasingGerm.ofChain rationalChain)).IsAccumulation := by
  rw [H.isAccumulation_increasing,
    H.accumulatesBelow_iff_cofinal (H.increasing_ne_bot _)]
  intro Y hY
  obtain ⟨q, hYq⟩ := (H.lt_increasing_iff_exists_principal Y rationalChain).1 hY
  let C := rationalCut (q.1 + 1)
  refine ⟨H.increasing (IncreasingGerm.ofChain C), ⟨.increasing, rfl⟩, ?_, ?_⟩
  · apply hYq.trans
    apply (H.principal_lt_increasing_ofChain q.1 C).2
    obtain ⟨r, hqr, hr⟩ := exists_between (lt_add_one q.1)
    exact ⟨⟨r, hr⟩, hqr⟩
  · have hCp : H.increasing (IncreasingGerm.ofChain C) < H.principal (q.1 + 1) :=
      (H.increasing_ofChain_lt_principal C _).2 (fun c => c.2)
    exact hCp.trans (H.member_lt_increasing rationalChain ⟨q.1 + 1, mem_univ _⟩)

example : ∃ f : ℕ → H ℚ, StrictMono f ∧
    (∀ n, (f n).IsNonprincipal ∧ f n < H.increasing (IncreasingGerm.ofChain rationalChain)) ∧
    IsLUB (range f) (H.increasing (IncreasingGerm.ofChain rationalChain)) :=
  (H.isAccumulation_increasing_iff_sequence _).1 rational_upper_accumulates

example : (H.decreasing (IncreasingGerm.ofChain rationalChain).toDual).IsAccumulation :=
  (H.isAccumulation_dual _).2 rational_upper_accumulates

example : (⊤ : H ℚ).IsIsolated := H.isIsolated_top
example : (⊥ : H ℚ).IsIsolated := H.isIsolated_bot
example : ¬(H.principal (0 : ℚ)).IsAccumulation := H.not_isAccumulation_principal _
example : ¬(H.principal (0 : ℚ)).IsIsolated := H.not_isIsolated_principal _
example : (⊤ : H (Fin 0)).IsIsolated := H.isIsolated_top
example : (⊥ : H (Fin 0)).IsIsolated := H.isIsolated_bot

#print axioms rational_upper_accumulates

end AharoniKorman.Completion.AccumulationExamples
