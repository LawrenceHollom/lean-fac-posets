import AharoniKorman.Completion.WitnessVacillation
import AharoniKorman.Tube.Quasifounded

namespace AharoniKorman

open Set Completion Completion.H

variable {α : Type*} [PartialOrder α]

/-- An induced subposet with no minimal or maximal point. -/
def IsOpenSubposet (C : Set α) : Prop :=
  (∀ x ∈ C, ∃ y ∈ C, y < x) ∧ (∀ x ∈ C, ∃ y ∈ C, x < y)

theorem IsOpenSubposet.image {β : Type*} [PartialOrder β] {C : Set α}
    (hC : IsOpenSubposet C) (e : α ↪o β) : IsOpenSubposet (e '' C) := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hlt⟩ := hC.1 x hx
    exact ⟨e y, ⟨y, hy, rfl⟩, e.strictMono hlt⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hlt⟩ := hC.2 x hx
    exact ⟨e y, ⟨y, hy, rfl⟩, e.strictMono hlt⟩

/-- The interval of principal points of a chain between two completion points. -/
def betweenInChain (C : Set α) (L U : H α) : Set α :=
  {x | x ∈ C ∧ L < H.principal x ∧ H.principal x < U}

theorem betweenInChain_saturated {C : Set α} (hC : IsSaturatedChain C) (L U : H α) :
    IsSaturatedChain (betweenInChain C L U) := by
  apply hC.restrict (fun _ hx => hx.1)
  intro x y z hx hy hz hxz hzy
  exact ⟨hz, hx.2.1.trans_le ((H.principal_le_principal _ _).2 hxz),
    ((H.principal_le_principal _ _).2 hzy).trans_lt hy.2.2⟩

/-- The interval between negative and positive witnesses is nonempty and open. -/
theorem betweenInChain_nonempty_open (C : SaturatedChain α)
    {g : DecreasingGerm α} {h : IncreasingGerm α}
    (hg : H.Witnesses C (H.decreasing g)) (hh : H.Witnesses C (H.increasing h))
    (hlt : H.decreasing g < H.increasing h) :
    (betweenInChain C (H.decreasing g) (H.increasing h)).Nonempty ∧
      IsOpenSubposet (betweenInChain C (H.decreasing g) (H.increasing h)) := by
  obtain ⟨A, hAC, hA, rfl⟩ := hg
  obtain ⟨B, hBC, hB, rfl⟩ := hh
  let D : DecreasingChain α := ⟨A, hA⟩
  let E : IncreasingChain α := ⟨B, hB⟩
  have hD (a : D.1) : H.decreasing (DecreasingGerm.ofChain D) < H.principal a.1 :=
    (H.decreasing_ofChain_lt_principal D a.1).2 (D.2.exists_lt a)
  have hE (b : E.1) : H.principal b.1 < H.increasing (IncreasingGerm.ofChain E) :=
    (H.principal_lt_increasing_ofChain b.1 E).2 (E.2.exists_gt b)
  obtain ⟨a, b, hab⟩ := (H.decreasing_ofChain_lt_increasing_ofChain D E).1 hlt
  refine ⟨⟨a.1, hAC a.2, hD a, ((H.principal_lt_principal _ _).2 hab).trans (hE b)⟩,
    ?_, ?_⟩
  · intro x hx
    obtain ⟨a, hax⟩ := (H.decreasing_ofChain_lt_principal D x).1 hx.2.1
    exact ⟨a.1, ⟨hAC a.2, hD a, ((H.principal_lt_principal _ _).2 hax).trans hx.2.2⟩, hax⟩
  · intro x hx
    obtain ⟨b, hxb⟩ := (H.principal_lt_increasing_ofChain x E).1 hx.2.2
    exact ⟨b.1, ⟨hBC b.2, hx.2.1.trans ((H.principal_lt_principal _ _).2 hxb), hE b⟩, hxb⟩

private theorem open_chains_of_descending_increasing (hvac : IsVacillating α)
    (g : ℕ → IncreasingGerm α) (hg : StrictAnti (fun n => H.increasing (g n))) :
    ∃ C : ℕ → Set α, (∀ n, IsSaturatedChain (C n) ∧ (C n).Nonempty ∧ IsOpenSubposet (C n)) ∧
      ∀ ⦃i j : ℕ⦄, i < j → SetStrictLT (C j) (C i) := by
  obtain ⟨e, h, D, he, hinter, hpos, hneg⟩ :=
    H.exists_alternating_witness_of_strictAnti_increasing hvac g hg
  let C : ℕ → Set α := fun n => betweenInChain D (H.decreasing (h n)) (H.increasing (g (e n)))
  refine ⟨C, fun n => ⟨betweenInChain_saturated D.saturated _ _,
    betweenInChain_nonempty_open D (hneg n) (hpos n) (hinter n).2⟩, ?_⟩
  intro i j hij x hx y hy
  have hmon : H.increasing (g (e j)) ≤ H.increasing (g (e (i + 1))) :=
    (hg.comp_strictMono he).antitone (Nat.succ_le_of_lt hij)
  exact (H.principal_lt_principal _ _).1
    (hx.2.2.trans (hmon.trans_lt ((hinter i).1.trans hy.2.1)))

/-- Paper `lem:find-open`: the intervals of a common witness chain between
successive opposite signs form an ordered sequence of open saturated chains. -/
theorem exists_ordered_open_chains (hvac : IsVacillating α)
    (hqf : ¬AharoniKorman.IsQuasifounded α) :
    ∃ C : ℕ → Set α, (∀ n, IsSaturatedChain (C n) ∧ (C n).Nonempty ∧ IsOpenSubposet (C n)) ∧
      ((∀ ⦃i j : ℕ⦄, i < j → SetStrictLT (C i) (C j)) ∨
        (∀ ⦃i j : ℕ⦄, i < j → SetStrictLT (C j) (C i))) := by
  classical
  rw [AharoniKorman.IsQuasifounded, not_and_or] at hqf
  rcases hqf with hpos | hneg
  · obtain ⟨g, hg⟩ := exists_increasingGerm_descent hpos
    obtain ⟨C, hc, hord⟩ := open_chains_of_descending_increasing hvac g hg
    exact ⟨C, hc, Or.inr hord⟩
  · obtain ⟨g, hg⟩ := exists_decreasingGerm_ascent hneg
    obtain ⟨e, h, D, he, hinter, hneg, hpos⟩ :=
      H.exists_alternating_witness_of_strictMono_decreasing hvac g hg
    let C : ℕ → Set α := fun n => betweenInChain D (H.decreasing (g (e n))) (H.increasing (h n))
    refine ⟨C, fun n => ⟨betweenInChain_saturated D.saturated _ _,
      betweenInChain_nonempty_open D (hneg n) (hpos n) (hinter n).1⟩,
      Or.inl ?_⟩
    intro i j hij x hx y hy
    have hmon : H.decreasing (g (e (i + 1))) ≤ H.decreasing (g (e j)) :=
      (hg.comp he).monotone (Nat.succ_le_of_lt hij)
    exact (H.principal_lt_principal _ _).1
      (hx.2.2.trans (((hinter i).2.trans_le hmon).trans hy.2.1))

/-- Paper `lem:vacillating-no-internal-is-quasifounded`. The consecutive-gap
argument from witness vacillation supplies the forbidden sum. -/
theorem IsVacillating.isQuasifounded_of_no_internal_increasing (hvac : IsVacillating α)
    (hno : ∀ (g : IncreasingGerm α) (x : α), ¬H.increasing g < H.principal x) :
    AharoniKorman.IsQuasifounded α := by
  constructor
  · by_contra! hn
    obtain ⟨g, hg⟩ := exists_increasingGerm_descent hn
    obtain ⟨x, hx, _⟩ := H.exists_principal_between_increasing (hg (Nat.zero_lt_succ 0))
    exact hno (g 1) x hx
  · by_contra! hn
    obtain ⟨g, hg⟩ := exists_decreasingGerm_ascent hn
    obtain ⟨e, h, _, _, hh, _, _⟩ :=
      H.exists_alternating_witness_of_strictMono_decreasing hvac g hg
    let D := (g (e 1)).representative
    obtain ⟨x, hx⟩ := D.1.nonempty
    have hxp : H.decreasing (g (e 1)) < H.principal x :=
      (H.strictLT_decreasing_principal (g (e 1)).representative_spec _).2
        (D.2.exists_lt ⟨x, hx⟩)
    exact hno (h 0) x ((hh 0).2.trans hxp)

theorem IsVacillating.isQuasifounded_of_no_internal_decreasing (hvac : IsVacillating α)
    (hno : ∀ (g : DecreasingGerm α) (x : α), ¬H.principal x < H.decreasing g) :
    AharoniKorman.IsQuasifounded α := by
  apply IsQuasifounded.orderDual (α := αᵒᵈ)
  apply hvac.orderDual.isQuasifounded_of_no_internal_increasing
  intro g x h
  exact hno g.toDual x ((H.dual_lt_dual (α := αᵒᵈ) _ _).2 h)

end AharoniKorman
