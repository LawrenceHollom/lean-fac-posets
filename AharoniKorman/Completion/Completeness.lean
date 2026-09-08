import AharoniKorman.Completion.LinearOrder
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Bounds.OrderIso

/-! Completeness of `H(C)` and the shape of non-attained bounds (`lem:h-complete`). -/

namespace AharoniKorman.Completion

open Set

variable {α : Type*} [LinearOrder α]

namespace H

private theorem middle_shape {A B C : H α} (hAB : A < B) (hBC : B < C) :
    (∃ x, B = principal x) ∨ (∃ g, B = increasing g) ∨ (∃ g, B = decreasing g) := by
  cases B with
  | principal x => exact Or.inl ⟨x, rfl⟩
  | increasing g => exact Or.inr (Or.inl ⟨g, rfl⟩)
  | decreasing g => exact Or.inr (Or.inr ⟨g, rfl⟩)
  | bottom => exact (not_lt_bot hAB).elim
  | top => exact (not_top_lt hBC).elim

/-- Three interior completion points force a principal point in the interval. -/
theorem principal_between_five {A B C D E : H α}
    (hAB : A < B) (hBC : B < C) (hCD : C < D) (hDE : D < E) :
    ∃ x : α, A < principal x ∧ principal x < E := by
  rcases middle_shape hAB (hBC.trans (hCD.trans hDE)) with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩
  all_goals first
    | exact ⟨b, hAB, hBC.trans (hCD.trans hDE)⟩
    | skip
  all_goals rcases middle_shape hBC (hCD.trans hDE) with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
  all_goals first
    | exact ⟨c, hAB.trans hBC, hCD.trans hDE⟩
    | (obtain ⟨x, hbx, hxc⟩ := exists_principal_between_increasing hBC
       exact ⟨x, hAB.trans hbx, hxc.trans (hCD.trans hDE)⟩)
    | (obtain ⟨x, hbx, hxc⟩ := exists_principal_between_decreasing hBC
       exact ⟨x, hAB.trans hbx, hxc.trans (hCD.trans hDE)⟩)
    | skip
  all_goals rcases middle_shape hCD hDE with ⟨d, rfl⟩ | ⟨d, rfl⟩ | ⟨d, rfl⟩
  all_goals first
    | exact ⟨d, (hAB.trans hBC).trans hCD, hDE⟩
    | (obtain ⟨x, hcx, hxd⟩ := exists_principal_between_increasing hCD
       exact ⟨x, (hAB.trans hBC).trans hcx, hxd.trans hDE⟩)
    | (obtain ⟨x, hcx, hxd⟩ := exists_principal_between_decreasing hCD
       exact ⟨x, (hAB.trans hBC).trans hcx, hxd.trans hDE⟩)
    | (obtain ⟨x, hbx, hxd⟩ := exists_principal_between_increasing (hBC.trans hCD)
       exact ⟨x, hAB.trans hbx, hxd.trans hDE⟩)
    | (obtain ⟨x, hbx, hxd⟩ := exists_principal_between_decreasing (hBC.trans hCD)
       exact ⟨x, hAB.trans hbx, hxd.trans hDE⟩)

theorem principal_approximation_of_no_greatest {D : Set (H α)}
    (hD : ∀ X ∈ D, ∃ Y ∈ D, X < Y) {X : H α} (hX : X ∈ D) :
    ∃ x : α, ∃ Y ∈ D, X < principal x ∧ principal x < Y := by
  obtain ⟨B, hB, hXB⟩ := hD X hX
  obtain ⟨C, hC, hBC⟩ := hD B hB
  obtain ⟨E, hE, hCE⟩ := hD C hC
  obtain ⟨F, hF, hEF⟩ := hD E hE
  obtain ⟨x, hXx, hxF⟩ := principal_between_five hXB hBC hCE hEF
  exact ⟨x, F, hF, hXx, hxF⟩

/-- Principal points below a member of the set (paper `lem:h-complete`). -/
def lowerPrincipals (D : Set (H α)) : Set α := {x | ∃ Y ∈ D, principal x < Y}

theorem lowerPrincipals_initial (D : Set (H α)) : IsInitialSegment (lowerPrincipals D) univ := by
  refine ⟨subset_univ _, ?_⟩
  rintro x y ⟨Y, hY, hxY⟩ _ hyx
  exact ⟨Y, hY, ((principal_le_principal y x).2 hyx).trans_lt hxY⟩

theorem lowerPrincipals_saturated (D : Set (H α)) : IsSaturatedChain (lowerPrincipals D) := by
  apply IsSaturatedChain.of_ordConnected (isChain_of_trichotomous _)
  constructor
  intro a _ b hb x hx
  exact (lowerPrincipals_initial D).2 hb (mem_univ x) hx.2

theorem lowerPrincipals_nonempty {D : Set (H α)} (hne : D.Nonempty)
    (hD : ∀ X ∈ D, ∃ Y ∈ D, X < Y) : (lowerPrincipals D).Nonempty := by
  obtain ⟨X, hX⟩ := hne
  obtain ⟨x, Y, hY, _, hxY⟩ := principal_approximation_of_no_greatest hD hX
  exact ⟨x, Y, hY, hxY⟩

/-- The explicit increasing chain used for a nonempty set without a greatest element. -/
def supChain (D : Set (H α)) (hne : D.Nonempty)
    (hD : ∀ X ∈ D, ∃ Y ∈ D, X < Y) : IncreasingChain α := by
  let C : SaturatedChain α :=
    ⟨lowerPrincipals D, lowerPrincipals_nonempty hne hD, lowerPrincipals_saturated D⟩
  refine ⟨C, ?_⟩
  rintro ⟨m, hm⟩
  obtain ⟨X, hX, hmX⟩ := m.2
  obtain ⟨x, Y, hY, hXx, hxY⟩ := principal_approximation_of_no_greatest hD hX
  have hx : x ∈ C := ⟨Y, hY, hxY⟩
  exact ((principal_lt_principal m.1 x).1 (hmX.trans hXx)).not_ge (hm ⟨x, hx⟩)

theorem member_lt_increasing (C : IncreasingChain α) (c : C.1) :
    principal c.1 < increasing (IncreasingGerm.ofChain C) := by
  obtain ⟨d, hcd⟩ := C.2.exists_gt c
  exact (principal_lt_increasing_ofChain c.1 C).2 ⟨d, hcd⟩

/-- The principal representatives are cofinal below their increasing germ. -/
theorem lt_increasing_iff_exists_principal (X : H α) (C : IncreasingChain α) :
    X < increasing (IncreasingGerm.ofChain C) ↔ ∃ c : C.1, X < principal c.1 := by
  constructor
  · intro h
    induction X using inductionOnRepresentatives with
    | hp x => exact (principal_lt_increasing_ofChain x C).1 h
    | hi D =>
      obtain ⟨c, hc⟩ := (increasing_ofChain_lt_increasing_ofChain D C).1 h
      exact ⟨c, (increasing_ofChain_lt_principal D c.1).2 hc⟩
    | hd D =>
      obtain ⟨d, c, hdc⟩ := (decreasing_ofChain_lt_increasing_ofChain D C).1 h
      exact ⟨c, (decreasing_ofChain_lt_principal D c.1).2 ⟨d, hdc⟩⟩
    | hb =>
      obtain ⟨c, hc⟩ := C.1.nonempty
      exact ⟨⟨c, hc⟩, bot_lt_iff_ne_bot.2 (principal_ne_bot c)⟩
    | ht => exact (not_top_lt h).elim
  · rintro ⟨c, hc⟩
    exact hc.trans (member_lt_increasing C c)

/-- Least-upper-bound proof for the explicit non-attained candidate. -/
theorem isLUB_supChain (D : Set (H α)) (hne : D.Nonempty)
    (hD : ∀ X ∈ D, ∃ Y ∈ D, X < Y) :
    IsLUB D (increasing (IncreasingGerm.ofChain (supChain D hne hD))) := by
  let C := supChain D hne hD
  constructor
  · intro X hX
    obtain ⟨x, Y, hY, hXx, hxY⟩ := principal_approximation_of_no_greatest hD hX
    have hx : x ∈ C.1 := ⟨Y, hY, hxY⟩
    exact (hXx.trans (member_lt_increasing C ⟨x, hx⟩)).le
  · intro Y hY
    by_contra h
    obtain ⟨c, hYc⟩ := (lt_increasing_iff_exists_principal Y C).1 (lt_of_not_ge h)
    obtain ⟨X, hX, hcX⟩ := c.2
    exact (hYc.trans hcX).not_ge (hY hX)

/-- Every set has a least upper bound, including the empty and attained cases. -/
theorem exists_isLUB (D : Set (H α)) : ∃ X, IsLUB D X := by
  classical
  by_cases hne : D.Nonempty
  · by_cases hg : ∃ X, IsGreatest D X
    · obtain ⟨X, hX⟩ := hg
      exact ⟨X, hX.isLUB⟩
    · have hD : ∀ X ∈ D, ∃ Y ∈ D, X < Y := by
        intro X hX
        by_contra h
        apply hg
        refine ⟨X, hX, ?_⟩
        intro Y hY
        exact le_of_not_gt (fun hXY => h ⟨Y, hY, hXY⟩)
      exact ⟨_, isLUB_supChain D hne hD⟩
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]
    exact ⟨⊥, isLUB_empty⟩

private noncomputable def chosenSup (D : Set (H α)) : H α := Classical.choose (exists_isLUB D)

private theorem chosenSup_spec (D : Set (H α)) : IsLUB D (chosenSup D) :=
  Classical.choose_spec (exists_isLUB D)

/-- Infima are constructed by applying the supremum construction in the dual completion. -/
private noncomputable def chosenInf (D : Set (H α)) : H α :=
  OrderDual.ofDual ((dualOrderIso (α := α)).symm
    (chosenSup (α := αᵒᵈ) ((H.dual (α := α)) '' D)))

private theorem chosenInf_spec (D : Set (H α)) : IsGLB D (chosenInf D) := by
  have h : IsLUB ((dualOrderIso (α := α)) '' (show Set (H α)ᵒᵈ from D))
      (chosenSup (H.dual '' D)) := chosenSup_spec _
  exact (dualOrderIso (α := α)).isLUB_image.1 h

noncomputable instance : BoundedOrder (H α) where

/-- Paper `lem:h-complete`: a chain's completion is a complete linear order. -/
noncomputable instance : CompleteLinearOrder (H α) where
  __ := LinearOrder.toBiheytingAlgebra (H α)
  __ := (inferInstance : LinearOrder (H α))
  sSup := chosenSup
  sInf := chosenInf
  isLUB_sSup := chosenSup_spec
  isGLB_sInf := chosenInf_spec

theorem sSup_eq_supChain (D : Set (H α)) (hne : D.Nonempty)
    (hD : ∀ X ∈ D, ∃ Y ∈ D, X < Y) :
    sSup D = increasing (IncreasingGerm.ofChain (supChain D hne hD)) :=
  (isLUB_supChain D hne hD).sSup_eq

/-- A non-attained bound of a nonempty set is a genuine germ, never a formal endpoint. -/
theorem sSup_eq_increasing_of_not_mem {D : Set (H α)} (hne : D.Nonempty)
    (hnot : sSup D ∉ D) : ∃ g, sSup D = increasing g := by
  have hD : ∀ X ∈ D, ∃ Y ∈ D, X < Y := by
    intro X hX
    by_contra h
    have hgreatest : IsGreatest D X :=
      ⟨hX, fun Y hY => le_of_not_gt (fun hXY => h ⟨Y, hY, hXY⟩)⟩
    exact hnot (hgreatest.isLUB.sSup_eq.symm ▸ hX)
  exact ⟨_, sSup_eq_supChain D hne hD⟩

/-- The nonempty hypothesis matters: the supremum of the empty set is the
decreasing endpoint. Non-attained suprema of nonempty sets are increasing germs. -/
theorem sSup_direction_of_not_mem {D : Set (H α)} (hne : D.Nonempty) (hnot : sSup D ∉ D) :
    (sSup D).direction = some .increasing := by
  obtain ⟨g, hg⟩ := sSup_eq_increasing_of_not_mem hne hnot
  rw [hg]
  rfl

theorem sInf_eq_dual_sSup (D : Set (H α)) : sInf D = (sSup (H.dual '' D)).dual := rfl

theorem sInf_eq_decreasing_of_not_mem {D : Set (H α)} (hne : D.Nonempty)
    (hnot : sInf D ∉ D) : ∃ g, sInf D = decreasing g := by
  have hn : sSup (H.dual '' D) ∉ H.dual '' D := by
    rintro ⟨X, hX, heq⟩
    apply hnot
    have heq' : sInf D = X := by rw [sInf_eq_dual_sSup, ← heq, dual_dual]
    exact heq'.symm ▸ hX
  obtain ⟨g, hg⟩ := sSup_eq_increasing_of_not_mem (hne.image H.dual) hn
  refine ⟨g.toDual, ?_⟩
  rw [sInf_eq_dual_sSup, hg]
  rfl

theorem sInf_direction_of_not_mem {D : Set (H α)} (hne : D.Nonempty) (hnot : sInf D ∉ D) :
    (sInf D).direction = some .decreasing := by
  have hn : sSup (H.dual '' D) ∉ H.dual '' D := by
    rintro ⟨X, hX, heq⟩
    apply hnot
    have heq' : sInf D = X := by
      rw [sInf_eq_dual_sSup, ← heq, dual_dual]
    exact heq'.symm ▸ hX
  have hd := sSup_direction_of_not_mem (hne.image H.dual) hn
  rw [sInf_eq_dual_sSup]
  exact (direction_dual (α := αᵒᵈ) (sSup (H.dual '' D))).trans (by rw [hd]; rfl)

theorem iSup_direction_of_strictMono (f : ℕ → H α) (hf : StrictMono f) :
    (⨆ n, f n).direction = some .increasing := by
  apply sSup_direction_of_not_mem (Set.range_nonempty f)
  rintro ⟨n, hn⟩
  have hlt := hf (Nat.lt_succ_self n)
  have hle : f (n + 1) ≤ sSup (Set.range f) := le_sSup ⟨n + 1, rfl⟩
  rw [← hn] at hle
  exact hlt.not_ge hle

theorem iInf_direction_of_strictAnti (f : ℕ → H α) (hf : StrictAnti f) :
    (⨅ n, f n).direction = some .decreasing := by
  apply sInf_direction_of_not_mem (Set.range_nonempty f)
  rintro ⟨n, hn⟩
  have hlt := hf (Nat.lt_succ_self n)
  have hle : sInf (Set.range f) ≤ f (n + 1) := sInf_le ⟨n + 1, rfl⟩
  rw [← hn] at hle
  exact hlt.not_ge hle

end H

end AharoniKorman.Completion
