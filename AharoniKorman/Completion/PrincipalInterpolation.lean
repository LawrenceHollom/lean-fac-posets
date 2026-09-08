import AharoniKorman.Completion.BoundaryProfiles
import AharoniKorman.Completion.Scattering
import AharoniKorman.Preliminaries.ScatteredCovers

/-! Principal points in maximal chains of the scattered completion.
The chain need not realize its nonprincipal members by unchanged germs. -/

namespace AharoniKorman.Completion

open Set

variable {α : Type*} [PartialOrder α]

namespace H

def PrincipalInterpolationBelow (K : Set (H α)) (g : H α) : Prop :=
  ∀ a ∈ K, a < g → ∃ e : α, principal e ∈ K ∧ a < principal e ∧ principal e < g

theorem exists_principal_below_increasing {a : H α} {g : IncreasingGerm α}
    (hag : a < increasing g) :
    ∃ e : α, a < principal e ∧ principal e < increasing g := by
  induction g using IncreasingGerm.inductionOn with
  | h C =>
    induction a using inductionOnRepresentatives with
    | hp x =>
      obtain ⟨c, hxc⟩ := (principal_lt_increasing_ofChain x C).1 hag
      obtain ⟨d, hcd⟩ := C.2.exists_gt c
      exact ⟨c.1, (principal_lt_principal _ _).2 hxc,
        (principal_lt_increasing_ofChain _ _).2 ⟨d, hcd⟩⟩
    | hi D => exact exists_principal_between_increasing hag
    | hd D =>
      obtain ⟨d, c, hdc⟩ := (decreasing_ofChain_lt_increasing_ofChain D C).1 hag
      obtain ⟨e, hce⟩ := C.2.exists_gt c
      exact ⟨c.1, (decreasing_ofChain_lt_principal D _).2 ⟨d, hdc⟩,
        (principal_lt_increasing_ofChain _ _).2 ⟨e, hce⟩⟩
    | hb =>
      obtain ⟨c, hc⟩ := C.1.nonempty
      exact ⟨c, bot_lt_iff_ne_bot.2 (principal_ne_bot c),
        IncreasingGerm.representative_mem_lowerProfile C ⟨c, hc⟩⟩
    | ht => exact (not_lt_of_ge le_top hag).elim

theorem exists_principal_above_decreasing {a : H α} {g : DecreasingGerm α}
    (hga : decreasing g < a) :
    ∃ e : α, decreasing g < principal e ∧ principal e < a := by
  have hd : a.dual < increasing g.toDual :=
    (dual_lt_dual a (decreasing g)).2 hga
  obtain ⟨e, hae, heg⟩ := exists_principal_below_increasing hd
  exact ⟨e, (dual_lt_dual (principal (show α from e)) (decreasing g)).1 heg,
    (dual_lt_dual a (principal (show α from e))).1 hae⟩

/-- Covers in a maximal chain are covers in the ambient completion. -/
theorem maxChain_covBy_val {K : Set (H α)} (hK : IsMaxChain (· ≤ ·) K)
    {x y : K} (hxy : x ⋖ y) : x.1 ⋖ y.1 := by
  refine ⟨hxy.1, ?_⟩
  intro z hxz hzy
  have hzK : z ∈ K := by
    have hcomp : ∀ a ∈ K, z ≠ a → z ≤ a ∨ a ≤ z := by
      intro a ha _
      rcases hK.1.total ha x.2 with hax | hxa
      · exact Or.inr (hax.trans hxz.le)
      rcases hK.1.total ha y.2 with hay | hya
      · by_cases heq : x.1 = a
        · exact Or.inr (heq ▸ hxz.le)
        by_cases heq' : a = y.1
        · exact Or.inl (heq' ▸ hzy.le)
        exact False.elim (hxy.2 (c := ⟨a, ha⟩)
          (show x.1 < a from lt_of_le_of_ne hxa heq)
          (show a < y.1 from lt_of_le_of_ne hay heq'))
      · exact Or.inl (hzy.le.trans hya)
    have heq : insert z K = K := (hK.2 (hK.1.insert hcomp) (Set.subset_insert _ _)).symm
    exact heq ▸ Set.mem_insert _ _
  exact hxy.2 (c := ⟨z, hzK⟩) hxz hzy

private theorem principalFree_no_consecutive_covers {K : Set (H α)}
    (hK : IsMaxChain (· ≤ ·) K) {a : K} {g : IncreasingGerm α}
    (hg : increasing g ∈ K)
    (hno : ¬ ∃ e : α, principal e ∈ K ∧ a.1 < principal e ∧ principal e < increasing g) :
    ∀ x y z : Ioc a (⟨increasing g, hg⟩ : K), x ⋖ y → y ⋖ z → False := by
  intro x y z hxy hyz
  have liftCov {u v : Ioc a (⟨increasing g, hg⟩ : K)} (huv : u ⋖ v) :
      u.1.1 ⋖ v.1.1 := by
    apply maxChain_covBy_val hK
    refine ⟨huv.1, ?_⟩
    intro b hub hbv
    have hbI : b ∈ Ioc a (⟨increasing g, hg⟩ : K) :=
      ⟨u.2.1.trans hub, hbv.le.trans v.2.2⟩
    exact huv.2 (c := ⟨b, hbI⟩) hub hbv
  have hyGenuine : (∃ d, y.1.1 = increasing d) ∨ (∃ d, y.1.1 = decreasing d) := by
    cases hy : y.1.1 with
    | principal p =>
      have hpg : principal p < increasing g :=
        lt_of_le_of_ne (hy ▸ y.2.2) (principal_ne_increasing p g)
      exact (hno ⟨p, hy ▸ y.1.2, hy ▸ y.2.1, hpg⟩).elim
    | increasing d => exact Or.inl ⟨d, rfl⟩
    | decreasing d => exact Or.inr ⟨d, rfl⟩
    | bottom =>
      have hay : a.1 < y.1.1 := y.2.1
      rw [hy] at hay
      exact (not_lt_of_ge bot_le hay).elim
    | top =>
      have htg : y.1.1 ≤ increasing g := y.2.2
      rw [hy] at htg
      exact (increasing_ne_top g (le_antisymm le_top htg)).elim
  rcases hyGenuine with ⟨d, hd⟩ | ⟨d, hd⟩
  · have hcov := liftCov hxy
    obtain ⟨p, hxp, hpy⟩ := exists_principal_below_increasing (hd ▸ hcov.1)
    exact hcov.2 hxp (hd ▸ hpy)
  · have hcov := liftCov hyz
    obtain ⟨p, hyp, hpz⟩ := exists_principal_above_decreasing (hd ▸ hcov.1)
    exact hcov.2 (hd ▸ hyp) hpz

/-- Scatteredness and maximality supply the interpolation needed by principal cuts. -/
theorem principalInterpolationBelow_of_maxChain (hα : IsScattered α)
    {K : Set (H α)} (hK : IsMaxChain (· ≤ ·) K)
    (g : IncreasingGerm α) (hg : increasing g ∈ K) :
    PrincipalInterpolationBelow K (increasing g) := by
  classical
  intro a ha hag
  by_contra hno
  let : LinearOrder K := hK.1.linearOrder
  let aK : K := ⟨a, ha⟩
  let gK : K := ⟨increasing g, hg⟩
  let I : Set K := Ioc aK gK
  have hsc : IsScattered I := ((isScattered hα).subtype K).subtype I
  have hno3 : ∀ {x y z : I}, x < y → y < z → False := fun hxy hyz =>
    hsc.no_three_of_no_consecutive_covers
      (principalFree_no_consecutive_covers hK hg hno) hxy hyz
  have hcover : ∃ b : K, b ⋖ gK := by
    by_cases hb : ∃ b : K, aK < b ∧ b < gK
    · obtain ⟨b, hab, hbg⟩ := hb
      refine ⟨b, hbg, ?_⟩
      intro c hbc hcg
      exact hno3 (x := ⟨b, hab, hbg.le⟩) (y := ⟨c, hab.trans hbc, hcg.le⟩)
        (z := ⟨gK, hag, le_rfl⟩) hbc hcg
    · exact ⟨aK, hag, fun c hac hcg => hb ⟨c, hac, hcg⟩⟩
  obtain ⟨b, hb⟩ := hcover
  have hcov := maxChain_covBy_val hK hb
  obtain ⟨p, hbp, hpg⟩ := exists_principal_below_increasing hcov.1
  exact hcov.2 hbp hpg

theorem maxChain_dual_image {K : Set (H α)} (hK : IsMaxChain (· ≤ ·) K) :
    IsMaxChain (· ≤ ·) (dual '' K) :=
  hK.symm.image (dualOrderIso (α := α))

def PrincipalInterpolationAbove (K : Set (H α)) (g : H α) : Prop :=
  ∀ a ∈ K, g < a → ∃ e : α, principal e ∈ K ∧ g < principal e ∧ principal e < a

theorem principalInterpolationAbove_of_maxChain (hα : IsScattered α)
    {K : Set (H α)} (hK : IsMaxChain (· ≤ ·) K)
    (g : DecreasingGerm α) (hg : decreasing g ∈ K) :
    PrincipalInterpolationAbove K (decreasing g) := by
  intro a ha hga
  have hdg : increasing g.toDual ∈ dual '' K := ⟨decreasing g, hg, rfl⟩
  obtain ⟨e, he, hae, heg⟩ :=
    principalInterpolationBelow_of_maxChain hα.orderDual (maxChain_dual_image hK)
      g.toDual hdg a.dual ⟨a, ha, rfl⟩ ((dual_lt_dual a (decreasing g)).2 hga)
  have heK : principal (show α from e) ∈ K := by
    obtain ⟨b, hb, hbe⟩ := he
    have hb' : b = principal (show α from e) := dual_injective hbe
    exact hb' ▸ hb
  exact ⟨e, heK, (dual_lt_dual (principal (show α from e)) (decreasing g)).1 heg,
    (dual_lt_dual a (principal (show α from e))).1 hae⟩

/-- The principal trace is nonempty unless the original poset is empty. -/
theorem principalTrace_nonempty [Nonempty α] (hα : IsScattered α)
    {K : Set (H α)} (hK : IsMaxChain (· ≤ ·) K) :
    ∃ e : α, principal e ∈ K := by
  classical
  by_contra hno
  have hk : ∀ a ∈ K, a = ⊥ ∨ a = ⊤ := by
    intro a ha
    cases a with
    | principal p => exact (hno ⟨p, ha⟩).elim
    | increasing g =>
      obtain ⟨p, hp, _⟩ := principalInterpolationBelow_of_maxChain hα hK g ha
        ⊥ hK.bot_mem (bot_lt_iff_ne_bot.2 (increasing_ne_bot g))
      exact (hno ⟨p, hp⟩).elim
    | decreasing g =>
      obtain ⟨p, hp, _⟩ := principalInterpolationAbove_of_maxChain hα hK g ha
        ⊤ hK.top_mem (lt_top_iff_ne_top.2 (decreasing_ne_top g))
      exact (hno ⟨p, hp⟩).elim
    | bottom => exact Or.inl rfl
    | top => exact Or.inr rfl
  obtain ⟨p⟩ := ‹Nonempty α›
  have hcomp : ∀ a ∈ K, principal p ≠ a → principal p ≤ a ∨ a ≤ principal p := by
    intro a ha _
    rcases hk a ha with rfl | rfl
    · exact Or.inr bot_le
    · exact Or.inl le_top
  have heq : insert (principal p) K = K :=
    (hK.2 (hK.1.insert hcomp) (Set.subset_insert _ _)).symm
  exact hno ⟨p, heq ▸ Set.mem_insert _ _⟩

end H

end AharoniKorman.Completion
