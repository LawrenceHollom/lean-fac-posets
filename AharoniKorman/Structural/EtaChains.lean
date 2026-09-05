import AharoniKorman.Preliminaries.Scattered
import AharoniKorman.Preliminaries.Intervals
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Denumerable
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Order.Zorn

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- A subset with order type eta. -/
def IsEtaChain (C : Set α) : Prop := Nonempty (ℚ ≃o C)

/-- An eta-chain maximal under inclusion among eta-chains. -/
def IsEtaMaximalChain (C : Set α) : Prop :=
  IsEtaChain C ∧ ∀ D : Set α, IsEtaChain D → C ⊆ D → D = C

/-- An eta-chain is a chain. -/
theorem IsEtaChain.isChain {C : Set α} (hC : IsEtaChain C) : IsChain (· ≤ ·) C := by
  obtain ⟨e⟩ := hC
  intro x hx y hy _
  let x' : C := ⟨x, hx⟩
  let y' : C := ⟨y, hy⟩
  rcases le_total (e.symm x') (e.symm y') with h | h
  · exact Or.inl (e.symm.le_iff_le.mp h)
  · exact Or.inr (e.symm.le_iff_le.mp h)

theorem IsEtaChain.nonempty {C : Set α} (hC : IsEtaChain C) : C.Nonempty := by
  obtain ⟨e⟩ := hC
  exact ⟨(e 0).1, (e 0).2⟩

theorem IsEtaChain.infinite {C : Set α} (hC : IsEtaChain C) : C.Infinite := by
  obtain ⟨e⟩ := hC
  have hrange := Set.infinite_range_of_injective (Subtype.val_injective.comp e.injective)
  apply hrange.mono
  rintro _ ⟨q, rfl⟩
  exact (e q).2

theorem IsEtaChain.exists_between {C : Set α} (hC : IsEtaChain C)
    {x y : α} (hx : x ∈ C) (hy : y ∈ C) (hxy : x < y) :
    ∃ z ∈ C, x < z ∧ z < y := by
  obtain ⟨e⟩ := hC
  let x' : C := ⟨x, hx⟩
  let y' : C := ⟨y, hy⟩
  have hxy' : x' < y' := hxy
  obtain ⟨q, hxq, hqy⟩ := DenselyOrdered.dense _ _ (e.symm.lt_iff_lt.mpr hxy')
  refine ⟨(e q).1, (e q).2, ?_, ?_⟩
  · change x' < e q
    simpa only [e.apply_symm_apply] using e.lt_iff_lt.mpr hxq
  · change e q < y'
    simpa only [e.apply_symm_apply] using e.lt_iff_lt.mpr hqy

theorem IsEtaChain.exists_lt {C : Set α} (hC : IsEtaChain C) {x : α} (hx : x ∈ C) :
    ∃ y ∈ C, y < x := by
  obtain ⟨e⟩ := hC
  let x' : C := ⟨x, hx⟩
  obtain ⟨q, hq⟩ := NoMinOrder.exists_lt (e.symm x')
  refine ⟨(e q).1, (e q).2, ?_⟩
  change e q < x'
  simpa only [e.apply_symm_apply] using e.lt_iff_lt.mpr hq

theorem IsEtaChain.exists_gt {C : Set α} (hC : IsEtaChain C) {x : α} (hx : x ∈ C) :
    ∃ y ∈ C, x < y := by
  obtain ⟨e⟩ := hC
  let x' : C := ⟨x, hx⟩
  obtain ⟨q, hq⟩ := NoMaxOrder.exists_gt (e.symm x')
  refine ⟨(e q).1, (e q).2, ?_⟩
  change x' < e q
  simpa only [e.apply_symm_apply] using e.lt_iff_lt.mpr hq

/-- Cantor's characterization of the rationals, in a set-level form convenient for this project. -/
theorem isEtaChain_of_countable_dense [Countable α] {C : Set α}
    (hchain : IsChain (· ≤ ·) C) (hne : C.Nonempty)
    (hdense : ∀ ⦃x y⦄, x ∈ C → y ∈ C → x < y → ∃ z ∈ C, x < z ∧ z < y)
    (hleft : ∀ x ∈ C, ∃ y ∈ C, y < x)
    (hright : ∀ x ∈ C, ∃ y ∈ C, x < y) : IsEtaChain C := by
  classical
  let : LinearOrder C := hchain.linearOrder
  let : Nonempty C := hne.to_subtype
  let : DenselyOrdered C := ⟨by
    intro x y hxy
    obtain ⟨z, hz, hxz, hzy⟩ := hdense x.2 y.2 hxy
    exact ⟨⟨z, hz⟩, hxz, hzy⟩⟩
  let : NoMinOrder C := ⟨by
    intro x
    obtain ⟨y, hy, hyx⟩ := hleft x.1 x.2
    exact ⟨⟨y, hy⟩, hyx⟩⟩
  let : NoMaxOrder C := ⟨by
    intro x
    obtain ⟨y, hy, hxy⟩ := hright x.1 x.2
    exact ⟨⟨y, hy⟩, hxy⟩⟩
  exact Order.iso_of_countable_dense ℚ C

/-- Every eta-chain in a countable poset extends to an inclusion-maximal eta-chain. -/
theorem IsEtaChain.exists_etaMaximal [Countable α] {C : Set α} (hC : IsEtaChain C) :
    ∃ D : Set α, C ⊆ D ∧ IsEtaMaximalChain D := by
  classical
  let candidates : Set (Set α) := {D | C ⊆ D ∧ IsEtaChain D}
  obtain ⟨D, hCD, hDmax⟩ := zorn_subset_nonempty candidates (by
      intro c hcandidates hchain hcnonempty
      let U : Set α := ⋃₀ c
      have hCU : C ⊆ U := by
        obtain ⟨E, hEc⟩ := hcnonempty
        exact (hcandidates hEc).1.trans (Set.subset_sUnion_of_mem hEc)
      have hUchain : IsChain (· ≤ ·) U := by
        intro x hx y hy hxy
        change x ∈ ⋃₀ c at hx
        change y ∈ ⋃₀ c at hy
        obtain ⟨X, hXc, hxX⟩ := hx
        obtain ⟨Y, hYc, hyY⟩ := hy
        rcases eq_or_ne X Y with rfl | hXY
        · exact (hcandidates hXc).2.isChain hxX hyY hxy
        · rcases hchain hXc hYc hXY with hsub | hsub
          · exact (hcandidates hYc).2.isChain (hsub hxX) hyY hxy
          · exact (hcandidates hXc).2.isChain hxX (hsub hyY) hxy
      have hUdense : ∀ ⦃x y⦄, x ∈ U → y ∈ U → x < y →
          ∃ z ∈ U, x < z ∧ z < y := by
        intro x y hx hy hxy
        change x ∈ ⋃₀ c at hx
        change y ∈ ⋃₀ c at hy
        obtain ⟨X, hXc, hxX⟩ := hx
        obtain ⟨Y, hYc, hyY⟩ := hy
        rcases eq_or_ne X Y with rfl | hXY
        · obtain ⟨z, hz, hxz, hzy⟩ := (hcandidates hXc).2.exists_between hxX hyY hxy
          exact ⟨z, Set.mem_sUnion_of_mem hz hXc, hxz, hzy⟩
        · rcases hchain hXc hYc hXY with hsub | hsub
          · obtain ⟨z, hz, hxz, hzy⟩ := (hcandidates hYc).2.exists_between (hsub hxX) hyY hxy
            exact ⟨z, Set.mem_sUnion_of_mem hz hYc, hxz, hzy⟩
          · obtain ⟨z, hz, hxz, hzy⟩ := (hcandidates hXc).2.exists_between hxX (hsub hyY) hxy
            exact ⟨z, Set.mem_sUnion_of_mem hz hXc, hxz, hzy⟩
      have hUeta : IsEtaChain U := isEtaChain_of_countable_dense hUchain (hC.nonempty.mono hCU)
        hUdense
        (fun x hx => by
          change x ∈ ⋃₀ c at hx
          obtain ⟨X, hXc, hxX⟩ := hx
          obtain ⟨y, hy, hyx⟩ := (hcandidates hXc).2.exists_lt hxX
          exact ⟨y, Set.mem_sUnion_of_mem hy hXc, hyx⟩)
        (fun x hx => by
          change x ∈ ⋃₀ c at hx
          obtain ⟨X, hXc, hxX⟩ := hx
          obtain ⟨y, hy, hxy⟩ := (hcandidates hXc).2.exists_gt hxX
          exact ⟨y, Set.mem_sUnion_of_mem hy hXc, hxy⟩)
      exact ⟨U, ⟨hCU, hUeta⟩, fun E hEc => Set.subset_sUnion_of_mem hEc⟩) C ⟨Subset.rfl, hC⟩
  refine ⟨D, hCD, (hDmax.prop).2, fun E hE hDE => ?_⟩
  exact (hDmax.eq_of_subset ⟨hCD.trans hDE, hE⟩ hDE).symm

/-- Paper Lemma `lem:eta-nesting`, in the set-level form used by replacement composition: a
rationally indexed sum of nonempty singleton-or-eta blocks has order type eta. -/
theorem eta_nesting [Countable α] (B : ℚ → Set α)
    (hne : ∀ q, (B q).Nonempty)
    (hshape : ∀ q, (∃ x, B q = {x}) ∨ IsEtaChain (B q))
    (hordered : ∀ ⦃p q : ℚ⦄, p < q → SetStrictLT (B p) (B q)) :
    IsEtaChain (⋃ q, B q) := by
  classical
  let U : Set α := ⋃ q, B q
  have hmem (q : ℚ) : B q ⊆ U := fun _ hx => Set.mem_iUnion_of_mem q hx
  have hUchain : IsChain (· ≤ ·) U := by
    intro x hx y hy hxy
    change x ∈ ⋃ q, B q at hx
    change y ∈ ⋃ q, B q at hy
    simp only [Set.mem_iUnion] at hx hy
    obtain ⟨p, hxp⟩ := hx
    obtain ⟨q, hyq⟩ := hy
    rcases lt_trichotomy p q with hpq | hpq | hqp
    · exact Or.inl (hordered hpq hxp hyq).le
    · subst q
      rcases hshape p with ⟨z, hz⟩ | heta
      · rw [hz] at hxp hyq
        simp only [Set.mem_singleton_iff] at hxp hyq
        exact False.elim (hxy (hxp.trans hyq.symm))
      · exact heta.isChain hxp hyq hxy
    · exact Or.inr (hordered hqp hyq hxp).le
  have hUdense : ∀ ⦃x y⦄, x ∈ U → y ∈ U → x < y →
      ∃ z ∈ U, x < z ∧ z < y := by
    intro x y hx hy hxy
    change x ∈ ⋃ q, B q at hx
    change y ∈ ⋃ q, B q at hy
    simp only [Set.mem_iUnion] at hx hy
    obtain ⟨p, hxp⟩ := hx
    obtain ⟨q, hyq⟩ := hy
    rcases lt_trichotomy p q with hpq | hpq | hqp
    · obtain ⟨r, hpr, hrq⟩ := DenselyOrdered.dense p q hpq
      obtain ⟨z, hzr⟩ := hne r
      exact ⟨z, hmem r hzr, hordered hpr hxp hzr, hordered hrq hzr hyq⟩
    · subst q
      rcases hshape p with ⟨z, hz⟩ | heta
      · rw [hz] at hxp hyq
        simp only [Set.mem_singleton_iff] at hxp hyq
        exact False.elim (hxy.ne (hxp.trans hyq.symm))
      · obtain ⟨z, hz, hxz, hzy⟩ := heta.exists_between hxp hyq hxy
        exact ⟨z, hmem p hz, hxz, hzy⟩
    · exact False.elim ((not_lt_of_ge hxy.le) (hordered hqp hyq hxp))
  have hUne : U.Nonempty := (hne 0).mono (hmem 0)
  apply isEtaChain_of_countable_dense hUchain hUne hUdense
  · intro x hx
    change x ∈ ⋃ q, B q at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨q, hxq⟩ := hx
    obtain ⟨p, hpq⟩ := NoMinOrder.exists_lt q
    obtain ⟨y, hyp⟩ := hne p
    exact ⟨y, hmem p hyp, hordered hpq hyp hxq⟩
  · intro x hx
    change x ∈ ⋃ q, B q at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨q, hxq⟩ := hx
    obtain ⟨p, hqp⟩ := NoMaxOrder.exists_gt q
    obtain ⟨y, hyp⟩ := hne p
    exact ⟨y, hmem p hyp, hordered hqp hxq hyp⟩

/-- Taking the convex hull inside an eta-chain preserves order type eta. -/
theorem etaChain_convexHullIn [Countable α] {S D : Set α} (hS : IsEtaChain S)
    (hSD : S ⊆ D) (hD : IsEtaChain D) : IsEtaChain (convexHullIn D S) := by
  let H := convexHullIn D S
  have hHD : H ⊆ D := convexHullIn_subset D S
  have hinterval : IsIntervalIn H D := convexHullIn_interval D S
  have hchain : IsChain (· ≤ ·) H := fun x hx y hy hxy =>
    hD.isChain (hHD hx) (hHD hy) hxy
  have hne : H.Nonempty := hS.nonempty.mono (subset_convexHullIn hSD)
  apply isEtaChain_of_countable_dense hchain hne
  · intro x y hx hy hxy
    obtain ⟨z, hzD, hxz, hzy⟩ := hD.exists_between (hHD hx) (hHD hy) hxy
    exact ⟨z, hinterval.2 hx hy hxy.le hzD hxz.le hzy.le, hxz, hzy⟩
  · intro x hx
    obtain ⟨hxD, a, ha, b, hb, hax, hxb⟩ := hx
    obtain ⟨y, hy, hya⟩ := hS.exists_lt ha
    exact ⟨y, subset_convexHullIn hSD hy, hya.trans_le hax⟩
  · intro x hx
    obtain ⟨hxD, a, ha, b, hb, hax, hxb⟩ := hx
    obtain ⟨y, hy, hby⟩ := hS.exists_gt hb
    exact ⟨y, subset_convexHullIn hSD hy, hxb.trans_lt hby⟩

theorem IsEtaChain.upperSection [Countable α] {S : Set α} (hS : IsEtaChain S)
    {a : α} (ha : a ∈ S) : IsEtaChain (S ∩ Set.Ioi a) := by
  have hsub : S ∩ Set.Ioi a ⊆ S := Set.inter_subset_left
  apply isEtaChain_of_countable_dense
    (fun x hx y hy hxy => hS.isChain (hsub hx) (hsub hy) hxy)
  · obtain ⟨x, hx, hax⟩ := hS.exists_gt ha
    exact ⟨x, hx, hax⟩
  · intro x y hx hy hxy
    obtain ⟨z, hz, hxz, hzy⟩ := hS.exists_between hx.1 hy.1 hxy
    exact ⟨z, ⟨hz, hx.2.trans hxz⟩, hxz, hzy⟩
  · intro x hx
    obtain ⟨y, hy, hay, hyx⟩ := hS.exists_between ha hx.1 hx.2
    exact ⟨y, ⟨hy, hay⟩, hyx⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hS.exists_gt hx.1
    exact ⟨y, ⟨hy, hx.2.trans hxy⟩, hxy⟩

theorem IsEtaChain.lowerSection [Countable α] {S : Set α} (hS : IsEtaChain S)
    {a : α} (ha : a ∈ S) : IsEtaChain (S ∩ Set.Iio a) := by
  have hsub : S ∩ Set.Iio a ⊆ S := Set.inter_subset_left
  apply isEtaChain_of_countable_dense
    (fun x hx y hy hxy => hS.isChain (hsub hx) (hsub hy) hxy)
  · obtain ⟨x, hx, hxa⟩ := hS.exists_lt ha
    exact ⟨x, hx, hxa⟩
  · intro x y hx hy hxy
    obtain ⟨z, hz, hxz, hzy⟩ := hS.exists_between hx.1 hy.1 hxy
    exact ⟨z, ⟨hz, hzy.trans hy.2⟩, hxz, hzy⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hS.exists_lt hx.1
    exact ⟨y, ⟨hy, hyx.trans hx.2⟩, hyx⟩
  · intro x hx
    obtain ⟨y, hy, hxy, hya⟩ := hS.exists_between hx.1 ha hx.2
    exact ⟨y, ⟨hy, hya⟩, hxy⟩

/-- Inserting a dense fibre immediately above one point of an eta-chain again gives an eta-chain. -/
theorem etaChain_union_fiber_above [Countable α] {C Y : Set α} {x : α}
    (hC : IsEtaChain C) (hx : x ∈ C) (hY : IsEtaChain Y)
    (hbelow : ∀ c ∈ C, c < x → ∀ y ∈ Y, c < y)
    (habove : ∀ c ∈ C, x < c → ∀ y ∈ Y, y < c)
    (hxY : ∀ y ∈ Y, x < y) : IsEtaChain (C ∪ Y) := by
  have hchain : IsChain (· ≤ ·) (C ∪ Y) := by
    intro a ha b hb hab
    rcases ha with haC | haY <;> rcases hb with hbC | hbY
    · exact hC.isChain haC hbC hab
    · by_cases hax : a = x
      · exact Or.inl (hax ▸ hxY b hbY).le
      · rcases hC.isChain haC hx hax with hle | hge
        · exact Or.inl (hbelow a haC (lt_of_le_of_ne hle hax) b hbY).le
        · exact Or.inr (habove a haC (lt_of_le_of_ne hge (Ne.symm hax)) b hbY).le
    · by_cases hbx : b = x
      · exact Or.inr (hbx ▸ hxY a haY).le
      · rcases hC.isChain hbC hx hbx with hle | hge
        · exact Or.inr (hbelow b hbC (lt_of_le_of_ne hle hbx) a haY).le
        · exact Or.inl (habove b hbC (lt_of_le_of_ne hge (Ne.symm hbx)) a haY).le
    · exact hY.isChain haY hbY hab
  apply isEtaChain_of_countable_dense hchain (hC.nonempty.mono Set.subset_union_left)
  · intro a b ha hb hab
    rcases ha with haC | haY <;> rcases hb with hbC | hbY
    · obtain ⟨z, hz, haz, hzb⟩ := hC.exists_between haC hbC hab
      exact ⟨z, Or.inl hz, haz, hzb⟩
    · by_cases hax : a = x
      · obtain ⟨z, hz, hzb⟩ := hY.exists_lt hbY
        exact ⟨z, Or.inr hz, hax ▸ hxY z hz, hzb⟩
      · rcases hC.isChain haC hx hax with hle | hge
        · obtain ⟨z, hz, haz, hzx⟩ := hC.exists_between haC hx (lt_of_le_of_ne hle hax)
          exact ⟨z, Or.inl hz, haz, hzx.trans (hxY b hbY)⟩
        · exact False.elim (asymm hab (habove a haC (lt_of_le_of_ne hge (Ne.symm hax)) b hbY))
    · by_cases hbx : b = x
      · exact False.elim (asymm hab (hbx ▸ hxY a haY))
      · rcases hC.isChain hx hbC (Ne.symm hbx) with hle | hge
        · obtain ⟨z, hz, hxz, hzb⟩ := hC.exists_between hx hbC (lt_of_le_of_ne hle (Ne.symm hbx))
          exact ⟨z, Or.inl hz, (habove z hz hxz a haY), hzb⟩
        · exact False.elim (asymm hab (hbelow b hbC (lt_of_le_of_ne hge hbx) a haY))
    · obtain ⟨z, hz, haz, hzb⟩ := hY.exists_between haY hbY hab
      exact ⟨z, Or.inr hz, haz, hzb⟩
  · intro a ha
    rcases ha with haC | haY
    · obtain ⟨z, hz, hza⟩ := hC.exists_lt haC
      exact ⟨z, Or.inl hz, hza⟩
    · obtain ⟨z, hz, hzx⟩ := hC.exists_lt hx
      exact ⟨z, Or.inl hz, hbelow z hz hzx a haY⟩
  · intro a ha
    rcases ha with haC | haY
    · obtain ⟨z, hz, haz⟩ := hC.exists_gt haC
      exact ⟨z, Or.inl hz, haz⟩
    · obtain ⟨z, hz, hxz⟩ := hC.exists_gt hx
      exact ⟨z, Or.inl hz, habove z hz hxz a haY⟩

private def ratOrderIsoDual : ℚ ≃o ℚᵒᵈ where
  toFun q := OrderDual.toDual (-q)
  invFun q := -q.ofDual
  left_inv q := by simp
  right_inv q := by
    change OrderDual.toDual (- -q.ofDual) = q
    simp
  map_rel_iff' := by
    intro p q
    change -q ≤ -p ↔ p ≤ q
    simp

private def subtypeOrderDualIso (S : Set α) :
    OrderDual S ≃o (show Set αᵒᵈ from S) where
  toFun x := ⟨x.ofDual.1, x.ofDual.2⟩
  invFun x := OrderDual.toDual ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intros; rfl

/-- The order-dual version of `etaChain_union_fiber_above`. -/
theorem etaChain_union_fiber_below [Countable α] {C Y : Set α} {x : α}
    (hC : IsEtaChain C) (hx : x ∈ C) (hY : IsEtaChain Y)
    (hbelow : ∀ c ∈ C, c < x → ∀ y ∈ Y, c < y)
    (habove : ∀ c ∈ C, x < c → ∀ y ∈ Y, y < c)
    (hYx : ∀ y ∈ Y, y < x) : IsEtaChain (C ∪ Y) := by
  let : Countable αᵒᵈ := ‹Countable α›
  have hCdual : @IsEtaChain αᵒᵈ inferInstance C := by
    obtain ⟨e⟩ := hC
    exact ⟨ratOrderIsoDual.trans (e.dual.trans (subtypeOrderDualIso C))⟩
  have hYdual : @IsEtaChain αᵒᵈ inferInstance Y := by
    obtain ⟨e⟩ := hY
    exact ⟨ratOrderIsoDual.trans (e.dual.trans (subtypeOrderDualIso Y))⟩
  have hdual : @IsEtaChain αᵒᵈ inferInstance (C ∪ Y) :=
    @etaChain_union_fiber_above αᵒᵈ inferInstance _ C Y x hCdual hx hYdual
      (fun c hc hxc y hy => habove c hc hxc y hy)
      (fun c hc hcx y hy => hbelow c hc hcx y hy)
      (fun y hy => hYx y hy)
  obtain ⟨e⟩ := hdual
  exact ⟨ratOrderIsoDual.trans
    (e.dual.trans (@subtypeOrderDualIso αᵒᵈ inferInstance (C ∪ Y)))⟩

end AharoniKorman
