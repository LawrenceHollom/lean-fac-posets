import AharoniKorman.Structural.EtaReplacement
import Mathlib.Data.EReal.Basic
import Mathlib.Order.Interval.Set.Infinite

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- The cut piece determined by `r` and a rationally indexed eta-chain.  This is the set denoted
`A_r` in the proof of Theorem 1.4. -/
def etaPiece {C : Set α} (e : ℚ ≃o C) (r : EReal) : Set α :=
  {x | (∀ q : ℚ, ((q : ℝ) : EReal) < r → (e q).1 < x) ∧
    (∀ q : ℚ, r < ((q : ℝ) : EReal) → x < (e q).1)}

theorem etaPiece_rational_mem {C : Set α} (e : ℚ ≃o C) (q : ℚ) :
    (e q).1 ∈ etaPiece e ((q : ℝ) : EReal) := by
  constructor
  · intro p hp
    exact e.lt_iff_lt.mpr (by exact_mod_cast EReal.coe_lt_coe_iff.mp hp)
  · intro p hp
    exact e.lt_iff_lt.mpr (by exact_mod_cast EReal.coe_lt_coe_iff.mp hp)

theorem etaPiece_ordered {C : Set α} (e : ℚ ≃o C) {r s : EReal} (hrs : r < s) :
    SetStrictLT (etaPiece e r) (etaPiece e s) := by
  obtain ⟨q, hrq, hqs⟩ := EReal.exists_rat_btwn_of_lt hrs
  intro x hx y hy
  exact (hx.2 q hrq).trans (hy.1 q hqs)

theorem etaPiece_ordConnected {C : Set α} (e : ℚ ≃o C) (r : EReal) :
    (etaPiece e r).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  constructor
  · intro q hqr
    exact (hx.1 q hqr).trans_le hz.1
  · intro q hrq
    exact hz.2.trans_lt (hy.2 q hrq)

/-- At a non-rational cut, adjoining an eta-chain contained in the cut piece to the original
eta-chain again gives an eta-chain. -/
theorem etaChain_union_etaPiece_of_not_rational [Countable α] {C S : Set α}
    (e : ℚ ≃o C) (r : EReal) (hS : IsEtaChain S) (hSr : S ⊆ etaPiece e r)
    (hirr : ∀ q : ℚ, r ≠ ((q : ℝ) : EReal)) : IsEtaChain (C ∪ S) := by
  have hC : IsEtaChain C := ⟨e⟩
  have cut_cases (q : ℚ) : ((q : ℝ) : EReal) < r ∨ r < ((q : ℝ) : EReal) := by
    rcases lt_trichotomy ((q : ℝ) : EReal) r with h | h | h
    · exact Or.inl h
    · exact False.elim (hirr q h.symm)
    · exact Or.inr h
  have hchain : IsChain (· ≤ ·) (C ∪ S) := by
    intro x hx y hy hxy
    rcases hx with hxC | hxS <;> rcases hy with hyC | hyS
    · exact hC.isChain hxC hyC hxy
    · let q := e.symm ⟨x, hxC⟩
      rcases cut_cases q with hqr | hrq
      · exact Or.inl (by
          have := (hSr hyS).1 q hqr
          simpa only [q, e.apply_symm_apply] using this.le)
      · exact Or.inr (by
          have := (hSr hyS).2 q hrq
          simpa only [q, e.apply_symm_apply] using this.le)
    · let q := e.symm ⟨y, hyC⟩
      rcases cut_cases q with hqr | hrq
      · exact Or.inr (by
          have := (hSr hxS).1 q hqr
          simpa only [q, e.apply_symm_apply] using this.le)
      · exact Or.inl (by
          have := (hSr hxS).2 q hrq
          simpa only [q, e.apply_symm_apply] using this.le)
    · exact hS.isChain hxS hyS hxy
  apply isEtaChain_of_countable_dense hchain (hC.nonempty.mono Set.subset_union_left)
  · intro x y hx hy hxy
    rcases hx with hxC | hxS <;> rcases hy with hyC | hyS
    · obtain ⟨z, hz, hxz, hzy⟩ := hC.exists_between hxC hyC hxy
      exact ⟨z, Or.inl hz, hxz, hzy⟩
    · let q := e.symm ⟨x, hxC⟩
      have hqr : ((q : ℝ) : EReal) < r := by
        rcases cut_cases q with h | h
        · exact h
        · have hyx : y < x := by
            have := (hSr hyS).2 q h
            simpa only [q, e.apply_symm_apply] using this
          exact False.elim (asymm hxy hyx)
      obtain ⟨p, hqp, hpr⟩ := EReal.exists_rat_btwn_of_lt hqr
      refine ⟨(e p).1, Or.inl (e p).2, ?_, ?_⟩
      · have : (e q).1 < (e p).1 :=
          e.lt_iff_lt.mpr (by exact_mod_cast EReal.coe_lt_coe_iff.mp hqp)
        simpa only [q, e.apply_symm_apply] using this
      · exact (hSr hyS).1 p hpr
    · let q := e.symm ⟨y, hyC⟩
      have hrq : r < ((q : ℝ) : EReal) := by
        rcases cut_cases q with h | h
        · have hyx : y < x := by
            have := (hSr hxS).1 q h
            simpa only [q, e.apply_symm_apply] using this
          exact False.elim (asymm hxy hyx)
        · exact h
      obtain ⟨p, hrp, hpq⟩ := EReal.exists_rat_btwn_of_lt hrq
      refine ⟨(e p).1, Or.inl (e p).2, ?_, ?_⟩
      · exact (hSr hxS).2 p hrp
      · have : (e p).1 < (e q).1 :=
          e.lt_iff_lt.mpr (by exact_mod_cast EReal.coe_lt_coe_iff.mp hpq)
        simpa only [q, e.apply_symm_apply] using this
    · obtain ⟨z, hz, hxz, hzy⟩ := hS.exists_between hxS hyS hxy
      exact ⟨z, Or.inr hz, hxz, hzy⟩
  · intro x hx
    rcases hx with hxC | hxS
    · obtain ⟨y, hy, hyx⟩ := hC.exists_lt hxC
      exact ⟨y, Or.inl hy, hyx⟩
    · obtain ⟨y, hy, hyx⟩ := hS.exists_lt hxS
      exact ⟨y, Or.inr hy, hyx⟩
  · intro x hx
    rcases hx with hxC | hxS
    · obtain ⟨y, hy, hxy⟩ := hC.exists_gt hxC
      exact ⟨y, Or.inl hy, hxy⟩
    · obtain ⟨y, hy, hxy⟩ := hS.exists_gt hxS
      exact ⟨y, Or.inr hy, hxy⟩

/-- An eta-chain lying in a rational cut piece is pointwise incomparable with the rational point
of the original eta-maximal chain.  Otherwise a one-sided eta tail could be adjoined to that
chain, contradicting eta-maximality. -/
theorem etaChain_in_rationalPiece_incomparable [Countable α] {C S : Set α}
    (hC : IsEtaMaximalChain C) (e : ℚ ≃o C) (q : ℚ)
    (hS : IsEtaChain S) (hSq : S ⊆ etaPiece e ((q : ℝ) : EReal)) :
    ∀ y ∈ S, Incomparable y (e q).1 := by
  intro y hy
  constructor
  · intro hyc
    obtain ⟨z, hz, hzy⟩ := hS.exists_lt hy
    let Y := S ∩ Set.Iio y
    have hY : IsEtaChain Y := hS.lowerSection hy
    have hUnion : IsEtaChain (C ∪ Y) := etaChain_union_fiber_below hC.1 (e q).2 hY
      (fun c hc hcq w hw => by
        let p := e.symm ⟨c, hc⟩
        have hcq' : (⟨c, hc⟩ : C) < e q := hcq
        have hpq : p < q := e.lt_iff_lt.mp (by
          simpa only [p, e.apply_symm_apply] using hcq')
        have hpq' : ((p : ℝ) : EReal) < ((q : ℝ) : EReal) := by exact_mod_cast hpq
        have := (hSq hw.1).1 p hpq'
        simpa only [p, e.apply_symm_apply] using this)
      (fun c hc hqc w hw => hw.2.trans (hyc.trans_lt hqc))
      (fun w hw => hw.2.trans_le hyc)
    have hEq := hC.2 (C ∪ Y) hUnion Set.subset_union_left
    have hzY : z ∈ Y := ⟨hz, hzy⟩
    have hzNotC : z ∉ C := by
      intro hzC
      let p := e.symm ⟨z, hzC⟩
      have hzq : (⟨z, hzC⟩ : C) < e q := hzy.trans_le hyc
      have hpq : p < q := e.lt_iff_lt.mp (by
        simpa only [p, e.apply_symm_apply] using hzq)
      have hpq' : ((p : ℝ) : EReal) < ((q : ℝ) : EReal) := by exact_mod_cast hpq
      have hbad := (hSq hz).1 p hpq'
      have : z < z := by simpa only [p, e.apply_symm_apply] using hbad
      exact this.false
    exact hzNotC (by rw [← hEq]; exact Or.inr hzY)
  · intro hcy
    obtain ⟨z, hz, hyz⟩ := hS.exists_gt hy
    let Y := S ∩ Set.Ioi y
    have hY : IsEtaChain Y := hS.upperSection hy
    have hUnion : IsEtaChain (C ∪ Y) := etaChain_union_fiber_above hC.1 (e q).2 hY
      (fun c hc hcq w hw => hcq.trans_le (hcy.trans_lt hw.2).le)
      (fun c hc hqc w hw => by
        let p := e.symm ⟨c, hc⟩
        have hqc' : e q < (⟨c, hc⟩ : C) := hqc
        have hqp : q < p := e.lt_iff_lt.mp (by
          simpa only [p, e.apply_symm_apply] using hqc')
        have hqp' : ((q : ℝ) : EReal) < ((p : ℝ) : EReal) := by exact_mod_cast hqp
        have := (hSq hw.1).2 p hqp'
        simpa only [p, e.apply_symm_apply] using this)
      (fun w hw => hcy.trans_lt hw.2)
    have hEq := hC.2 (C ∪ Y) hUnion Set.subset_union_left
    have hzY : z ∈ Y := ⟨hz, hyz⟩
    have hzNotC : z ∉ C := by
      intro hzC
      let p := e.symm ⟨z, hzC⟩
      have hqz : e q < (⟨z, hzC⟩ : C) := hcy.trans_lt hyz
      have hqp : q < p := e.lt_iff_lt.mp (by
        simpa only [p, e.apply_symm_apply] using hqz)
      have hqp' : ((q : ℝ) : EReal) < ((p : ℝ) : EReal) := by exact_mod_cast hqp
      have hbad := (hSq hz).2 p hqp'
      have : z < z := by simpa only [p, e.apply_symm_apply] using hbad
      exact this.false
    exact hzNotC (by rw [← hEq]; exact Or.inr hzY)

private def rationalReplacementCore {C : Set α} (e : ℚ ≃o C) (q : ℚ) (S : Set α) : Set α :=
  ⋃ p : ℚ, if p = q then S else {(e p).1}

private theorem rationalReplacementCore_eta [Countable α] {C S : Set α}
    (e : ℚ ≃o C) (q : ℚ) (hS : IsEtaChain S)
    (hSq : S ⊆ etaPiece e ((q : ℝ) : EReal)) :
    IsEtaChain (rationalReplacementCore e q S) := by
  let B : ℚ → Set α := fun p => if p = q then S else {(e p).1}
  have hBne : ∀ p, (B p).Nonempty := by
    intro p
    by_cases hpq : p = q
    · simpa [B, hpq] using hS.nonempty
    · simp [B, hpq]
  have hBshape : ∀ p, (∃ x, B p = {x}) ∨ IsEtaChain (B p) := by
    intro p
    by_cases hpq : p = q
    · exact Or.inr (by simpa [B, hpq] using hS)
    · exact Or.inl ⟨(e p).1, by simp [B, hpq]⟩
  have hBordered : ∀ ⦃p r : ℚ⦄, p < r → SetStrictLT (B p) (B r) := by
    intro p r hpr x hx y hy
    by_cases hpq : p = q
    · subst p
      have hrq : r ≠ q := ne_of_gt hpr
      have hqr' : ((q : ℝ) : EReal) < ((r : ℝ) : EReal) := by exact_mod_cast hpr
      have hxS : x ∈ S := by simpa [B] using hx
      have hyr : y = (e r).1 := by simpa [B, hrq] using hy
      simpa [hyr] using (hSq hxS).2 r hqr'
    · by_cases hrq : r = q
      · subst r
        have hpq' : ((p : ℝ) : EReal) < ((q : ℝ) : EReal) := by exact_mod_cast hpr
        have hxp : x = (e p).1 := by simpa [B, hpq] using hx
        have hyS : y ∈ S := by simpa [B] using hy
        simpa [hxp] using (hSq hyS).1 p hpq'
      · have hxp : x = (e p).1 := by simpa [B, hpq] using hx
        have hyr : y = (e r).1 := by simpa [B, hrq] using hy
        simpa [hxp, hyr] using e.lt_iff_lt.mpr hpr
  simpa only [rationalReplacementCore, B] using eta_nesting B hBne hBshape hBordered

private theorem rationalReplacementCore_contains_other {C S : Set α}
    (e : ℚ ≃o C) (q p : ℚ) (hpq : p ≠ q) :
    (e p).1 ∈ rationalReplacementCore e q S := by
  apply Set.mem_iUnion_of_mem p
  simp [hpq]

/-- Replacing the rational point `e q` by an eta-chain in its cut piece yields a nontrivial
eta-replacement, provided that chain is incomparable with `e q`. -/
theorem etaReplacement_at_rational_piece [Countable α] {C S : Set α}
    (hC : IsEtaMaximalChain C) (e : ℚ ≃o C) (q : ℚ)
    (hS : IsEtaChain S) (hSq : S ⊆ etaPiece e ((q : ℝ) : EReal)) :
    ∃ D : Set α, ∃ f : EtaReplacement C D, ¬ f.Trivial := by
  classical
  let U := rationalReplacementCore e q S
  have hUeta : IsEtaChain U := rationalReplacementCore_eta e q hS hSq
  obtain ⟨D, hUD, hD⟩ := hUeta.exists_etaMaximal
  have other_mem_D (x : C) (hxq : x.1 ≠ (e q).1) : x.1 ∈ D := by
    let p := e.symm x
    have hpq : p ≠ q := by
      intro hpq
      apply hxq
      calc
        x.1 = (e p).1 := congrArg Subtype.val (e.apply_symm_apply x).symm
        _ = (e q).1 := congrArg Subtype.val (congrArg e hpq)
    apply hUD
    have := rationalReplacementCore_contains_other (S := S) e q p hpq
    simpa only [p, e.apply_symm_apply] using this
  let F : C → Set α := fun x =>
    if hxq : x.1 = (e q).1 then convexHullIn D S else {x.1}
  have hSsubD : S ⊆ D := by
    intro y hy
    apply hUD
    apply Set.mem_iUnion_of_mem q
    simpa [rationalReplacementCore] using hy
  let f : EtaReplacement C D :=
    { source := hC
      target := hD
      image := F
      image_nonempty := fun x => by
        by_cases hxq : x.1 = (e q).1
        · exact hS.nonempty.mono (by
            simpa [F, hxq] using (subset_convexHullIn hSsubD : S ⊆ convexHullIn D S))
        · simp [F, hxq]
      image_interval := fun x => by
        by_cases hxq : x.1 = (e q).1
        · simpa [F, hxq] using convexHullIn_interval D S
        · refine ⟨by simpa [F, hxq] using other_mem_D x hxq, ?_⟩
          rintro z hz w hw hzw a haD hza haw
          have hz' : z = x.1 := by simpa [F, hxq] using hz
          have hw' : w = x.1 := by simpa [F, hxq] using hw
          subst z
          subst w
          have haz : a = x.1 := le_antisymm haw hza
          subst a
          simp [F, hxq]
      image_shape := fun x => by
        by_cases hxq : x.1 = (e q).1
        · right
          simpa [F, hxq] using etaChain_convexHullIn hS hSsubD hD.1
        · left
          simp [F, hxq]
      source_lt_image := fun x y hxy z hz => by
        by_cases hyq : y.1 = (e q).1
        · let p := e.symm x
          have hpq : p < q := e.lt_iff_lt.mp (by
            have hxq' : x.1 < (e q).1 := hxy.trans_eq hyq
            have : x < e q := hxq'
            simpa only [p, e.apply_symm_apply] using this)
          have hpq' : ((p : ℝ) : EReal) < ((q : ℝ) : EReal) := by exact_mod_cast hpq
          have hzHull : z ∈ convexHullIn D S := by simpa [F, hyq] using hz
          obtain ⟨_, a, haS, b, hbS, haz, hzb⟩ := hzHull
          have hxa := (hSq haS).1 p hpq'
          simpa only [p, e.apply_symm_apply] using hxa.trans_le haz
        · have hzEq : z = y.1 := by simpa [F, hyq] using hz
          simpa only [hzEq] using hxy
      image_lt_source := fun x y hxy z hz => by
        by_cases hxq : x.1 = (e q).1
        · let p := e.symm y
          have hqp : q < p := e.lt_iff_lt.mp (by
            have hqy' : (e q).1 < y.1 := hxq.symm.trans_lt hxy
            have : e q < y := hqy'
            simpa only [p, e.apply_symm_apply] using this)
          have hqp' : ((q : ℝ) : EReal) < ((p : ℝ) : EReal) := by exact_mod_cast hqp
          have hzHull : z ∈ convexHullIn D S := by simpa [F, hxq] using hz
          obtain ⟨_, a, haS, b, hbS, haz, hzb⟩ := hzHull
          have hby := (hSq hbS).2 p hqp'
          simpa only [p, e.apply_symm_apply] using hzb.trans_lt hby
        · have hzEq : z = x.1 := by simpa [F, hxq] using hz
          simpa only [hzEq] using hxy }
  refine ⟨D, f, ?_⟩
  intro htriv
  have heta : IsEtaChain (f.image (e q)) := by
    simpa [f, F] using etaChain_convexHullIn hS hSsubD hD.1
  have hsingleton := htriv (e q)
  rw [hsingleton] at heta
  exact heta.infinite (Set.finite_singleton (e q).1)

/-- Every cut piece associated with an eta-strongly-maximal chain is scattered. -/
theorem etaPiece_scattered_of_etaStronglyMaximal [Countable α] {C : Set α}
    (hC : IsEtaStronglyMaximal C) (e : ℚ ≃o C) (r : EReal) :
    IsScattered (etaPiece e r) := by
  rintro ⟨k⟩
  let S : Set α := Set.range (fun q : ℚ => (k q).1)
  have hkInjective : Function.Injective (fun q : ℚ => (k q).1) :=
    Subtype.val_injective.comp k.injective
  let k' : ℚ ≃o S :=
    { toEquiv := Equiv.ofInjective (fun q : ℚ => (k q).1) hkInjective
      map_rel_iff' := fun {_ _} => k.le_iff_le }
  have hS : IsEtaChain S := ⟨k'⟩
  have hSr : S ⊆ etaPiece e r := by
    rintro _ ⟨q, rfl⟩
    exact (k q).2
  by_cases hrat : ∃ q : ℚ, r = ((q : ℝ) : EReal)
  · obtain ⟨q, rfl⟩ := hrat
    obtain ⟨D, f, hf⟩ := etaReplacement_at_rational_piece hC.1 e q hS hSr
    exact hf (hC.2 D f)
  · have hirr : ∀ q : ℚ, r ≠ ((q : ℝ) : EReal) := by
      intro q hq
      exact hrat ⟨q, hq⟩
    have hUnion := etaChain_union_etaPiece_of_not_rational e r hS hSr hirr
    have hEq := hC.1.2 (C ∪ S) hUnion Set.subset_union_left
    obtain ⟨y, hyS⟩ := hS.nonempty
    have hyC : y ∈ C := by
      rw [← hEq]
      exact Or.inr hyS
    let q := e.symm ⟨y, hyC⟩
    rcases lt_trichotomy ((q : ℝ) : EReal) r with hqr | heq | hrq
    · have hbad := (hSr hyS).1 q hqr
      have : y < y := by simpa only [q, e.apply_symm_apply] using hbad
      exact this.false
    · exact False.elim (hirr q heq.symm)
    · have hbad := (hSr hyS).2 q hrq
      have : y < y := by simpa only [q, e.apply_symm_apply] using hbad
      exact this.false

/-- If a point belongs to no cut piece, it is incomparable with at least two points of the
rational eta-chain.  The proof makes explicit the Dedekind-cut argument implicit in the paper. -/
theorem exists_two_incomparable_rational_of_not_mem_etaPieces {C : Set α}
    (e : ℚ ≃o C) {x : α} (hx : x ∉ ⋃ r, etaPiece e r) :
    ∃ p q : ℚ, p < q ∧ Incomparable x (e p).1 ∧ Incomparable x (e q).1 := by
  classical
  by_contra htwo
  push_neg at htwo
  let N : Set ℚ := {q | Incomparable x (e q).1}
  have hNsub : N.Subsingleton := by
    intro p hp q hq
    by_contra hpq
    rcases lt_or_gt_of_ne hpq with hpq | hqp
    · exact (htwo p q hpq hp) hq
    · exact (htwo q p hqp hq) hp
  by_cases hNne : N.Nonempty
  · obtain ⟨q, hqN⟩ := hNne
    have hNq : N = {q} := hNsub.eq_singleton_of_mem hqN
    have hxPiece : x ∈ etaPiece e ((q : ℝ) : EReal) := by
      constructor
      · intro p hpq'
        have hpq : p < q := by exact_mod_cast EReal.coe_lt_coe_iff.mp hpq'
        have hpNotN : p ∉ N := by simpa [hNq] using ne_of_lt hpq
        have hcomp : x ≤ (e p).1 ∨ (e p).1 ≤ x := by
          simpa only [Relation.SymmGen] using (not_incompRel_iff_symmGen.mp hpNotN)
        rcases hcomp with hxp | hpx
        · have : x < (e q).1 := hxp.trans_lt (e.lt_iff_lt.mpr hpq)
          exact False.elim (hqN.not_le this.le)
        · exact lt_of_le_of_ne hpx (fun h => hqN.not_le (calc
            x = (e p).1 := h.symm
            _ ≤ (e q).1 := (e.lt_iff_lt.mpr hpq).le))
      · intro p hqp'
        have hqp : q < p := by exact_mod_cast EReal.coe_lt_coe_iff.mp hqp'
        have hpNotN : p ∉ N := by simpa [hNq] using ne_of_gt hqp
        have hcomp : x ≤ (e p).1 ∨ (e p).1 ≤ x := by
          simpa only [Relation.SymmGen] using (not_incompRel_iff_symmGen.mp hpNotN)
        rcases hcomp with hxp | hpx
        · exact lt_of_le_of_ne hxp (fun h => hqN.not_ge (calc
            (e q).1 ≤ (e p).1 := (e.lt_iff_lt.mpr hqp).le
            _ = x := h.symm))
        · have heqp : (e q).1 < (e p).1 := e.lt_iff_lt.mpr hqp
          have : (e q).1 < x := heqp.trans_le hpx
          exact False.elim (hqN.not_ge this.le)
    exact hx (Set.mem_iUnion_of_mem (((q : ℝ) : EReal)) hxPiece)
  · have hNempty : N = ∅ := Set.not_nonempty_iff_eq_empty.mp hNne
    let L : Set EReal := {r | ∃ q : ℚ, r = ((q : ℝ) : EReal) ∧ (e q).1 < x}
    let r : EReal := sSup L
    have hcomp (q : ℚ) : x ≤ (e q).1 ∨ (e q).1 ≤ x := by
      have : q ∉ N := by simp [hNempty]
      simpa only [Relation.SymmGen] using (not_incompRel_iff_symmGen.mp this)
    have hxPiece : x ∈ etaPiece e r := by
      constructor
      · intro q hqr
        rw [show r = sSup L from rfl] at hqr
        obtain ⟨a, haL, hqa⟩ := (lt_sSup_iff.mp hqr)
        obtain ⟨p, rfl, hpx⟩ := haL
        have hqp : q < p := by exact_mod_cast EReal.coe_lt_coe_iff.mp hqa
        have heqp : (e q).1 < (e p).1 := e.lt_iff_lt.mpr hqp
        exact heqp.trans hpx
      · intro q hrq
        have hnle : ¬ (e q).1 ≤ x := by
          intro hqx
          have hq_le_r : ((q : ℝ) : EReal) ≤ r := by
            rw [show r = sSup L from rfl]
            rcases hqx.eq_or_lt with heq | hlt
            · rw [le_sSup_iff_forall_lt]
              intro b hbq
              obtain ⟨p, hbp, hpq⟩ := EReal.exists_rat_btwn_of_lt hbq
              refine ⟨((p : ℝ) : EReal), ⟨p, rfl, ?_⟩, hbp⟩
              have : (e p).1 < (e q).1 := e.lt_iff_lt.mpr
                (by exact_mod_cast EReal.coe_lt_coe_iff.mp hpq)
              simpa only [heq] using this
            · exact le_sSup ⟨q, rfl, hlt⟩
          exact (not_le_of_gt hrq) hq_le_r
        rcases hcomp q with hxq | hqx
        · exact lt_of_le_of_ne hxq (fun heq => hnle heq.ge)
        · exact False.elim (hnle hqx)
    exact hx (Set.mem_iUnion_of_mem r hxPiece)

theorem etaPieces_outside_incomparable {C : Set α} (e : ℚ ≃o C) (x : α)
    (hx : x ∉ ⋃ r, etaPiece e r) :
    ∃ I : Set EReal, I.OrdConnected ∧ I.Infinite ∧
      ∀ r ∈ I, ∀ y ∈ etaPiece e r, Incomparable x y := by
  obtain ⟨p, q, hpq, hxp, hxq⟩ :=
    exists_two_incomparable_rational_of_not_mem_etaPieces e hx
  obtain ⟨m, hpm, hmq⟩ := DenselyOrdered.dense p q hpq
  obtain ⟨a, hpa, ham⟩ := DenselyOrdered.dense p m hpm
  obtain ⟨b, hmb, hbq⟩ := DenselyOrdered.dense m q hmq
  let a' : EReal := ((a : ℝ) : EReal)
  let b' : EReal := ((b : ℝ) : EReal)
  have hab' : a' < b' := by
    dsimp [a', b']
    exact_mod_cast ham.trans hmb
  refine ⟨Set.Icc a' b', Set.ordConnected_Icc, Set.Icc_infinite hab', ?_⟩
  intro r hr y hy
  have hp_r : ((p : ℝ) : EReal) < r := by
    have hpa' : ((p : ℝ) : EReal) < a' := by
      dsimp [a']
      exact_mod_cast hpa
    exact hpa'.trans_le hr.1
  have hr_q : r < ((q : ℝ) : EReal) := by
    have hbq' : b' < ((q : ℝ) : EReal) := by
      dsimp [b']
      exact_mod_cast hbq
    exact hr.2.trans_lt hbq'
  have hepy : (e p).1 < y := hy.1 p hp_r
  have hyeq : y < (e q).1 := hy.2 q hr_q
  constructor
  · intro hxy
    exact hxq.not_le (hxy.trans_lt hyeq).le
  · intro hyx
    exact hxp.not_ge (hepy.trans_le hyx).le

/-- The five conclusions of Theorem 1.4, packaged for reuse by the reduction theorem. -/
structure ScatteredDecomposition (α : Type*) [PartialOrder α] where
  piece : EReal → Set α
  rational_nonempty : ∀ q : ℚ, (piece ((q : ℝ) : EReal)).Nonempty
  ordered : ∀ ⦃r s : EReal⦄, r < s → SetStrictLT (piece r) (piece s)
  outside_incomparable : ∀ x, x ∉ ⋃ r, piece r →
    ∃ I : Set EReal, I.OrdConnected ∧ I.Infinite ∧
      ∀ r ∈ I, ∀ y ∈ piece r, Incomparable x y
  piece_ordConnected : ∀ r, (piece r).OrdConnected
  piece_scattered : ∀ r, IsScattered (piece r)

/-- Theorem 1.4 / paper `thm:structural` (Stage 2 target). -/
theorem structural_decomposition [Countable α] (hfac : IsFAC α) :
    IsScattered α ∨ Nonempty (ScatteredDecomposition α) := by
  classical
  by_cases hscattered : IsScattered α
  · exact Or.inl hscattered
  · right
    obtain ⟨C, hC⟩ := exists_etaStronglyMaximal hfac hscattered
    obtain ⟨e⟩ := hC.1.1
    exact ⟨
      { piece := etaPiece e
        rational_nonempty := fun q => ⟨(e q).1, etaPiece_rational_mem e q⟩
        ordered := fun _ _ hrs => etaPiece_ordered e hrs
        outside_incomparable := fun x hx => etaPieces_outside_incomparable e x hx
        piece_ordConnected := etaPiece_ordConnected e
        piece_scattered := etaPiece_scattered_of_etaStronglyMaximal hC e }
    ⟩

end AharoniKorman
