import AharoniKorman.Completion.SaturatedChain
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Set.UnorderedInterval

/-! Finite-distance classes on saturated chains (`def:finite-distance`). -/

namespace AharoniKorman.Completion

open Set

variable {α : Type*} [PartialOrder α]

/-- Two points of a chain are at finite distance when their symmetric open interval is finite. -/
def FiniteDistance (C : SaturatedChain α) (x y : C) : Prop :=
  (uIoo x y).Finite

@[refl] theorem FiniteDistance.refl (C : SaturatedChain α) (x : C) :
    FiniteDistance C x x := by
  simp [FiniteDistance]

@[symm] theorem FiniteDistance.symm {C : SaturatedChain α} {x y : C}
    (h : FiniteDistance C x y) : FiniteDistance C y x := by
  simpa only [FiniteDistance, uIoo_comm] using h

theorem finite_uIcc_of_finiteDistance {C : SaturatedChain α} {x y : C}
    (h : FiniteDistance C x y) : (uIcc x y).Finite := by
  apply (Set.finite_singleton x).union ((Set.finite_singleton y).union h) |>.subset
  intro z hz
  by_cases hzx : z = x
  · exact Or.inl (by simpa [hzx])
  right
  by_cases hzy : z = y
  · exact Or.inl (by simpa [hzy])
  right
  rcases (mem_uIcc.mp hz) with hxy | hyx
  · exact mem_uIoo_of_lt (lt_of_le_of_ne hxy.1 (Ne.symm hzx))
      (lt_of_le_of_ne hxy.2 hzy)
  · exact mem_uIoo_of_gt (lt_of_le_of_ne hyx.1 (Ne.symm hzy))
      (lt_of_le_of_ne hyx.2 hzx)

@[trans] theorem FiniteDistance.trans {C : SaturatedChain α} {x y z : C}
    (hxy : FiniteDistance C x y) (hyz : FiniteDistance C y z) :
    FiniteDistance C x z := by
  apply ((finite_uIcc_of_finiteDistance hxy).union
    (finite_uIcc_of_finiteDistance hyz)).subset
  exact uIoo_subset_uIcc_self.trans uIcc_subset_uIcc_union_uIcc

/-- The finite-distance setoid on a bundled saturated chain. -/
def finiteDistanceSetoid (C : SaturatedChain α) : Setoid C where
  r := FiniteDistance C
  iseqv := ⟨FiniteDistance.refl C, FiniteDistance.symm, FiniteDistance.trans⟩

/-- The points in the finite-distance class represented by `x`. -/
def finiteDistanceClassSet (C : SaturatedChain α) (x : C) : Set C :=
  {y | FiniteDistance C x y}

@[simp] theorem mem_finiteDistanceClassSet {C : SaturatedChain α} {x y : C} :
    y ∈ finiteDistanceClassSet C x ↔ FiniteDistance C x y := Iff.rfl

theorem finiteDistance_of_mem_uIcc {C : SaturatedChain α} {x y z : C}
    (hxy : FiniteDistance C x y) (hz : z ∈ uIcc x y) : FiniteDistance C x z := by
  apply (finite_uIcc_of_finiteDistance hxy).subset
  exact uIoo_subset_uIcc_self.trans (uIcc_subset_uIcc_left hz)

/-- Every finite-distance class is convex in its source chain. -/
theorem finiteDistanceClassSet_ordConnected (C : SaturatedChain α) (x : C) :
    (finiteDistanceClassSet C x).OrdConnected := by
  constructor
  intro y hy z hz w hywz
  have hxy : FiniteDistance C x y := hy
  have hxz : FiniteDistance C x z := hz
  have hyz : FiniteDistance C y z := FiniteDistance.trans hxy.symm hxz
  have hyw : FiniteDistance C y w :=
    finiteDistance_of_mem_uIcc hyz (mem_uIcc_of_le hywz.1 hywz.2)
  exact FiniteDistance.trans hxy hyw

/-- Finite-distance classes represented by equivalent points are equal. -/
theorem finiteDistanceClassSet_eq {C : SaturatedChain α} {x y : C}
    (hxy : FiniteDistance C x y) :
    finiteDistanceClassSet C x = finiteDistanceClassSet C y := by
  ext z
  constructor
  · intro hxz
    exact FiniteDistance.trans hxy.symm hxz
  · intro hyz
    exact FiniteDistance.trans hxy hyz

/-- Distinct finite-distance classes are disjoint. -/
theorem finiteDistanceClassSet_disjoint {C : SaturatedChain α} {x y : C}
    (hxy : ¬FiniteDistance C x y) :
    Disjoint (finiteDistanceClassSet C x) (finiteDistanceClassSet C y) := by
  rw [Set.disjoint_left]
  intro z hxz hyz
  exact hxy (FiniteDistance.trans hxz hyz.symm)

/-- Distinct convex distance classes are strictly ordered exactly as any chosen representatives. -/
theorem finiteDistanceClassSet_strictLT_iff {C : SaturatedChain α} {x y : C}
    (hxyFar : ¬FiniteDistance C x y) :
    SetStrictLT (finiteDistanceClassSet C x) (finiteDistanceClassSet C y) ↔ x < y := by
  constructor
  · intro h
    exact h (FiniteDistance.refl C x) (FiniteDistance.refl C y)
  · intro hxy a ha b hb
    by_contra hab
    have hba : b ≤ a := le_of_not_gt hab
    have hxA : x ∈ finiteDistanceClassSet C x := FiniteDistance.refl C x
    have hyB : y ∈ finiteDistanceClassSet C y := FiniteDistance.refl C y
    have hdisj := Set.disjoint_left.mp (finiteDistanceClassSet_disjoint hxyFar)
    by_cases hax : a ≤ x
    · have hxB : x ∈ finiteDistanceClassSet C y :=
        (finiteDistanceClassSet_ordConnected C y).out hb hyB
          ⟨hba.trans hax, hxy.le⟩
      exact hdisj hxA hxB
    · have hxa : x < a := lt_of_not_ge hax
      by_cases hya : y ≤ a
      · have hyA : y ∈ finiteDistanceClassSet C x :=
          (finiteDistanceClassSet_ordConnected C x).out hxA ha
            ⟨hxy.le, hya⟩
        exact hdisj hyA hyB
      · have hay : a < y := lt_of_not_ge hya
        have haB : a ∈ finiteDistanceClassSet C y :=
          (finiteDistanceClassSet_ordConnected C y).out hb hyB
            ⟨hba, hay.le⟩
        exact hdisj ha haB

/-- Quotient of a saturated chain by finite distance. -/
abbrev FiniteDistanceClass (C : SaturatedChain α) := Quotient (finiteDistanceSetoid C)

/-- Public constructor for a finite-distance class. -/
def FiniteDistanceClass.mk {C : SaturatedChain α} (x : C) : FiniteDistanceClass C :=
  Quotient.mk _ x

@[simp] theorem FiniteDistanceClass.mk_eq_mk {C : SaturatedChain α} {x y : C} :
    FiniteDistanceClass.mk x = FiniteDistanceClass.mk y ↔ FiniteDistance C x y :=
  Quotient.eq_iff_equiv

private def finiteDistanceClassLE {C : SaturatedChain α} (x y : C) : Prop :=
  FiniteDistance C x y ∨ x < y

private theorem finiteDistanceClassLE_congr {C : SaturatedChain α} {x x' y y' : C}
    (hxx : FiniteDistance C x x') (hyy : FiniteDistance C y y') :
    finiteDistanceClassLE x y ↔ finiteDistanceClassLE x' y' := by
  have convert : ∀ {a a' b b' : C}, FiniteDistance C a a' → FiniteDistance C b b' →
      finiteDistanceClassLE a b → finiteDistanceClassLE a' b' := by
    intro a a' b b' haa hbb h
    rcases h with hab | hab
    · exact Or.inl (FiniteDistance.trans haa.symm (FiniteDistance.trans hab hbb))
    · by_cases ha'b' : FiniteDistance C a' b'
      · exact Or.inl ha'b'
      · have habFar : ¬FiniteDistance C a b := by
          intro h
          exact ha'b' (FiniteDistance.trans haa.symm (FiniteDistance.trans h hbb))
        have hclasses := (finiteDistanceClassSet_strictLT_iff habFar).mpr hab
        exact Or.inr (hclasses haa hbb)
  exact ⟨convert hxx hyy, convert hxx.symm hyy.symm⟩

private theorem finiteDistanceClassLE_trans {C : SaturatedChain α} {x y z : C} :
    finiteDistanceClassLE x y → finiteDistanceClassLE y z → finiteDistanceClassLE x z := by
  rintro (hxy | hxy) (hyz | hyz)
  · exact Or.inl (FiniteDistance.trans hxy hyz)
  · by_cases hxz : FiniteDistance C x z
    · exact Or.inl hxz
    · have hyzFar : ¬FiniteDistance C y z := fun h => hxz (FiniteDistance.trans hxy h)
      have hclasses := (finiteDistanceClassSet_strictLT_iff hyzFar).mpr hyz
      exact Or.inr (hclasses hxy.symm (FiniteDistance.refl C z))
  · by_cases hxz : FiniteDistance C x z
    · exact Or.inl hxz
    · have hxyFar : ¬FiniteDistance C x y := fun h => hxz (FiniteDistance.trans h hyz)
      have hclasses := (finiteDistanceClassSet_strictLT_iff hxyFar).mpr hxy
      exact Or.inr (hclasses (FiniteDistance.refl C x) hyz)
  · exact Or.inr (hxy.trans hyz)

private def finiteDistanceQuotientLE (C : SaturatedChain α)
    (X Y : FiniteDistanceClass C) : Prop :=
  Quotient.liftOn₂ X Y finiteDistanceClassLE fun _ _ _ _ hxx hyy =>
    propext (finiteDistanceClassLE_congr hxx hyy)

noncomputable instance (C : SaturatedChain α) : LinearOrder (FiniteDistanceClass C) where
  le := finiteDistanceQuotientLE C
  le_refl := by
    intro X
    induction X using Quotient.inductionOn with
    | _ x => exact Or.inl (FiniteDistance.refl C x)
  le_trans := by
    intro X Y Z hXY hYZ
    induction X using Quotient.inductionOn with
    | _ x =>
      induction Y using Quotient.inductionOn with
      | _ y =>
        induction Z using Quotient.inductionOn with
        | _ z => exact finiteDistanceClassLE_trans hXY hYZ
  le_antisymm := by
    intro X Y hXY hYX
    induction X using Quotient.inductionOn with
    | _ x =>
      induction Y using Quotient.inductionOn with
      | _ y =>
        rcases hXY with hxy | hxy
        · exact Quotient.sound hxy
        rcases hYX with hyx | hyx
        · exact Quotient.sound hyx.symm
        · exact False.elim (hxy.not_gt hyx)
  le_total := by
    intro X Y
    induction X using Quotient.inductionOn with
    | _ x =>
      induction Y using Quotient.inductionOn with
      | _ y =>
        by_cases hxy : FiniteDistance C x y
        · exact Or.inl (Or.inl hxy)
        rcases lt_trichotomy x y with hlt | heq | hgt
        · exact Or.inl (Or.inr hlt)
        · exact False.elim (hxy (heq ▸ FiniteDistance.refl C x))
        · exact Or.inr (Or.inr hgt)
  toDecidableLE := Classical.decRel _

@[simp] theorem FiniteDistanceClass.mk_le_mk {C : SaturatedChain α} {x y : C} :
    FiniteDistanceClass.mk x ≤ FiniteDistanceClass.mk y ↔
      FiniteDistance C x y ∨ x < y := Iff.rfl

@[simp] theorem FiniteDistanceClass.mk_lt_mk {C : SaturatedChain α} {x y : C} :
    FiniteDistanceClass.mk x < FiniteDistanceClass.mk y ↔
      x < y ∧ ¬FiniteDistance C x y := by
  rw [lt_iff_le_not_ge, FiniteDistanceClass.mk_le_mk,
    FiniteDistanceClass.mk_le_mk]
  constructor
  · rintro ⟨hxy | hxy, hnot⟩
    · exact False.elim (hnot (Or.inl hxy.symm))
    · refine ⟨hxy, ?_⟩
      intro hdist
      exact hnot (Or.inl hdist.symm)
  · rintro ⟨hxy, hfar⟩
    refine ⟨Or.inr hxy, ?_⟩
    rintro (hyx | hyx)
    · exact hfar hyx.symm
    · exact hxy.not_gt hyx

/-- Public quotient induction principle. -/
theorem FiniteDistanceClass.inductionOn {C : SaturatedChain α}
    {motive : FiniteDistanceClass C → Prop} (X : FiniteDistanceClass C)
    (h : ∀ x : C, motive (FiniteDistanceClass.mk x)) : motive X :=
  Quotient.inductionOn X h

/-- A represented distance class has a least point. -/
def FiniteDistanceClassSetHasMin (C : SaturatedChain α) (x : C) : Prop :=
  ∃ m ∈ finiteDistanceClassSet C x, ∀ y ∈ finiteDistanceClassSet C x, m ≤ y

/-- A represented distance class has a greatest point. -/
def FiniteDistanceClassSetHasMax (C : SaturatedChain α) (x : C) : Prop :=
  ∃ m ∈ finiteDistanceClassSet C x, ∀ y ∈ finiteDistanceClassSet C x, y ≤ m

theorem finiteDistanceClassSetHasMin_congr {C : SaturatedChain α} {x y : C}
    (hxy : FiniteDistance C x y) :
    FiniteDistanceClassSetHasMin C x ↔ FiniteDistanceClassSetHasMin C y := by
  rw [FiniteDistanceClassSetHasMin, FiniteDistanceClassSetHasMin,
    finiteDistanceClassSet_eq hxy]

theorem finiteDistanceClassSetHasMax_congr {C : SaturatedChain α} {x y : C}
    (hxy : FiniteDistance C x y) :
    FiniteDistanceClassSetHasMax C x ↔ FiniteDistanceClassSetHasMax C y := by
  rw [FiniteDistanceClassSetHasMax, FiniteDistanceClassSetHasMax,
    finiteDistanceClassSet_eq hxy]

/-- Representative-independent assertion that a finite-distance class has a least point. -/
def FiniteDistanceClass.HasMin {C : SaturatedChain α}
    (X : FiniteDistanceClass C) : Prop :=
  Quotient.liftOn X (FiniteDistanceClassSetHasMin C) fun _ _ hxy =>
    propext (finiteDistanceClassSetHasMin_congr hxy)

/-- Representative-independent assertion that a finite-distance class has a greatest point. -/
def FiniteDistanceClass.HasMax {C : SaturatedChain α}
    (X : FiniteDistanceClass C) : Prop :=
  Quotient.liftOn X (FiniteDistanceClassSetHasMax C) fun _ _ hxy =>
    propext (finiteDistanceClassSetHasMax_congr hxy)

@[simp] theorem FiniteDistanceClass.hasMin_mk {C : SaturatedChain α} (x : C) :
    (FiniteDistanceClass.mk x).HasMin ↔ FiniteDistanceClassSetHasMin C x := Iff.rfl

@[simp] theorem FiniteDistanceClass.hasMax_mk {C : SaturatedChain α} (x : C) :
    (FiniteDistanceClass.mk x).HasMax ↔ FiniteDistanceClassSetHasMax C x := Iff.rfl

theorem finiteDistanceClassSet_finite_of_hasMin_hasMax {C : SaturatedChain α} {x : C}
    (hmin : FiniteDistanceClassSetHasMin C x)
    (hmax : FiniteDistanceClassSetHasMax C x) :
    (finiteDistanceClassSet C x).Finite := by
  obtain ⟨m, hm, hmlower⟩ := hmin
  obtain ⟨M, hM, hMupper⟩ := hmax
  have hmM : FiniteDistance C m M :=
    FiniteDistance.trans hm.symm hM
  exact (finite_uIcc_of_finiteDistance hmM).subset fun y hy =>
    mem_uIcc_of_le (hmlower y hy) (hMupper y hy)

/-- Endpoint-shape alternatives for a distance class.  This intentionally records only the
finite/minimum/maximum information needed downstream, without choosing concrete order isomorphisms
with `ω`, `ω*`, or `ℤ`. -/
theorem finiteDistanceClassSet_shape (C : SaturatedChain α) (x : C) :
    (finiteDistanceClassSet C x).Finite ∨
    ((finiteDistanceClassSet C x).Infinite ∧
      FiniteDistanceClassSetHasMin C x ∧ ¬FiniteDistanceClassSetHasMax C x) ∨
    ((finiteDistanceClassSet C x).Infinite ∧
      ¬FiniteDistanceClassSetHasMin C x ∧ FiniteDistanceClassSetHasMax C x) ∨
    ((finiteDistanceClassSet C x).Infinite ∧
      ¬FiniteDistanceClassSetHasMin C x ∧ ¬FiniteDistanceClassSetHasMax C x) := by
  classical
  by_cases hfinite : (finiteDistanceClassSet C x).Finite
  · exact Or.inl hfinite
  have hinfinite : (finiteDistanceClassSet C x).Infinite := hfinite
  by_cases hmin : FiniteDistanceClassSetHasMin C x
  · by_cases hmax : FiniteDistanceClassSetHasMax C x
    · exact False.elim (hinfinite (finiteDistanceClassSet_finite_of_hasMin_hasMax hmin hmax))
    · exact Or.inr (Or.inl ⟨hinfinite, hmin, hmax⟩)
  · by_cases hmax : FiniteDistanceClassSetHasMax C x
    · exact Or.inr (Or.inr (Or.inl ⟨hinfinite, hmin, hmax⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hinfinite, hmin, hmax⟩))

end AharoniKorman.Completion
