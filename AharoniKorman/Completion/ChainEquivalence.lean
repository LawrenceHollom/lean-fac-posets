import AharoniKorman.Completion.FiniteDistance
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Preorder.Finite

/-! Mutually finite incomparability and increasing/decreasing chain equivalence. -/

namespace AharoniKorman.Completion

open Set

variable {α : Type*} [PartialOrder α]

/-- The trace on `C` of the points incomparable with an ambient point. -/
def incomparabilityTrace (C : SaturatedChain α) (x : α) : Set C :=
  {c | Incomparable c.1 x}

/-- Two chains have mutually finite incomparability when both are maximal in their common convex
hull and every cross-chain incomparability trace is finite. -/
structure MutuallyFiniteIncomparability (C D : SaturatedChain α) : Prop where
  maximal : MutuallyMaximalInConvexHull C D
  left_finite : ∀ y : D, (incomparabilityTrace C y.1).Finite
  right_finite : ∀ x : C, (incomparabilityTrace D x.1).Finite

/-- Equality or incomparability between representatives of two chains. -/
def CrossRelated {C D : SaturatedChain α} (x : C) (y : D) : Prop :=
  x.1 = y.1 ∨ Incomparable x.1 y.1

theorem incomparabilityTrace_ordConnected (C : SaturatedChain α) (x : α) :
    (incomparabilityTrace C x).OrdConnected := by
  constructor
  intro a ha c hc b habc
  by_contra hb
  rcases not_incompRel_iff_symmGen.mp hb with hbx | hxb
  · exact ha.not_le ((show a.1 ≤ b.1 from habc.1).trans hbx)
  · exact hc.not_ge (hxb.trans (show b.1 ≤ c.1 from habc.2))

theorem MutuallyFiniteIncomparability.left_trace_interval
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D) (y : D) :
    (incomparabilityTrace C y.1).Finite ∧ (incomparabilityTrace C y.1).OrdConnected :=
  ⟨h.left_finite y, incomparabilityTrace_ordConnected C y.1⟩

theorem MutuallyFiniteIncomparability.right_trace_interval
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D) (x : C) :
    (incomparabilityTrace D x.1).Finite ∧ (incomparabilityTrace D x.1).OrdConnected :=
  ⟨h.right_finite x, incomparabilityTrace_ordConnected D x.1⟩

private theorem mem_common_convexHull_left (C D : SaturatedChain α) (x : C) :
    x.1 ∈ convexHull ((C : Set α) ∪ D) :=
  ⟨x.1, Or.inl x.2, x.1, Or.inl x.2, le_rfl, le_rfl⟩

private theorem mem_common_convexHull_right (C D : SaturatedChain α) (y : D) :
    y.1 ∈ convexHull ((C : Set α) ∪ D) :=
  ⟨y.1, Or.inr y.2, y.1, Or.inr y.2, le_rfl, le_rfl⟩

/-- Every source point is equal or incomparable to a target point. -/
theorem MutuallyFiniteIncomparability.exists_crossRelated_right
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D) (x : C) :
    ∃ y : D, CrossRelated x y := by
  by_cases hxD : x.1 ∈ D
  · exact ⟨⟨x.1, hxD⟩, Or.inl rfl⟩
  obtain ⟨y, hyD, hxy⟩ :=
    h.maximal.right_incomparable (mem_common_convexHull_left C D x) hxD
  exact ⟨⟨y, hyD⟩, Or.inr hxy⟩

/-- Symmetric form of `exists_crossRelated_right`. -/
theorem MutuallyFiniteIncomparability.exists_crossRelated_left
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D) (y : D) :
    ∃ x : C, CrossRelated x y := by
  by_cases hyC : y.1 ∈ C
  · exact ⟨⟨y.1, hyC⟩, Or.inl rfl⟩
  obtain ⟨x, hxC, hyx⟩ :=
    h.maximal.left_incomparable (mem_common_convexHull_right C D y) hyC
  exact ⟨⟨x, hxC⟩, Or.inr hyx.symm⟩

private theorem CrossRelated.lower_le_of_comparable
    {C D : SaturatedChain α} {x c : C} {y : D}
    (hxy : CrossRelated x y) (hcx : c < x)
    (hcomp : c.1 ≤ y.1 ∨ y.1 ≤ c.1) : c.1 ≤ y.1 := by
  rcases hxy with hxy | hxy
  · exact (show c.1 ≤ x.1 from hcx.le).trans (le_of_eq hxy)
  rcases hcomp with hcy | hyc
  · exact hcy
  · exact False.elim (hxy.not_ge (hyc.trans (show c.1 ≤ x.1 from hcx.le)))

private theorem CrossRelated.le_upper_of_comparable
    {C D : SaturatedChain α} {x c : C} {y : D}
    (hxy : CrossRelated x y) (hxc : x < c)
    (hcomp : c.1 ≤ y.1 ∨ y.1 ≤ c.1) : y.1 ≤ c.1 := by
  rcases hxy with hxy | hxy
  · exact (le_of_eq hxy.symm).trans (show x.1 ≤ c.1 from hxc.le)
  rcases hcomp with hcy | hyc
  · exact False.elim (hxy.not_le ((show x.1 ≤ c.1 from hxc.le).trans hcy))
  · exact hyc

/-- Two target representatives related to the same source point have finite distance. -/
theorem MutuallyFiniteIncomparability.crossRelated_same_source
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D)
    {x : C} {y z : D} (hxy : CrossRelated x y) (hxz : CrossRelated x z) :
    FiniteDistance D y z := by
  rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
  · exact (FiniteDistanceClass.mk_eq_mk.mp
      (show FiniteDistanceClass.mk y = FiniteDistanceClass.mk z by
        congr 1
        exact Subtype.ext (hxy.symm.trans hxz)))
  · have hyz : Incomparable y.1 z.1 := by simpa only [← hxy] using hxz
    rcases D.isChain.total y.2 z.2 with hyzle | hzyle
    · exact False.elim (hyz.not_le hyzle)
    · exact False.elim (hyz.not_ge hzyle)
  · have hyz : Incomparable y.1 z.1 := by
      have := hxy.symm
      simpa only [← hxz] using this
    rcases D.isChain.total y.2 z.2 with hyzle | hzyle
    · exact False.elim (hyz.not_le hyzle)
    · exact False.elim (hyz.not_ge hzyle)
  · apply (h.right_finite x).subset
    intro w hw
    rw [uIoo_eq_union] at hw
    rcases hw with hywz | hzw
    · by_contra hxw
      rcases not_incompRel_iff_symmGen.mp hxw with hxlew | hwlex
      · exact hxy.not_ge ((show y.1 ≤ w.1 from hywz.1.le).trans hxlew)
      · exact hxz.not_le (hwlex.trans (show w.1 ≤ z.1 from hywz.2.le))
    · by_contra hxw
      rcases not_incompRel_iff_symmGen.mp hxw with hxlew | hwlex
      · exact hxz.not_ge ((show z.1 ≤ w.1 from hzw.1.le).trans hxlew)
      · exact hxy.not_le (hwlex.trans (show w.1 ≤ y.1 from hzw.2.le))

/-- The representative relation respects finite-distance classes in the source.  This is the
finite-pigeonhole core of `lem:sim-equivalence-bijection`. -/
theorem MutuallyFiniteIncomparability.crossRelated_respects_finiteDistance
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D)
    {x x' : C} {y y' : D} (hxx' : FiniteDistance C x x')
    (hxy : CrossRelated x y) (hx'y' : CrossRelated x' y') :
    FiniteDistance D y y' := by
  classical
  have ordered : ∀ {a b : C} {p q : D}, a ≤ b → FiniteDistance C a b →
      CrossRelated a p → CrossRelated b q → FiniteDistance D p q := by
    intro a b p q hab habFinite hap hbq
    by_contra hpqFinite
    let K : Set C := uIcc a b ∪ incomparabilityTrace C p.1 ∪ incomparabilityTrace C q.1
    have hKfinite : K.Finite :=
      ((finite_uIcc_of_finiteDistance habFinite).union (h.left_finite p)).union
        (h.left_finite q)
    have witness_mem_K {z : D} (hz : z ∈ uIoo p q) {c : C}
        (hcz : Incomparable c.1 z.1) : c ∈ K := by
      by_cases hca : c < a
      · by_cases hcp : Incomparable c.1 p.1
        · exact Or.inl (Or.inr hcp)
        by_cases hcq : Incomparable c.1 q.1
        · exact Or.inr hcq
        have hclep := hap.lower_le_of_comparable hca
          (not_incompRel_iff_symmGen.mp hcp)
        have hcleq := hbq.lower_le_of_comparable (hca.trans_le hab)
          (not_incompRel_iff_symmGen.mp hcq)
        rw [uIoo_eq_union] at hz
        rcases hz with hpzq | hqzp
        · exact False.elim (hcz.not_le (hclep.trans hpzq.1.le))
        · exact False.elim (hcz.not_le (hcleq.trans hqzp.1.le))
      have hac : a ≤ c := le_of_not_gt hca
      by_cases hbc : b < c
      · by_cases hcp : Incomparable c.1 p.1
        · exact Or.inl (Or.inr hcp)
        by_cases hcq : Incomparable c.1 q.1
        · exact Or.inr hcq
        have hplec := hap.le_upper_of_comparable (hab.trans_lt hbc)
          (not_incompRel_iff_symmGen.mp hcp)
        have hqlec := hbq.le_upper_of_comparable hbc
          (not_incompRel_iff_symmGen.mp hcq)
        rw [uIoo_eq_union] at hz
        rcases hz with hpzq | hqzp
        · exact False.elim (hcz.not_ge
            ((show z.1 ≤ q.1 from hpzq.2.le).trans hqlec))
        · exact False.elim (hcz.not_ge
            ((show z.1 ≤ p.1 from hqzp.2.le).trans hplec))
      · exact Or.inl (Or.inl (mem_uIcc_of_le hac (le_of_not_gt hbc)))
    let common : Set D := {z | z ∈ uIoo p q ∧ z.1 ∈ C}
    have hcommonFinite : common.Finite := by
      let A : Set α := Subtype.val '' (uIcc a b : Set C)
      have hAfin : A.Finite := (finite_uIcc_of_finiteDistance habFinite).image Subtype.val
      apply (hAfin.preimage Subtype.val_injective.injOn).subset
      intro z hz
      change z ∈ uIoo p q ∧ z.1 ∈ C at hz
      change z.1 ∈ A
      let c : C := ⟨z.1, hz.2⟩
      have hca : ¬c < a := by
        intro hca
        have hclep := hap.lower_le_of_comparable hca
          (D.isChain.total z.2 p.2)
        have hcleq := hbq.lower_le_of_comparable (hca.trans_le hab)
          (D.isChain.total z.2 q.2)
        have hzJ := hz.1
        rw [uIoo_eq_union] at hzJ
        rcases hzJ with hpzq | hqzp
        · exact hpzq.1.not_ge hclep
        · exact hqzp.1.not_ge hcleq
      have hbc : ¬b < c := by
        intro hbc
        have hplec := hap.le_upper_of_comparable (hab.trans_lt hbc)
          (D.isChain.total z.2 p.2)
        have hqlec := hbq.le_upper_of_comparable hbc
          (D.isChain.total z.2 q.2)
        have hzJ := hz.1
        rw [uIoo_eq_union] at hzJ
        rcases hzJ with hpzq | hqzp
        · have hqz : q.1 ≤ z.1 := hqlec
          exact (show z.1 < q.1 from hpzq.2).not_ge hqz
        · have hpz : p.1 ≤ z.1 := hplec
          exact (show z.1 < p.1 from hqzp.2).not_ge hpz
      exact ⟨c, mem_uIcc_of_le (le_of_not_gt hca) (le_of_not_gt hbc), rfl⟩
    let U : Set D := ⋃ c ∈ K, incomparabilityTrace D c.1
    have hUfinite : U.Finite := hKfinite.biUnion fun c _ => h.right_finite c
    have hsubset : uIoo p q ⊆ common ∪ U := by
      intro z hz
      by_cases hzC : z.1 ∈ C
      · exact Or.inl ⟨hz, hzC⟩
      obtain ⟨c, hcC, hzc⟩ :=
        h.maximal.left_incomparable (mem_common_convexHull_right C D z) hzC
      let cC : C := ⟨c, hcC⟩
      have hcK : cC ∈ K := witness_mem_K hz hzc.symm
      right
      exact Set.mem_iUnion_of_mem cC (Set.mem_iUnion_of_mem hcK hzc)
    exact hpqFinite ((hcommonFinite.union hUfinite).subset hsubset)
  rcases le_total x x' with hle | hge
  · exact ordered hle hxx' hxy hx'y'
  · exact (ordered hge hxx'.symm hx'y' hxy).symm

/-- Symmetry of mutually finite incomparability. -/
theorem MutuallyFiniteIncomparability.symm {C D : SaturatedChain α}
    (h : MutuallyFiniteIncomparability C D) : MutuallyFiniteIncomparability D C where
  maximal := by
    constructor
    · simpa only [Set.union_comm] using h.maximal.right
    · simpa only [Set.union_comm] using h.maximal.left
  left_finite := h.right_finite
  right_finite := h.left_finite

private theorem convexHull_saturatedChain_self (C : SaturatedChain α) :
    convexHull (C : Set α) = C := by
  apply Set.Subset.antisymm
  · rintro x ⟨a, ha, b, hb, hax, hxb⟩
    exact C.ordConnected.out ha hb ⟨hax, hxb⟩
  · intro x hx
    exact ⟨x, hx, x, hx, le_rfl, le_rfl⟩

/-- A saturated chain has mutually finite incomparability with itself. -/
theorem MutuallyFiniteIncomparability.refl (C : SaturatedChain α) :
    MutuallyFiniteIncomparability C C where
  maximal := by
    have hhull : convexHull ((C : Set α) ∪ C) = C := by
      simpa only [Set.union_self] using convexHull_saturatedChain_self C
    have hmax : IsMaximalChainIn C (convexHull ((C : Set α) ∪ C)) := by
      refine ⟨?_, C.isChain, ?_⟩
      · rw [hhull]
      · intro D hD hsub hCD
        apply Set.Subset.antisymm hCD
        rw [hhull] at hsub
        exact hsub
    exact ⟨hmax, hmax⟩
  left_finite := by
    intro y
    apply Set.Finite.subset Set.finite_empty
    intro x hx
    rcases C.isChain.total x.2 y.2 with hxy | hyx
    · exact hx.not_le hxy
    · exact hx.not_ge hyx
  right_finite := by
    intro x
    apply Set.Finite.subset Set.finite_empty
    intro y hy
    rcases C.isChain.total y.2 x.2 with hyx | hxy
    · exact hy.not_le hyx
    · exact hy.not_ge hxy

/-- Correspondence between finite-distance classes, expressed without selecting representatives. -/
def DistanceClassesCorrespond {C D : SaturatedChain α}
    (X : FiniteDistanceClass C) (Y : FiniteDistanceClass D) : Prop :=
  ∃ x : C, ∃ y : D,
    X = FiniteDistanceClass.mk x ∧ Y = FiniteDistanceClass.mk y ∧ CrossRelated x y

theorem CrossRelated.symm {C D : SaturatedChain α} {x : C} {y : D}
    (h : CrossRelated x y) : CrossRelated y x :=
  h.elim (fun heq => Or.inl heq.symm) (fun hinc => Or.inr hinc.symm)

theorem DistanceClassesCorrespond.symm {C D : SaturatedChain α}
    {X : FiniteDistanceClass C} {Y : FiniteDistanceClass D}
    (h : DistanceClassesCorrespond X Y) : DistanceClassesCorrespond Y X := by
  obtain ⟨x, y, rfl, rfl, hxy⟩ := h
  exact ⟨y, x, rfl, rfl, hxy.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩

theorem MutuallyFiniteIncomparability.class_correspondence_exists_right
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D)
    (X : FiniteDistanceClass C) :
    ∃ Y : FiniteDistanceClass D, DistanceClassesCorrespond X Y := by
  induction X using FiniteDistanceClass.inductionOn with
  | _ x =>
    obtain ⟨y, hxy⟩ := h.exists_crossRelated_right x
    exact ⟨FiniteDistanceClass.mk y, x, y, rfl, rfl, hxy⟩

theorem MutuallyFiniteIncomparability.class_correspondence_exists_left
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D)
    (Y : FiniteDistanceClass D) :
    ∃ X : FiniteDistanceClass C, DistanceClassesCorrespond X Y := by
  obtain ⟨X, hYX⟩ := h.symm.class_correspondence_exists_right Y
  exact ⟨X, hYX.symm⟩

theorem MutuallyFiniteIncomparability.class_correspondence_unique_right
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D)
    {X : FiniteDistanceClass C} {Y Y' : FiniteDistanceClass D}
    (hXY : DistanceClassesCorrespond X Y) (hXY' : DistanceClassesCorrespond X Y') : Y = Y' := by
  obtain ⟨x, y, rfl, rfl, hxy⟩ := hXY
  obtain ⟨x', y', hxx', rfl, hx'y'⟩ := hXY'
  have hdist : FiniteDistance C x x' := by
    rw [FiniteDistanceClass.mk_eq_mk] at hxx'
    exact hxx'
  rw [FiniteDistanceClass.mk_eq_mk]
  exact h.crossRelated_respects_finiteDistance hdist hxy hx'y'

theorem MutuallyFiniteIncomparability.class_correspondence_unique_left
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D)
    {X X' : FiniteDistanceClass C} {Y : FiniteDistanceClass D}
    (hXY : DistanceClassesCorrespond X Y) (hX'Y : DistanceClassesCorrespond X' Y) : X = X' :=
  h.symm.class_correspondence_unique_right hXY.symm hX'Y.symm

/-- The unique target class corresponding to a source class. -/
noncomputable def MutuallyFiniteIncomparability.classMap
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D) :
    FiniteDistanceClass C → FiniteDistanceClass D := fun X =>
  Classical.choose (h.class_correspondence_exists_right X)

theorem MutuallyFiniteIncomparability.classMap_corresponds
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D)
    (X : FiniteDistanceClass C) : DistanceClassesCorrespond X (h.classMap X) :=
  Classical.choose_spec (h.class_correspondence_exists_right X)

private theorem MutuallyFiniteIncomparability.crossRelated_strictMono
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D)
    {x x' : C} {y y' : D} (hxx' : x < x') (hfar : ¬FiniteDistance C x x')
    (hxy : CrossRelated x y) (hx'y' : CrossRelated x' y') : y < y' := by
  have htargetFar : ¬FiniteDistance D y y' := by
    intro hdist
    exact hfar (h.symm.crossRelated_respects_finiteDistance hdist hxy.symm hx'y'.symm)
  by_contra hnot
  have hy'y_le : y' ≤ y := le_of_not_gt hnot
  have hy'ne : y' ≠ y := fun heq => htargetFar (heq ▸ FiniteDistance.refl D y)
  have hy'y : y' < y := lt_of_le_of_ne hy'y_le hy'ne
  have hxy' : CrossRelated x y' := by
    right
    by_contra hcomp
    rcases not_incompRel_iff_symmGen.mp hcomp with hxy'le | hy'x
    · have hxyl : x.1 < y.1 := hxy'le.trans_lt hy'y
      exact hxy.elim
        (fun heq => hxyl.ne heq)
        (fun hinc => hinc.not_le hxyl.le)
    · have hy'x' : y'.1 < x'.1 := hy'x.trans_lt hxx'
      exact hx'y'.elim
        (fun heq => hy'x'.ne heq.symm)
        (fun hinc => hinc.not_ge hy'x'.le)
  exact htargetFar (h.crossRelated_same_source hxy hxy')

theorem MutuallyFiniteIncomparability.classMap_strictMono
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D) :
    StrictMono h.classMap := by
  intro X X' hXX'
  obtain ⟨x, y, hX, hY, hxy⟩ := h.classMap_corresponds X
  obtain ⟨x', y', hX', hY', hx'y'⟩ := h.classMap_corresponds X'
  rw [hX, hX', FiniteDistanceClass.mk_lt_mk] at hXX'
  rw [hY, hY', FiniteDistanceClass.mk_lt_mk]
  refine ⟨h.crossRelated_strictMono hXX'.1 hXX'.2 hxy hx'y', ?_⟩
  intro hdist
  exact hXX'.2 (h.symm.crossRelated_respects_finiteDistance hdist hxy.symm hx'y'.symm)

private theorem MutuallyFiniteIncomparability.correspondence_preserves_hasMax
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D)
    {X : FiniteDistanceClass C} {Y : FiniteDistanceClass D}
    (hXY : DistanceClassesCorrespond X Y) (hmax : X.HasMax) : Y.HasMax := by
  classical
  obtain ⟨x, y, rfl, rfl, hxy⟩ := hXY
  rw [FiniteDistanceClass.hasMax_mk] at hmax ⊢
  obtain ⟨m, hxm, hmmax⟩ := hmax
  obtain ⟨d, hmd⟩ := h.exists_crossRelated_right m
  have hyd : FiniteDistance D y d :=
    h.crossRelated_respects_finiteDistance hxm hxy hmd
  by_contra hnoMax
  let S : Set D := insert d (incomparabilityTrace D m.1)
  have hSfinite : S.Finite := (Set.finite_singleton d).union (h.right_finite m)
  have hSnonempty : S.Nonempty := ⟨d, Set.mem_insert d _⟩
  have hSclass : S ⊆ finiteDistanceClassSet D y := by
    intro w hw
    rcases hw with rfl | hw
    · exact hyd
    · exact FiniteDistance.trans hyd
        (h.crossRelated_same_source hmd (Or.inr hw.symm))
  obtain ⟨b, hbS, hbmax⟩ := hSfinite.exists_maximal hSnonempty
  have hbUpper : ∀ w ∈ S, w ≤ b := by
    intro w hw
    rcases le_total w b with hwb | hbw
    · exact hwb
    · exact hbmax hw hbw
  have hbClass : b ∈ finiteDistanceClassSet D y := hSclass hbS
  have hnotUpper : ¬∀ z ∈ finiteDistanceClassSet D y, z ≤ b := by
    intro hb
    exact hnoMax ⟨b, hbClass, hb⟩
  push_neg at hnotUpper
  obtain ⟨z, hzClass, hzb⟩ := hnotUpper
  have hbz : b < z := hzb
  have hdb : d ≤ b := hbUpper d (Set.mem_insert d _)
  have hdz : d.1 < z.1 := hdb.trans_lt hbz
  have hzNotTrace : z ∉ incomparabilityTrace D m.1 := by
    intro hz
    exact (not_lt_of_ge (hbUpper z (Set.mem_insert_of_mem d hz))) hbz
  have hnzlem : ¬z.1 ≤ m.1 := by
    intro hzm
    exact hmd.elim
      (fun heq => hdz.not_ge (hzm.trans (le_of_eq heq)))
      (fun hinc => hinc.not_ge (hdz.le.trans hzm))
  have hmz : m.1 < z.1 := by
    rcases not_incompRel_iff_symmGen.mp hzNotTrace with hzm | hmz
    · exact False.elim (hnzlem hzm)
    · exact lt_of_le_of_ne hmz (fun heq => hnzlem (le_of_eq heq.symm))
  have hdzFinite : FiniteDistance D d z := FiniteDistance.trans hyd.symm hzClass
  have hzNotC : z.1 ∉ C := by
    intro hzC
    let zC : C := ⟨z.1, hzC⟩
    have hmzFinite : FiniteDistance C m zC :=
      h.symm.crossRelated_respects_finiteDistance hdzFinite hmd.symm (Or.inl rfl)
    have hxzFinite : FiniteDistance C x zC := FiniteDistance.trans hxm hmzFinite
    exact (not_lt_of_ge (hmmax zC hxzFinite)) hmz
  have hzComparable : ∀ c : C, ¬Incomparable c.1 z.1 := by
    intro c hcz
    have hmcFinite : FiniteDistance C m c :=
      h.symm.crossRelated_respects_finiteDistance hdzFinite hmd.symm
        (Or.inr hcz.symm)
    have hxcFinite : FiniteDistance C x c := FiniteDistance.trans hxm hmcFinite
    have hczle : c.1 ≤ z.1 :=
      (show c.1 ≤ m.1 from hmmax c hxcFinite).trans (le_of_lt hmz)
    exact hcz.not_le hczle
  have hins : IsChain (· ≤ ·) (insert z.1 (C : Set α)) := by
    apply C.isChain.insert
    intro c hc hne
    exact (not_incompRel_iff_symmGen.mp (hzComparable ⟨c, hc⟩)).symm
  have hsub : insert z.1 (C : Set α) ⊆ convexHull ((C : Set α) ∪ D) := by
    intro w hw
    rcases hw with rfl | hw
    · exact mem_common_convexHull_right C D z
    · exact h.maximal.left.subset hw
  have heq := h.maximal.left.maximal hins hsub (Set.subset_insert z.1 C)
  have hzInsert : z.1 ∈ insert z.1 (C : Set α) := Set.mem_insert z.1 C
  rw [← heq] at hzInsert
  exact hzNotC hzInsert

theorem MutuallyFiniteIncomparability.classMap_preserves_hasMax
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D)
    (X : FiniteDistanceClass C) : X.HasMax ↔ (h.classMap X).HasMax := by
  constructor
  · exact h.correspondence_preserves_hasMax (h.classMap_corresponds X)
  · intro hmax
    exact h.symm.correspondence_preserves_hasMax
      (h.classMap_corresponds X).symm hmax

private theorem MutuallyFiniteIncomparability.correspondence_preserves_hasMin
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D)
    {X : FiniteDistanceClass C} {Y : FiniteDistanceClass D}
    (hXY : DistanceClassesCorrespond X Y) (hmin : X.HasMin) : Y.HasMin := by
  classical
  obtain ⟨x, y, rfl, rfl, hxy⟩ := hXY
  rw [FiniteDistanceClass.hasMin_mk] at hmin ⊢
  obtain ⟨m, hxm, hmmin⟩ := hmin
  obtain ⟨d, hmd⟩ := h.exists_crossRelated_right m
  have hyd : FiniteDistance D y d :=
    h.crossRelated_respects_finiteDistance hxm hxy hmd
  by_contra hnoMin
  let S : Set D := insert d (incomparabilityTrace D m.1)
  have hSfinite : S.Finite := (Set.finite_singleton d).union (h.right_finite m)
  have hSnonempty : S.Nonempty := ⟨d, Set.mem_insert d _⟩
  have hSclass : S ⊆ finiteDistanceClassSet D y := by
    intro w hw
    rcases hw with rfl | hw
    · exact hyd
    · exact FiniteDistance.trans hyd
        (h.crossRelated_same_source hmd (Or.inr hw.symm))
  obtain ⟨b, hbS, hbmin⟩ := hSfinite.exists_minimal hSnonempty
  have hbLower : ∀ w ∈ S, b ≤ w := by
    intro w hw
    rcases le_total b w with hbw | hwb
    · exact hbw
    · exact hbmin hw hwb
  have hbClass : b ∈ finiteDistanceClassSet D y := hSclass hbS
  have hnotLower : ¬∀ z ∈ finiteDistanceClassSet D y, b ≤ z := by
    intro hb
    exact hnoMin ⟨b, hbClass, hb⟩
  push_neg at hnotLower
  obtain ⟨z, hzClass, hzb⟩ := hnotLower
  have hzb' : z < b := hzb
  have hbd : b ≤ d := hbLower d (Set.mem_insert d _)
  have hzd : z.1 < d.1 := hzb'.trans_le hbd
  have hzNotTrace : z ∉ incomparabilityTrace D m.1 := by
    intro hz
    exact (not_lt_of_ge (hbLower z (Set.mem_insert_of_mem d hz))) hzb'
  have hnmlez : ¬m.1 ≤ z.1 := by
    intro hmz
    exact hmd.elim
      (fun heq => hzd.not_ge ((le_of_eq heq.symm).trans hmz))
      (fun hinc => hinc.not_le (hmz.trans hzd.le))
  have hzm : z.1 < m.1 := by
    rcases not_incompRel_iff_symmGen.mp hzNotTrace with hzm | hmz
    · exact lt_of_le_of_ne hzm (fun heq => hnmlez (le_of_eq heq.symm))
    · exact False.elim (hnmlez hmz)
  have hdzFinite : FiniteDistance D d z := FiniteDistance.trans hyd.symm hzClass
  have hzNotC : z.1 ∉ C := by
    intro hzC
    let zC : C := ⟨z.1, hzC⟩
    have hmzFinite : FiniteDistance C m zC :=
      h.symm.crossRelated_respects_finiteDistance hdzFinite hmd.symm (Or.inl rfl)
    have hxzFinite : FiniteDistance C x zC := FiniteDistance.trans hxm hmzFinite
    exact (not_lt_of_ge (hmmin zC hxzFinite)) hzm
  have hzComparable : ∀ c : C, ¬Incomparable c.1 z.1 := by
    intro c hcz
    have hmcFinite : FiniteDistance C m c :=
      h.symm.crossRelated_respects_finiteDistance hdzFinite hmd.symm
        (Or.inr hcz.symm)
    have hxcFinite : FiniteDistance C x c := FiniteDistance.trans hxm hmcFinite
    have hzcle : z.1 ≤ c.1 :=
      (le_of_lt hzm).trans (show m.1 ≤ c.1 from hmmin c hxcFinite)
    exact hcz.not_ge hzcle
  have hins : IsChain (· ≤ ·) (insert z.1 (C : Set α)) := by
    apply C.isChain.insert
    intro c hc hne
    exact (not_incompRel_iff_symmGen.mp (hzComparable ⟨c, hc⟩)).symm
  have hsub : insert z.1 (C : Set α) ⊆ convexHull ((C : Set α) ∪ D) := by
    intro w hw
    rcases hw with rfl | hw
    · exact mem_common_convexHull_right C D z
    · exact h.maximal.left.subset hw
  have heq := h.maximal.left.maximal hins hsub (Set.subset_insert z.1 C)
  have hzInsert : z.1 ∈ insert z.1 (C : Set α) := Set.mem_insert z.1 C
  rw [← heq] at hzInsert
  exact hzNotC hzInsert

theorem MutuallyFiniteIncomparability.classMap_preserves_hasMin
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D)
    (X : FiniteDistanceClass C) : X.HasMin ↔ (h.classMap X).HasMin := by
  constructor
  · exact h.correspondence_preserves_hasMin (h.classMap_corresponds X)
  · intro hmin
    exact h.symm.correspondence_preserves_hasMin
      (h.classMap_corresponds X).symm hmin

/-- Paper Lemma `lem:sim-equivalence-bijection`: mutually finite-incomparable chains have
canonically order-isomorphic finite-distance quotients. -/
noncomputable def MutuallyFiniteIncomparability.classOrderIso
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D) :
    FiniteDistanceClass C ≃o FiniteDistanceClass D := by
  let e : FiniteDistanceClass C ≃ FiniteDistanceClass D :=
    { toFun := h.classMap
      invFun := h.symm.classMap
      left_inv := fun X => (h.class_correspondence_unique_left
        (h.classMap_corresponds X)
        (h.symm.classMap_corresponds (h.classMap X)).symm).symm
      right_inv := fun Y => (h.class_correspondence_unique_right
        (h.symm.classMap_corresponds Y).symm
        (h.classMap_corresponds (h.symm.classMap Y))).symm }
  exact e.toOrderIso h.classMap_strictMono.monotone h.symm.classMap_strictMono.monotone

/-- Saturated chains with no greatest point.  Principal chains are deliberately excluded before
taking the increasing-chain quotient. -/
def IncreasingChain (α : Type*) [PartialOrder α] :=
  {C : SaturatedChain α // C.NoTop}

/-- Saturated chains with no least point.  Principal chains are deliberately excluded before
taking the decreasing-chain quotient. -/
def DecreasingChain (α : Type*) [PartialOrder α] :=
  {C : SaturatedChain α // C.NoBottom}

instance : Coe (IncreasingChain α) (SaturatedChain α) := ⟨Subtype.val⟩
instance : Coe (DecreasingChain α) (SaturatedChain α) := ⟨Subtype.val⟩

/-- View a decreasing chain as an increasing chain in the dual order. -/
def DecreasingChain.toDual (C : DecreasingChain α) : IncreasingChain αᵒᵈ :=
  ⟨C.1.dual, (SaturatedChain.dual_noTop_iff C.1).2 C.2⟩

theorem SaturatedChain.NoTop.exists_gt {C : SaturatedChain α}
    (h : C.NoTop) (x : C) : ∃ y : C, x < y := by
  by_contra hex
  apply h
  refine ⟨x, ?_⟩
  intro y
  exact le_of_not_gt (fun hxy => hex ⟨y, hxy⟩)

theorem SaturatedChain.NoBottom.exists_lt {C : SaturatedChain α}
    (h : C.NoBottom) (x : C) : ∃ y : C, y < x := by
  by_contra hex
  apply h
  refine ⟨x, ?_⟩
  intro y
  exact le_of_not_gt (fun hyx => hex ⟨y, hyx⟩)

/-- A nonempty final segment of a chain without a top again has no top. -/
theorem IncreasingChain.finalSegment_noTop (C : IncreasingChain α)
    (C' : SaturatedChain α)
    (hC' : IsFinalSegment (C' : Set α) (C.1 : Set α)) : C'.NoTop := by
  intro htop
  obtain ⟨m, hm⟩ := htop
  let mC : C.1 := ⟨m.1, hC'.1 m.2⟩
  obtain ⟨y, hmy⟩ := C.2.exists_gt mC
  have hyC' : y.1 ∈ C' := hC'.2 m.2 y.2 hmy.le
  exact (not_lt_of_ge (hm ⟨y.1, hyC'⟩)) hmy

/-- A nonempty initial segment of a chain without a bottom again has no bottom. -/
theorem DecreasingChain.initialSegment_noBottom (C : DecreasingChain α)
    (C' : SaturatedChain α)
    (hC' : IsInitialSegment (C' : Set α) (C.1 : Set α)) : C'.NoBottom := by
  intro hbot
  obtain ⟨m, hm⟩ := hbot
  let mC : C.1 := ⟨m.1, hC'.1 m.2⟩
  obtain ⟨y, hym⟩ := C.2.exists_lt mC
  have hyC' : y.1 ∈ C' := hC'.2 m.2 y.2 hym.le
  exact (not_lt_of_ge (hm ⟨y.1, hyC'⟩)) hym

/-- Increasing equivalence: suitable final segments have mutually finite incomparability. -/
def IncreasingEquivalent (C D : IncreasingChain α) : Prop :=
  ∃ C' D' : SaturatedChain α,
    IsFinalSegment (C' : Set α) (C.1 : Set α) ∧
      IsFinalSegment (D' : Set α) (D.1 : Set α) ∧
      MutuallyFiniteIncomparability C' D'

/-- Decreasing equivalence, defined through increasing equivalence in the dual order. -/
def DecreasingEquivalent (C D : DecreasingChain α) : Prop :=
  IncreasingEquivalent C.toDual D.toDual

private theorem isFinalSegment_refl (C : Set α) : IsFinalSegment C C := by
  refine ⟨Set.Subset.rfl, ?_⟩
  intro x y hx hy hxy
  exact hy

/-- Nonempty final segments of one chain are nested. -/
theorem finalSegments_comparable {A B : Set α} {C : SaturatedChain α}
    (hA : IsFinalSegment A C) (hB : IsFinalSegment B C) : A ⊆ B ∨ B ⊆ A := by
  classical
  by_cases hAB : A ⊆ B
  · exact Or.inl hAB
  right
  intro b hbB
  by_contra hbA
  obtain ⟨a, haA, haB⟩ := Set.not_subset.mp hAB
  rcases C.isChain.total (hA.1 haA) (hB.1 hbB) with hab | hba
  · exact hbA (hA.2 haA (hB.1 hbB) hab)
  · exact haB (hB.2 hbB (hA.1 haA) hba)

theorem IncreasingEquivalent.refl (C : IncreasingChain α) : IncreasingEquivalent C C :=
  ⟨C.1, C.1, isFinalSegment_refl (C.1 : Set α), isFinalSegment_refl (C.1 : Set α),
    MutuallyFiniteIncomparability.refl C.1⟩

theorem IncreasingEquivalent.symm {C D : IncreasingChain α}
    (h : IncreasingEquivalent C D) : IncreasingEquivalent D C := by
  obtain ⟨C', D', hC', hD', hCD⟩ := h
  exact ⟨D', C', hD', hC', hCD.symm⟩

theorem DecreasingEquivalent.refl (C : DecreasingChain α) : DecreasingEquivalent C C :=
  IncreasingEquivalent.refl C.toDual

theorem DecreasingEquivalent.symm {C D : DecreasingChain α}
    (h : DecreasingEquivalent C D) : DecreasingEquivalent D C :=
  IncreasingEquivalent.symm h

end AharoniKorman.Completion
