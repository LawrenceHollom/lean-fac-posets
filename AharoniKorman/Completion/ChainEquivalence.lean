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

private theorem maximalIn_convexHull_union_of_crossRelated {C D : SaturatedChain α}
    (hcontact : ∀ d : D, ∃ c : C, CrossRelated c d) :
    IsMaximalChainIn C (convexHull ((C : Set α) ∪ D)) := by
  refine ⟨fun x hx => mem_common_convexHull_left C D ⟨x, hx⟩, C.isChain, ?_⟩
  intro S hS hsub hCS
  apply Subset.antisymm hCS
  intro z hz
  obtain ⟨a, ha, b, hb, haz, hzb⟩ := hsub hz
  have hcomp (c : C) : z ≤ c.1 ∨ c.1 ≤ z := hS.total hz (hCS c.2)
  have hlo : ∃ c : C, c.1 ≤ z := by
    rcases ha with ha | ha
    · exact ⟨⟨a, ha⟩, haz⟩
    obtain ⟨c, hca⟩ := hcontact ⟨a, ha⟩
    refine ⟨c, ?_⟩
    by_contra hc
    have hac : a < c.1 := haz.trans_lt (lt_of_le_not_ge ((hcomp c).resolve_right hc) hc)
    exact hca.elim (fun he => hac.ne he.symm) (fun hi => hi.not_ge hac.le)
  have hhi : ∃ c : C, z ≤ c.1 := by
    rcases hb with hb | hb
    · exact ⟨⟨b, hb⟩, hzb⟩
    obtain ⟨c, hcb⟩ := hcontact ⟨b, hb⟩
    refine ⟨c, ?_⟩
    by_contra hc
    have hcb' : c.1 < b := (lt_of_le_not_ge ((hcomp c).resolve_left hc) hc).trans_le hzb
    exact hcb.elim hcb'.ne (fun hi => hi.not_le hcb'.le)
  obtain ⟨l, hl⟩ := hlo
  obtain ⟨r, hr⟩ := hhi
  exact C.mem_of_between l.2 r.2 hl hr (fun c hc => hcomp ⟨c, hc⟩)

/-- For saturated chains, the paper's nonempty equality-or-incomparability
traces imply the joint convex-hull maximality formulation. -/
theorem MutuallyFiniteIncomparability.of_finite_crossRelated {C D : SaturatedChain α}
    (hleft : ∀ y : D, (incomparabilityTrace C y.1).Finite)
    (hright : ∀ x : C, (incomparabilityTrace D x.1).Finite)
    (hcontactLeft : ∀ y : D, ∃ x : C, CrossRelated x y)
    (hcontactRight : ∀ x : C, ∃ y : D, CrossRelated x y) :
    MutuallyFiniteIncomparability C D := by
  refine ⟨⟨maximalIn_convexHull_union_of_crossRelated hcontactLeft, ?_⟩, hleft, hright⟩
  rw [union_comm]
  apply maximalIn_convexHull_union_of_crossRelated
  intro x
  obtain ⟨y, hxy | hxy⟩ := hcontactRight x
  · exact ⟨y, Or.inl hxy.symm⟩
  · exact ⟨y, Or.inr hxy.symm⟩

/-- Paper `def:mutually-finite-incomp`: both equality-or-incomparability traces
are finite and nonempty at every point. -/
theorem mutuallyFiniteIncomparability_iff_crossRelated {C D : SaturatedChain α} :
    MutuallyFiniteIncomparability C D ↔
      (∀ x : C, ({y : D | CrossRelated x y} : Set D).Finite ∧
        ({y : D | CrossRelated x y} : Set D).Nonempty) ∧
      (∀ y : D, ({x : C | CrossRelated x y} : Set C).Finite ∧
        ({x : C | CrossRelated x y} : Set C).Nonempty) := by
  constructor
  · intro h
    constructor
    · intro x
      have heq : ({y : D | x.1 = y.1} : Set D).Finite :=
        Set.Subsingleton.finite (fun _ hy _ hz => Subtype.ext (hy.symm.trans hz))
      refine ⟨(heq.union (h.right_finite x)).subset ?_, h.exists_crossRelated_right x⟩
      rintro y (hey | hxy)
      · exact Or.inl hey
      · exact Or.inr hxy.symm
    · intro y
      have heq : ({x : C | x.1 = y.1} : Set C).Finite :=
        Set.Subsingleton.finite (fun _ hx _ hz => Subtype.ext (hx.trans hz.symm))
      exact ⟨heq.union (h.left_finite y), h.exists_crossRelated_left y⟩
  · rintro ⟨hD, hC⟩
    exact MutuallyFiniteIncomparability.of_finite_crossRelated
      (fun y => (hC y).1.subset (fun _ hx => Or.inr hx))
      (fun x => (hD x).1.subset (fun _ hy => Or.inr hy.symm))
      (fun y => (hC y).2) (fun x => (hD x).2)

theorem MutuallyFiniteIncomparability.dual {C D : SaturatedChain α}
    (h : MutuallyFiniteIncomparability C D) : MutuallyFiniteIncomparability C.dual D.dual := by
  apply MutuallyFiniteIncomparability.of_finite_crossRelated
  · intro d
    exact (h.left_finite ⟨d.1, d.2⟩).subset (fun _ hx => ⟨hx.2, hx.1⟩)
  · intro c
    exact (h.right_finite ⟨c.1, c.2⟩).subset (fun _ hx => ⟨hx.2, hx.1⟩)
  · intro d
    obtain ⟨c, hc | hc⟩ := h.exists_crossRelated_left ⟨d.1, d.2⟩
    · exact ⟨⟨c.1, c.2⟩, Or.inl hc⟩
    · exact ⟨⟨c.1, c.2⟩, Or.inr ⟨hc.2, hc.1⟩⟩
  · intro c
    obtain ⟨d, hd | hd⟩ := h.exists_crossRelated_right ⟨c.1, c.2⟩
    · exact ⟨⟨d.1, d.2⟩, Or.inl hd⟩
    · exact ⟨⟨d.1, d.2⟩, Or.inr ⟨hd.2, hd.1⟩⟩

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

/-- Saturation means maximality in the chain's own convex hull. -/
theorem SaturatedChain.maximalIn_convexHull (C : SaturatedChain α) :
    IsMaximalChainIn C (convexHull (C : Set α)) := by
  refine ⟨fun x hx => ⟨x, hx, x, hx, le_rfl, le_rfl⟩, C.isChain, ?_⟩
  intro D hD hsub hCD
  apply Set.Subset.antisymm hCD
  intro x hx
  obtain ⟨a, ha, b, hb, hax, hxb⟩ := hsub hx
  exact C.mem_of_between ha hb hax hxb (fun c hc => hD.total hx (hCD hc))

/-- A saturated chain has mutually finite incomparability with itself. -/
theorem MutuallyFiniteIncomparability.refl (C : SaturatedChain α) :
    MutuallyFiniteIncomparability C C where
  maximal := by
    have hmax : IsMaximalChainIn C (convexHull ((C : Set α) ∪ C)) := by
      simpa only [Set.union_self] using C.maximalIn_convexHull
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

/-- Different corresponding distance classes are separated in the ambient order, in both cross
directions.  This is the main geometric interface used when composing normalized witnesses. -/
theorem MutuallyFiniteIncomparability.crossRelated_separates
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D)
    {x x' : C} {y y' : D} (hxx' : FiniteDistanceClass.mk x < FiniteDistanceClass.mk x')
    (hxy : CrossRelated x y) (hx'y' : CrossRelated x' y') :
    x.1 < y'.1 ∧ y.1 < x'.1 := by
  rw [FiniteDistanceClass.mk_lt_mk] at hxx'
  have hyy' : y < y' := h.crossRelated_strictMono hxx'.1 hxx'.2 hxy hx'y'
  have htargetFar : ¬FiniteDistance D y y' := by
    intro hdist
    exact hxx'.2
      (h.symm.crossRelated_respects_finiteDistance hdist hxy.symm hx'y'.symm)
  have hxy'Comp : ¬Incomparable x.1 y'.1 := by
    intro hinc
    exact htargetFar (h.crossRelated_same_source hxy (Or.inr hinc))
  have hnotY'LeX : ¬y'.1 ≤ x.1 := by
    intro hy'x
    exact hxy.elim
      (fun heq => (not_lt_of_ge (hy'x.trans (le_of_eq heq)))
        (show y.1 < y'.1 from hyy'))
      (fun hinc => hinc.not_ge
        ((show y.1 ≤ y'.1 from hyy'.le).trans hy'x))
  have hxy'Le : x.1 ≤ y'.1 := by
    rcases not_incompRel_iff_symmGen.mp hxy'Comp with hxy' | hy'x
    · exact hxy'
    · exact False.elim (hnotY'LeX hy'x)
  have hxy'Lt : x.1 < y'.1 :=
    lt_of_le_of_ne hxy'Le (fun heq => hnotY'LeX (le_of_eq heq.symm))
  have hyx'Comp : ¬Incomparable y.1 x'.1 := by
    intro hinc
    exact hxx'.2 (h.symm.crossRelated_same_source hxy.symm (Or.inr hinc))
  have hnotX'LeY : ¬x'.1 ≤ y.1 := by
    intro hx'y
    exact hx'y'.elim
      (fun heq => (not_lt_of_ge ((le_of_eq heq.symm).trans hx'y))
        (show y.1 < y'.1 from hyy'))
      (fun hinc => hinc.not_le
        (hx'y.trans (show y.1 ≤ y'.1 from hyy'.le)))
  have hyx'Le : y.1 ≤ x'.1 := by
    rcases not_incompRel_iff_symmGen.mp hyx'Comp with hyx' | hx'y
    · exact hyx'
    · exact False.elim (hnotX'LeY hx'y)
  exact ⟨hxy'Lt,
    lt_of_le_of_ne hyx'Le (fun heq => hnotX'LeY (le_of_eq heq.symm))⟩

/-- A no-top target is cofinal above every point of a mutually finite-incomparable source. -/
theorem MutuallyFiniteIncomparability.exists_right_gt
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D)
    (hD : D.NoTop) (x : C) : ∃ y : D, x.1 < y.1 := by
  classical
  obtain ⟨d, hxd⟩ := h.exists_crossRelated_right x
  let S : Set D := insert d (incomparabilityTrace D x.1)
  have hSfinite : S.Finite := (Set.finite_singleton d).union (h.right_finite x)
  obtain ⟨b, hbS, hbmax⟩ := hSfinite.exists_maximal ⟨d, Set.mem_insert d _⟩
  have hbUpper : ∀ w ∈ S, w ≤ b := by
    intro w hw
    rcases le_total w b with hwb | hbw
    · exact hwb
    · exact hbmax hw hbw
  obtain ⟨y, hby⟩ := hD.exists_gt b
  have hyNotTrace : y ∉ incomparabilityTrace D x.1 := by
    intro hy
    exact (not_lt_of_ge (hbUpper y (Set.mem_insert_of_mem d hy))) hby
  have hnotYLeX : ¬y.1 ≤ x.1 := by
    intro hyx
    have hdy : d.1 < y.1 := (hbUpper d (Set.mem_insert d _)).trans_lt hby
    exact hxd.elim
      (fun heq => (not_lt_of_ge (hyx.trans (le_of_eq heq))) hdy)
      (fun hinc => hinc.not_ge (hdy.le.trans hyx))
  rcases not_incompRel_iff_symmGen.mp hyNotTrace with hyx | hxy
  · exact False.elim (hnotYLeX hyx)
  · exact ⟨y, lt_of_le_of_ne hxy (fun heq => hnotYLeX (le_of_eq heq.symm))⟩

/-- Symmetric cofinality form. -/
theorem MutuallyFiniteIncomparability.exists_left_gt
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D)
    (hC : C.NoTop) (y : D) : ∃ x : C, y.1 < x.1 :=
  h.symm.exists_right_gt hC y

/-- Paper `lem:mfi-max-iff-max`, increasing direction. -/
theorem MutuallyFiniteIncomparability.hasTop_iff {C D : SaturatedChain α}
    (h : MutuallyFiniteIncomparability C D) : C.HasTop ↔ D.HasTop := by
  have preserves {A B : SaturatedChain α} (hAB : MutuallyFiniteIncomparability A B)
      (hA : A.HasTop) : B.HasTop := by
    by_contra hB
    obtain ⟨m, hm⟩ := hA
    obtain ⟨b, hmb⟩ := hAB.exists_right_gt hB m
    obtain ⟨a, hab⟩ := hAB.exists_crossRelated_left b
    have hab' : a.1 < b.1 := (show a.1 ≤ m.1 from hm a).trans_lt hmb
    exact hab.elim hab'.ne (fun hi => hi.not_le hab'.le)
  exact ⟨preserves h, preserves h.symm⟩

/-- Paper `lem:mfi-max-iff-max`, decreasing direction. -/
theorem MutuallyFiniteIncomparability.hasBottom_iff {C D : SaturatedChain α}
    (h : MutuallyFiniteIncomparability C D) : C.HasBottom ↔ D.HasBottom := by
  simpa only [SaturatedChain.dual_hasTop_iff] using h.dual.hasTop_iff

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

/-- Paper `lem:mfi-canonical-isomorphism`: mutually finite-incomparable chains have
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

theorem MutuallyFiniteIncomparability.classOrderIso_mk_of_crossRelated
    {C D : SaturatedChain α} (h : MutuallyFiniteIncomparability C D)
    {x : C} {y : D} (hxy : CrossRelated x y) :
    h.classOrderIso (FiniteDistanceClass.mk x) = FiniteDistanceClass.mk y :=
  h.class_correspondence_unique_right (h.classMap_corresponds _) ⟨x, y, rfl, rfl, hxy⟩

/-- The class `X` as a saturated subchain of the original poset. -/
def FiniteDistanceClass.chain {C : SaturatedChain α} (X : FiniteDistanceClass C) :
    SaturatedChain α where
  carrier := {a | ∃ ha : a ∈ C, FiniteDistanceClass.mk (⟨a, ha⟩ : C) = X}
  nonempty := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep X
    exact ⟨x.1, x.2, rfl⟩
  saturated := by
    apply C.saturated.restrict (fun _ ha => ha.choose)
    rintro a b z ⟨ha, haX⟩ ⟨hb, hbX⟩ hz haz hzb
    refine ⟨hz, ?_⟩
    rw [← haX, FiniteDistanceClass.mk_eq_mk]
    exact ((finiteDistanceClassSet_ordConnected C (⟨a, ha⟩ : C)).out
      (FiniteDistance.refl C _) (FiniteDistanceClass.mk_eq_mk.mp (haX.trans hbX.symm))
      ⟨haz, hzb⟩).symm

/-- Paper `lem:mfi-quotient`: corresponding finite-distance classes have
mutually finite incomparability. -/
theorem MutuallyFiniteIncomparability.classOrderIso_mfi {C D : SaturatedChain α}
    (h : MutuallyFiniteIncomparability C D) (X : FiniteDistanceClass C) :
    MutuallyFiniteIncomparability X.chain (h.classOrderIso X).chain := by
  let left (a : X.chain) : C := ⟨a.1, a.2.choose⟩
  let right (b : (h.classOrderIso X).chain) : D := ⟨b.1, b.2.choose⟩
  apply MutuallyFiniteIncomparability.of_finite_crossRelated
  · intro b
    exact (h.left_finite (right b)).of_injective (f := fun a => ⟨left a.1, a.2⟩)
      (fun _ _ eq => Subtype.ext (Subtype.ext (congrArg (fun t => t.1.1) eq)))
  · intro a
    exact (h.right_finite (left a)).of_injective (f := fun b => ⟨right b.1, b.2⟩)
      (fun _ _ eq => Subtype.ext (Subtype.ext (congrArg (fun t => t.1.1) eq)))
  · intro b
    obtain ⟨a, hab⟩ := h.exists_crossRelated_left (right b)
    have ha : FiniteDistanceClass.mk a = X := h.classOrderIso.injective
      ((h.classOrderIso_mk_of_crossRelated hab).trans b.2.choose_spec)
    exact ⟨⟨a.1, a.2, ha⟩, hab⟩
  · intro a
    obtain ⟨b, hab⟩ := h.exists_crossRelated_right (left a)
    have hb : FiniteDistanceClass.mk b = h.classOrderIso X :=
      (h.classOrderIso_mk_of_crossRelated hab).symm.trans
        (congrArg h.classOrderIso a.2.choose_spec)
    exact ⟨⟨b.1, b.2, hb⟩, hab⟩

/-- Paper `lem:mfi-quotient`: different corresponding classes are cross-ordered. -/
theorem MutuallyFiniteIncomparability.classOrderIso_separates {C D : SaturatedChain α}
    (h : MutuallyFiniteIncomparability C D) {X Y : FiniteDistanceClass C} (hXY : X < Y) :
    SetStrictLT (X.chain : Set α) (h.classOrderIso Y).chain ∧
      SetStrictLT ((h.classOrderIso X).chain : Set α) Y.chain := by
  have separate {a c : α} (ha : a ∈ X.chain) (hc : c ∈ Y.chain) :
      ∀ {b d : α} (hb : b ∈ (h.classOrderIso X).chain) (hd : d ∈ (h.classOrderIso Y).chain),
      CrossRelated (⟨a, ha.choose⟩ : C) (⟨b, hb.choose⟩ : D) →
      CrossRelated (⟨c, hc.choose⟩ : C) (⟨d, hd.choose⟩ : D) →
      a < d ∧ b < c := by
    intro b d hb hd hab hcd
    have hclasses : FiniteDistanceClass.mk (⟨a, ha.choose⟩ : C) <
        FiniteDistanceClass.mk (⟨c, hc.choose⟩ : C) := by
      rw [ha.choose_spec, hc.choose_spec]
      exact hXY
    exact h.crossRelated_separates hclasses hab hcd
  constructor
  · intro a ha d hd
    obtain ⟨b, hab⟩ := (h.classOrderIso_mfi X).exists_crossRelated_right ⟨a, ha⟩
    obtain ⟨c, hcd⟩ := (h.classOrderIso_mfi Y).exists_crossRelated_left ⟨d, hd⟩
    exact (separate ha c.2 b.2 hd hab hcd).1
  · intro b hb c hc
    obtain ⟨a, hab⟩ := (h.classOrderIso_mfi X).exists_crossRelated_left ⟨b, hb⟩
    obtain ⟨d, hcd⟩ := (h.classOrderIso_mfi Y).exists_crossRelated_right ⟨c, hc⟩
    exact (separate a.2 hc hb d.2 hab hcd).2

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
