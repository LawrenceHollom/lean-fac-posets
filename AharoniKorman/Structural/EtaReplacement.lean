import AharoniKorman.Structural.EtaChains
import AharoniKorman.Preliminaries.FAC
import AharoniKorman.Preliminaries.ReplacementOrder
import Mathlib.Order.Zorn

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- Witness data for replacing points of one eta-maximal chain by singleton or eta intervals. -/
structure EtaReplacement (C D : Set α) where
  source : IsEtaMaximalChain C
  target : IsEtaMaximalChain D
  image : C → Set α
  image_nonempty : ∀ x, (image x).Nonempty
  image_interval : ∀ x, IsIntervalIn (image x) D
  image_shape : ∀ x, image x = {x.1} ∨ IsEtaChain (image x)
  source_lt_image : ∀ x y : C, x.1 < y.1 → ∀ z ∈ image y, x.1 < z
  image_lt_source : ∀ x y : C, x.1 < y.1 → ∀ z ∈ image x, z < y.1

def EtaReplacement.Trivial {C D : Set α} (f : EtaReplacement C D) : Prop :=
  ∀ x, f.image x = {x.1}

/-- The replacement relation between eta-maximal chains. -/
def EtaReplaces (C D : Set α) : Prop := Nonempty (EtaReplacement C D)

/-- The identity replacement. -/
def EtaReplacement.identity {C : Set α} (hC : IsEtaMaximalChain C) :
    EtaReplacement C C where
  source := hC
  target := hC
  image x := {x.1}
  image_nonempty x := Set.singleton_nonempty x.1
  image_interval x := by
    refine ⟨Set.singleton_subset_iff.mpr x.2, ?_⟩
    rintro _ rfl _ rfl _ z _ hxz hzx
    exact Set.mem_singleton_iff.mpr (le_antisymm hzx hxz)
  image_shape x := Or.inl rfl
  source_lt_image x y hxy z hz := by simpa only [Set.mem_singleton_iff] using hz ▸ hxy
  image_lt_source x y hxy z hz := by simpa only [Set.mem_singleton_iff] using hz ▸ hxy

theorem etaReplaces_refl {C : Set α} (hC : IsEtaMaximalChain C) : EtaReplaces C C :=
  ⟨EtaReplacement.identity hC⟩

/-- Paper Lemma `lem:etalt-comparability`. -/
theorem EtaReplacement.image_strictLT {C D : Set α} (f : EtaReplacement C D)
    {x y : C} (hxy : x.1 < y.1) : SetStrictLT (f.image x) (f.image y) := by
  obtain ⟨z, hzC, hxz, hzy⟩ := f.source.1.exists_between x.2 y.2 hxy
  intro u hu v hv
  exact (f.image_lt_source x ⟨z, hzC⟩ hxz u hu).trans
    (f.source_lt_image ⟨z, hzC⟩ y hzy v hv)

/-- Images of ordered source points are ordered even when taken from two different replacement
witnesses with the same source and target. -/
theorem EtaReplacement.cross_image_strictLT {C D : Set α}
    (f g : EtaReplacement C D) {x y : C} (hxy : x.1 < y.1)
    {u v : α} (hu : u ∈ f.image x) (hv : v ∈ g.image y) : u < v := by
  obtain ⟨z, hzC, hxz, hzy⟩ := f.source.1.exists_between x.2 y.2 hxy
  exact (f.image_lt_source x ⟨z, hzC⟩ hxz u hu).trans
    (g.source_lt_image ⟨z, hzC⟩ y hzy v hv)

theorem EtaReplacement.images_disjoint {C D : Set α} (f : EtaReplacement C D)
    {x y : C} (hxy : x ≠ y) : Disjoint (f.image x) (f.image y) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  rcases f.source.1.isChain x.2 y.2 hval with hle | hge
  · exact (f.image_strictLT (lt_of_le_of_ne hle hval) hzx hzy).ne rfl
  · exact (f.image_strictLT (lt_of_le_of_ne hge hval.symm) hzy hzx).ne rfl

theorem EtaReplacement.trivial_source_subset {C D : Set α} (f : EtaReplacement C D)
    (hf : f.Trivial) : C ⊆ D := by
  intro x hx
  have : x ∈ f.image ⟨x, hx⟩ := by
    rw [hf]
    exact Set.mem_singleton x
  exact (f.image_interval _).1 this

theorem EtaReplacement.eq_of_trivial {C D : Set α} (f : EtaReplacement C D)
    (hf : f.Trivial) : C = D :=
  (f.source.2 D f.target.1 (f.trivial_source_subset hf)).symm

private def EtaReplacement.toTarget {C D : Set α} (f : EtaReplacement C D)
    (x : C) (z : f.image x) : D := ⟨z.1, (f.image_interval x).1 z.2⟩

private def composedRaw {C D E : Set α} (f : EtaReplacement C D)
    (g : EtaReplacement D E) (x : C) : Set α :=
  ⋃ z : f.image x, g.image (f.toTarget x z)

private theorem composedRaw_nonempty {C D E : Set α} (f : EtaReplacement C D)
    (g : EtaReplacement D E) (x : C) : (composedRaw f g x).Nonempty := by
  obtain ⟨z, hz⟩ := f.image_nonempty x
  obtain ⟨w, hw⟩ := g.image_nonempty (f.toTarget x ⟨z, hz⟩)
  exact ⟨w, Set.mem_iUnion_of_mem ⟨z, hz⟩ hw⟩

private theorem composedRaw_subset {C D E : Set α} (f : EtaReplacement C D)
    (g : EtaReplacement D E) (x : C) : composedRaw f g x ⊆ E := by
  intro w hw
  simp only [composedRaw, Set.mem_iUnion] at hw
  obtain ⟨z, hwz⟩ := hw
  exact (g.image_interval _).1 hwz

private theorem composedRaw_of_singleton {C D E : Set α} (f : EtaReplacement C D)
    (g : EtaReplacement D E) (x : C) (hx : f.image x = {x.1}) :
    composedRaw f g x = g.image ⟨x.1, (f.image_interval x).1 (by simp [hx])⟩ := by
  apply Set.Subset.antisymm
  · intro w hw
    simp only [composedRaw, Set.mem_iUnion] at hw
    obtain ⟨z, hwz⟩ := hw
    have hz : z.1 = x.1 := by
      exact Set.mem_singleton_iff.mp (show z.1 ∈ {x.1} from hx ▸ z.2)
    simpa only [EtaReplacement.toTarget, hz] using hwz
  · intro w hw
    apply Set.mem_iUnion_of_mem (show f.image x from ⟨x.1, by simp [hx]⟩)
    exact hw

/-- Paper Lemma `lem:etalt-transitive`: replacement witnesses compose by taking the convex hull,
inside the final chain, of the iterated images. -/
def EtaReplacement.comp [Countable α] {C D E : Set α}
    (g : EtaReplacement D E) (f : EtaReplacement C D) : EtaReplacement C E where
  source := f.source
  target := g.target
  image x := convexHullIn E (composedRaw f g x)
  image_nonempty x := (composedRaw_nonempty f g x).mono
    (subset_convexHullIn (composedRaw_subset f g x))
  image_interval x := convexHullIn_interval E (composedRaw f g x)
  image_shape x := by
    rcases f.image_shape x with hx | hx
    · let xD : D := ⟨x.1, (f.image_interval x).1 (by simp [hx])⟩
      have hraw := composedRaw_of_singleton f g x hx
      rw [hraw, convexHullIn_eq_self (g.image_interval xD)]
      exact g.image_shape xD
    · right
      obtain ⟨e⟩ := hx
      let B : ℚ → Set α := fun q => g.image (f.toTarget x (e q))
      have hB : IsEtaChain (⋃ q, B q) := eta_nesting B
        (fun q => g.image_nonempty _)
        (fun q => by
          rcases g.image_shape (f.toTarget x (e q)) with h | h
          · exact Or.inl ⟨_, h⟩
          · exact Or.inr h)
        (fun p q hpq => g.image_strictLT (e.lt_iff_lt.mpr hpq))
      have hraw : composedRaw f g x = ⋃ q, B q := by
        apply Set.Subset.antisymm
        · intro w hw
          simp only [composedRaw, Set.mem_iUnion] at hw
          obtain ⟨z, hwz⟩ := hw
          exact Set.mem_iUnion_of_mem (e.symm z) (by simpa [B] using hwz)
        · intro w hw
          simp only [Set.mem_iUnion] at hw
          obtain ⟨q, hwq⟩ := hw
          exact Set.mem_iUnion_of_mem (e q) (by simpa [B] using hwq)
      rw [hraw]
      apply etaChain_convexHullIn hB
      · simpa only [← hraw] using composedRaw_subset f g x
      · exact g.target.1
  source_lt_image x y hxy z hz := by
    obtain ⟨w, hwC, hxw, hwy⟩ := f.source.1.exists_between x.2 y.2 hxy
    obtain ⟨u, hu⟩ := f.image_nonempty ⟨w, hwC⟩
    obtain ⟨_, a, haRaw, b, hbRaw, haz, hzb⟩ := hz
    simp only [composedRaw, Set.mem_iUnion] at haRaw
    obtain ⟨d, had⟩ := haRaw
    have hxu : x.1 < u := f.source_lt_image x ⟨w, hwC⟩ hxw u hu
    have hud : u < d.1 := f.image_strictLT hwy hu d.2
    have hua : u < a := g.source_lt_image (f.toTarget ⟨w, hwC⟩ ⟨u, hu⟩)
      (f.toTarget y d) hud a had
    exact hxu.trans (hua.trans_le haz)
  image_lt_source x y hxy z hz := by
    obtain ⟨w, hwC, hxw, hwy⟩ := f.source.1.exists_between x.2 y.2 hxy
    obtain ⟨u, hu⟩ := f.image_nonempty ⟨w, hwC⟩
    obtain ⟨_, a, haRaw, b, hbRaw, haz, hzb⟩ := hz
    simp only [composedRaw, Set.mem_iUnion] at hbRaw
    obtain ⟨d, hbd⟩ := hbRaw
    have hdu : d.1 < u := f.image_strictLT hxw d.2 hu
    have hbu : b < u := g.image_lt_source (f.toTarget x d)
      (f.toTarget ⟨w, hwC⟩ ⟨u, hu⟩) hdu b hbd
    have huy : u < y.1 := f.image_lt_source ⟨w, hwC⟩ y hwy u hu
    exact hzb.trans_lt (hbu.trans huy)

theorem etaReplaces_trans [Countable α] {C D E : Set α} :
    EtaReplaces C D → EtaReplaces D E → EtaReplaces C E := by
  rintro ⟨f⟩ ⟨g⟩
  exact ⟨g.comp f⟩

theorem EtaReplacement.eq_source_of_mem_image {C D : Set α} (f : EtaReplacement C D)
    (x : C) {y : α} (hyC : y ∈ C) (hyImage : y ∈ f.image x) : y = x.1 := by
  by_contra hyx
  rcases f.source.1.isChain hyC x.2 hyx with hyxle | hxyle
  · have hyxlt : y < x.1 := lt_of_le_of_ne hyxle hyx
    exact (f.source_lt_image ⟨y, hyC⟩ x hyxlt y hyImage).ne rfl
  · have hxylt : x.1 < y := lt_of_le_of_ne hxyle (Ne.symm hyx)
    exact (f.image_lt_source x ⟨y, hyC⟩ hxylt y hyImage).ne rfl

/-- Paper Lemma `lem:etalt-incomparability`: a genuinely new point in a replacement fibre is
incomparable with the source point it replaces. -/
theorem EtaReplacement.image_incomparable [Countable α] {C D : Set α}
    (f : EtaReplacement C D) (x : C) {y : α} (hy : y ∈ f.image x) (hyx : y ≠ x.1) :
    Incomparable y x.1 := by
  have hImageEta : IsEtaChain (f.image x) := by
    rcases f.image_shape x with hsingleton | heta
    · exfalso
      exact hyx (Set.mem_singleton_iff.mp (hsingleton ▸ hy))
    · exact heta
  refine ⟨?_, ?_⟩
  · intro hy_le_x
    have hy_lt_x : y < x.1 := lt_of_le_of_ne hy_le_x hyx
    let Y := f.image x ∩ Set.Iio y
    have hY : IsEtaChain Y := hImageEta.lowerSection hy
    have hUnion : IsEtaChain (C ∪ Y) := etaChain_union_fiber_below f.source.1 x.2 hY
      (fun c hc hcx z hz => f.source_lt_image ⟨c, hc⟩ x hcx z hz.1)
      (fun c hc hxc z hz => f.image_lt_source x ⟨c, hc⟩ hxc z hz.1)
      (fun z hz => hz.2.trans hy_lt_x)
    obtain ⟨z, hzY⟩ := hY.nonempty
    have hzNotC : z ∉ C := by
      intro hzC
      have hzx := f.eq_source_of_mem_image x hzC hzY.1
      exact (hzY.2.trans hy_lt_x).ne hzx
    have hEq := f.source.2 (C ∪ Y) hUnion Set.subset_union_left
    exact hzNotC (by rw [← hEq]; exact Or.inr hzY)
  · intro hx_le_y
    have hx_lt_y : x.1 < y := lt_of_le_of_ne hx_le_y (Ne.symm hyx)
    let Y := f.image x ∩ Set.Ioi y
    have hY : IsEtaChain Y := hImageEta.upperSection hy
    have hUnion : IsEtaChain (C ∪ Y) := etaChain_union_fiber_above f.source.1 x.2 hY
      (fun c hc hcx z hz => f.source_lt_image ⟨c, hc⟩ x hcx z hz.1)
      (fun c hc hxc z hz => f.image_lt_source x ⟨c, hc⟩ hxc z hz.1)
      (fun z hz => hx_lt_y.trans hz.2)
    obtain ⟨z, hzY⟩ := hY.nonempty
    have hzNotC : z ∉ C := by
      intro hzC
      have hzx := f.eq_source_of_mem_image x hzC hzY.1
      exact (hx_lt_y.trans hzY.2).ne hzx.symm
    have hEq := f.source.2 (C ∪ Y) hUnion Set.subset_union_left
    exact hzNotC (by rw [← hEq]; exact Or.inr hzY)

theorem EtaReplacement.self_trivial {C : Set α} (f : EtaReplacement C C) : f.Trivial := by
  intro x
  apply Set.Subset.antisymm
  · intro y hy
    exact Set.mem_singleton_iff.mpr (f.eq_source_of_mem_image x ((f.image_interval x).1 hy) hy)
  · obtain ⟨y, hy⟩ := f.image_nonempty x
    have hyx := f.eq_source_of_mem_image x ((f.image_interval x).1 hy) hy
    simpa only [Set.singleton_subset_iff, ← hyx] using hy

theorem EtaReplacement.trivial_left_of_comp_trivial [Countable α]
    {C D E : Set α} (g : EtaReplacement D E) (f : EtaReplacement C D)
    (hcomp : (g.comp f).Trivial) : f.Trivial := by
  intro x
  rcases f.image_shape x with hx | heta
  · exact hx
  · exfalso
    obtain ⟨d, hd⟩ := heta.nonempty
    obtain ⟨e, he, hde⟩ := heta.exists_gt hd
    let dD : D := ⟨d, (f.image_interval x).1 hd⟩
    let eD : D := ⟨e, (f.image_interval x).1 he⟩
    obtain ⟨u, hu⟩ := g.image_nonempty dD
    obtain ⟨v, hv⟩ := g.image_nonempty eD
    have huComp : u ∈ (g.comp f).image x :=
      subset_convexHullIn (composedRaw_subset f g x)
        (Set.mem_iUnion_of_mem (show f.image x from ⟨d, hd⟩) hu)
    have hvComp : v ∈ (g.comp f).image x :=
      subset_convexHullIn (composedRaw_subset f g x)
        (Set.mem_iUnion_of_mem (show f.image x from ⟨e, he⟩) hv)
    have hux : u = x.1 := Set.mem_singleton_iff.mp (hcomp x ▸ huComp)
    have hvx : v = x.1 := Set.mem_singleton_iff.mp (hcomp x ▸ hvComp)
    have hne : dD ≠ eD := fun h => hde.ne (congrArg Subtype.val h)
    exact Set.disjoint_left.mp (g.images_disjoint hne) hu (by simpa [hux, hvx] using hv)

theorem EtaReplacement.comp_image_eta_of_image_eta [Countable α]
    {C D E : Set α} (g : EtaReplacement D E) (f : EtaReplacement C D) (x : C)
    (heta : IsEtaChain (f.image x)) : IsEtaChain ((g.comp f).image x) := by
  rcases (g.comp f).image_shape x with hsingleton | hresult
  · exfalso
    obtain ⟨d, hd⟩ := heta.nonempty
    obtain ⟨e, he, hde⟩ := heta.exists_gt hd
    let dD : D := ⟨d, (f.image_interval x).1 hd⟩
    let eD : D := ⟨e, (f.image_interval x).1 he⟩
    obtain ⟨u, hu⟩ := g.image_nonempty dD
    obtain ⟨v, hv⟩ := g.image_nonempty eD
    have huComp : u ∈ (g.comp f).image x :=
      subset_convexHullIn (composedRaw_subset f g x)
        (Set.mem_iUnion_of_mem (show f.image x from ⟨d, hd⟩) hu)
    have hvComp : v ∈ (g.comp f).image x :=
      subset_convexHullIn (composedRaw_subset f g x)
        (Set.mem_iUnion_of_mem (show f.image x from ⟨e, he⟩) hv)
    have huv : u = v := (Set.mem_singleton_iff.mp (hsingleton ▸ huComp)).trans
      (Set.mem_singleton_iff.mp (hsingleton ▸ hvComp)).symm
    have hne : dD ≠ eD := fun h => hde.ne (congrArg Subtype.val h)
    exact Set.disjoint_left.mp (g.images_disjoint hne) hu (huv ▸ hv)
  · exact hresult

theorem etaReplaces_antisymm [Countable α] {C D : Set α}
    (hCD : EtaReplaces C D) (hDC : EtaReplaces D C) : C = D := by
  obtain ⟨f⟩ := hCD
  obtain ⟨g⟩ := hDC
  have hgf : (g.comp f).Trivial := (g.comp f).self_trivial
  exact f.eq_of_trivial (EtaReplacement.trivial_left_of_comp_trivial g f hgf)

/-- Paper Lemma `lem:etalt-antisymmetric`, in its persistence form: once a source point is
removed, no later replacement can reintroduce it. -/
theorem EtaReplacement.not_mem_of_not_mem_comp [Countable α]
    {C D E : Set α} (f : EtaReplacement C D) (g : EtaReplacement D E)
    {x : α} (hxC : x ∈ C) (hxD : x ∉ D) : x ∉ E := by
  intro hxE
  let xC : C := ⟨x, hxC⟩
  have hfEta : IsEtaChain (f.image xC) := by
    rcases f.image_shape xC with hsingleton | heta
    · have hxmem : x ∈ f.image xC := hsingleton.symm ▸ Set.mem_singleton x
      exact False.elim (hxD ((f.image_interval xC).1 hxmem))
    · exact heta
  let h := g.comp f
  have hhEta : IsEtaChain (h.image xC) := g.comp_image_eta_of_image_eta f xC hfEta
  obtain ⟨y, hyF⟩ := hhEta.nonempty
  have hyE : y ∈ E := (h.image_interval xC).1 hyF
  have contradiction_above (Y : Set α) (hY : IsEtaChain Y)
      (hYF : Y ⊆ h.image xC) (hxY : ∀ z ∈ Y, x < z) : False := by
    have hUnion : IsEtaChain (C ∪ Y) := etaChain_union_fiber_above h.source.1 hxC hY
      (fun c hc hcx z hz => h.source_lt_image ⟨c, hc⟩ xC hcx z (hYF hz))
      (fun c hc hxc z hz => h.image_lt_source xC ⟨c, hc⟩ hxc z (hYF hz)) hxY
    obtain ⟨z, hzY⟩ := hY.nonempty
    have hzNotC : z ∉ C := by
      intro hzC
      have hzx := h.eq_source_of_mem_image xC hzC (hYF hzY)
      exact (hxY z hzY).ne hzx.symm
    have hEq := h.source.2 (C ∪ Y) hUnion Set.subset_union_left
    exact hzNotC (by rw [← hEq]; exact Or.inr hzY)
  have contradiction_below (Y : Set α) (hY : IsEtaChain Y)
      (hYF : Y ⊆ h.image xC) (hYx : ∀ z ∈ Y, z < x) : False := by
    have hUnion : IsEtaChain (C ∪ Y) := etaChain_union_fiber_below h.source.1 hxC hY
      (fun c hc hcx z hz => h.source_lt_image ⟨c, hc⟩ xC hcx z (hYF hz))
      (fun c hc hxc z hz => h.image_lt_source xC ⟨c, hc⟩ hxc z (hYF hz)) hYx
    obtain ⟨z, hzY⟩ := hY.nonempty
    have hzNotC : z ∉ C := by
      intro hzC
      have hzx := h.eq_source_of_mem_image xC hzC (hYF hzY)
      exact (hYx z hzY).ne hzx
    have hEq := h.source.2 (C ∪ Y) hUnion Set.subset_union_left
    exact hzNotC (by rw [← hEq]; exact Or.inr hzY)
  rcases eq_or_ne y x with rfl | hyx
  · let Y := h.image xC ∩ Set.Ioi y
    exact contradiction_above Y (hhEta.upperSection hyF) Set.inter_subset_left (fun z hz => hz.2)
  · rcases h.target.1.isChain hyE hxE hyx with hyxle | hxyle
    · have hyxlt : y < x := lt_of_le_of_ne hyxle hyx
      let Y := h.image xC ∩ Set.Iio y
      exact contradiction_below Y (hhEta.lowerSection hyF) Set.inter_subset_left
        (fun z hz => hz.2.trans hyxlt)
    · have hxylt : x < y := lt_of_le_of_ne hxyle (Ne.symm hyx)
      let Y := h.image xC ∩ Set.Ioi y
      exact contradiction_above Y (hhEta.upperSection hyF) Set.inter_subset_left
        (fun z hz => hxylt.trans hz.2)

theorem EtaReplacement.image_eq_singleton_of_mem_target [Countable α]
    {C D : Set α} (f : EtaReplacement C D) (x : C) (hxD : x.1 ∈ D) :
    f.image x = {x.1} := by
  rcases f.image_shape x with h | heta
  · exact h
  · exfalso
    obtain ⟨y, hy⟩ := heta.nonempty
    by_cases hyx : y = x.1
    · obtain ⟨z, hz, hyz⟩ := heta.exists_gt hy
      have hzD := (f.image_interval x).1 hz
      have hzx : z ≠ x.1 := fun h => hyz.ne (hyx.trans h.symm)
      have hinc := f.image_incomparable x hz hzx
      rcases f.target.1.isChain hzD hxD hzx with h | h
      · exact hinc.not_le h
      · exact hinc.not_ge h
    · have hyD := (f.image_interval x).1 hy
      have hinc := f.image_incomparable x hy hyx
      rcases f.target.1.isChain hyD hxD hyx with h | h
      · exact hinc.not_le h
      · exact hinc.not_ge h

/-- Eta-maximal chains bundled as the carrier of the replacement partial order. -/
structure EtaChainObject (α : Type*) [PartialOrder α] where
  carrier : Set α
  etaMaximal : IsEtaMaximalChain carrier

instance : SetLike (EtaChainObject α) α where
  coe C := C.carrier
  coe_injective C D h := by cases C; cases D; cases h; rfl

instance [Countable α] : PartialOrder (EtaChainObject α) where
  le C D := EtaReplaces C.carrier D.carrier
  le_refl C := etaReplaces_refl C.etaMaximal
  le_trans _ _ _ := etaReplaces_trans
  le_antisymm C D hCD hDC := by
    apply SetLike.coe_injective
    exact etaReplaces_antisymm hCD hDC

/-- A strict replacement removes at least one point of its source chain. -/
theorem EtaChainObject.exists_mem_not_mem_of_lt [Countable α]
    {C D : EtaChainObject α} (hCD : C < D) :
    ∃ x : α, x ∈ C.carrier ∧ x ∉ D.carrier := by
  obtain ⟨f⟩ := hCD.le
  by_contra h
  push_neg at h
  have htrivial : f.Trivial := fun x =>
    f.image_eq_singleton_of_mem_target x (h x.1 x.2)
  have hcarriers : C.carrier = D.carrier := f.eq_of_trivial htrivial
  exact hCD.ne (SetLike.coe_injective hcarriers)

/-- Composite of a finite consecutive sequence of replacement witnesses. -/
def iterEtaReplacement [Countable α] (C : ℕ → EtaChainObject α)
    (step : ∀ n, EtaReplacement (C n).carrier (C (n + 1)).carrier) :
    ∀ n k, EtaReplacement (C n).carrier (C (n + k)).carrier
  | n, 0 => EtaReplacement.identity (C n).etaMaximal
  | n, k + 1 => (step (n + k)).comp (iterEtaReplacement C step n k)

theorem iterEtaReplacement_not_mem [Countable α] (C : ℕ → EtaChainObject α)
    (step : ∀ n, EtaReplacement (C n).carrier (C (n + 1)).carrier)
    {n : ℕ} {x : α} (hx : x ∈ C n) (hxNext : x ∉ C (n + 1)) (k : ℕ) :
    x ∉ C ((n + 1) + k) := by
  exact (step n).not_mem_of_not_mem_comp (iterEtaReplacement C step (n + 1) k) hx hxNext

/-- A witness obtained by composing the consecutive replacements between two stages. -/
noncomputable def etaReplacementBetween [Countable α] (C : ℕ → EtaChainObject α)
    (step : ∀ n, EtaReplacement (C n).carrier (C (n + 1)).carrier)
    {n m : ℕ} (hnm : n ≤ m) : EtaReplacement (C n).carrier (C m).carrier := by
  let k := m - n
  have hnk : n + k = m := Nat.add_sub_of_le hnm
  simpa only [hnk] using iterEtaReplacement C step n k

/-- A point together with a stage at which it occurs in a replacement sequence. -/
structure EtaState (C : ℕ → EtaChainObject α) where
  stage : ℕ
  point : α
  mem_carrier : point ∈ C stage

def EtaState.asPoint {C : ℕ → EtaChainObject α} (a : EtaState C) : (C a.stage).carrier :=
  ⟨a.point, a.mem_carrier⟩

/-- A later, genuinely different point lying in a replacement image of a state. -/
def EtaDescendant [Countable α] (C : ℕ → EtaChainObject α)
    (a b : EtaState C) : Prop :=
  a.stage < b.stage ∧ ∃ f : EtaReplacement (C a.stage).carrier (C b.stage).carrier,
    b.point ∈ f.image a.asPoint ∧ b.point ≠ a.point

theorem etaDescendant_incomparable [Countable α] {C : ℕ → EtaChainObject α}
    {a b : EtaState C} (h : EtaDescendant C a b) : Incomparable b.point a.point := by
  obtain ⟨_, f, hmem, hne⟩ := h
  exact f.image_incomparable a.asPoint hmem hne

theorem etaDescendant_trans [Countable α] {C : ℕ → EtaChainObject α}
    {a b c : EtaState C} (hab' : EtaDescendant C a b) (hbc' : EtaDescendant C b c) :
    EtaDescendant C a c := by
  obtain ⟨hab, f, hbf, hbne⟩ := hab'
  obtain ⟨hbc, g, hcg, hcne⟩ := hbc'
  have hcComp : c.point ∈ (g.comp f).image a.asPoint := by
    apply subset_convexHullIn (composedRaw_subset f g a.asPoint)
    have hbTarget : f.toTarget a.asPoint ⟨b.point, hbf⟩ = b.asPoint := Subtype.ext rfl
    exact Set.mem_iUnion_of_mem
      (show f.image a.asPoint from ⟨b.point, hbf⟩) (by simpa only [hbTarget] using hcg)
  have hane : c.point ≠ a.point := by
    have haNotB : a.point ∉ (C b.stage).carrier := by
      intro haB
      have hsingle := f.image_eq_singleton_of_mem_target a.asPoint haB
      exact hbne (Set.mem_singleton_iff.mp (hsingle ▸ hbf))
    have haNotC := f.not_mem_of_not_mem_comp g a.mem_carrier haNotB
    intro hca
    exact haNotC (hca ▸ c.mem_carrier)
  exact ⟨hab.trans hbc, g.comp f, hcComp, hane⟩

private def etaDescRel [Countable α] (C : ℕ → EtaChainObject α) :
    EtaState C → EtaState C → Prop := fun child parent => EtaDescendant C parent child

/-- FAC rules out an infinite branch in the replacement forest. -/
theorem etaDescRel_wellFounded [Countable α] (hfac : IsFAC α)
    (C : ℕ → EtaChainObject α) : WellFounded (etaDescRel C) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun chain => ?_⟩
  let a : ℕ → EtaState C := chain.1
  have hedge (n : ℕ) : EtaDescendant C (a n) (a (n + 1)) := chain.2 n
  have hdesc : ∀ j i : ℕ, i < j → EtaDescendant C (a i) (a j) := by
    intro j
    induction j with
    | zero =>
        intro i hi
        exact False.elim (Nat.not_lt_zero i hi)
    | succ j ih =>
        intro i hi
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hij | hij
        · exact etaDescendant_trans (ih i hij) (hedge j)
        · subst i
          exact hedge j
  let p : ℕ → α := fun n => (a n).point
  have hpInjective : Function.Injective p := by
    intro i j hp
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hinc := etaDescendant_incomparable (hdesc j i hij)
      exact hinc.ne (by simpa only [p] using hp.symm)
    · have hinc := etaDescendant_incomparable (hdesc i j hji)
      exact hinc.ne (by simpa only [p] using hp)
  let A : Set α := Set.range p
  have hAinfinite : A.Infinite := Set.infinite_range_of_injective hpInjective
  have hAantichain : IsAntichain (· ≤ ·) A := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hpne hle
    have hij : i ≠ j := fun hij => hpne (congrArg p hij)
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact (etaDescendant_incomparable (hdesc j i hij)).not_ge hle
    · exact (etaDescendant_incomparable (hdesc i j hji)).not_le hle
  exact hAinfinite (hfac A hAantichain)

def EtaState.Stable {C : ℕ → EtaChainObject α} (a : EtaState C) : Prop :=
  ∀ m, a.stage ≤ m → a.point ∈ C m

/-- A stable point reached from a state by a (possibly identity) replacement. -/
structure EtaTerminalDesc [Countable α] (C : ℕ → EtaChainObject α)
    (a : EtaState C) where
  state : EtaState C
  stage_le : a.stage ≤ state.stage
  replacement : EtaReplacement (C a.stage).carrier (C state.stage).carrier
  mem_image : state.point ∈ replacement.image a.asPoint
  stable : state.Stable

/-- Every vertex of the replacement forest has a terminal descendant. -/
theorem exists_etaTerminalDesc [Countable α] (hfac : IsFAC α)
    (C : ℕ → EtaChainObject α)
    (step : ∀ n, EtaReplacement (C n).carrier (C (n + 1)).carrier)
    (a : EtaState C) : Nonempty (EtaTerminalDesc C a) := by
  classical
  let R := etaDescRel C
  have hRwf : WellFounded R := etaDescRel_wellFounded hfac C
  apply hRwf.induction a
  intro a ih
  by_cases hstable : a.Stable
  · exact ⟨
      { state := a
        stage_le := le_rfl
        replacement := EtaReplacement.identity (C a.stage).etaMaximal
        mem_image := Set.mem_singleton a.point
        stable := hstable }
    ⟩
  · unfold EtaState.Stable at hstable
    push Not at hstable
    obtain ⟨m, ham, haNotM⟩ := hstable
    have ham' : a.stage < m := lt_of_le_of_ne ham (fun h => by
      subst m
      exact haNotM a.mem_carrier)
    let f := etaReplacementBetween C step ham
    obtain ⟨y, hyf⟩ := f.image_nonempty a.asPoint
    have hyM : y ∈ C m := (f.image_interval a.asPoint).1 hyf
    let b : EtaState C := ⟨m, y, hyM⟩
    have hyne : b.point ≠ a.point := by
      intro hya
      exact haNotM (hya ▸ b.mem_carrier)
    have hab : EtaDescendant C a b := ⟨ham', f, hyf, hyne⟩
    obtain ⟨d⟩ := ih b hab
    have hmemComp : d.state.point ∈ (d.replacement.comp f).image a.asPoint := by
      apply subset_convexHullIn (composedRaw_subset f d.replacement a.asPoint)
      have hbTarget : f.toTarget a.asPoint ⟨b.point, hyf⟩ = b.asPoint := Subtype.ext rfl
      exact Set.mem_iUnion_of_mem (show f.image a.asPoint from ⟨b.point, hyf⟩)
        (by simpa only [hbTarget] using d.mem_image)
    exact ⟨
      { state := d.state
        stage_le := ham.trans d.stage_le
        replacement := d.replacement.comp f
        mem_image := hmemComp
        stable := d.stable }
    ⟩

theorem EtaTerminalDesc.mem_image_at [Countable α] {C : ℕ → EtaChainObject α}
    (step : ∀ n, EtaReplacement (C n).carrier (C (n + 1)).carrier)
    {a : EtaState C} (d : EtaTerminalDesc C a) {m : ℕ} (hm : d.state.stage ≤ m) :
    ∃ f : EtaReplacement (C a.stage).carrier (C m).carrier,
      d.state.point ∈ f.image a.asPoint := by
  let g := etaReplacementBetween C step hm
  have hpointM : d.state.point ∈ C m := d.stable m hm
  have hgSingleton := g.image_eq_singleton_of_mem_target d.state.asPoint hpointM
  have hgmem : d.state.point ∈ g.image d.state.asPoint := by
    rw [hgSingleton]
    exact Set.mem_singleton d.state.point
  refine ⟨g.comp d.replacement, ?_⟩
  apply subset_convexHullIn (composedRaw_subset d.replacement g a.asPoint)
  have htarget : d.replacement.toTarget a.asPoint
      ⟨d.state.point, d.mem_image⟩ = d.state.asPoint := Subtype.ext rfl
  exact Set.mem_iUnion_of_mem
    (show d.replacement.image a.asPoint from ⟨d.state.point, d.mem_image⟩)
    (by simpa only [htarget] using hgmem)

def EtaTerminalDesc.prepend [Countable α] {C : ℕ → EtaChainObject α}
    {a b : EtaState C} (hab : a.stage ≤ b.stage)
    (f : EtaReplacement (C a.stage).carrier (C b.stage).carrier)
    (hb : b.point ∈ f.image a.asPoint) (d : EtaTerminalDesc C b) :
    EtaTerminalDesc C a := by
  have hmemComp : d.state.point ∈ (d.replacement.comp f).image a.asPoint := by
    apply subset_convexHullIn (composedRaw_subset f d.replacement a.asPoint)
    have hbTarget : f.toTarget a.asPoint ⟨b.point, hb⟩ = b.asPoint := Subtype.ext rfl
    exact Set.mem_iUnion_of_mem (show f.image a.asPoint from ⟨b.point, hb⟩)
      (by simpa only [hbTarget] using d.mem_image)
  exact
    { state := d.state
      stage_le := hab.trans d.stage_le
      replacement := d.replacement.comp f
      mem_image := hmemComp
      stable := d.stable }

theorem etaTerminalDesc_strictLT [Countable α] {C : ℕ → EtaChainObject α}
    (step : ∀ n, EtaReplacement (C n).carrier (C (n + 1)).carrier)
    {a b : EtaState C} (habStage : a.stage = b.stage) (hab : a.point < b.point)
    (da : EtaTerminalDesc C a) (db : EtaTerminalDesc C b) :
    da.state.point < db.state.point := by
  cases a with
  | mk n x hx =>
    cases b with
    | mk m y hy =>
      dsimp at habStage
      subst m
      let M := max da.state.stage db.state.stage
      obtain ⟨f, haf⟩ := da.mem_image_at step
        (show da.state.stage ≤ M from le_max_left _ _)
      obtain ⟨g, hbg⟩ := db.mem_image_at step
        (show db.state.stage ≤ M from le_max_right _ _)
      exact f.cross_image_strictLT g hab haf hbg

/-- Points that persist from some stage onward. -/
def etaStableLimit (C : ℕ → EtaChainObject α) : Set α :=
  {x | ∃ n, ∀ m, n ≤ m → x ∈ C m}

theorem EtaTerminalDesc.mem_stableLimit [Countable α] {C : ℕ → EtaChainObject α}
    {a : EtaState C} (d : EtaTerminalDesc C a) : d.state.point ∈ etaStableLimit C :=
  ⟨d.state.stage, d.stable⟩

/-- The corrected liminf step: terminal descendants are constructed first and used to prove that
the stable limit itself has order type eta. -/
theorem etaStableLimit_isEtaChain [Countable α] (hfac : IsFAC α)
    (C : ℕ → EtaChainObject α)
    (step : ∀ n, EtaReplacement (C n).carrier (C (n + 1)).carrier) :
    IsEtaChain (etaStableLimit C) := by
  classical
  have hchain : IsChain (· ≤ ·) (etaStableLimit C) := by
    intro x hx y hy hxy
    obtain ⟨nx, hx⟩ := hx
    obtain ⟨ny, hy⟩ := hy
    let m := max nx ny
    exact (C m).etaMaximal.1.isChain (hx m (le_max_left _ _))
      (hy m (le_max_right _ _)) hxy
  have hne : (etaStableLimit C).Nonempty := by
    obtain ⟨x, hx⟩ := (C 0).etaMaximal.1.nonempty
    let a : EtaState C := ⟨0, x, hx⟩
    obtain ⟨d⟩ := exists_etaTerminalDesc hfac C step a
    exact ⟨d.state.point, d.mem_stableLimit⟩
  apply isEtaChain_of_countable_dense hchain hne
  · intro x y hx hy hxy
    obtain ⟨nx, hxstable⟩ := hx
    obtain ⟨ny, hystable⟩ := hy
    let m := max nx ny
    have hxM : x ∈ C m := hxstable m (le_max_left _ _)
    have hyM : y ∈ C m := hystable m (le_max_right _ _)
    obtain ⟨z, hzM, hxz, hzy⟩ := (C m).etaMaximal.1.exists_between hxM hyM hxy
    let a : EtaState C := ⟨m, z, hzM⟩
    obtain ⟨d⟩ := exists_etaTerminalDesc hfac C step a
    refine ⟨d.state.point, d.mem_stableLimit, ?_, ?_⟩
    · exact d.replacement.source_lt_image ⟨x, hxM⟩ a.asPoint hxz
        d.state.point d.mem_image
    · exact d.replacement.image_lt_source a.asPoint ⟨y, hyM⟩ hzy
        d.state.point d.mem_image
  · intro x hx
    obtain ⟨n, hxstable⟩ := hx
    have hxN : x ∈ C n := hxstable n le_rfl
    obtain ⟨z, hzN, hzx⟩ := (C n).etaMaximal.1.exists_lt hxN
    let a : EtaState C := ⟨n, z, hzN⟩
    obtain ⟨d⟩ := exists_etaTerminalDesc hfac C step a
    refine ⟨d.state.point, d.mem_stableLimit, ?_⟩
    exact d.replacement.image_lt_source a.asPoint ⟨x, hxN⟩ hzx
      d.state.point d.mem_image
  · intro x hx
    obtain ⟨n, hxstable⟩ := hx
    have hxN : x ∈ C n := hxstable n le_rfl
    obtain ⟨z, hzN, hxz⟩ := (C n).etaMaximal.1.exists_gt hxN
    let a : EtaState C := ⟨n, z, hzN⟩
    obtain ⟨d⟩ := exists_etaTerminalDesc hfac C step a
    refine ⟨d.state.point, d.mem_stableLimit, ?_⟩
    exact d.replacement.source_lt_image ⟨x, hxN⟩ a.asPoint hxz
      d.state.point d.mem_image

/-- A source state has a nonempty singleton-or-eta family of terminal descendants. -/
theorem exists_etaTerminalFiber [Countable α] (hfac : IsFAC α)
    (C : ℕ → EtaChainObject α)
    (step : ∀ n, EtaReplacement (C n).carrier (C (n + 1)).carrier)
    (a : EtaState C) :
    ∃ F : Set α, F.Nonempty ∧ (F = {a.point} ∨ IsEtaChain F) ∧
      ∀ z ∈ F, ∃ d : EtaTerminalDesc C a, d.state.point = z := by
  classical
  by_cases hstable : a.Stable
  · refine ⟨{a.point}, Set.singleton_nonempty _, Or.inl rfl, ?_⟩
    intro z hz
    have hza : z = a.point := Set.mem_singleton_iff.mp hz
    let d : EtaTerminalDesc C a :=
      { state := a
        stage_le := le_rfl
        replacement := EtaReplacement.identity (C a.stage).etaMaximal
        mem_image := Set.mem_singleton a.point
        stable := hstable }
    exact ⟨d, hza.symm⟩
  · unfold EtaState.Stable at hstable
    push Not at hstable
    obtain ⟨m, ham, haNotM⟩ := hstable
    have ham' : a.stage < m := lt_of_le_of_ne ham (fun h => by
      subst m
      exact haNotM a.mem_carrier)
    let f := etaReplacementBetween C step ham
    have hImageEta : IsEtaChain (f.image a.asPoint) := by
      rcases f.image_shape a.asPoint with hsingle | heta
      · have haImage : a.point ∈ f.image a.asPoint := by
          rw [hsingle]
          exact Set.mem_singleton a.point
        exact False.elim (haNotM ((f.image_interval a.asPoint).1 haImage))
      · exact heta
    let X := f.image a.asPoint
    let child : X → EtaState C := fun y =>
      ⟨m, y.1, (f.image_interval a.asPoint).1 y.2⟩
    have hchild (y : X) : Nonempty (EtaTerminalDesc C (child y)) :=
      exists_etaTerminalDesc hfac C step (child y)
    let d (y : X) : EtaTerminalDesc C (child y) := Classical.choice (hchild y)
    let t : X → α := fun y => (d y).state.point
    have htStrict : StrictMono t := by
      intro x y hxy
      exact etaTerminalDesc_strictLT (a := child x) (b := child y) step rfl hxy (d x) (d y)
    letI : LinearOrder X := hImageEta.isChain.linearOrder
    let tEmb : X ↪o α := OrderEmbedding.ofStrictMono t htStrict
    obtain ⟨eX⟩ := hImageEta
    let k : ℚ ↪o α := eX.toOrderEmbedding.trans tEmb
    let F : Set α := Set.range k
    have hkInjective : Function.Injective k := k.injective
    let kIso : ℚ ≃o F :=
      { toEquiv := Equiv.ofInjective k hkInjective
        map_rel_iff' := fun {_ _} => k.le_iff_le }
    have hFeta : IsEtaChain F := ⟨kIso⟩
    refine ⟨F, hFeta.nonempty, Or.inr hFeta, ?_⟩
    intro z hz
    obtain ⟨q, rfl⟩ := hz
    let y : X := eX q
    let db : EtaTerminalDesc C (child y) := d y
    let da : EtaTerminalDesc C a := db.prepend ham f y.2
    exact ⟨da, rfl⟩

/-- The corrected countable-chain upper-bound lemma.  The stable limit is first shown to be eta;
only then is it extended to an eta-maximal chain. -/
theorem etaReplacement_sequence_upperBound [Countable α] (hfac : IsFAC α)
    (C : ℕ → EtaChainObject α)
    (step : ∀ n, EtaReplacement (C n).carrier (C (n + 1)).carrier) :
    ∃ upper : EtaChainObject α, ∀ n, C n ≤ upper := by
  classical
  let L := etaStableLimit C
  have hLeta : IsEtaChain L := etaStableLimit_isEtaChain hfac C step
  obtain ⟨D, hLD, hD⟩ := hLeta.exists_etaMaximal
  let upper : EtaChainObject α := ⟨D, hD⟩
  refine ⟨upper, fun n => ?_⟩
  have hfiber (x : (C n).carrier) :
      ∃ F : Set α, F.Nonempty ∧ (F = {x.1} ∨ IsEtaChain F) ∧
        ∀ z ∈ F, ∃ d : EtaTerminalDesc C ⟨n, x.1, x.2⟩, d.state.point = z :=
    exists_etaTerminalFiber hfac C step ⟨n, x.1, x.2⟩
  choose F hFne hFshape hFterminal using hfiber
  have hFsubL (x : (C n).carrier) : F x ⊆ L := by
    intro z hz
    obtain ⟨d, rfl⟩ := hFterminal x z hz
    exact d.mem_stableLimit
  have hFsubD (x : (C n).carrier) : F x ⊆ D := (hFsubL x).trans hLD
  let f : EtaReplacement (C n).carrier D :=
    { source := (C n).etaMaximal
      target := hD
      image := fun x => convexHullIn D (F x)
      image_nonempty := fun x => (hFne x).mono (subset_convexHullIn (hFsubD x))
      image_interval := fun x => convexHullIn_interval D (F x)
      image_shape := fun x => by
        rcases hFshape x with hsingle | heta
        · left
          rw [hsingle]
          apply Set.Subset.antisymm
          · rintro z ⟨hzD, a, ha, b, hb, haz, hzb⟩
            have ha' : a = x.1 := Set.mem_singleton_iff.mp ha
            have hb' : b = x.1 := Set.mem_singleton_iff.mp hb
            subst a
            subst b
            exact Set.mem_singleton_iff.mpr (le_antisymm hzb haz)
          · exact subset_convexHullIn (by simpa [hsingle] using hFsubD x)
        · right
          exact etaChain_convexHullIn heta (hFsubD x) hD.1
      source_lt_image := fun x y hxy z hz => by
        obtain ⟨_, a, haF, b, hbF, haz, hzb⟩ := hz
        obtain ⟨d, hda⟩ := hFterminal y a haF
        have hxa : x.1 < d.state.point := d.replacement.source_lt_image x y hxy
          d.state.point d.mem_image
        have hxa' : x.1 < a := by simpa [hda] using hxa
        exact hxa'.trans_le haz
      image_lt_source := fun x y hxy z hz => by
        obtain ⟨_, a, haF, b, hbF, haz, hzb⟩ := hz
        obtain ⟨d, hdb⟩ := hFterminal x b hbF
        have hby : d.state.point < y.1 := d.replacement.image_lt_source x y hxy
          d.state.point d.mem_image
        have hby' : b < y.1 := by simpa [hdb] using hby
        exact hzb.trans_lt hby' }
  exact ⟨f⟩

/-- A chain admitting no nontrivial eta replacement. -/
def IsEtaStronglyMaximal (C : Set α) : Prop :=
  IsEtaMaximalChain C ∧
    ∀ (D : Set α) (f : EtaReplacement C D), f.Trivial

/-- Every nonempty chain in the eta-replacement order has an upper bound.  Strict replacements
permanently remove an ambient point, so the countability of `α` supplies a countable cofinal
subchain.  Its running maxima form a replacement sequence, whose upper bound is constructed from
terminal descendants above. -/
theorem etaReplacement_chain_upperBound [Countable α] (hfac : IsFAC α)
    (s : Set (EtaChainObject α)) (hs : IsChain (· ≤ ·) s) (hne : s.Nonempty) :
    ∃ upper : EtaChainObject α, ∀ C ∈ s, C ≤ upper := by
  classical
  by_cases htop : ∃ U ∈ s, ∀ C ∈ s, C ≤ U
  · obtain ⟨U, hUs, hU⟩ := htop
    exact ⟨U, hU⟩
  have habove (C : EtaChainObject α) (hCs : C ∈ s) :
      ∃ D ∈ s, C < D := by
    by_contra hnone
    have hUpper : ∀ D ∈ s, D ≤ C := by
      intro D hDs
      rcases hs.total hDs hCs with hDC | hCD
      · exact hDC
      · by_cases hEq : D = C
        · simpa [hEq]
        · have hlt : C < D := lt_of_le_of_ne hCD (fun h => hEq h.symm)
          exact False.elim (hnone ⟨D, hDs, hlt⟩)
    exact htop ⟨C, hCs, hUpper⟩
  let I : Set α := {x | ∃ A ∈ s, ∃ B ∈ s,
    A < B ∧ x ∈ A.carrier ∧ x ∉ B.carrier}
  have hIne : I.Nonempty := by
    obtain ⟨C, hCs⟩ := hne
    obtain ⟨D, hDs, hCD⟩ := habove C hCs
    obtain ⟨x, hxC, hxD⟩ := C.exists_mem_not_mem_of_lt hCD
    exact ⟨x, C, hCs, D, hDs, hCD, hxC, hxD⟩
  letI : Nonempty I := ⟨⟨hIne.choose, hIne.choose_spec⟩⟩
  have hwitness (i : I) : ∃ A ∈ s, ∃ B ∈ s,
      A < B ∧ i.1 ∈ A.carrier ∧ i.1 ∉ B.carrier := i.2
  choose A hAs B hBs hAB hiA hiB using hwitness
  have hcofinal (C : EtaChainObject α) (hCs : C ∈ s) :
      ∃ i : I, C ≤ B i := by
    obtain ⟨D, hDs, hCD⟩ := habove C hCs
    obtain ⟨x, hxC, hxD⟩ := C.exists_mem_not_mem_of_lt hCD
    let i : I := ⟨x, C, hCs, D, hDs, hCD, hxC, hxD⟩
    refine ⟨i, ?_⟩
    rcases hs.total hCs (hBs i) with hCB | hBC
    · exact hCB
    · exfalso
      obtain ⟨rAB⟩ := (hAB i).le
      obtain ⟨rBC⟩ := hBC
      exact (rAB.not_mem_of_not_mem_comp rBC (hiA i) (hiB i)) hxC
  obtain ⟨enum, henum⟩ := exists_surjective_nat I
  let f : ℕ → EtaChainObject α := fun n => B (enum n)
  have hfmem (n : ℕ) : f n ∈ s := hBs (enum n)
  let R : ℕ → EtaChainObject α := runningMax f
  have hRmem (n : ℕ) : R n ∈ s := runningMax_mem hs hfmem n
  have hRmono : Monotone R := monotone_nat_of_le_succ fun n =>
    runningMax_le_succ hs hfmem n
  have hstep (n : ℕ) : EtaReplacement (R n).carrier (R (n + 1)).carrier :=
    Classical.choice (hRmono (Nat.le_succ n))
  obtain ⟨upper, hupper⟩ := etaReplacement_sequence_upperBound hfac R hstep
  refine ⟨upper, fun C hCs => ?_⟩
  obtain ⟨i, hCi⟩ := hcofinal C hCs
  obtain ⟨n, hn⟩ := henum i
  have henumLe : B i ≤ R n := by
    simpa [R, f, hn] using runningMax_self_le hs hfmem n
  exact hCi.trans (henumLe.trans (hupper n))

theorem exists_etaStronglyMaximal [Countable α] (hfac : IsFAC α)
    (hns : ¬ IsScattered α) : ∃ C : Set α, IsEtaStronglyMaximal C := by
  classical
  have hObject : Nonempty (EtaChainObject α) := by
    have hetaEmbedding : Nonempty (ℚ ↪o α) := by
      by_contra h
      exact hns h
    obtain ⟨e⟩ := hetaEmbedding
    let Q : Set α := Set.range e
    have hQeta : IsEtaChain Q := by
      let e' : ℚ ≃o Q :=
        { toEquiv := Equiv.ofInjective e e.injective
          map_rel_iff' := fun {_ _} => e.le_iff_le }
      exact ⟨e'⟩
    obtain ⟨C, _, hC⟩ := hQeta.exists_etaMaximal
    exact ⟨⟨C, hC⟩⟩
  let _ := hObject
  obtain ⟨C, hCmax⟩ := exists_maximal_of_nonempty_chains_bounded
    (fun s hs hne => etaReplacement_chain_upperBound hfac s hs hne) le_trans
  refine ⟨C.carrier, C.etaMaximal, fun D f => ?_⟩
  let D' : EtaChainObject α := ⟨D, f.target⟩
  have hCD : C ≤ D' := ⟨f⟩
  have hDC : D' ≤ C := hCmax D' hCD
  have hEq : C = D' := le_antisymm hCD hDC
  have hcarriers : C.carrier = D := congrArg EtaChainObject.carrier hEq
  subst D
  exact f.self_trivial

end AharoniKorman
