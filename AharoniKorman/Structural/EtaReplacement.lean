import AharoniKorman.Structural.EtaChains
import AharoniKorman.Preliminaries.FAC
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

/-- A chain admitting no nontrivial eta replacement. -/
def IsEtaStronglyMaximal (C : Set α) : Prop :=
  IsEtaMaximalChain C ∧
    ∀ (D : Set α) (f : EtaReplacement C D), f.Trivial

/-- Limit theorem for replacement chains.  This is the formal boundary of the manuscript's
forest construction in Lemmas 5.9 and 5.10. -/
theorem etaReplacement_chain_upperBound [Countable α] (hfac : IsFAC α)
    (s : Set (EtaChainObject α)) (hs : IsChain (· ≤ ·) s) (hne : s.Nonempty) :
    ∃ upper : EtaChainObject α, ∀ C ∈ s, C ≤ upper := by
  sorry

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
