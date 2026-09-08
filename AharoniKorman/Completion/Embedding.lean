import AharoniKorman.Completion.Scattering

/-! Admissible suborders and their induced completion maps (paper `obs:embedding`). -/

namespace AharoniKorman.Completion

open Set

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

/-- An order embedding is admissible when it preserves saturated chains. -/
def SaturationPreserving (e : α ↪o β) : Prop :=
  ∀ S : Set α, IsSaturatedChain S → IsSaturatedChain (e '' S)

theorem saturationPreserving_subtype_of_ordConnected {S : Set α} (hS : S.OrdConnected) :
    SaturationPreserving (α := S) (β := α) (OrderEmbedding.subtype S) := by
  intro C hC
  refine ⟨hC.1.image (OrderEmbedding.subtype S), ?_⟩
  rintro _ _ x ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hax hxb hcomp
  have hxS : x ∈ S := hS.out a.2 b.2 ⟨hax, hxb⟩
  refine ⟨⟨x, hxS⟩, ?_, rfl⟩
  exact hC.2 ha hb hax hxb (fun c hc => hcomp c.1 ⟨c, hc, rfl⟩)

theorem saturationPreserving_subtype_of_saturated {S : Set α} (hS : IsSaturatedChain S) :
    SaturationPreserving (α := S) (β := α) (OrderEmbedding.subtype S) := by
  intro C hC
  refine ⟨hC.1.image (OrderEmbedding.subtype S), ?_⟩
  rintro _ _ x ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hax hxb hcomp
  have hxS : x ∈ S := hS.2 a.2 b.2 hax hxb (by
    intro s hs
    by_cases hsa : s ≤ a.1
    · exact Or.inr (hsa.trans hax)
    by_cases hbs : b.1 ≤ s
    · exact Or.inl (hxb.trans hbs)
    have has := (hS.1.total a.2 hs).resolve_right hsa
    have hsb := (hS.1.total hs b.2).resolve_right hbs
    have hsC : (⟨s, hs⟩ : S) ∈ C := hC.2 ha hb has hsb (by
      intro c hc
      exact hS.1.total hs c.2)
    exact hcomp s ⟨⟨s, hs⟩, hsC, rfl⟩)
  refine ⟨⟨x, hxS⟩, ?_, rfl⟩
  exact hC.2 ha hb hax hxb (fun c hc => hcomp c.1 ⟨c, hc, rfl⟩)

def SaturatedChain.map (C : SaturatedChain α) (e : α ↪o β) (he : SaturationPreserving e) :
    SaturatedChain β := ⟨e '' (C : Set α), C.nonempty.image e, he C C.saturated⟩

@[simp] theorem SaturatedChain.mem_map_iff (C : SaturatedChain α) (e : α ↪o β)
    (he : SaturationPreserving e) (y : β) : y ∈ C.map e he ↔ y ∈ e '' (C : Set α) := Iff.rfl

@[simp] theorem SaturatedChain.mem_map (C : SaturatedChain α) (e : α ↪o β)
    (he : SaturationPreserving e) (x : α) : e x ∈ C.map e he ↔ x ∈ C := by
  constructor
  · rintro ⟨y, hy, heq⟩
    exact e.injective heq ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

/-- The order isomorphism from a saturated chain to its image. -/
noncomputable def SaturatedChain.mapOrderIso (C : SaturatedChain α) (e : α ↪o β)
    (he : SaturationPreserving e) : C ≃o C.map e he := by
  let f : C ↪o C.map e he := OrderEmbedding.ofMapLEIff
    (fun x => ⟨e x.1, ⟨x.1, x.2, rfl⟩⟩) (by intro x y; exact e.le_iff_le)
  exact OrderIso.ofSurjective f (by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)

@[simp] theorem SaturatedChain.mapOrderIso_apply (C : SaturatedChain α) (e : α ↪o β)
    (he : SaturationPreserving e) (x : C) : (C.mapOrderIso e he x).1 = e x.1 := rfl

theorem SaturatedChain.map_noTop (C : SaturatedChain α) (e : α ↪o β)
    (he : SaturationPreserving e) (h : C.NoTop) : (C.map e he).NoTop := by
  rintro ⟨m, hm⟩
  apply h
  let f := C.mapOrderIso e he
  refine ⟨f.symm m, fun x => ?_⟩
  simpa only [f.symm_apply_apply] using f.symm.monotone (hm (f x))

def IncreasingChain.map (C : IncreasingChain α) (e : α ↪o β) (he : SaturationPreserving e) :
    IncreasingChain β := ⟨C.1.map e he, C.1.map_noTop e he C.2⟩

@[simp] theorem IncreasingChain.map_val (C : IncreasingChain α) (e : α ↪o β)
    (he : SaturationPreserving e) : (C.map e he).1 = C.1.map e he := rfl

@[simp] theorem SaturatedChain.map_forall (C : SaturatedChain α) (e : α ↪o β)
    (he : SaturationPreserving e) (P : β → Prop) :
    (∀ y : C.map e he, P y.1) ↔ ∀ x : C, P (e x.1) := by
  constructor
  · intro h x; exact h (C.mapOrderIso e he x)
  · rintro h ⟨_, x, hx, rfl⟩; exact h ⟨x, hx⟩

@[simp] theorem SaturatedChain.map_exists (C : SaturatedChain α) (e : α ↪o β)
    (he : SaturationPreserving e) (P : β → Prop) :
    (∃ y : C.map e he, P y.1) ↔ ∃ x : C, P (e x.1) := by
  constructor
  · rintro ⟨⟨_, x, hx, rfl⟩, h⟩; exact ⟨⟨x, hx⟩, h⟩
  · rintro ⟨x, h⟩; exact ⟨C.mapOrderIso e he x, h⟩

theorem SaturatedChain.map_final {S C : SaturatedChain α} (e : α ↪o β)
    (he : SaturationPreserving e) (h : IsFinalSegment (S : Set α) C) :
    IsFinalSegment (S.map e he : Set β) (C.map e he) := by
  refine ⟨Set.image_mono h.1, ?_⟩
  rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ hxy
  exact ⟨y, h.2 hx hy (e.le_iff_le.1 hxy), rfl⟩

theorem SaturatedChain.finite_trace_map_iff (C : SaturatedChain α) (e : α ↪o β)
    (he : SaturationPreserving e) (x : α) :
    (incomparabilityTrace (C.map e he) (e x)).Finite ↔ (incomparabilityTrace C x).Finite := by
  let f := C.mapOrderIso e he
  have ht : incomparabilityTrace (C.map e he) (e x) = f '' incomparabilityTrace C x := by
    ext y
    constructor
    · intro hy
      refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
      have hy' : Incomparable (e (f.symm y).1) (e x) := by
        have hf : e (f.symm y).1 = y.1 := congrArg Subtype.val (f.apply_symm_apply y)
        rw [hf]
        exact hy
      exact ⟨fun h => hy'.not_le (e.monotone h), fun h => hy'.not_ge (e.monotone h)⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨fun h => hz.not_le (e.le_iff_le.1 h), fun h => hz.not_ge (e.le_iff_le.1 h)⟩
  rw [ht]
  exact Set.finite_image_iff f.injective.injOn

/-- Exact finite/cofinal characterization used to transport equivalence. It
separates the finite-trace clauses from common-hull maximality. -/
theorem IncreasingEquivalent.iff_finite_cofinal (C D : IncreasingChain α) :
    IncreasingEquivalent C D ↔ ∃ S T : SaturatedChain α,
      IsFinalSegment (S : Set α) C.1 ∧ IsFinalSegment (T : Set α) D.1 ∧
      (∀ s : S, ∃ t : T, s.1 < t.1) ∧ (∀ t : T, ∃ s : S, t.1 < s.1) ∧
      (∀ t : T, (incomparabilityTrace S t.1).Finite) ∧
      (∀ s : S, (incomparabilityTrace T s.1).Finite) := by
  constructor
  · rintro ⟨S, T, hS, hT, hST⟩
    exact ⟨S, T, hS, hT, hST.exists_right_gt (D.finalSegment_noTop T hT),
      hST.exists_left_gt (C.finalSegment_noTop S hS), hST.left_finite, hST.right_finite⟩
  · rintro ⟨S, T, hS, hT, hST, hTS, hl, hr⟩
    obtain ⟨S', T', hS', hT', h⟩ := normalize_finite_cofinal hST hTS hl hr
    exact ⟨S', T', isFinalSegment_trans hS' hS, isFinalSegment_trans hT' hT, h⟩

theorem IncreasingEquivalent.map {C D : IncreasingChain α} (h : IncreasingEquivalent C D)
    (e : α ↪o β) (he : SaturationPreserving e) :
    IncreasingEquivalent (C.map e he) (D.map e he) := by
  obtain ⟨S, T, hS, hT, hST, hTS, hl, hr⟩ := (IncreasingEquivalent.iff_finite_cofinal C D).1 h
  apply (IncreasingEquivalent.iff_finite_cofinal _ _).2
  refine ⟨S.map e he, T.map e he, SaturatedChain.map_final e he hS,
    SaturatedChain.map_final e he hT, ?_, ?_, ?_, ?_⟩
  · rintro ⟨_, s, hs, rfl⟩
    obtain ⟨t, hst⟩ := hST ⟨s, hs⟩
    exact ⟨T.mapOrderIso e he t, e.strictMono hst⟩
  · rintro ⟨_, t, ht, rfl⟩
    obtain ⟨s, hts⟩ := hTS ⟨t, ht⟩
    exact ⟨S.mapOrderIso e he s, e.strictMono hts⟩
  · rintro ⟨_, t, ht, rfl⟩
    exact (S.finite_trace_map_iff e he t).2 (hl ⟨t, ht⟩)
  · rintro ⟨_, s, hs, rfl⟩
    exact (T.finite_trace_map_iff e he s).2 (hr ⟨s, hs⟩)

/-- Pull a nonempty final segment of an image back to the original chain. -/
def SaturatedChain.pullbackFinal (C : SaturatedChain α) (e : α ↪o β)
    (he : SaturationPreserving e) (S : SaturatedChain β)
    (hS : IsFinalSegment (S : Set β) (C.map e he)) : SaturatedChain α :=
  C.restrict .increasing (e ⁻¹' (S : Set β))
    ⟨fun x hx => (C.mem_map e he x).1 (hS.1 hx),
      fun _ y hx hy hxy => hS.2 hx ((C.mem_map e he y).2 hy) (e.monotone hxy)⟩
    (by
      obtain ⟨s, hs⟩ := S.nonempty
      obtain ⟨x, _, rfl⟩ := hS.1 hs
      exact ⟨x, hs⟩)

theorem SaturatedChain.pullbackFinal_final (C : SaturatedChain α) (e : α ↪o β)
    (he : SaturationPreserving e) (S : SaturatedChain β)
    (hS : IsFinalSegment (S : Set β) (C.map e he)) :
    IsFinalSegment (C.pullbackFinal e he S hS : Set α) C :=
  ⟨fun x hx => (C.mem_map e he x).1 (hS.1 hx),
    fun _ y hx hy hxy => hS.2 hx ((C.mem_map e he y).2 hy) (e.monotone hxy)⟩

theorem SaturatedChain.map_pullbackFinal (C : SaturatedChain α) (e : α ↪o β)
    (he : SaturationPreserving e) (S : SaturatedChain β)
    (hS : IsFinalSegment (S : Set β) (C.map e he)) :
    (C.pullbackFinal e he S hS).map e he = S := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hs
    obtain ⟨x, _, rfl⟩ := hS.1 hs
    exact ⟨x, hs, rfl⟩

theorem IncreasingEquivalent.of_map {C D : IncreasingChain α} (e : α ↪o β)
    (he : SaturationPreserving e) (h : IncreasingEquivalent (C.map e he) (D.map e he)) :
    IncreasingEquivalent C D := by
  obtain ⟨S, T, hS, hT, hST, hTS, hl, hr⟩ :=
    (IncreasingEquivalent.iff_finite_cofinal _ _).1 h
  let S0 := C.1.pullbackFinal e he S hS
  let T0 := D.1.pullbackFinal e he T hT
  have hS0 : S0.map e he = S := C.1.map_pullbackFinal e he S hS
  have hT0 : T0.map e he = T := D.1.map_pullbackFinal e he T hT
  rw [← hS0, ← hT0] at hST hTS hl hr
  apply (IncreasingEquivalent.iff_finite_cofinal C D).2
  refine ⟨S0, T0, C.1.pullbackFinal_final e he S hS,
    D.1.pullbackFinal_final e he T hT, ?_, ?_, ?_, ?_⟩
  · intro s
    obtain ⟨⟨_, t, ht, rfl⟩, hst⟩ := hST (S0.mapOrderIso e he s)
    exact ⟨⟨t, ht⟩, e.lt_iff_lt.1 hst⟩
  · intro t
    obtain ⟨⟨_, s, hs, rfl⟩, hts⟩ := hTS (T0.mapOrderIso e he t)
    exact ⟨⟨s, hs⟩, e.lt_iff_lt.1 hts⟩
  · intro t
    exact (S0.finite_trace_map_iff e he t.1).1 (hl (T0.mapOrderIso e he t))
  · intro s
    exact (T0.finite_trace_map_iff e he s.1).1 (hr (S0.mapOrderIso e he s))

@[simp] theorem IncreasingEquivalent.map_iff (C D : IncreasingChain α) (e : α ↪o β)
    (he : SaturationPreserving e) :
    IncreasingEquivalent (C.map e he) (D.map e he) ↔ IncreasingEquivalent C D :=
  ⟨IncreasingEquivalent.of_map e he, fun h => h.map e he⟩

theorem SaturationPreserving.dual {e : α ↪o β} (he : SaturationPreserving e) :
    SaturationPreserving e.dual := fun S hS => (he S hS.dual).dual

def DecreasingChain.map (C : DecreasingChain α) (e : α ↪o β) (he : SaturationPreserving e) :
    DecreasingChain β := (C.toDual.map e.dual he.dual).toDual

@[simp] theorem DecreasingChain.map_val (C : DecreasingChain α) (e : α ↪o β)
    (he : SaturationPreserving e) : (C.map e he).1 = C.1.map e he := by
  apply SetLike.ext
  intro x
  rfl

@[simp] theorem DecreasingEquivalent.map_iff (C D : DecreasingChain α) (e : α ↪o β)
    (he : SaturationPreserving e) :
    DecreasingEquivalent (C.map e he) (D.map e he) ↔ DecreasingEquivalent C D := by
  change IncreasingEquivalent (C.toDual.map e.dual he.dual).toDual.toDual
    (D.toDual.map e.dual he.dual).toDual.toDual ↔ _
  rw [IncreasingChain.toDual_toDual, IncreasingChain.toDual_toDual]
  exact IncreasingEquivalent.map_iff C.toDual D.toDual e.dual he.dual

def IncreasingGerm.map (e : α ↪o β) (he : SaturationPreserving e) :
    IncreasingGerm α → IncreasingGerm β :=
  IncreasingGerm.lift (fun C => IncreasingGerm.ofChain (C.map e he))
    (fun _ _ h => IncreasingGerm.ofChain_eq_iff.2 (h.map e he))

@[simp] theorem IncreasingGerm.map_ofChain (e : α ↪o β) (he : SaturationPreserving e)
    (C : IncreasingChain α) :
    IncreasingGerm.map e he (IncreasingGerm.ofChain C) = IncreasingGerm.ofChain (C.map e he) := rfl

theorem IncreasingGerm.map_injective (e : α ↪o β) (he : SaturationPreserving e) :
    Function.Injective (IncreasingGerm.map e he) := by
  intro g h
  induction g using IncreasingGerm.inductionOn with
  | h C =>
    induction h using IncreasingGerm.inductionOn with
    | h D => simp only [map_ofChain, ofChain_eq_iff, IncreasingEquivalent.map_iff, imp_self]

def DecreasingGerm.map (e : α ↪o β) (he : SaturationPreserving e) :
    DecreasingGerm α → DecreasingGerm β :=
  DecreasingGerm.lift (fun C => DecreasingGerm.ofChain (C.map e he))
    (fun C D h => DecreasingGerm.ofChain_eq_iff.2 ((DecreasingEquivalent.map_iff C D e he).2 h))

@[simp] theorem DecreasingGerm.map_ofChain (e : α ↪o β) (he : SaturationPreserving e)
    (C : DecreasingChain α) :
    DecreasingGerm.map e he (DecreasingGerm.ofChain C) = DecreasingGerm.ofChain (C.map e he) :=
  DecreasingGerm.lift_ofChain _ _ _

theorem DecreasingGerm.map_injective (e : α ↪o β) (he : SaturationPreserving e) :
    Function.Injective (DecreasingGerm.map e he) := by
  intro g h
  induction g using DecreasingGerm.inductionOn with
  | h C =>
    induction h using DecreasingGerm.inductionOn with
    | h D => simp only [map_ofChain, ofChain_eq_iff, DecreasingEquivalent.map_iff, imp_self]

namespace H

def map (e : α ↪o β) (he : SaturationPreserving e) : H α → H β
  | principal x => principal (e x)
  | increasing g => increasing (IncreasingGerm.map e he g)
  | decreasing g => decreasing (DecreasingGerm.map e he g)
  | bottom => bottom
  | top => top

@[simp] theorem map_principal (e : α ↪o β) (he : SaturationPreserving e) (x : α) :
    map e he (principal x) = principal (e x) := rfl
@[simp] theorem map_bot (e : α ↪o β) (he : SaturationPreserving e) :
    map e he (⊥ : H α) = ⊥ := rfl
@[simp] theorem map_top (e : α ↪o β) (he : SaturationPreserving e) :
    map e he (⊤ : H α) = ⊤ := rfl
@[simp] theorem direction_map (e : α ↪o β) (he : SaturationPreserving e) (X : H α) :
    (map e he X).direction = X.direction := by cases X <;> rfl

theorem map_injective (e : α ↪o β) (he : SaturationPreserving e) :
    Function.Injective (map e he) := by
  intro X Y h
  cases X <;> cases Y <;> simp only [map, H.principal.injEq, H.increasing.injEq,
    H.decreasing.injEq, reduceCtorEq] at h ⊢
  all_goals first | contradiction | rfl | exact e.injective h |
    exact IncreasingGerm.map_injective e he h | exact DecreasingGerm.map_injective e he h

@[simp] theorem map_lt_map (e : α ↪o β) (he : SaturationPreserving e) (X Y : H α) :
    map e he X < map e he Y ↔ X < Y := by
  induction X using inductionOnRepresentatives <;>
    induction Y using inductionOnRepresentatives <;>
    simp only [map, IncreasingGerm.map_ofChain, DecreasingGerm.map_ofChain,
      principal_lt_principal, principal_lt_increasing_ofChain, increasing_ofChain_lt_principal,
      principal_lt_decreasing_ofChain, decreasing_ofChain_lt_principal,
      increasing_ofChain_lt_increasing_ofChain, increasing_ofChain_lt_decreasing_ofChain,
      decreasing_ofChain_lt_increasing_ofChain, decreasing_ofChain_lt_decreasing_ofChain,
      IncreasingChain.map_val, SaturatedChain.map_exists, e.lt_iff_lt]
  all_goals simp [e.lt_iff_lt, lt_iff_strictLT, StrictLT]

@[simp] theorem map_le_map (e : α ↪o β) (he : SaturationPreserving e) (X Y : H α) :
    map e he X ≤ map e he Y ↔ X ≤ Y := by
  simp only [le_iff_eq_or_lt, map_lt_map, (map_injective e he).eq_iff]

/-- Paper `obs:embedding`: an admissible inclusion induces an embedding of completions. -/
noncomputable def mapEmbedding (e : α ↪o β) (he : SaturationPreserving e) : H α ↪o H β :=
  OrderEmbedding.ofMapLEIff (map e he) (map_le_map e he)

@[simp] theorem mapEmbedding_apply (e : α ↪o β) (he : SaturationPreserving e) (X : H α) :
    mapEmbedding e he X = map e he X := rfl

theorem Represents.map {C : SaturatedChain α} {X : H α} (h : Represents C X)
    (e : α ↪o β) (he : SaturationPreserving e) : Represents (C.map e he) (map e he X) := by
  cases X with
  | principal x => exact h.elim
  | bottom => exact h.elim
  | top => exact h.elim
  | increasing g =>
    obtain ⟨hn, hC⟩ := h
    have hg : IncreasingGerm.ofChain (show IncreasingChain α from ⟨C, hn⟩) = g := hC
    rw [← hg]
    exact ⟨C.map_noTop e he hn,
      (IncreasingGerm.map_ofChain e he (show IncreasingChain α from ⟨C, hn⟩)).symm⟩
  | decreasing g =>
    obtain ⟨hn, hC⟩ := h
    have hg : DecreasingGerm.ofChain (show DecreasingChain α from ⟨C, hn⟩) = g := hC
    rw [← hg]
    let D : DecreasingChain α := ⟨C, hn⟩
    have hD : Represents (D.map e he).1 (decreasing (DecreasingGerm.map e he
        (DecreasingGerm.ofChain D))) :=
      (represents_decreasing _ _).2 (DecreasingGerm.map_ofChain e he D).symm
    rw [DecreasingChain.map_val] at hD
    exact hD

end H

end AharoniKorman.Completion
