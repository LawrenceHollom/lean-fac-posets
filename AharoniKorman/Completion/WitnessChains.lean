import AharoniKorman.Completion.ChainSuborder
import Mathlib.Data.Int.Interval

/-! Witness chains and principal separators from the chain-extension section. -/

namespace AharoniKorman.Completion

open Set

variable {α : Type*} [PartialOrder α]

namespace H

/-- A point of the paper's `N(P)`. The internal formal endpoints have no representatives. -/
def IsGenuineNonprincipal (X : H α) : Prop := X.IsNonprincipal ∧ X ≠ ⊥ ∧ X ≠ ⊤

/-- `C` witnesses `X` when it contains a saturated representative of `X`. -/
def Witnesses (C : SaturatedChain α) (X : H α) : Prop :=
  ∃ A : SaturatedChain α, (A : Set α) ⊆ C ∧ Represents A X

/-- Equivalently, the point lies in the image of `N(C)` under the natural embedding. -/
theorem witnesses_iff_in_completion (C : SaturatedChain α) (X : H α) :
    Witnesses C X ↔ ∃ Y : H (C : Set α), Y.IsGenuineNonprincipal ∧
      mapEmbedding (OrderEmbedding.subtype (C : Set α))
        (saturationPreserving_subtype_of_saturated C.saturated) Y = X := by
  let e : (C : Set α) ↪o α := OrderEmbedding.subtype _
  let he : SaturationPreserving e := saturationPreserving_subtype_of_saturated C.saturated
  constructor
  · rintro ⟨A, hAC, hA⟩
    cases X with
    | principal _ | bottom | top => exact hA.elim
    | increasing g =>
        obtain ⟨hn, rfl⟩ := hA
        let B : IncreasingChain α := ⟨A, hn⟩
        let Y : H (C : Set α) := increasing (IncreasingGerm.ofChain (B.within hAC))
        refine ⟨Y, ⟨⟨.increasing, rfl⟩, ⟨increasing_ne_bot _, increasing_ne_top _⟩⟩, ?_⟩
        exact congrArg (fun D => increasing (IncreasingGerm.ofChain D)) (B.map_within hAC he)
    | decreasing g =>
        obtain ⟨hn, rfl⟩ := hA
        let B : DecreasingChain α := ⟨A, hn⟩
        let Y : H (C : Set α) := decreasing (DecreasingGerm.ofChain (B.within hAC))
        refine ⟨Y, ⟨⟨.decreasing, rfl⟩, ⟨decreasing_ne_bot _, decreasing_ne_top _⟩⟩, ?_⟩
        exact congrArg (fun D => decreasing (DecreasingGerm.ofChain D)) (B.map_within hAC he)
  · rintro ⟨Y, ⟨hy, hb, ht⟩, rfl⟩
    obtain ⟨B, hB⟩ := exists_representative hy hb ht
    exact ⟨B.map e he, fun _ ⟨y, _, hy'⟩ => hy' ▸ y.2, hB.map e he⟩

private theorem exists_saturatedChain_superset {S : Set α} (hS : IsChain (· ≤ ·) S)
    (hne : S.Nonempty) : ∃ C : SaturatedChain α, S ⊆ C := by
  obtain ⟨T, hT, hST⟩ := hS.exists_maxChain
  refine ⟨⟨T, hne.mono hST, hT.1, ?_⟩, hST⟩
  intro _ _ z _ _ _ _ hz
  rw [hT.2 (hT.1.insert fun c hc _ => hz c hc) (Set.subset_insert z T)]
  exact Set.mem_insert z T

private theorem represents_restrict_increasing (C : IncreasingChain α)
    (S : SaturatedChain α) (hS : IsFinalSegment (S : Set α) C.1) :
    Represents S (increasing (IncreasingGerm.ofChain C)) := by
  refine ⟨C.finalSegment_noTop S hS, IncreasingGerm.ofChain_eq_iff.mpr ?_⟩
  exact ⟨S, S, ⟨Subset.rfl, fun _ _ _ hy _ => hy⟩, hS,
    MutuallyFiniteIncomparability.refl S⟩

private theorem represents_restrict_decreasing (C : DecreasingChain α)
    (S : SaturatedChain α) (hS : IsInitialSegment (S : Set α) C.1) :
    Represents S (decreasing (DecreasingGerm.ofChain C)) := by
  refine ⟨C.initialSegment_noBottom S hS, DecreasingGerm.ofChain_eq_iff.mpr ?_⟩
  exact ⟨S.dual, S.dual, ⟨Subset.rfl, fun _ _ _ hy _ => hy⟩, hS,
    MutuallyFiniteIncomparability.refl S.dual⟩

private theorem exists_ordered_representatives {X Y : H α}
    (hX : X.IsGenuineNonprincipal) (hY : Y.IsGenuineNonprincipal) (hXY : X < Y) :
    ∃ A B : SaturatedChain α, Represents A X ∧ Represents B Y ∧
      SetStrictLT (A : Set α) B := by
  obtain ⟨A, hA⟩ := exists_representative hX.1 hX.2.1 hX.2.2
  obtain ⟨B, hB⟩ := exists_representative hY.1 hY.2.1 hY.2.2
  suffices ∃ d e : OrderDirection, (∀ S : SaturatedChain α,
      IsDirectionalSegment d (S : Set α) A → Represents S X) ∧
      (∀ T : SaturatedChain α, IsDirectionalSegment e (T : Set α) B → Represents T Y) ∧
      Domination.SegmentLT d e A B by
    obtain ⟨d, e, hAX, hBY, S, T, hS, hnS, hT, hnT, hST⟩ := this
    cases d <;> cases e <;>
      exact ⟨A.restrict _ S hS hnS, B.restrict _ T hT hnT, hAX _ hS, hBY _ hT, hST⟩
  cases X with
  | principal _ | bottom | top => exact hA.elim
  | increasing g =>
    obtain ⟨hnA, rfl⟩ := hA
    let A' : IncreasingChain α := ⟨A, hnA⟩
    cases Y with
    | principal _ | bottom | top => exact hB.elim
    | increasing h =>
      obtain ⟨hnB, rfl⟩ := hB
      let B' : IncreasingChain α := ⟨B, hnB⟩
      exact ⟨.increasing, .increasing, represents_restrict_increasing A',
        represents_restrict_increasing B',
        (Domination.segmentLT_increasingIncreasing A' B').mpr
          ((increasing_ofChain_lt_increasing_ofChain A' B').mp hXY)⟩
    | decreasing h =>
      obtain ⟨hnB, rfl⟩ := hB
      let B' : DecreasingChain α := ⟨B, hnB⟩
      exact ⟨.increasing, .decreasing, represents_restrict_increasing A',
        represents_restrict_decreasing B',
        (Domination.segmentLT_increasingDecreasing A' B').mpr
          ((increasing_ofChain_lt_decreasing_ofChain A' B').mp hXY)⟩
  | decreasing g =>
    obtain ⟨hnA, rfl⟩ := hA
    let A' : DecreasingChain α := ⟨A, hnA⟩
    cases Y with
    | principal _ | bottom | top => exact hB.elim
    | increasing h =>
      obtain ⟨hnB, rfl⟩ := hB
      let B' : IncreasingChain α := ⟨B, hnB⟩
      exact ⟨.decreasing, .increasing, represents_restrict_decreasing A',
        represents_restrict_increasing B',
        (Domination.segmentLT_decreasingIncreasing A' B').mpr
          ((decreasing_ofChain_lt_increasing_ofChain A' B').mp hXY)⟩
    | decreasing h =>
      obtain ⟨hnB, rfl⟩ := hB
      let B' : DecreasingChain α := ⟨B, hnB⟩
      exact ⟨.decreasing, .decreasing, represents_restrict_decreasing A',
        represents_restrict_decreasing B',
        (Domination.segmentLT_decreasingDecreasing A' B').mpr
          ((decreasing_ofChain_lt_decreasing_ofChain A' B').mp hXY)⟩

/-- Paper `lem:witness-two-points`: extend the chain given by ordered representatives. -/
theorem exists_witnesses_of_comparable {X Y : H α} (hX : X.IsGenuineNonprincipal)
    (hY : Y.IsGenuineNonprincipal) (hXY : Comparable X Y) :
    ∃ C : SaturatedChain α, Witnesses C X ∧ Witnesses C Y := by
  have strict {U V : H α} (hU : U.IsGenuineNonprincipal) (hV : V.IsGenuineNonprincipal)
      (hUV : U < V) : ∃ C : SaturatedChain α, Witnesses C U ∧ Witnesses C V := by
    obtain ⟨A, B, hA, hB, hAB⟩ := exists_ordered_representatives hU hV hUV
    have hchain : IsChain (· ≤ ·) ((A : Set α) ∪ B) := by
      rintro a (ha | ha) b (hb | hb) hne
      · exact A.isChain ha hb hne
      · exact Or.inl (hAB ha hb).le
      · exact Or.inr (hAB hb ha).le
      · exact B.isChain ha hb hne
    obtain ⟨C, hC⟩ := exists_saturatedChain_superset hchain (A.nonempty.mono subset_union_left)
    exact ⟨C, ⟨A, subset_union_left.trans hC, hA⟩, ⟨B, subset_union_right.trans hC, hB⟩⟩
  rcases hXY with hXY | hYX
  · rcases lt_or_eq_of_le hXY with h | rfl
    · exact strict hX hY h
    · obtain ⟨A, hA⟩ := exists_representative hX.1 hX.2.1 hX.2.2
      exact ⟨A, ⟨A, Subset.rfl, hA⟩, ⟨A, Subset.rfl, hA⟩⟩
  · rcases lt_or_eq_of_le hYX with h | rfl
    · obtain ⟨C, hCY, hCX⟩ := strict hY hX h
      exact ⟨C, hCX, hCY⟩
    · obtain ⟨A, hA⟩ := exists_representative hX.1 hX.2.1 hX.2.2
      exact ⟨A, ⟨A, Subset.rfl, hA⟩, ⟨A, Subset.rfl, hA⟩⟩

private theorem exists_principal_between_signed {X Y : H α}
    (hX : X.IsGenuineNonprincipal) (hY : Y.IsGenuineNonprincipal) (hXY : X < Y)
    (hdir : X.direction = some .decreasing ∨ Y.direction = some .increasing) :
    ∃ x : α, X < principal x ∧ principal x < Y := by
  cases X <;> cases Y <;>
    simp [IsGenuineNonprincipal, IsNonprincipal, direction, Bot.bot, Top.top] at hX hY hdir
  case increasing.increasing => exact exists_principal_between_increasing hXY
  case decreasing.increasing g h =>
    obtain ⟨a, b, hab⟩ := (strictLT_decreasing_increasing g.representative_spec
      h.representative_spec).mp hXY
    obtain ⟨a', ha'⟩ := g.representative.2.exists_lt a
    exact ⟨a.1, (strictLT_decreasing_principal g.representative_spec _).mpr ⟨a', ha'⟩,
      (strictLT_principal_increasing h.representative_spec _).mpr ⟨b, hab⟩⟩
  case decreasing.decreasing => exact exists_principal_between_decreasing hXY

/-- Paper `lem:find-intermediate`: work in the completion of a common witness chain. -/
theorem exists_principal_between_nonprincipal {X Y : H α}
    (hX : X.IsGenuineNonprincipal) (hY : Y.IsGenuineNonprincipal) (hXY : X < Y)
    (hdir : X.direction = some .decreasing ∨ Y.direction = some .increasing) :
    ∃ x : α, X < principal x ∧ principal x < Y := by
  obtain ⟨C, hC⟩ := exists_witnesses_of_comparable hX hY (Or.inl hXY.le)
  obtain ⟨U, hU, rfl⟩ := (witnesses_iff_in_completion C X).mp hC.1
  obtain ⟨V, hV, rfl⟩ := (witnesses_iff_in_completion C Y).mp hC.2
  let e : H (C : Set α) ↪o H α := mapEmbedding (OrderEmbedding.subtype (C : Set α))
    (saturationPreserving_subtype_of_saturated C.saturated)
  have hUV : U < V := e.lt_iff_lt.mp hXY
  have hdir' : U.direction = some .decreasing ∨ V.direction = some .increasing := by
    simpa only [mapEmbedding_apply, direction_map] using hdir
  obtain ⟨x, hUx, hxV⟩ := exists_principal_between_signed hU hV hUV hdir'
  exact ⟨x.1, e.strictMono hUx, e.strictMono hxV⟩

private theorem exists_representative_above (g : IncreasingGerm α) {x : α}
    (hx : principal x < increasing g) :
    ∃ A : SaturatedChain α, Represents A (increasing g) ∧ ∀ a ∈ A, x < a := by
  obtain ⟨c, hc⟩ := (strictLT_principal_increasing g.representative_spec x).mp hx
  let C := g.representative
  refine ⟨C.1.tail c, ?_, fun a ha => hc.trans_le ha.2⟩
  rw [← g.representative_spec]
  exact represents_restrict_increasing C _ (C.1.tail_final c)

private theorem exists_representative_below (g : DecreasingGerm α) {x : α}
    (hx : decreasing g < principal x) :
    ∃ A : SaturatedChain α, Represents A (decreasing g) ∧ ∀ a ∈ A, a < x := by
  have hx' : principal (show αᵒᵈ from x) < increasing g.toDual :=
    (dual_lt_dual (principal x) (decreasing g)).mpr hx
  obtain ⟨A, hA, hAx⟩ := exists_representative_above g.toDual hx'
  exact ⟨A.dual, hA.dual, hAx⟩

private theorem Represents.principal_lt_of_increasing {A : SaturatedChain α}
    {g : IncreasingGerm α} (hA : Represents A (increasing g)) {x : α} (hx : x ∈ A) :
    principal x < increasing g := by
  obtain ⟨hn, hg⟩ := hA
  exact (strictLT_principal_increasing hg x).mpr (hn.exists_gt ⟨x, hx⟩)

private theorem Represents.lt_principal_of_decreasing {A : SaturatedChain α}
    {g : DecreasingGerm α} (hA : Represents A (decreasing g)) {x : α} (hx : x ∈ A) :
    decreasing g < principal x := by
  obtain ⟨hn, hg⟩ := hA
  exact (strictLT_decreasing_principal hg x).mpr (hn.exists_lt ⟨x, hx⟩)

private theorem exists_predecessor_in_interval {ι : Type*} [LinearOrder ι]
    [LocallyFiniteOrder ι] {i j : ι} (hij : i < j) : ∃ k, i ≤ k ∧ k ⋖ j := by
  obtain ⟨k, hk, hmax⟩ := (Set.finite_Ico i j).exists_maximal ⟨i, le_rfl, hij⟩
  exact ⟨k, hk.1, hk.2, fun t hkt htj => hkt.not_ge (hmax ⟨hk.1.trans hkt.le, htj⟩ hkt.le)⟩

private theorem exists_successor_in_interval {ι : Type*} [LinearOrder ι]
    [LocallyFiniteOrder ι] {i j : ι} (hij : i < j) : ∃ k, i ⋖ k ∧ k ≤ j := by
  obtain ⟨k, hk, hmin⟩ := (Set.finite_Ioc i j).exists_minimal ⟨j, hij, le_rfl⟩
  exact ⟨k, ⟨hk.1, fun t hit htk => htk.not_ge (hmin ⟨hit, htk.le.trans hk.2⟩ htk.le)⟩, hk.2⟩

/-- Paper `lem:simultaneous-witness-infinite`: choose a separator in each adjacent
gap with the required direction and restrict the two neighboring representatives. -/
theorem exists_witnesses_of_strictMono {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι]
    [Nonempty ι] (f : ι → H α) (hf : StrictMono f) (hgen : ∀ i, (f i).IsGenuineNonprincipal) :
    ∃ C : SaturatedChain α, ∀ i, Witnesses C (f i) := by
  classical
  let needsCut (i j : ι) := (f i).direction = some .decreasing ∨ (f j).direction = some .increasing
  have hcut (i j : ι) (hij : i ⋖ j) (hs : needsCut i j) :
      ∃ x, f i < principal x ∧ principal x < f j :=
    exists_principal_between_nonprincipal (hgen i) (hgen j) (hf hij.lt) hs
  let cut (i j : ι) (hij : i ⋖ j) (hs : needsCut i j) := Classical.choose (hcut i j hij hs)
  have cut_spec (i j : ι) (hij : i ⋖ j) (hs : needsCut i j) :
      f i < principal (cut i j hij hs) ∧ principal (cut i j hij hs) < f j :=
    Classical.choose_spec (hcut i j hij hs)
  have slices (i : ι) : ∃ A : SaturatedChain α, Represents A (f i) ∧
      ((∀ g, f i = increasing g → ∀ j (hji : j ⋖ i) (hs : needsCut j i),
        ∀ a ∈ A, cut j i hji hs < a) ∧
      (∀ g, f i = decreasing g → ∀ j (hij : i ⋖ j) (hs : needsCut i j),
        ∀ a ∈ A, a < cut i j hij hs)) := by
    have hX := hgen i
    cases hfi : f i with
    | principal _ | bottom | top =>
      rw [hfi] at hX
      simp [IsGenuineNonprincipal, IsNonprincipal, direction, Bot.bot, Top.top] at hX
    | increasing g =>
      by_cases hp : ∃ j, j ⋖ i
      · obtain ⟨j, hji⟩ := hp
        have hs : needsCut j i := Or.inr (by rw [hfi]; rfl)
        have hb := (cut_spec j i hji hs).2
        rw [hfi] at hb
        obtain ⟨A, hA, hAb⟩ := exists_representative_above g hb
        refine ⟨A, hA, ?_, by simp⟩
        intro _ _ k hki hk a ha
        obtain rfl : k = j := hki.unique_left hji
        exact hAb a ha
      · exact ⟨g.representative.1, ⟨g.representative.2, g.representative_spec⟩,
          fun _ _ j hji => (hp ⟨j, hji⟩).elim, by simp⟩
    | decreasing g =>
      by_cases hs : ∃ j, i ⋖ j
      · obtain ⟨j, hij⟩ := hs
        have hb : needsCut i j := Or.inl (by rw [hfi]; rfl)
        have hx := (cut_spec i j hij hb).1
        rw [hfi] at hx
        obtain ⟨A, hA, hAx⟩ := exists_representative_below g hx
        refine ⟨A, hA, by simp, ?_⟩
        intro _ _ k hik hk a ha
        obtain rfl : k = j := hik.unique_right hij
        exact hAx a ha
      · exact ⟨g.representative.1, ⟨g.representative.2, g.representative_spec⟩,
          by simp, fun _ _ j hij => (hs ⟨j, hij⟩).elim⟩
  choose A hA using slices
  have ordered {i j : ι} (hij : i < j) : SetStrictLT (A i : Set α) (A j) := by
    intro a ha b hb
    have hi := (hA i).1
    have hj := (hA j).1
    cases hfi : f i <;> cases hfj : f j <;> rw [hfi] at hi <;> rw [hfj] at hj
    all_goals try exact hi.elim
    all_goals try exact hj.elim
    case increasing.increasing g h =>
      obtain ⟨k, hik, hkj⟩ := exists_predecessor_in_interval hij
      have hs : needsCut k j := Or.inr (by rw [hfj]; rfl)
      have hax : principal a < f i := hfi ▸ hi.principal_lt_of_increasing ha
      exact (principal_lt_principal a b).mp <|
        (((hax.trans_le (hf.monotone hik)).trans (cut_spec k j hkj hs).1).trans
          ((principal_lt_principal _ _).mpr ((hA j).2.1 h hfj k hkj hs b hb)))
    case increasing.decreasing =>
      exact (principal_lt_principal a b).mp <|
        ((hfi ▸ hi.principal_lt_of_increasing ha : principal a < f i).trans (hf hij)).trans
          (hfj ▸ hj.lt_principal_of_decreasing hb : f j < principal b)
    case decreasing.increasing g h =>
      by_cases hcover : i ⋖ j
      · have hs : needsCut i j := Or.inl (by rw [hfi]; rfl)
        exact ((hA i).2.2 g hfi j hcover hs a ha).trans ((hA j).2.1 h hfj i hcover hs b hb)
      · obtain ⟨m, him, hmj⟩ := exists_lt_lt_of_not_covBy hij hcover
        obtain ⟨k, hik, hkm⟩ := exists_successor_in_interval him
        obtain ⟨l, hml, hlj⟩ := exists_predecessor_in_interval hmj
        have hs : needsCut i k := Or.inl (by rw [hfi]; rfl)
        have ht : needsCut l j := Or.inr (by rw [hfj]; rfl)
        have hka : principal a < f k :=
          ((principal_lt_principal _ _).mpr ((hA i).2.2 g hfi k hik hs a ha)).trans
            (cut_spec i k hik hs).2
        have hlb : f l < principal b := (cut_spec l j hlj ht).1.trans
          ((principal_lt_principal _ _).mpr ((hA j).2.1 h hfj l hlj ht b hb))
        exact (principal_lt_principal a b).mp ((hka.trans_le (hf.monotone (hkm.trans hml))).trans hlb)
    case decreasing.decreasing g h =>
      obtain ⟨k, hik, hkj⟩ := exists_successor_in_interval hij
      have hs : needsCut i k := Or.inl (by rw [hfi]; rfl)
      have hka : principal a < f k :=
        ((principal_lt_principal _ _).mpr ((hA i).2.2 g hfi k hik hs a ha)).trans
          (cut_spec i k hik hs).2
      exact (principal_lt_principal a b).mp ((hka.trans_le (hf.monotone hkj)).trans
        (hfj ▸ hj.lt_principal_of_decreasing hb : f j < principal b))
  let S := ⋃ i, (A i : Set α)
  have hS : IsChain (· ≤ ·) S := by
    intro a ha b hb hab
    obtain ⟨i, hai⟩ := mem_iUnion.mp ha
    obtain ⟨j, hbj⟩ := mem_iUnion.mp hb
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact Or.inl (ordered hij hai hbj).le
    · exact (A i).isChain hai hbj hab
    · exact Or.inr (ordered hji hbj hai).le
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨C, hC⟩ := exists_saturatedChain_superset hS
    ((A i).nonempty.mono (subset_iUnion (fun j => (A j : Set α)) i))
  exact ⟨C, fun j => ⟨A j, (subset_iUnion (fun k => (A k : Set α)) j).trans hC, (hA j).1⟩⟩

/-- The integer-suborder formulation of `lem:simultaneous-witness-infinite`,
with the empty index set witnessed by the empty chain. -/
theorem exists_witnesses_on_integer_suborder {I : Set ℤ} (f : I → H α)
    (hf : StrictMono f) (hgen : ∀ i, (f i).IsGenuineNonprincipal) :
    ∃ C : Set α, IsSaturatedChain C ∧
      ∀ i, ∃ A : SaturatedChain α, (A : Set α) ⊆ C ∧ Represents A (f i) := by
  classical
  by_cases hI : Nonempty I
  · let : Nonempty I := hI
    let : LocallyFiniteOrder I := (OrderEmbedding.subtype I).locallyFiniteOrder
    obtain ⟨C, hC⟩ := exists_witnesses_of_strictMono f hf hgen
    exact ⟨C, C.saturated, hC⟩
  · refine ⟨∅, ⟨IsChain.empty, ?_⟩, fun i => (hI ⟨i⟩).elim⟩
    intro _ _ _ h _ _ _ _
    exact h.elim

end H

end AharoniKorman.Completion
