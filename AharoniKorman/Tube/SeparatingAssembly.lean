import AharoniKorman.Tube.Separating
import Mathlib.Order.Zorn

/-! Maximal tubes assembled from an unchanged family of separating tubes. -/

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- Distinct blocks are strictly ordered as whole sets. -/
def OrderedTubeFamily (B : Set (Set α)) : Prop :=
  (∀ T ∈ B, IsTube T) ∧ B.Pairwise (fun S T => SetStrictLT S T ∨ SetStrictLT T S)

theorem OrderedTubeFamily.isTube_sUnion {B : Set (Set α)} (hB : OrderedTubeFamily B) :
    IsTube (⋃₀ B) := by
  rintro x ⟨T, hTB, hxT⟩
  apply (hB.1 T hTB x hxT).subset
  rintro y ⟨⟨S, hSB, hyS⟩, hinc⟩
  have hST : S = T := by
    by_contra hne
    rcases hB.2 hSB hTB hne with h | h
    · exact hinc.not_ge (h hyS hxT).le
    · exact hinc.not_le (h hxT hyS).le
  exact ⟨hST ▸ hyS, hinc⟩

/-- All blocks in this family have the stronger separation property. -/
def SeparatingTubeFamily (B : Set (Set α)) : Prop :=
  (∀ T ∈ B, IsSeparatingTube T) ∧
    B.Pairwise (fun S T => SetStrictLT S T ∨ SetStrictLT T S)

theorem SeparatingTubeFamily.ordered {B : Set (Set α)} (hB : SeparatingTubeFamily B) :
    OrderedTubeFamily B := ⟨fun T hT => (hB.1 T hT).1, hB.2⟩

theorem exists_maximal_separatingTubeFamily :
    ∃ B : Set (Set α), Maximal SeparatingTubeFamily B := by
  classical
  apply zorn_subset {B | SeparatingTubeFamily B}
  intro c hc hchain
  refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun S hS => Set.subset_sUnion_of_mem hS⟩
  · rintro T ⟨B, hB, hTB⟩
    exact (hc hB).1 T hTB
  · rintro S ⟨B, hB, hSB⟩ T ⟨D, hD, hTD⟩ hne
    rcases hchain.total hB hD with hBD | hDB
    · exact (hc hD).2 (hBD hSB) hTD hne
    · exact (hc hB).2 hSB (hDB hTD) hne

/-- The strict gap with lower block set `L`. Empty and unrealizable cuts are allowed. -/
def tubeGap (B : Set (Set α)) (L : Set B) : Set α :=
  {x | ∀ T : B,
    (T ∈ L → ∀ t ∈ T.1, t < x) ∧ (T ∉ L → ∀ t ∈ T.1, x < t)}

theorem tubeGap_ordConnected (B : Set (Set α)) (L : Set B) :
    OrdConnected (tubeGap B L) := by
  constructor
  intro x hx y hy z hz T
  exact ⟨fun h t ht => (hx T).1 h t ht |>.trans_le hz.1,
    fun h t ht => hz.2.trans_lt ((hy T).2 h t ht)⟩

theorem tubeGap_disjoint_sUnion (B : Set (Set α)) (L : Set B) :
    Disjoint (tubeGap B L) (⋃₀ B) := by
  classical
  apply Set.disjoint_left.mpr
  rintro x hx ⟨T, hTB, hxT⟩
  by_cases h : (⟨T, hTB⟩ : B) ∈ L
  · exact (lt_irrefl x) ((hx ⟨T, hTB⟩).1 h x hxT)
  · exact (lt_irrefl x) ((hx ⟨T, hTB⟩).2 h x hxT)

theorem tubeGap_ordered_block (B : Set (Set α)) (L : Set B) {T : Set α} (hT : T ∈ B) :
    SetStrictLT T (tubeGap B L) ∨ SetStrictLT (tubeGap B L) T := by
  classical
  by_cases h : (⟨T, hT⟩ : B) ∈ L
  · exact Or.inl (fun _ ht _ hx => (hx ⟨T, hT⟩).1 h _ ht)
  · exact Or.inr (fun _ hx _ ht => (hx ⟨T, hT⟩).2 h _ ht)

theorem tubeGap_ordered {B : Set (Set α)} (hB : ∀ T ∈ B, T.Nonempty)
    {L M : Set B} (hne : L ≠ M) :
    SetStrictLT (tubeGap B L) (tubeGap B M) ∨
      SetStrictLT (tubeGap B M) (tubeGap B L) := by
  classical
  have hn : ¬ ∀ T, T ∈ L ↔ T ∈ M := Set.ext_iff.not.mp hne
  push Not at hn
  obtain ⟨T, hT⟩ := hn
  obtain ⟨t, ht⟩ := hB T.1 T.2
  rcases hT with ⟨hL, hM⟩ | ⟨hL, hM⟩
  · right
    intro x hx y hy
    exact ((hx T).2 hM t ht).trans ((hy T).1 hL t ht)
  · left
    intro x hx y hy
    exact ((hx T).2 hL t ht).trans ((hy T).1 hM t ht)

theorem SeparatingTubeFamily.outside_gap_or_infinite {B : Set (Set α)}
    (hB : SeparatingTubeFamily B) {x : α} (hx : x ∉ ⋃₀ B) :
    (∃ L : Set B, x ∈ tubeGap B L) ∨
      ∃ T ∈ B, (T ∩ incomparableSet x).Infinite := by
  classical
  by_cases hi : ∃ T ∈ B, (T ∩ incomparableSet x).Infinite
  · exact Or.inr hi
  left
  refine ⟨{T | ∀ t ∈ T.1, t < x}, ?_⟩
  intro T
  refine ⟨fun h => h, ?_⟩
  intro hn
  have hxT : x ∉ T.1 := fun h => hx ⟨T.1, T.2, h⟩
  rcases (hB.1 T.1 T.2).2.2 x hxT with h | h | h
  · exact h
  · exact False.elim (hn h)
  · exact False.elim (hi ⟨T.1, T.2, h⟩)

theorem maximal_separatingTubeFamily.no_separatingTube_in_gap
    {B : Set (Set α)} (hB : Maximal SeparatingTubeFamily B)
    (L : Set B) : ¬ ∃ T ⊆ tubeGap B L, IsSeparatingTube T := by
  classical
  rintro ⟨T, hTG, hT⟩
  have hnot : T ∉ B := by
    intro hTB
    obtain ⟨t, ht⟩ := hT.2.1
    exact Set.disjoint_left.mp (tubeGap_disjoint_sUnion B L) (hTG ht) ⟨T, hTB, ht⟩
  have hadd : SeparatingTubeFamily (insert T B) := by
    constructor
    · intro S hS
      rcases hS with rfl | hS
      · exact hT
      · exact hB.prop.1 S hS
    · intro S hS U hU hne
      rcases hS with rfl | hS <;> rcases hU with rfl | hU
      · exact False.elim (hne rfl)
      · rcases tubeGap_ordered_block B L hU with h | h
        · exact Or.inr (fun _ hu _ ht => h hu (hTG ht))
        · exact Or.inl (fun _ ht _ hu => h (hTG ht) hu)
      · rcases tubeGap_ordered_block B L hS with h | h
        · exact Or.inl (fun _ hs _ ht => h hs (hTG ht))
        · exact Or.inr (fun _ ht _ hs => h (hTG ht) hs)
      · exact hB.prop.2 hS hU hne
  exact hnot (hB.2 hadd (Set.subset_insert T B) (Set.mem_insert T B))

/- The family is kept literally unchanged: taking a union here never takes a
limit of replaced chains or of their germs. -/

/-- A local-to-global principle for maximal tubes. Countability, FAC and
vacillation are not needed for this assembly step itself. -/
theorem exists_isMaximalTube_of_convex_regions
    (hregion : ∀ V : Set α, OrdConnected V → V.Nonempty →
      (∃ T, IsMaximalTubeIn V T) ∨ (∃ T ⊆ V, IsSeparatingTube T)) :
    ∃ T : Set α, IsMaximalTube T := by
  classical
  obtain ⟨B, hB⟩ := exists_maximal_separatingTubeFamily (α := α)
  have hgap : ∀ L : Set B, ∃ T, IsMaximalTubeIn (tubeGap B L) T := by
    intro L
    by_cases hne : (tubeGap B L).Nonempty
    · rcases hregion (tubeGap B L) (tubeGap_ordConnected B L) hne with h | h
      · exact h
      · exact False.elim (maximal_separatingTubeFamily.no_separatingTube_in_gap hB L h)
    · have he := Set.not_nonempty_iff_eq_empty.mp hne
      refine ⟨∅, Set.empty_subset _, ?_, ?_⟩
      · intro x hx
        exact False.elim hx
      · intro x hx
        simp only [he, Set.mem_empty_iff_false] at hx
  choose Tg hTg using hgap
  let D : Set (Set α) := B ∪ Set.range Tg
  have hD : OrderedTubeFamily D := by
    constructor
    · intro T hT
      rcases hT with hT | ⟨L, rfl⟩
      · exact (hB.prop.1 T hT).1
      · exact (hTg L).2.1
    · intro S hS T hT hne
      rcases hS with hS | ⟨L, rfl⟩ <;> rcases hT with hT | ⟨M, rfl⟩
      · exact hB.prop.2 hS hT hne
      · rcases tubeGap_ordered_block B M hS with h | h
        · exact Or.inl (fun _ hs _ ht => h hs ((hTg M).1 ht))
        · exact Or.inr (fun _ ht _ hs => h ((hTg M).1 ht) hs)
      · rcases tubeGap_ordered_block B L hT with h | h
        · exact Or.inr (fun _ ht _ hs => h ht ((hTg L).1 hs))
        · exact Or.inl (fun _ hs _ ht => h ((hTg L).1 hs) ht)
      · have hLM : L ≠ M := fun h => hne (congrArg Tg h)
        rcases tubeGap_ordered (fun U hU => (hB.prop.1 U hU).2.1) hLM with h | h
        · exact Or.inl (fun _ hs _ ht => h ((hTg L).1 hs) ((hTg M).1 ht))
        · exact Or.inr (fun _ ht _ hs => h ((hTg M).1 ht) ((hTg L).1 hs))
  refine ⟨⋃₀ D, (isMaximalTube_iff _).mpr ⟨hD.isTube_sUnion, ?_⟩⟩
  intro x hx
  have hxB : x ∉ ⋃₀ B := by
    rintro ⟨T, hTB, hxT⟩
    exact hx ⟨T, Or.inl hTB, hxT⟩
  rcases hB.prop.outside_gap_or_infinite hxB with ⟨L, hxL⟩ | ⟨T, hTB, hi⟩
  · have hxT : x ∉ Tg L := fun h => hx ⟨Tg L, Or.inr ⟨L, rfl⟩, h⟩
    apply ((hTg L).2.2 x hxL hxT).mono
    rintro y ⟨hy, hinc⟩
    exact ⟨⟨Tg L, Or.inr ⟨L, rfl⟩, hy⟩, hinc⟩
  · apply hi.mono
    rintro y ⟨hy, hinc⟩
    exact ⟨⟨T, Or.inl hTB, hy⟩, hinc⟩

end AharoniKorman
