import AharoniKorman.External.Zaguia
import AharoniKorman.Preliminaries.Choice
import Mathlib.Data.Set.Finite.Lattice

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- Paper Lemma `lem:extend-spine-partition`: every outside point has infinitely many compatible
blocks in any spine partition of a maximal tube. -/
theorem outside_incomparable_blocks [Countable α] (hfac : IsFAC α)
    {T C : Set α} (hT : IsMaximalTube T) (S : SpineData T C) {y : α} (hy : y ∉ T) :
    {x : C | ∀ z ∈ S.block x, Incomparable y z}.Infinite := by
  classical
  let allIncomparable : Set C := {x | ∀ z ∈ S.block x, Incomparable y z}
  let someIncomparable : Set C :=
    {x | ∃ z ∈ S.block x, Incomparable y z}
  have hOutside : (T ∩ incomparableSet y).Infinite :=
    (isMaximalTube_iff T).mp hT |>.2 y hy
  have hSome : someIncomparable.Infinite := by
    intro hSomeFinite
    apply hOutside
    apply (hSomeFinite.biUnion fun x _ => hfac _ (S.block_antichain x)).subset
    rintro z ⟨hzT, hzy⟩
    have hzUnion : z ∈ ⋃ x, S.block x := by
      rw [S.iUnion_blocks]
      exact hzT
    simp only [Set.mem_iUnion] at hzUnion
    obtain ⟨x, hzx⟩ := hzUnion
    exact Set.mem_iUnion_of_mem x <| Set.mem_iUnion_of_mem ⟨z, hzx, hzy⟩ hzx
  intro hAllInfinite
  have hAllFinite : allIncomparable.Finite := by
    simpa only [allIncomparable] using hAllInfinite
  let mixed : Set C := someIncomparable \ allIncomparable
  have hMixed : mixed.Infinite := hSome.sdiff hAllFinite
  let M := mixed
  have : Infinite M := Set.infinite_coe_iff.mpr hMixed

  have z_exists (m : M) : ∃ z ∈ S.block m.1, Incomparable y z := m.2.1
  let z : M → α := fun m => Classical.choose (z_exists m)
  have z_spec (m : M) : z m ∈ S.block m.1 ∧ Incomparable y (z m) :=
    Classical.choose_spec (z_exists m)

  have a_exists (m : M) : ∃ a ∈ S.block m.1, Comparable y a := by
    have hm := m.2.2
    simp only [allIncomparable, Set.mem_ofPred_eq] at hm
    push Not at hm
    obtain ⟨a, ha, hnot⟩ := hm
    exact ⟨a, ha, not_incompRel_iff_symmGen.mp hnot⟩
  let a : M → α := fun m => Classical.choose (a_exists m)
  have a_spec (m : M) : a m ∈ S.block m.1 ∧ Comparable y (a m) :=
    Classical.choose_spec (a_exists m)

  have choice_injective (w : M → α) (hw : ∀ m, w m ∈ S.block m.1) :
      Function.Injective w := by
    intro m n hmn
    apply Subtype.ext
    by_contra hidx
    have hd := Set.disjoint_left.mp (S.blocks_disjoint m.1 n.1 hidx)
    exact hd (hw m) (by simpa [← hmn] using hw n)
  have z_injective : Function.Injective z := choice_injective z fun m => (z_spec m).1
  have a_injective : Function.Injective a := choice_injective a fun m => (a_spec m).1
  have z_mem_T (m : M) : z m ∈ T := S.block_subset m.1 (z_spec m).1
  have a_mem_T (m : M) : a m ∈ T := S.block_subset m.1 (a_spec m).1
  have za_incomparable (m : M) : Incomparable (z m) (a m) := by
    have hne : z m ≠ a m := by
      intro heq
      exact (not_symmGen_iff.mpr (z_spec m).2) (by simpa [heq] using (a_spec m).2)
    exact ⟨S.block_antichain m.1 (z_spec m).1 (a_spec m).1 hne,
      S.block_antichain m.1 (a_spec m).1 (z_spec m).1 hne.symm⟩

  let e : ℕ ↪ M := Infinite.natEmbedding M
  obtain ⟨g, hMonotone⟩ :=
    hfac.exists_strictMono_or_strictAnti_subsequence (z_injective.comp e.injective)
  let idx : ℕ → M := fun n => e (g n)
  have idx_injective : Function.Injective idx := e.injective.comp g.injective
  have zseq_injective : Function.Injective (fun n => z (idx n)) :=
    z_injective.comp idx_injective
  have aseq_injective : Function.Injective (fun n => a (idx n)) :=
    a_injective.comp idx_injective
  have later_z_comparable (k : ℕ) :
      ∃ n, k < n ∧ Comparable (a (idx k)) (z (idx n)) := by
    let tail : ℕ → α := fun n => z (idx (n + k + 1))
    have htail : Function.Injective tail := by
      intro m n hmn
      have hindex : m + k + 1 = n + k + 1 := zseq_injective hmn
      omega
    have hTailInfinite : (Set.range tail).Infinite := Set.infinite_range_of_injective htail
    obtain ⟨w, ⟨n, rfl⟩, hw⟩ :=
      hTailInfinite.exists_notMem_finite (hT.1 _ (a_mem_T (idx k)))
    refine ⟨n + k + 1, by omega, ?_⟩
    apply not_incompRel_iff_symmGen.mp
    intro hinc
    exact hw ⟨z_mem_T _, hinc⟩

  have later_a_comparable :
      ∃ n, 0 < n ∧ Comparable (z (idx 0)) (a (idx n)) := by
    let tail : ℕ → α := fun n => a (idx (n + 1))
    have htail : Function.Injective tail := by
      intro m n hmn
      have hindex : m + 1 = n + 1 := aseq_injective hmn
      omega
    have hTailInfinite : (Set.range tail).Infinite := Set.infinite_range_of_injective htail
    obtain ⟨w, ⟨n, rfl⟩, hw⟩ :=
      hTailInfinite.exists_notMem_finite (hT.1 _ (z_mem_T (idx 0)))
    refine ⟨n + 1, by omega, ?_⟩
    apply not_incompRel_iff_symmGen.mp
    intro hinc
    exact hw ⟨a_mem_T _, hinc⟩

  rcases hMonotone with hIncreasing | hDecreasing
  · have hIncreasing' : StrictMono (fun n => z (idx n)) := by
      intro m n hmn
      exact hIncreasing hmn
    have a_lt_y (k : ℕ) : a (idx k) < y := by
      obtain ⟨n, hkn, hcomp⟩ := later_z_comparable k
      have hzz : z (idx k) < z (idx n) := hIncreasing' hkn
      have hnotReverse : ¬z (idx n) ≤ a (idx k) := fun h =>
        (za_incomparable (idx k)).not_le (hzz.le.trans h)
      have haz : a (idx k) ≤ z (idx n) := by
        rcases hcomp with h | h
        · exact h
        · exact False.elim (hnotReverse h)
      have hne : a (idx k) ≠ z (idx n) := by
        intro heq
        exact (not_symmGen_iff.mpr (z_spec (idx n)).2) (by
          simpa [heq] using (a_spec (idx k)).2)
      have haz' : a (idx k) < z (idx n) := lt_of_le_of_ne haz hne
      rcases (a_spec (idx k)).2 with hya | hay
      · exact False.elim ((z_spec (idx n)).2.not_le (hya.trans haz'.le))
      · exact lt_of_le_of_ne hay fun heq => (z_spec (idx n)).2.not_lt (heq ▸ haz')
    obtain ⟨n, hn, hcomp⟩ := later_a_comparable
    have hzz : z (idx 0) < z (idx n) := hIncreasing' hn
    have hnotReverse : ¬a (idx n) ≤ z (idx 0) := fun h =>
      (za_incomparable (idx n)).not_ge (h.trans hzz.le)
    have hza : z (idx 0) ≤ a (idx n) := by
      rcases hcomp with h | h
      · exact h
      · exact False.elim (hnotReverse h)
    have hza' : z (idx 0) < a (idx n) := lt_of_le_of_ne hza fun heq =>
      (z_spec (idx 0)).2.not_gt (heq ▸ a_lt_y n)
    exact (z_spec (idx 0)).2.not_gt (hza'.trans (a_lt_y n))

  · have hDecreasing' : StrictAnti (fun n => z (idx n)) := by
      intro m n hmn
      exact hDecreasing hmn
    have y_lt_a (k : ℕ) : y < a (idx k) := by
      obtain ⟨n, hkn, hcomp⟩ := later_z_comparable k
      have hzz : z (idx n) < z (idx k) := hDecreasing' hkn
      have hnotForward : ¬a (idx k) ≤ z (idx n) := fun h =>
        (za_incomparable (idx k)).not_ge (h.trans hzz.le)
      have hza : z (idx n) ≤ a (idx k) := by
        rcases hcomp with h | h
        · exact False.elim (hnotForward h)
        · exact h
      have hne : z (idx n) ≠ a (idx k) := by
        intro heq
        exact (not_symmGen_iff.mpr (z_spec (idx n)).2) (by
          simpa [← heq] using (a_spec (idx k)).2)
      have hza' : z (idx n) < a (idx k) := lt_of_le_of_ne hza hne
      rcases (a_spec (idx k)).2 with hya | hay
      · exact lt_of_le_of_ne hya fun heq => (z_spec (idx n)).2.not_gt (hza'.trans_eq heq.symm)
      · exact False.elim ((z_spec (idx n)).2.not_ge (hza'.le.trans hay))
    obtain ⟨n, hn, hcomp⟩ := later_a_comparable
    have hzz : z (idx n) < z (idx 0) := hDecreasing' hn
    have hnotForward : ¬z (idx 0) ≤ a (idx n) := fun h =>
      (za_incomparable (idx n)).not_le (hzz.le.trans h)
    have haz : a (idx n) ≤ z (idx 0) := by
      rcases hcomp with h | h
      · exact False.elim (hnotForward h)
      · exact h
    have haz' : a (idx n) < z (idx 0) := lt_of_le_of_ne haz fun heq =>
      (z_spec (idx 0)).2.not_lt ((y_lt_a n).trans_eq heq)
    exact (z_spec (idx 0)).2.not_lt ((y_lt_a n).trans haz')

/-- Countably assign outside points to distinct compatible blocks and extend the partition. -/
theorem extend_spineData [Countable α] (hfac : IsFAC α)
    {T C : Set α} (hT : IsMaximalTube T) (S : SpineData T C) :
    Nonempty (SpineData (Set.univ : Set α) C) := by
  classical
  let Outside := {y : α // y ∉ T}
  let compatible : Outside → Set C := fun y =>
    {x | ∀ z ∈ S.block x, Incomparable y.1 z}
  have hcompatible (y : Outside) : (compatible y).Infinite := by
    simpa only [compatible] using outside_incomparable_blocks hfac hT S y.2
  obtain ⟨assign, hassign_injective, hassign⟩ :=
    exists_injective_selector compatible hcompatible
  let added : C → Set α := fun x =>
    {y | ∃ hy : y ∉ T, assign ⟨y, hy⟩ = x}
  let block' : C → Set α := fun x => S.block x ∪ added x

  have assigned_compatible (y : Outside) :
      ∀ z ∈ S.block (assign y), Incomparable y.1 z := by
    simpa [compatible] using hassign y
  have block'_antichain (x : C) : IsAntichain (· ≤ ·) (block' x) := by
    intro p hp q hq hpq
    rcases hp with hpOld | hpAdded
    · rcases hq with hqOld | hqAdded
      · exact S.block_antichain x hpOld hqOld hpq
      · obtain ⟨hqOutside, hqAssigned⟩ := hqAdded
        have hinc : Incomparable q p := assigned_compatible ⟨q, hqOutside⟩ p <| by
          simpa only [hqAssigned] using hpOld
        exact hinc.not_ge
    · rcases hq with hqOld | hqAdded
      · obtain ⟨hpOutside, hpAssigned⟩ := hpAdded
        have hinc : Incomparable p q := assigned_compatible ⟨p, hpOutside⟩ q <| by
          simpa only [hpAssigned] using hqOld
        exact hinc.not_le
      · obtain ⟨hpOutside, hpAssigned⟩ := hpAdded
        obtain ⟨hqOutside, hqAssigned⟩ := hqAdded
        have hsubtype : (⟨p, hpOutside⟩ : Outside) = ⟨q, hqOutside⟩ :=
          hassign_injective (hpAssigned.trans hqAssigned.symm)
        exact False.elim <| hpq (congrArg Subtype.val hsubtype)

  have blocks'_disjoint (x y : C) (hxy : x ≠ y) : Disjoint (block' x) (block' y) := by
    rw [Set.disjoint_left]
    intro p hp hq
    rcases hp with hpOld | hpAdded
    · rcases hq with hqOld | hqAdded
      · exact Set.disjoint_left.mp (S.blocks_disjoint x y hxy) hpOld hqOld
      · obtain ⟨hpOutside, _⟩ := hqAdded
        exact hpOutside (S.block_subset x hpOld)
    · rcases hq with hqOld | hqAdded
      · obtain ⟨hpOutside, _⟩ := hpAdded
        exact hpOutside (S.block_subset y hqOld)
      · obtain ⟨hpOutside, hpAssigned⟩ := hpAdded
        obtain ⟨hqOutside, hqAssigned⟩ := hqAdded
        exact hxy (hpAssigned.symm.trans hqAssigned)

  refine ⟨{
    chain := S.chain
    chain_subset := fun _ _ => Set.mem_univ _
    block := block'
    block_antichain := block'_antichain
    mem_block := fun x => Or.inl (S.mem_block x)
    blocks_disjoint := blocks'_disjoint
    iUnion_blocks := ?_
  }⟩
  ext p
  constructor
  · intro _
    exact Set.mem_univ p
  · intro _
    by_cases hp : p ∈ T
    · have hpUnion : p ∈ ⋃ x, S.block x := by simpa [S.iUnion_blocks] using hp
      simp only [Set.mem_iUnion] at hpUnion ⊢
      obtain ⟨x, hpx⟩ := hpUnion
      exact ⟨x, Or.inl hpx⟩
    · exact Set.mem_iUnion_of_mem (assign ⟨p, hp⟩) <| Or.inr ⟨hp, rfl⟩

end AharoniKorman
