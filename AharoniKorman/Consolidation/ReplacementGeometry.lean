import AharoniKorman.Consolidation.LocalReplacement
import AharoniKorman.Final.HullConvexity

namespace AharoniKorman.Consolidation

noncomputable section

open Set Completion

variable {α : Type*} [PartialOrder α]

structure IncreasingFan (C : MaximalChains α) where
  point : α
  point_mem : point ∈ C.carrier
  seq : ℕ → α
  strict : StrictMono seq
  incomparable : ∀ n, Incomparable (seq n) point
  finite_trace : ∀ n, (C.carrier ∩ incomparableSet (seq n)).Finite

namespace IncreasingFan

variable {C : MaximalChains α} (G : IncreasingFan C)

def middle : Set α := {x | x ∈ C.carrier ∧ ∃ n, Incomparable (G.seq n) x}
def left : Set α := {x | x ∈ C.carrier ∧ x < G.point ∧ x ∉ G.middle}
def right : Set α := {x | x ∈ C.carrier ∧ G.point < x ∧ x ∉ G.middle}

theorem point_middle : G.point ∈ G.middle := ⟨G.point_mem, 0, G.incomparable 0⟩

theorem incomparable_between {y a b x : α} (ha : Incomparable y a) (hb : Incomparable y b)
    (hax : a ≤ x) (hxb : x ≤ b) : Incomparable y x :=
  ⟨fun hyx => hb.not_le (hyx.trans hxb), fun hxy => ha.not_ge (hax.trans hxy)⟩

theorem middle_convex {a b x : α} (ha : a ∈ G.middle) (hb : b ∈ G.middle)
    (hx : x ∈ C.carrier) (hax : a ≤ x) (hxb : x ≤ b) : x ∈ G.middle := by
  obtain ⟨haC, n, han⟩ := ha
  obtain ⟨hbC, m, hbm⟩ := hb
  refine ⟨hx, ?_⟩
  rcases C.isMaximal.1.total hx G.point_mem with hxk | hkx
  · exact ⟨n, incomparable_between han (G.incomparable n) hax hxk⟩
  · exact ⟨m, incomparable_between (G.incomparable m) hbm hkx hxb⟩

def middleChain : SaturatedChain α :=
  ⟨G.middle, ⟨G.point, G.point_middle⟩,
    C.isSaturated.restrict (fun _ hx => hx.1) (fun _ _ _ ha hb hx hax hxb => G.middle_convex ha hb hx hax hxb)⟩

theorem decomposition : C.carrier = (G.left ∪ G.middle) ∪ G.right := by
  ext x
  constructor
  · intro hx
    by_cases hxJ : x ∈ G.middle
    · exact Or.inl (Or.inr hxJ)
    have hne : x ≠ G.point := fun h => hxJ (h.symm ▸ G.point_middle)
    rcases C.isMaximal.1.total hx G.point_mem with hxk | hkx
    · exact Or.inl (Or.inl ⟨hx, lt_of_le_of_ne hxk hne, hxJ⟩)
    · exact Or.inr ⟨hx, lt_of_le_of_ne hkx hne.symm, hxJ⟩
  · rintro ((h | h) | h) <;> exact h.1

theorem left_middle : SetStrictLT G.left G.middle := by
  intro l hl j hj
  rcases C.isMaximal.1.total hl.1 hj.1 with hlj | hjl
  · exact lt_of_le_of_ne hlj (fun heq => hl.2.2 (heq.symm ▸ hj))
  · exact False.elim (hl.2.2 (G.middle_convex hj G.point_middle hl.1 hjl hl.2.1.le))

theorem middle_right : SetStrictLT G.middle G.right := by
  intro j hj r hr
  rcases C.isMaximal.1.total hj.1 hr.1 with hjr | hrj
  · exact lt_of_le_of_ne hjr (fun heq => hr.2.2 (heq ▸ hj))
  · exact False.elim (hr.2.2 (G.middle_convex G.point_middle hj hr.1 hr.2.1.le hrj))

theorem left_seq {l : α} (hl : l ∈ G.left) (n : ℕ) : l < G.seq n := by
  have hinc : ¬Incomparable (G.seq n) l := fun h => hl.2.2 ⟨hl.1, n, h⟩
  rcases not_incompRel_iff_symmGen.1 hinc with h | h
  · exact False.elim ((G.incomparable n).not_le (h.trans hl.2.1.le))
  · exact lt_of_le_of_ne h (fun heq => (G.incomparable n).not_le (heq ▸ hl.2.1.le))

theorem seq_right {r : α} (hr : r ∈ G.right) (n : ℕ) : G.seq n < r := by
  have hinc : ¬Incomparable (G.seq n) r := fun h => hr.2.2 ⟨hr.1, n, h⟩
  rcases not_incompRel_iff_symmGen.1 hinc with h | h
  · exact lt_of_le_of_ne h (fun heq => (G.incomparable n).not_ge (heq.symm ▸ hr.2.1.le))
  · exact False.elim ((G.incomparable n).not_ge (hr.2.1.le.trans h))

/-- The union has finite initial intervals without making the individual traces nested. -/
theorem finite_initial : FiniteInitialIntervals G.middle := by
  intro p hp
  obtain ⟨hpC, n, hnp⟩ := hp
  apply ((G.finite_trace 0).union (G.finite_trace n)).subset
  rintro x ⟨⟨hxC, m, hmx⟩, hxp⟩
  rcases C.isMaximal.1.total hxC G.point_mem with hxk | hkx
  · refine Or.inl ⟨hxC, ?_⟩
    exact ⟨fun h => (G.incomparable 0).not_le (h.trans hxk),
      fun h => hmx.not_ge (h.trans (G.strict.monotone (Nat.zero_le m)))⟩
  · exact Or.inr ⟨hxC, incomparable_between (G.incomparable n) hnp hkx hxp⟩

theorem middle_above_seq (hinf : G.middle.Infinite) (n : ℕ) : ∃ j ∈ G.middle, G.seq n < j := by
  classical
  let F := (C.carrier ∩ incomparableSet (G.seq n)) ∪ (G.middle ∩ Iic G.point)
  have hF : F.Finite := (G.finite_trace n).union (G.finite_initial G.point G.point_middle)
  have hex : ∃ j ∈ G.middle, j ∉ F := by
    by_contra! hno
    exact hinf (hF.subset hno)
  obtain ⟨j, hj, hjF⟩ := hex
  have hinc : ¬Incomparable (G.seq n) j := fun h => hjF (Or.inl ⟨hj.1, h⟩)
  have hkj : G.point < j := by
    rcases C.isMaximal.1.total G.point_mem hj.1 with h | h
    · exact lt_of_le_of_ne h (fun heq => hjF (Or.inr ⟨hj, heq.symm.le⟩))
    · exact False.elim (hjF (Or.inr ⟨hj, h⟩))
  refine ⟨j, hj, ?_⟩
  rcases not_incompRel_iff_symmGen.1 hinc with h | h
  · exact lt_of_le_of_ne h (fun heq => (G.incomparable n).not_ge (heq.symm ▸ hkj.le))
  · exact False.elim ((G.incomparable n).not_ge (hkj.le.trans h))

include G in
theorem exists_replacement : Nonempty (LocalReplacement C) := by
  classical
  let S : Set α := (G.left ∪ G.right) ∪ range G.seq
  have hchain : IsChain (· ≤ ·) S := by
    rintro x ((hxl | hxr) | ⟨i, rfl⟩) y ((hyl | hyr) | ⟨j, rfl⟩) _
    · exact C.isMaximal.1.total hxl.1 hyl.1
    · exact C.isMaximal.1.total hxl.1 hyr.1
    · exact Or.inl (G.left_seq hxl j).le
    · exact C.isMaximal.1.total hxr.1 hyl.1
    · exact C.isMaximal.1.total hxr.1 hyr.1
    · exact Or.inr (G.seq_right hxr j).le
    · exact Or.inr (G.left_seq hyl i).le
    · exact Or.inl (G.seq_right hyr i).le
    · exact (le_total i j).elim (fun h => Or.inl (G.strict.monotone h)) (fun h => Or.inr (G.strict.monotone h))
  obtain ⟨D, hD, hSD⟩ := hchain.exists_maxChain
  let E : MaximalChains α := ⟨D, hD⟩
  have hyD : ∀ n, G.seq n ∈ D := fun n => hSD (Or.inr ⟨n, rfl⟩)
  let Yset := convexHullIn D (range G.seq)
  have hyY : ∀ n, G.seq n ∈ Yset := fun n =>
    ⟨hyD n, G.seq n, ⟨n, rfl⟩, G.seq n, ⟨n, rfl⟩, le_rfl, le_rfl⟩
  have hYsat : IsSaturatedChain Yset := E.isSaturated.restrict (fun _ hx => hx.1) (by
    rintro a b x ⟨haD, l, hl, r, hr, hla, har⟩ ⟨hbD, l', hl', r', hr', hlb, hbr⟩ hx hax hxb
    exact ⟨hx, l, hl, r', hr', hla.trans hax, hxb.trans hbr⟩)
  let Ychain : SaturatedChain α := ⟨Yset, ⟨G.seq 0, hyY 0⟩, hYsat⟩
  have hYtop : Ychain.NoTop := by
    rintro ⟨m, hm⟩
    obtain ⟨hmD, l, hl, r, ⟨n, rfl⟩, hlm, hmr⟩ := m.2
    have hmn : m.1 < G.seq (n + 1) := hmr.trans_lt (G.strict (Nat.lt_succ_self n))
    exact hmn.not_ge (hm ⟨G.seq (n + 1), hyY (n + 1)⟩)
  let Y : IncreasingChain α := ⟨Ychain, hYtop⟩
  refine ⟨{
    target := E
    left := G.left
    middle := G.middleChain
    right := G.right
    decomposition := G.decomposition
    left_middle := G.left_middle
    middle_right := G.middle_right
    finite_initial := G.finite_initial
    replacement := Y
    left_replacement := ?_
    replacement_right := ?_
    left_target := fun _ h => hSD (Or.inl (Or.inl h))
    right_target := fun _ h => hSD (Or.inl (Or.inr h))
    replacement_target := fun _ h => h.1
    profile_control := ?_
    separating_point := ⟨G.point, G.point_mem, ?_⟩ }⟩
  · rintro l hl y ⟨hyD, a, ⟨n, rfl⟩, b, hb, hay, hyb⟩
    exact (G.left_seq hl n).trans_le hay
  · rintro y ⟨hyD, a, ha, b, ⟨n, rfl⟩, hay, hyb⟩ r hr
    exact hyb.trans_lt (G.seq_right hr n)
  · rintro hinf y ⟨hyD, a, ha, b, ⟨n, rfl⟩, hay, hyb⟩
    obtain ⟨j, hj, hnj⟩ := G.middle_above_seq hinf n
    exact ⟨j, hj, hyb.trans_lt hnj⟩
  · have hpoint := subset_finiteIncomparabilityHull C.isMaximal.1 G.point_mem
    have hconv := finiteIncomparabilityHull_trace_ordConnected hpoint
    rintro y ⟨_, a, ⟨n, rfl⟩, b, ⟨m, rfl⟩, hay, hyb⟩
    exact (hconv.out ⟨G.finite_trace n, (G.incomparable n).symm⟩
      ⟨G.finite_trace m, (G.incomparable m).symm⟩ ⟨hay, hyb⟩).2

end IncreasingFan

end

end AharoniKorman.Consolidation
