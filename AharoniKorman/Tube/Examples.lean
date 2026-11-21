import AharoniKorman.Tube.Spine
import Mathlib.Order.WithBot

/-! Figure `fig:maximal-tube`, with rails A, B and C numbered 0, 1 and 2. -/

namespace AharoniKorman.TubeExample

open Set

structure RailPoint where
  level : ℕ
  rail : Fin 3

instance : PartialOrder RailPoint where
  le x y := (x.rail = y.rail ∧ x.level ≤ y.level) ∨ (x.rail ≠ 0 ∧ x.level < y.level)
  le_refl x := Or.inl ⟨rfl, le_rfl⟩
  le_trans x y z hxy hyz := by
    rcases hxy with ⟨hr, hl⟩ | ⟨hr, hl⟩ <;> rcases hyz with ⟨hr', hl'⟩ | ⟨hr', hl'⟩
    · exact Or.inl ⟨hr.trans hr', hl.trans hl'⟩
    · exact Or.inr ⟨hr ▸ hr', hl.trans_lt hl'⟩
    · exact Or.inr ⟨hr, hl.trans_le hl'⟩
    · exact Or.inr ⟨hr, hl.trans hl'⟩
  le_antisymm x y hxy hyx := by
    rcases hxy with ⟨hr, hl⟩ | ⟨_, hl⟩ <;> rcases hyx with ⟨_, hl'⟩ | ⟨_, hl'⟩
    · cases x
      cases y
      simp only [RailPoint.mk.injEq]
      exact ⟨le_antisymm hl hl', hr⟩
    · exact (hl'.not_ge hl).elim
    · exact (hl.not_ge hl').elim
    · exact (hl.not_ge hl'.le).elim

abbrev Model := WithBot (WithTop RailPoint)

def atLevel (n : ℕ) (j : Fin 3) : Model := ↑(↑(RailPoint.mk n j) : WithTop RailPoint)

private theorem atLevel_inj {n m : ℕ} {j k : Fin 3} :
    atLevel n j = atLevel m k → n = m ∧ j = k := by
  simp [atLevel, RailPoint.mk.injEq]

private theorem atLevel_le {n m : ℕ} {j k : Fin 3} :
    atLevel n j ≤ atLevel m k ↔ (j = k ∧ n ≤ m) ∨ (j ≠ 0 ∧ n < m) := by
  simp only [atLevel, WithBot.coe_le_coe, WithTop.coe_le_coe]
  rfl

private theorem model_cases (x : Model) : x = ⊥ ∨ x = ⊤ ∨ ∃ n j, x = atLevel n j := by
  induction x using WithBot.recBotCoe with
  | bot => exact Or.inl rfl
  | coe x =>
    induction x using WithTop.recTopCoe with
    | top => exact Or.inr (Or.inl rfl)
    | coe x => exact Or.inr (Or.inr ⟨x.level, x.rail, by cases x; rfl⟩)

def maximalTube : Set Model := (range fun n : ℕ => atLevel n 0)ᶜ

private theorem rail_zero_not_mem (n : ℕ) : atLevel n 0 ∉ maximalTube :=
  fun hn => hn (mem_range_self n)

private theorem rail_nonzero_mem {j : Fin 3} (hj : j ≠ 0) (n : ℕ) :
    atLevel n j ∈ maximalTube := by
  rintro ⟨m, hm⟩
  exact hj (atLevel_inj hm.symm).2

private def bounded (n : ℕ) : Set Model :=
  range fun x : Fin (n + 1) × Fin 3 => atLevel x.1.1 x.2

private theorem bounded_finite (n : ℕ) : (bounded n).Finite := finite_range _

private theorem mem_bounded {n m : ℕ} {j : Fin 3} (hm : m ≤ n) :
    atLevel m j ∈ bounded n := ⟨(⟨m, Nat.lt_succ_of_le hm⟩, j), rfl⟩

private theorem high_rail_incomp_zero {n m : ℕ} {j : Fin 3} (hj : j ≠ 0) (hnm : n ≤ m) :
    Incomparable (atLevel n 0) (atLevel m j) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (atLevel_le.mp h).elim (fun h' => hj h'.1.symm) (fun h' => h'.1 rfl)
  · exact (atLevel_le.mp h).elim (fun h' => hj h'.1) (fun h' => h'.2.not_ge hnm)

private theorem outside_incomp_infinite (n : ℕ) :
    (maximalTube ∩ incomparableSet (atLevel n 0)).Infinite := by
  let f (m : ℕ) := atLevel (m + n) 1
  have hf : Function.Injective f := fun x y h => Nat.add_right_cancel (atLevel_inj h).1
  apply (infinite_range_of_injective hf).mono
  rintro _ ⟨m, rfl⟩
  exact ⟨rail_nonzero_mem (by decide) _, high_rail_incomp_zero (by decide) (Nat.le_add_left _ _)⟩

theorem isMaximalTube_maximalTube : IsMaximalTube maximalTube := by
  apply (isMaximalTube_iff _).mpr
  constructor
  · intro x hx
    rcases model_cases x with rfl | rfl | ⟨n, j, rfl⟩
    · exact finite_empty.subset fun y hy => (hy.2.not_le bot_le).elim
    · exact finite_empty.subset fun y hy => (hy.2.not_ge le_top).elim
    have hj : j ≠ 0 := fun hj => rail_zero_not_mem n (hj ▸ hx)
    apply (bounded_finite n).subset
    intro y hy
    rcases model_cases y with rfl | rfl | ⟨m, k, rfl⟩
    · exact (hy.2.not_ge bot_le).elim
    · exact (hy.2.not_le le_top).elim
    exact mem_bounded (le_of_not_gt fun h => hy.2.not_le (atLevel_le.mpr (Or.inr ⟨hj, h⟩)))
  · intro x hx
    have hr : x ∈ range fun n : ℕ => atLevel n 0 := by
      simpa only [maximalTube, mem_compl_iff, not_not] using hx
    obtain ⟨n, rfl⟩ := hr
    exact outside_incomp_infinite n

/-- The tube in Figure `fig:maximal-tube` is the unique inclusion-maximal tube. -/
theorem maximalTube_unique {U : Set Model} (hU : IsMaximalTube U) : U = maximalTube := by
  classical
  have no_zero (n : ℕ) : atLevel n 0 ∉ U := by
    intro hn
    have hsmall : (U ∩ maximalTube).Finite := by
      apply (((hU.1 _ hn).union (bounded_finite n)).union
        ((finite_singleton (⊥ : Model)).union (finite_singleton (⊤ : Model)))).subset
      intro x hx
      rcases model_cases x with rfl | rfl | ⟨m, j, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      by_cases hmn : m ≤ n
      · exact Or.inl (Or.inr (mem_bounded hmn))
      · have hj : j ≠ 0 := fun hj => rail_zero_not_mem m (hj ▸ hx.2)
        exact Or.inl (Or.inl ⟨hx.1, high_rail_incomp_zero hj (le_of_not_ge hmn)⟩)
    apply outside_incomp_infinite n (hsmall.subset ?_)
    intro x hx
    refine ⟨?_, hx.1⟩
    by_contra hnot
    rcases model_cases x with rfl | rfl | ⟨m, j, rfl⟩
    · exact hx.2.not_ge bot_le
    · exact hx.2.not_le le_top
    have hj : j ≠ 0 := fun hj => rail_zero_not_mem m (hj ▸ hx.1)
    have hfinite : (U ∩ incomparableSet (atLevel m j)).Finite := by
      apply (hsmall.union (bounded_finite m)).subset
      intro y hy
      by_cases hyT : y ∈ maximalTube
      · exact Or.inl ⟨hy.1, hyT⟩
      · have hyr : y ∈ range fun i : ℕ => atLevel i 0 := by
          simpa only [maximalTube, mem_compl_iff, not_not] using hyT
        obtain ⟨i, rfl⟩ := hyr
        exact Or.inr (mem_bounded (le_of_not_gt fun h =>
          hy.2.not_le (atLevel_le.mpr (Or.inr ⟨hj, h⟩))))
    exact ((isMaximalTube_iff U).mp hU).2 _ hnot hfinite
  have hsub : U ⊆ maximalTube := by
    rintro x hx ⟨n, rfl⟩
    exact no_zero n hx
  apply subset_antisymm hsub
  intro x hx
  by_contra hnot
  exact hU.2 x hnot (hU.1.insert ((isMaximalTube_maximalTube.1 x hx).subset
    (inter_subset_inter_left _ hsub)))

private def railAssignment (j : Fin 3) (x : Model) : Model :=
  WithBot.recBotCoe ⊥ (fun y : WithTop RailPoint =>
    WithTop.recTopCoe ⊤ (fun p => atLevel p.level j) y) x

private theorem assignment_on_rail (j : Fin 3) (n : ℕ) (k : Fin 3) :
    railAssignment j (atLevel n k) = atLevel n j := rfl

private theorem assignment_spine (j : Fin 3) : SpineAssignment (railAssignment j) := by
  constructor
  · intro x
    rcases model_cases x with rfl | rfl | ⟨n, k, rfl⟩
    · rfl
    · rfl
    · rw [assignment_on_rail, assignment_on_rail]
  · intro x y
    rcases model_cases x with rfl | rfl | ⟨n, k, rfl⟩
    · exact Or.inl bot_le
    · exact Or.inr le_top
    rcases model_cases y with rfl | rfl | ⟨m, k', rfl⟩
    · exact Or.inr bot_le
    · exact Or.inl le_top
    rw [assignment_on_rail, assignment_on_rail]
    exact (le_total n m).imp (fun h => atLevel_le.mpr (Or.inl ⟨rfl, h⟩))
      (fun h => atLevel_le.mpr (Or.inl ⟨rfl, h⟩))
  · intro x y hxy
    rcases model_cases x with rfl | rfl | ⟨n, k, rfl⟩
    · rcases model_cases y with rfl | rfl | ⟨m, k', rfl⟩
      · exact (lt_irrefl _ hxy).elim
      · exact hxy.ne
      · change (⊥ : Model) ≠ atLevel m j
        simp [atLevel]
    · exact (not_lt_of_ge le_top hxy).elim
    · rcases model_cases y with rfl | rfl | ⟨m, k', rfl⟩
      · exact (not_lt_of_ge bot_le hxy).elim
      · intro he
        have htop : (↑(RailPoint.mk n j) : WithTop RailPoint) = ⊤ := WithBot.coe_inj.mp he
        exact WithTop.coe_ne_top htop
      · intro he
        have he' : atLevel n j = atLevel m j := he
        have hnm : n = m := (atLevel_inj he').1
        rcases atLevel_le.mp hxy.le with ⟨hk, _⟩ | ⟨_, h⟩
        · exact hxy.ne (by rw [hnm, hk])
        · exact h.ne hnm

/-- Each rail, together with the two endpoints, is a spine as claimed in the figure. -/
theorem rail_is_spine (j : Fin 3) :
    Nonempty (SpineData univ ({⊥, ⊤} ∪ range (fun n : ℕ => atLevel n j))) := by
  have heq : range (railAssignment j) = ({⊥, ⊤} ∪ range (fun n : ℕ => atLevel n j)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rcases model_cases y with rfl | rfl | ⟨n, k, rfl⟩
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr ⟨n, rfl⟩
    · rintro ((rfl | rfl) | ⟨n, rfl⟩)
      · exact ⟨⊥, rfl⟩
      · exact ⟨⊤, rfl⟩
      · exact ⟨atLevel n j, rfl⟩
  exact heq ▸ (assignment_spine j).spineData

end AharoniKorman.TubeExample
