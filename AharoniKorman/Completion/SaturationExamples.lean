import AharoniKorman.Completion.SaturatedChain
import Mathlib.Order.Basic
import Mathlib.Order.Fin.Basic
import Lean.Elab.Tactic.Omega

/-! A regression example for the manuscript's saturation definition. -/

namespace AharoniKorman.Completion.SaturationExamples

/-- Three points on one side of the four-point diamond. -/
def diamondChain : Set (Fin 2 × Fin 2) := {x | x.2 ≤ x.1}

theorem diamond_saturated : IsSaturatedChain diamondChain := by
  constructor
  · intro x hx y hy _
    change (x.1 ≤ y.1 ∧ x.2 ≤ y.2) ∨ (y.1 ≤ x.1 ∧ y.2 ≤ x.2)
    change x.2 ≤ x.1 at hx
    change y.2 ≤ y.1 at hy
    omega
  · intro a b x _ _ _ _ hcomp
    change x.2 ≤ x.1
    rcases hcomp (1, 0) (show (0 : Fin 2) ≤ 1 from by decide) with h | h
    · exact h.2.trans (Fin.zero_le _)
    · exact (Fin.le_last _).trans h.1

theorem diamond_not_ordConnected : ¬diamondChain.OrdConnected := by
  intro h
  have h00 : (0, 0) ∈ diamondChain := show (0 : Fin 2) ≤ 0 from le_rfl
  have h11 : (1, 1) ∈ diamondChain := show (1 : Fin 2) ≤ 1 from le_rfl
  have h01 : (0, 1) ∈ diamondChain := h.out h00 h11 (by decide)
  exact (by decide : ¬(1 : Fin 2) ≤ 0) h01

end AharoniKorman.Completion.SaturationExamples
