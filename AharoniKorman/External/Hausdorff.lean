import AharoniKorman.Preliminaries.Scattered
import Mathlib.Order.WithBot

/-! Isolated classical scattered-linear-order input. -/

namespace AharoniKorman.External

open Set

/-- The exact corollary of Hausdorff's classification retained as an external input.

Every scattered linear order which contains an increasing copy of `ω` has a nonempty convex
suborder which is increasing, still contains `ω`, and contains no copy of `ω + 1` (represented by
`WithTop ℕ`). In a linear ambient order, saturation is equivalent to convexity.
-/
axiom exists_saturated_omega_no_omegaSucc {α : Type*} [LinearOrder α]
    (hscattered : IsScattered α) (homega : Nonempty (ℕ ↪o α)) :
    ∃ C : Set α,
      IsSaturatedChain C ∧
      C.Nonempty ∧
      (∀ x ∈ C, ∃ y ∈ C, x < y) ∧
      Nonempty (ℕ ↪o C) ∧
      ¬Nonempty (WithTop ℕ ↪o C)

/-- The order-dual form of `exists_saturated_omega_no_omegaSucc`. -/
theorem exists_saturated_omegaStar_no_omegaSuccStar {α : Type*} [LinearOrder α]
    (hscattered : IsScattered α)
    (homega : Nonempty (ℕ ↪o (αᵒᵈ))) :
    ∃ C : Set α,
      @IsSaturatedChain αᵒᵈ inferInstance C ∧
      C.Nonempty ∧
      (∀ x ∈ C, ∃ y ∈ C, y < x) ∧
      Nonempty (ℕ ↪o {x : αᵒᵈ // x ∈ C}) ∧
      ¬Nonempty (WithTop ℕ ↪o {x : αᵒᵈ // x ∈ C}) := by
  exact exists_saturated_omega_no_omegaSucc hscattered.orderDual homega

end AharoniKorman.External
