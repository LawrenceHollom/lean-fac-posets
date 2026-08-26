import AharoniKorman.Preliminaries.Chains
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Antichain

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- The finite antichain condition: every antichain is finite. -/
def IsFAC (α : Type*) [PartialOrder α] : Prop :=
  ∀ A : Set α, IsAntichain (· ≤ ·) A → A.Finite

theorem IsFAC.antichain_finite (h : IsFAC α) {A : Set α}
    (hA : IsAntichain (· ≤ ·) A) : A.Finite := h A hA

/-- FAC is inherited by induced subposets. -/
theorem IsFAC.subtype (h : IsFAC α) (S : Set α) : IsFAC S := by
  sorry

/-- FAC is invariant under order duality. -/
theorem isFAC_orderDual_iff : IsFAC αᵒᵈ ↔ IsFAC α := by
  sorry

/-- Paper fact `fact:infinite-chain`, isolated as the Ramsey-theoretic input. -/
theorem IsFAC.exists_infinite_chain (hfac : IsFAC α) [Infinite α] :
    ∃ C : Set α, IsChain (· ≤ ·) C ∧ C.Infinite := by
  sorry

end AharoniKorman
