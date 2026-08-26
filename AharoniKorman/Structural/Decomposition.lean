import AharoniKorman.Structural.EtaReplacement
import Mathlib.Data.EReal.Basic

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- The five conclusions of Theorem 1.4, packaged for reuse by the reduction theorem. -/
structure ScatteredDecomposition (α : Type*) [PartialOrder α] where
  piece : EReal → Set α
  rational_nonempty : ∀ q : ℚ, (piece ((q : ℝ) : EReal)).Nonempty
  ordered : ∀ ⦃r s : EReal⦄, r < s → SetStrictLT (piece r) (piece s)
  outside_incomparable : ∀ x, x ∉ ⋃ r, piece r →
    ∃ I : Set EReal, I.OrdConnected ∧ I.Infinite ∧
      ∀ r ∈ I, ∀ y ∈ piece r, Incomparable x y
  piece_ordConnected : ∀ r, (piece r).OrdConnected
  piece_scattered : ∀ r, IsScattered (piece r)

/-- Theorem 1.4 / paper `thm:structural` (Stage 2 target). -/
theorem structural_decomposition [Countable α] (hfac : IsFAC α) :
    IsScattered α ∨ Nonempty (ScatteredDecomposition α) := by
  sorry

end AharoniKorman
