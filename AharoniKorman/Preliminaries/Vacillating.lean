import AharoniKorman.Preliminaries.FAC
import Mathlib.Order.WellFounded

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- A chain expressed as an omega-sum of infinite co-wellfounded blocks. -/
def IsOmegaSumOfInfiniteCowellfounded (C : Set α) : Prop :=
  ∃ B : ℕ → Set α,
    C = ⋃ n, B n ∧
    (∀ n, (B n).Infinite) ∧
    (∀ n, WellFounded (fun x y : B n => x > y)) ∧
    (∀ ⦃i j : ℕ⦄, i < j → SetStrictLT (B i) (B j))

/-- The paper's forbidden saturated-chain condition, in both order directions. -/
def IsVacillating (α : Type*) [PartialOrder α] : Prop :=
  ∀ C : Set α, IsSaturatedChain C →
    ¬ IsOmegaSumOfInfiniteCowellfounded C ∧
    ¬ @IsOmegaSumOfInfiniteCowellfounded αᵒᵈ inferInstance C

/-- Vacillation is inherited by convex induced subposets. -/
theorem IsVacillating.ordConnected_subtype (h : IsVacillating α) {S : Set α}
    (hS : S.OrdConnected) : IsVacillating S := by
  sorry

end AharoniKorman
