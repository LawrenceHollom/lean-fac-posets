import AharoniKorman.Preliminaries.Chains
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Antichain
import Mathlib.Order.OrderIsoNat

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

/-- Every injective sequence in an FAC poset has a strictly monotone subsequence. -/
theorem IsFAC.exists_strictMono_or_strictAnti_subsequence (hfac : IsFAC α)
    {f : ℕ → α} (hf : Function.Injective f) :
    ∃ g : ℕ ↪o ℕ, StrictMono (f ∘ g) ∨ StrictAnti (f ∘ g) := by
  classical
  obtain ⟨g, hIncreasing | hNotIncreasing⟩ :=
    exists_increasing_or_nonincreasing_subseq (· < ·) f
  · exact ⟨g, Or.inl hIncreasing⟩
  obtain ⟨g', hDecreasing | hNotDecreasing⟩ :=
    exists_increasing_or_nonincreasing_subseq (· > ·) (f ∘ g)
  · refine ⟨g'.trans g, Or.inr ?_⟩
    intro m n hmn
    exact hDecreasing m n hmn
  · exfalso
    let A : Set α := Set.range (f ∘ g ∘ g')
    have hA_infinite : A.Infinite := by
      apply Set.infinite_range_of_injective
      exact hf.comp (g.injective.comp g'.injective)
    have hA_antichain : IsAntichain (· ≤ ·) A := by
      rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ hne hle
      have hmn : m ≠ n := by
        intro h
        apply hne
        simp [h]
      rcases hmn.lt_or_gt with hmn | hnm
      · have hlt : f (g (g' m)) < f (g (g' n)) := lt_of_le_of_ne hle hne
        exact hNotIncreasing _ _ (g'.strictMono hmn) hlt
      · have hlt : f (g (g' m)) < f (g (g' n)) := lt_of_le_of_ne hle hne
        exact hNotDecreasing _ _ hnm hlt
    exact hA_infinite (hfac A hA_antichain)

end AharoniKorman
