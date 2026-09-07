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
  intro A hA
  apply Set.Finite.of_finite_image (f := Subtype.val) (h (Subtype.val '' A) ?_)
  · exact Subtype.val_injective.injOn
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy hle
    apply hA hx hy
    · exact fun h => hxy (congrArg Subtype.val h)
    · exact hle

/-- FAC is invariant under order duality. -/
theorem isFAC_orderDual_iff : IsFAC αᵒᵈ ↔ IsFAC α := by
  constructor
  · intro h A hA
    exact h A hA.swap
  · intro h A hA
    exact h A hA.swap

/-- FAC transported to the order dual. -/
theorem IsFAC.orderDual (h : IsFAC α) : IsFAC αᵒᵈ :=
  isFAC_orderDual_iff.mpr h

/-- FAC transported back from the order dual. -/
theorem IsFAC.of_orderDual (h : IsFAC αᵒᵈ) : IsFAC α :=
  isFAC_orderDual_iff.mp h

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

/-- The range of a strictly monotone sequence is infinite. -/
theorem infinite_range_of_strictMono {f : ℕ → α} (hf : StrictMono f) :
    (Set.range f).Infinite :=
  Set.infinite_range_of_injective hf.injective

/-- The range of a strictly antitone sequence is infinite. -/
theorem infinite_range_of_strictAnti {f : ℕ → α} (hf : StrictAnti f) :
    (Set.range f).Infinite :=
  Set.infinite_range_of_injective hf.injective

/-- Subtype form of the monotone-subsequence lemma. -/
theorem IsFAC.exists_strictMono_or_strictAnti_sequence_in (hfac : IsFAC α)
    {S : Set α} (hS : S.Infinite) :
    ∃ f : ℕ → S, StrictMono f ∨ StrictAnti f := by
  let e : ℕ ↪ S := hS.natEmbedding S
  obtain ⟨g, hg⟩ := (hfac.subtype S).exists_strictMono_or_strictAnti_subsequence e.injective
  exact ⟨e ∘ g, hg⟩

/-- Paper fact `fact:infinite-chain`, obtained from the two-colour infinite monotone-subsequence
theorem `exists_increasing_or_nonincreasing_subseq`. -/
theorem IsFAC.exists_infinite_chain (hfac : IsFAC α) [Infinite α] :
    ∃ C : Set α, IsChain (· ≤ ·) C ∧ C.Infinite := by
  let e := Infinite.natEmbedding α
  obtain ⟨g, hmono | hanti⟩ :=
    hfac.exists_strictMono_or_strictAnti_subsequence e.injective
  · exact ⟨Set.range (e ∘ g), hmono.monotone.isChain_range,
      infinite_range_of_strictMono hmono⟩
  · exact ⟨Set.range (e ∘ g), hanti.antitone.isChain_range,
      infinite_range_of_strictAnti hanti⟩

end AharoniKorman
