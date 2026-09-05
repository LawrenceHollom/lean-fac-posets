import Mathlib.Data.Countable.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range

/-!
Classical countable choice lemmas used when extending a spine partition.
-/

namespace AharoniKorman

open Function Set

universe u v

/-- A countable family of infinite sets has a system of distinct representatives.

This elementary special case of Hall's theorem is proved greedily after enumerating the index
type.  It is useful here because the representatives must be distinct even when two outside
points of a tube are comparable. -/
theorem exists_injective_selector {ι : Type u} {β : Type v} [Countable ι]
    (S : ι → Set β) (hS : ∀ i, (S i).Infinite) :
    ∃ f : ι → β, Injective f ∧ ∀ i, f i ∈ S i := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      exact ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  | inr hι =>
      let _ := hι
      obtain ⟨e, he⟩ := exists_surjective_nat ι
      let step : (n : ℕ) → ((m : ℕ) → m < n → β) → β := fun n previous =>
        Classical.choose <| (hS (e n)).exists_notMem_finite <|
          Set.finite_range fun m : Fin n => previous m.1 m.2
      let pick : ℕ → β := fun n => Nat.strongRecOn n step
      have pick_spec (n : ℕ) :
          pick n ∈ S (e n) ∧ pick n ∉ Set.range (fun m : Fin n => pick m.1) := by
        change (@Nat.strongRecOn (fun _ => β) n step) ∈ S (e n) ∧
          (@Nat.strongRecOn (fun _ => β) n step) ∉ Set.range
            (fun m : Fin n => @Nat.strongRecOn (fun _ => β) m.1 step)
        rw [Nat.strongRecOn_eq]
        exact Classical.choose_spec <| (hS (e n)).exists_notMem_finite <|
          Set.finite_range fun m : Fin n => @Nat.strongRecOn (fun _ => β) m.1 step
      have pick_injective : Injective pick := by
        intro m n hmn
        rcases lt_trichotomy m n with hlt | rfl | hgt
        · exact False.elim <| (pick_spec n).2 ⟨⟨m, hlt⟩, hmn⟩
        · rfl
        · exact False.elim <| (pick_spec m).2 ⟨⟨n, hgt⟩, hmn.symm⟩
      let first : ι → ℕ := fun i => Nat.find (he i)
      have first_spec (i : ι) : e (first i) = i := Nat.find_spec (he i)
      have first_injective : Injective first := by
        intro i j hij
        rw [← first_spec i, ← first_spec j, hij]
      refine ⟨pick ∘ first, pick_injective.comp first_injective, fun i => ?_⟩
      simpa [first_spec i] using (pick_spec (first i)).1

end AharoniKorman
