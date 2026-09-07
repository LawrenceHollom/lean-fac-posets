import AharoniKorman.Preliminaries.Chains
import Mathlib.Data.Countable.Basic
import Mathlib.Order.Zorn

/-! Reusable countable-chain and maximality tools for replacement orders. -/

namespace AharoniKorman

open Set

/-- Running maximum of a sequence whose values lie in a chain of a partial order. -/
def runningMax {β : Type*} [PartialOrder β] [DecidableLE β] (f : ℕ → β) : ℕ → β :=
  fun n => Nat.rec (f 0)
    (fun k previous => if previous ≤ f (k + 1) then f (k + 1) else previous) n

@[simp] theorem runningMax_zero {β : Type*} [PartialOrder β] [DecidableLE β]
    (f : ℕ → β) : runningMax f 0 = f 0 := by
  simp [runningMax]

@[simp] theorem runningMax_succ {β : Type*} [PartialOrder β] [DecidableLE β]
    (f : ℕ → β) (n : ℕ) :
    runningMax f (n + 1) =
      if runningMax f n ≤ f (n + 1) then f (n + 1) else runningMax f n := by
  rfl

theorem runningMax_mem {β : Type*} [PartialOrder β] [DecidableLE β] {s : Set β}
    (hs : IsChain (· ≤ ·) s) {f : ℕ → β} (hf : ∀ n, f n ∈ s) :
    ∀ n, runningMax f n ∈ s := by
  intro n
  induction n with
  | zero => simpa using hf 0
  | succ n ih =>
      rw [runningMax_succ]
      split
      · exact hf (n + 1)
      · exact ih

theorem runningMax_le_succ {β : Type*} [PartialOrder β] [DecidableLE β] {s : Set β}
    (hs : IsChain (· ≤ ·) s) {f : ℕ → β} (hf : ∀ n, f n ∈ s) (n : ℕ) :
    runningMax f n ≤ runningMax f (n + 1) := by
  rw [runningMax_succ]
  split_ifs with h
  · exact h
  · exact le_rfl

theorem runningMax_self_le {β : Type*} [PartialOrder β] [DecidableLE β] {s : Set β}
    (hs : IsChain (· ≤ ·) s) {f : ℕ → β} (hf : ∀ n, f n ∈ s) :
    ∀ n, f n ≤ runningMax f n := by
  intro n
  cases n with
  | zero => exact le_rfl
  | succ n =>
      rw [runningMax_succ]
      split_ifs with h
      · exact le_rfl
      · rcases hs.total (runningMax_mem hs hf n) (hf (n + 1)) with h' | h'
        · exact False.elim (h h')
        · exact h'

/-- Every member of a finite prefix lies below its running maximum. -/
theorem runningMax_prefix_le {β : Type*} [PartialOrder β] [DecidableLE β] {s : Set β}
    (hs : IsChain (· ≤ ·) s) {f : ℕ → β} (hf : ∀ n, f n ∈ s)
    {k n : ℕ} (hkn : k ≤ n) : f k ≤ runningMax f n := by
  have hmono : Monotone (runningMax f) :=
    monotone_nat_of_le_succ (runningMax_le_succ hs hf)
  exact (runningMax_self_le hs hf k).trans (hmono hkn)

/-- A nonempty countable type admits a surjective enumeration by the naturals. -/
theorem exists_surjective_enumeration (ι : Type*) [Countable ι] [Nonempty ι] :
    ∃ e : ℕ → ι, Function.Surjective e :=
  exists_surjective_nat ι

/-- Set-specialized enumeration which takes nonemptiness as an ordinary hypothesis. -/
theorem exists_surjective_set_enumeration {β : Type*} {s : Set β}
    [Countable s] (hs : s.Nonempty) : ∃ e : ℕ → s, Function.Surjective e := by
  letI : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  exact AharoniKorman.exists_surjective_enumeration s

/-- A countable cofinal family in a chain can be monotonized without losing cofinality. -/
theorem exists_monotone_cofinal_sequence {β ι : Type*} [PartialOrder β]
    [Countable ι] [Nonempty ι] {s : Set β} (hs : IsChain (· ≤ ·) s)
    (f : ι → β) (hf : ∀ i, f i ∈ s)
    (hcofinal : ∀ x ∈ s, ∃ i, x ≤ f i) :
    ∃ g : ℕ → β,
      (∀ n, g n ∈ s) ∧ Monotone g ∧ ∀ x ∈ s, ∃ n, x ≤ g n := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_enumeration ι
  let g : ℕ → β := runningMax (f ∘ e)
  have hfe (n : ℕ) : (f ∘ e) n ∈ s := hf (e n)
  refine ⟨g, runningMax_mem hs hfe,
    monotone_nat_of_le_succ (runningMax_le_succ hs hfe), ?_⟩
  intro x hx
  obtain ⟨i, hxi⟩ := hcofinal x hx
  obtain ⟨n, rfl⟩ := he i
  exact ⟨n, hxi.trans (runningMax_self_le hs hfe n)⟩

/-- Zorn wrapper for replacement orders: nonempty-chain upper bounds give a maximal object above
any prescribed starting object. -/
theorem exists_maximal_above_of_nonempty_chain_upperBounds {β : Type*} [PartialOrder β]
    (start : β)
    (hupper : ∀ c : Set β, IsChain (· ≤ ·) c → c.Nonempty →
      ∃ upper : β, ∀ x ∈ c, x ≤ upper) :
    ∃ maximal : β, start ≤ maximal ∧ IsMax maximal := by
  apply zorn_le_nonempty_Ici₀ start
  intro c hcIcc hc y hy
  obtain ⟨upper, hupperC⟩ := hupper c hc ⟨y, hy⟩
  exact ⟨upper, hupperC⟩
  exact le_rfl

end AharoniKorman
