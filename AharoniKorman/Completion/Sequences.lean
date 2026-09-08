import AharoniKorman.Completion.Completeness
import AharoniKorman.Completion.BoundaryProfiles
import Mathlib.Data.Set.Countable

/-! Countable cofinal sequences for the completion API.

Countability is imposed on the original chain, not on its possibly uncountable completion.
No completion or germ implementation is unfolded here.
-/

namespace AharoniKorman.Completion

open Set

private theorem exists_strictMono_dominating {β : Type*} [LinearOrder β] [NoMaxOrder β]
    (b : ℕ → β) : ∃ f : ℕ → β, StrictMono f ∧ ∀ n, b n < f n := by
  classical
  choose next hnext using fun x : β => exists_gt x
  let f : ℕ → β := Nat.rec (next (b 0)) (fun n x => next (max x (b (n + 1))))
  have hstep (n : ℕ) : f n < f (n + 1) :=
    (le_max_left _ _).trans_lt (hnext _)
  refine ⟨f, strictMono_nat_of_lt_succ hstep, ?_⟩
  intro n
  cases n with
  | zero => exact hnext _
  | succ n => exact (le_max_right _ _).trans_lt (hnext _)

/-- A countable linear order without a maximum has a strictly increasing cofinal sequence. -/
theorem exists_strictMono_cofinal_sequence {β : Type*} [LinearOrder β]
    [Countable β] [Nonempty β] [NoMaxOrder β] :
    ∃ f : ℕ → β, StrictMono f ∧ ∀ x, ∃ n, x < f n := by
  obtain ⟨e, he⟩ := exists_surjective_nat β
  obtain ⟨f, hf, hdom⟩ := exists_strictMono_dominating e
  refine ⟨f, hf, ?_⟩
  intro x
  obtain ⟨n, rfl⟩ := he x
  exact ⟨n, hdom n⟩

namespace IncreasingChain

variable {α : Type*} [PartialOrder α]

theorem exists_cofinal_sequence [Countable α] (C : IncreasingChain α) :
    ∃ f : ℕ → C.1, StrictMono f ∧ ∀ c : C.1, ∃ n, c < f n := by
  let : Nonempty C.1 := C.1.nonempty.to_subtype
  let : NoMaxOrder C.1 := ⟨C.2.exists_gt⟩
  exact exists_strictMono_cofinal_sequence

/-- Checking cofinality on cofinal sequences is equivalent to the representative formula. -/
theorem cofinalAbove_iff_sequences (C D : IncreasingChain α)
    (c : ℕ → C.1) (d : ℕ → D.1)
    (hc : ∀ x : C.1, ∃ n, x < c n) (hd : ∀ y : D.1, ∃ n, y < d n) :
    (IncreasingGerm.ofChain C).CofinalAbove (IncreasingGerm.ofChain D) ↔
      ∀ n, ∃ m, (d n).1 < (c m).1 := by
  rw [IncreasingGerm.cofinalAbove_ofChain_iff]
  constructor
  · intro h n
    obtain ⟨x, hdx⟩ := h (d n)
    obtain ⟨m, hxm⟩ := hc x
    exact ⟨m, hdx.trans hxm⟩
  · intro h y
    obtain ⟨n, hyn⟩ := hd y
    obtain ⟨m, hnm⟩ := h n
    exact ⟨c m, (show y.1 < (d n).1 from hyn).trans hnm⟩

theorem bicomparable_iff_sequences (C D : IncreasingChain α)
    (c : ℕ → C.1) (d : ℕ → D.1)
    (hc : ∀ x : C.1, ∃ n, x < c n) (hd : ∀ y : D.1, ∃ n, y < d n) :
    (IncreasingGerm.ofChain C).Bicomparable (IncreasingGerm.ofChain D) ↔
      (∀ n, ∃ m, (d n).1 < (c m).1) ∧ (∀ n, ∃ m, (c n).1 < (d m).1) := by
  rw [IncreasingGerm.bicomparable_iff, cofinalAbove_iff_sequences C D c d hc hd,
    cofinalAbove_iff_sequences D C d c hd hc]

end IncreasingChain

namespace DecreasingChain

variable {α : Type*} [PartialOrder α]

theorem exists_coinitial_sequence [Countable α] (C : DecreasingChain α) :
    ∃ f : ℕ → C.1, StrictAnti f ∧ ∀ c : C.1, ∃ n, f n < c := by
  let : Countable αᵒᵈ := ‹Countable α›
  exact C.toDual.exists_cofinal_sequence

theorem bicomparable_iff_sequences (C D : DecreasingChain α)
    (c : ℕ → C.1) (d : ℕ → D.1)
    (hc : ∀ x : C.1, ∃ n, c n < x) (hd : ∀ y : D.1, ∃ n, d n < y) :
    (DecreasingGerm.ofChain C).Bicomparable (DecreasingGerm.ofChain D) ↔
      (∀ n, ∃ m, (c m).1 < (d n).1) ∧ (∀ n, ∃ m, (d m).1 < (c n).1) :=
  IncreasingChain.bicomparable_iff_sequences C.toDual D.toDual c d hc hd

end DecreasingChain

namespace H

variable {α : Type*} [LinearOrder α]

/-- A set without a greatest member has a countable cofinal sequence when the original
chain is countable, even when the whole completion is uncountable. -/
theorem exists_strictMono_cofinal_in [Countable α] {D : Set (H α)} (hne : D.Nonempty)
    (hD : ∀ X ∈ D, ∃ Y ∈ D, X < Y) :
    ∃ f : ℕ → H α, (∀ n, f n ∈ D) ∧ StrictMono f ∧ ∀ X ∈ D, ∃ n, X < f n := by
  classical
  let T := lowerPrincipals D
  let : Nonempty T := (lowerPrincipals_nonempty hne hD).to_subtype
  obtain ⟨e, he⟩ := exists_surjective_nat T
  choose b hb using fun n => (e n).2
  let bD (n : ℕ) : D := ⟨b n, (hb n).1⟩
  let : NoMaxOrder D := ⟨fun x => by
    obtain ⟨y, hy, hxy⟩ := hD x.1 x.2
    exact ⟨⟨y, hy⟩, hxy⟩⟩
  obtain ⟨f, hf, hbf⟩ := exists_strictMono_dominating bD
  refine ⟨fun n => (f n).1, fun n => (f n).2, fun i j hij => hf hij, ?_⟩
  intro X hX
  obtain ⟨p, Y, hY, hXp, hpY⟩ := principal_approximation_of_no_greatest hD hX
  obtain ⟨n, hn⟩ := he ⟨p, Y, hY, hpY⟩
  have heq : (e n).1 = p := congrArg Subtype.val hn
  have hpb : principal p < b n := by simpa only [heq] using (hb n).2
  exact ⟨n, (hXp.trans hpb).trans (hbf n)⟩

/-- Cofinal sequence form of a non-attained supremum. -/
theorem exists_strictMono_isLUB [Countable α] {D : Set (H α)} (hne : D.Nonempty)
    (hD : ∀ X ∈ D, ∃ Y ∈ D, X < Y) :
    ∃ f : ℕ → H α, (∀ n, f n ∈ D) ∧ StrictMono f ∧
      (∀ X ∈ D, ∃ n, X < f n) ∧ IsLUB (range f) (sSup D) := by
  obtain ⟨f, hfD, hf, hcof⟩ := exists_strictMono_cofinal_in hne hD
  refine ⟨f, hfD, hf, hcof, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact le_sSup (hfD n)
  · intro z hz
    apply sSup_le
    intro X hX
    obtain ⟨n, hn⟩ := hcof X hX
    exact hn.le.trans (hz ⟨n, rfl⟩)

end H

end AharoniKorman.Completion
