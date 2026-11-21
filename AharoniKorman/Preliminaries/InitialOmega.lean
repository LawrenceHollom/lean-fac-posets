import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.WellFounded

namespace AharoniKorman

/-- The first `ω` elements of an infinite well-order form an initial segment. -/
theorem exists_initial_natEmbedding {β : Type*} [LinearOrder β] [Infinite β]
    (hw : WellFounded ((· < ·) : β → β → Prop)) :
    ∃ e : ℕ ↪o β, ∀ (x : β) (n : ℕ), x ≤ e n → ∃ m, e m = x := by
  classical
  let next (s : Finset β) := hw.min {x | x ∉ s} (s.exists_notMem)
  have outside (s : Finset β) : next s ∉ s :=
    show next s ∈ {x | x ∉ s} from hw.min_mem {x | x ∉ s} (s.exists_notMem)
  have min_le (s : Finset β) {x : β} (hx : x ∉ s) : next s ≤ x :=
    hw.min_le (s := {x | x ∉ s}) hx
  let used : ℕ → Finset β := Nat.rec ∅ (fun _ s => insert (next s) s)
  let a (n : ℕ) := next (used n)
  have succ_used (n : ℕ) : used (n + 1) = insert (a n) (used n) := rfl
  have mono_used : Monotone used := monotone_nat_of_le_succ fun n => by
    rw [succ_used]
    exact Finset.subset_insert _ _
  have mono : StrictMono a := by
    intro m n hmn
    have ha : a n ∉ used n := outside _
    have hab : a m ∈ used n := mono_used hmn (by rw [succ_used]; exact Finset.mem_insert_self _ _)
    exact lt_of_le_of_ne (min_le _ fun h => ha (mono_used hmn.le h)) fun h => ha (h ▸ hab)
  have used_from_a : ∀ n i, i ∈ used n → ∃ m, a m = i := by
    intro n
    induction n with
    | zero => simp [used]
    | succ n ih =>
      intro i hi
      rw [succ_used] at hi
      rcases Finset.mem_insert.mp hi with heq | hi
      · exact ⟨n, heq.symm⟩
      · exact ih i hi
  refine ⟨OrderEmbedding.ofStrictMono a mono, ?_⟩
  intro i n hi
  rcases Classical.em ((i : β) ∈ used n) with h | h
  · exact used_from_a n i h
  · exact ⟨n, (min_le _ h).antisymm hi⟩

end AharoniKorman
