import AharoniKorman.External.HausdorffInduction
import AharoniKorman.Preliminaries.InitialOmega
import Mathlib.Order.WithBot

namespace AharoniKorman

/-- A strictly increasing sequence and a strict upper bound give a copy of `ω + 1`. -/
theorem omegaSucc_embedding_of_bounded_sequence {β : Type*} [LinearOrder β]
    {f : ℕ → β} (hf : StrictMono f) {b : β} (hb : ∀ n, f n < b) :
    Nonempty (WithTop ℕ ↪o β) := by
  let g : WithTop ℕ → β := fun x => x.recTopCoe b f
  refine ⟨OrderEmbedding.ofStrictMono g ?_⟩
  intro x y hxy
  induction x using WithTop.recTopCoe with
  | top => exact False.elim (not_top_lt hxy)
  | coe n =>
    induction y using WithTop.recTopCoe with
    | top => exact hb n
    | coe m => exact hf (WithTop.coe_lt_coe.1 hxy)

end AharoniKorman

namespace AharoniKorman.External

open Set

universe u

variable {α : Type u} [LinearOrder α]

private theorem stabilizes_of_finite {ι : Type*} [LinearOrder ι] [Finite ι]
    (f : ℕ → ι) (hf : Monotone f) : ∃ n, ∀ m ≥ n, f m = f n := by
  obtain ⟨_, ⟨n, rfl⟩, hmax⟩ := (Set.toFinite (range f)).exists_maximal (range_nonempty f)
  exact ⟨n, fun m hm => (hmax (mem_range_self m) (hf hm)).antisymm (hf hm)⟩

private theorem stabilizes_of_reverse_wellOrder {ι : Type*} [LinearOrder ι]
    (hw : WellFounded ((· > ·) : ι → ι → Prop))
    (f : ℕ → ι) (hf : Monotone f) : ∃ n, ∀ m ≥ n, f m = f n := by
  obtain ⟨_, ⟨n, rfl⟩, hmax⟩ := hw.has_min (range f) (range_nonempty f)
  exact ⟨n, fun m hm => (le_of_not_gt (hmax (f m) (mem_range_self m))).antisymm (hf hm)⟩

private theorem no_omega_in_sum {ι : Type*} [LinearOrder ι] (B : ι → Set α)
    (hB : ∀ i, ¬Nonempty (ℕ ↪o B i))
    (hord : ∀ ⦃i j⦄, i < j → SetStrictLT (B i) (B j))
    (stabilizes : ∀ (f : ℕ → ι), Monotone f → ∃ n, ∀ m ≥ n, f m = f n) :
    ¬Nonempty (ℕ ↪o (⋃ i, B i)) := by
  classical
  rintro ⟨e⟩
  have in_block (n : ℕ) : ∃ i, (e n).1 ∈ B i := mem_iUnion.mp (e n).2
  choose index hindex using in_block
  have himono : Monotone index := by
    intro m n hmn
    by_contra hnot
    have ht := hord (lt_of_not_ge hnot) (hindex n) (hindex m)
    exact ht.not_ge (e.monotone hmn)
  obtain ⟨n, hn⟩ := stabilizes index himono
  apply hB (index n)
  refine ⟨OrderEmbedding.ofStrictMono (fun k => ⟨(e (n + k)).1, ?_⟩) ?_⟩
  · exact hn (n + k) (Nat.le_add_right _ _) ▸ hindex (n + k)
  · intro a b hab
    exact e.strictMono (Nat.add_lt_add_left hab n)

private theorem atom_of_omega_sum (B : ℕ → Set α) (hne : ∀ i, (B i).Nonempty)
    (hB : ∀ i, ¬Nonempty (ℕ ↪o B i))
    (hord : ∀ ⦃i j⦄, i < j → SetStrictLT (B i) (B j)) :
    Nonempty (ℕ ↪o (⋃ i, B i)) ∧ ¬Nonempty (WithTop ℕ ↪o (⋃ i, B i)) := by
  classical
  constructor
  · choose x hx using hne
    exact ⟨OrderEmbedding.ofStrictMono (fun n => ⟨x n, mem_iUnion.mpr ⟨n, hx n⟩⟩)
      (fun _ _ h => hord h (hx _) (hx _))⟩
  · rintro ⟨e⟩
    obtain ⟨m, hm⟩ := mem_iUnion.mp (e ⊤).2
    have in_prefix (n : ℕ) : (e (n : WithTop ℕ)).1 ∈ ⋃ i : Fin (m + 1), B i := by
      obtain ⟨i, hi⟩ := mem_iUnion.mp (e (n : WithTop ℕ)).2
      have hlt : (e (n : WithTop ℕ)).1 < (e ⊤).1 := e.strictMono (WithTop.coe_lt_top n)
      have hle : i ≤ m := le_of_not_gt fun h => (hord h hm hi).not_gt hlt
      exact mem_iUnion.mpr ⟨⟨i, Nat.lt_succ_of_le hle⟩, hi⟩
    refine no_omega_in_sum (fun i : Fin (m + 1) => B i) (fun i => hB i)
      (fun {_ _} h => hord h) stabilizes_of_finite ⟨?_⟩
    exact OrderEmbedding.ofStrictMono (fun n => ⟨(e (n : WithTop ℕ)).1, in_prefix n⟩)
      (fun _ _ h => e.strictMono (WithTop.coe_lt_coe.mpr h))

private def HasAtomicInterval (S : Set α) : Prop :=
  ∃ T ⊆ S, T.OrdConnected ∧ Nonempty (ℕ ↪o T) ∧ ¬Nonempty (WithTop ℕ ↪o T)

private theorem atom_of_well_ordered_sum {ι : Type u} [LinearOrder ι]
    (hw : WellFounded ((· < ·) : ι → ι → Prop)) (B : ι → Set α)
    (hne : ∀ i, (B i).Nonempty) (hUnion : (⋃ i, B i).OrdConnected)
    (hord : ∀ ⦃i j⦄, i < j → SetStrictLT (B i) (B j))
    (hB : ∀ i, ¬Nonempty (ℕ ↪o B i)) (hOmega : Nonempty (ℕ ↪o (⋃ i, B i))) :
    HasAtomicInterval (⋃ i, B i) := by
  classical
  by_cases hfin : Finite ι
  · exact (no_omega_in_sum B hB hord stabilizes_of_finite hOmega).elim
  let : Infinite ι := not_finite_iff_infinite.mp hfin
  obtain ⟨a, ha_initial⟩ := exists_initial_natEmbedding hw
  let S := ⋃ n, B (a n)
  have hsub : S ⊆ ⋃ i, B i := iUnion_subset fun n => subset_iUnion B (a n)
  have hconv : S.OrdConnected := by
    constructor
    intro x hx y hy z hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hUnion.out (hsub hx) (hsub hy) hz)
    have hle : i ≤ a n := le_of_not_gt fun h => (hord h hn hi).not_ge hz.2
    obtain ⟨m, rfl⟩ := ha_initial i n hle
    exact mem_iUnion.mpr ⟨m, hi⟩
  exact ⟨S, hsub, hconv, atom_of_omega_sum (B ∘ a) (fun n => hne (a n)) (fun n => hB (a n))
    (fun {_ _} h => hord (a.strictMono h))⟩

private theorem atom_of_well_ordered_set {S : Set α} (hconv : S.OrdConnected)
    (hw : WellFounded ((· < ·) : S → S → Prop)) (hOmega : Nonempty (ℕ ↪o S)) :
    HasAtomicInterval S := by
  let B (i : S) : Set α := {i.1}
  have hUnion : (⋃ i, B i) = S := by
    ext x
    simp only [B, mem_iUnion, mem_singleton_iff]
    exact ⟨fun ⟨i, hi⟩ => hi.symm ▸ i.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hne (i : S) : (B i).Nonempty := singleton_nonempty i.1
  have hord {i j : S} (hij : i < j) : SetStrictLT (B i) (B j) := by
    rintro x rfl y rfl
    exact hij
  have hb (i : S) : ¬Nonempty (ℕ ↪o B i) := by
    let : Finite (B i) := (Set.finite_singleton i.1).to_subtype
    rintro ⟨e⟩
    exact (not_finite_iff_infinite.mpr (inferInstance : Infinite ℕ)) (Finite.of_injective e e.injective)
  exact hUnion ▸ atom_of_well_ordered_sum hw B hne (hUnion.symm ▸ hconv) (fun {_ _} h => hord h) hb
    (hUnion.symm ▸ hOmega)

/-- The paper's induction for `lem:exists-atomic` on a scattered linear order. -/
theorem exists_atomic_convex_interval (hsc : IsScattered α) (hOmega : Nonempty (ℕ ↪o α)) :
    ∃ T : Set α, T.OrdConnected ∧ Nonempty (ℕ ↪o T) ∧ ¬Nonempty (WithTop ℕ ↪o T) := by
  classical
  have step := scattered_well_sum_induction hsc
    (fun S => Nonempty (ℕ ↪o S) → HasAtomicInterval S) ?_ ?_
  · obtain ⟨e⟩ := hOmega
    let emb : α ↪o (univ : Set α) :=
      OrderEmbedding.ofMapLEIff (fun a => ⟨a, mem_univ a⟩) (fun _ _ => Iff.rfl)
    obtain ⟨T, _, hconv, ht, hn⟩ := step ⟨e.trans emb⟩
    exact ⟨T, hconv, ht, hn⟩
  · intro S hconv hwell hS
    rcases hwell with h | h
    · exact atom_of_well_ordered_set hconv h hS
    · obtain ⟨e⟩ := hS
      obtain ⟨n, hn⟩ := stabilizes_of_reverse_wellOrder h e e.monotone
      exact (e.strictMono (Nat.lt_succ_self n)).ne (hn (n + 1) (Nat.le_succ n)).symm |>.elim
  · intro ι _ hwell B hne _ hUnion hord IH hS
    by_cases hSome : ∃ i, Nonempty (ℕ ↪o B i)
    · obtain ⟨i, hi⟩ := hSome
      obtain ⟨T, hT, hconv, ht, hn⟩ := IH i hi
      exact ⟨T, hT.trans (subset_iUnion B i), hconv, ht, hn⟩
    have hb (i : ι) : ¬Nonempty (ℕ ↪o B i) := fun hi => hSome ⟨i, hi⟩
    rcases hwell with h | h
    · exact atom_of_well_ordered_sum h B hne hUnion hord hb hS
    · exact (no_omega_in_sum B hb hord (stabilizes_of_reverse_wellOrder h) hS).elim

end AharoniKorman.External
