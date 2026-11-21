import AharoniKorman.Consolidation.AtomicIsolation
import AharoniKorman.Preliminaries.FAC

/-! The FAC part of the atomic escape argument: a sequence of strictly shrinking
positive atomic cuts has a strictly decreasing subsequence in domination order. -/

namespace AharoniKorman.Consolidation

open Set Completion

variable {α : Type*} [PartialOrder α]

/-- The antichain-selection step of `lem:domination`. Strict inclusions
encode successive nontrivial consolidations on positive omega atoms. -/
theorem exists_antichain_meeting_increasing_chains (A : ℕ → IncreasingChain α)
    (hcuts : StrictAnti (fun n => (IncreasingGerm.ofChain (A n)).lowerProfile))
    (hnot : ∀ i j : ℕ, i < j →
      ¬H.increasing (IncreasingGerm.ofChain (A j)) < H.increasing (IncreasingGerm.ofChain (A i))) :
    ∃ S : Set α, S.Infinite ∧ IsAntichain (· ≤ ·) S ∧
      ∀ n, ∃! x, x ∈ S ∧ x ∈ (A n).1 := by
  classical
  have hmarker (i : ℕ) : ∃ a : (A i).1,
      ∀ j, i < j → ∀ b : (A j).1, ¬a.1 ≤ b.1 := by
    obtain ⟨p, hp, hpnot⟩ := Set.exists_of_ssubset (hcuts (Nat.lt_succ_self i))
    obtain ⟨a, hpa⟩ := (IncreasingGerm.mem_lowerProfile_ofChain (A i) p).1 hp
    refine ⟨a, fun j hij b hab => ?_⟩
    apply hpnot
    apply hcuts.antitone (Nat.succ_le_of_lt hij)
    exact (IncreasingGerm.mem_lowerProfile_ofChain (A j) p).2 ⟨b, hpa.trans_le hab⟩
  choose marker hmarker using hmarker
  have hnext (n : ℕ) (v : ∀ i, i < n → (A i).1) :
      ∃ b : (A n).1, marker n ≤ b ∧ ∀ i (hi : i < n), ¬b.1 ≤ (v i hi).1 := by
    have hescape (i : Fin n) : ∃ b : (A n).1, ¬b.1 ≤ (v i i.2).1 := by
      by_contra! hb
      apply hnot i n i.2
      apply lt_trans (b := H.principal (v i i.2).1)
      · apply (H.increasing_ofChain_lt_principal (A n) _).2
        intro b
        obtain ⟨c, hbc⟩ := (A n).2.exists_gt b
        exact (show b.1 < c.1 from hbc).trans_le (hb c)
      · exact IncreasingGerm.representative_mem_lowerProfile (A i) (v i i.2)
    choose w hw using hescape
    obtain ⟨b, hb, hmax⟩ := ((Set.finite_range w).insert (marker n)).exists_maximal
      ⟨marker n, Set.mem_insert _ _⟩
    have hle (u : (A n).1) (hu : u ∈ insert (marker n) (range w)) : u ≤ b :=
      (le_total u b).elim id (hmax hu)
    refine ⟨b, hle _ (Set.mem_insert _ _), fun i hi hbi => ?_⟩
    have hwb : w ⟨i, hi⟩ ≤ b := hle _ (Set.mem_insert_of_mem _ (mem_range_self _))
    exact hw ⟨i, hi⟩ ((show (w ⟨i, hi⟩).1 ≤ b.1 from hwb).trans hbi)
  choose next hnext using hnext
  let z : ∀ n, (A n).1 := Nat.strongRec next
  have hz (n : ℕ) : marker n ≤ z n ∧ ∀ i (hi : i < n), ¬(z n).1 ≤ (z i).1 := by
    dsimp only [z]
    rw [Nat.strongRec_eq]
    exact hnext n _
  have hzforward {i j : ℕ} (hij : i < j) : ¬(z i).1 ≤ (z j).1 :=
    fun h => hmarker i j hij (z j) ((show (marker i).1 ≤ (z i).1 from (hz i).1).trans h)
  have hzinj : Function.Injective (fun n => (z n).1) := by
    intro i j heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact hzforward hij heq.le
    · exact hzforward hji heq.ge
  have hantichain : IsAntichain (· ≤ ·) (range (fun n => (z n).1)) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne hij
    have hneij : i ≠ j := fun h => hne (h ▸ rfl)
    rcases lt_or_gt_of_ne hneij with hlt | hgt
    · exact hzforward hlt hij
    · exact (hz i).2 j hgt hij
  refine ⟨_, Set.infinite_range_of_injective hzinj, hantichain,
    fun n => ⟨(z n).1, ⟨mem_range_self n, (z n).2⟩, ?_⟩⟩
  intro x hx
  by_contra hne
  exact ((A n).1.isChain.total hx.2 (z n).2).elim
    (hantichain hx.1 (mem_range_self n) hne)
    (hantichain (mem_range_self n) hx.1 (fun h => hne h.symm))

/-- The first assertion of Lemma 2.1. Only FAC and atomicity are needed here;
quasifoundedness is needed for the subsequent absence of a principal lower bound. -/
theorem exists_strictAnti_subsequence_of_positive_atomic_cut_descent
    (hfac : IsFAC α) (g : ℕ → IncreasingGerm α) (hg : ∀ n, IsPositiveAtom (g n))
    (hcuts : StrictAnti (fun n => (g n).lowerProfile)) :
    ∃ e : ℕ ↪o ℕ, StrictAnti (fun n => H.increasing (g (e n))) := by
  classical
  obtain ⟨e, he | he⟩ :=
    exists_increasing_or_nonincreasing_subseq (· > ·) (fun n => H.increasing (g n))
  · exact ⟨e, he⟩
  · exfalso
    choose A hAg hA using fun n => hg (e n)
    change ∀ n, IncreasingGerm.ofChain (A n) = g (e n) at hAg
    have hstrict : StrictAnti (fun n => (IncreasingGerm.ofChain (A n)).lowerProfile) := by
      intro i j hij
      simpa only [hAg] using hcuts (e.strictMono hij)
    obtain ⟨S, hSinf, hSanti, _⟩ := exists_antichain_meeting_increasing_chains A hstrict
      (by simpa only [hAg] using he)
    exact hSinf (hfac _ hSanti)

end AharoniKorman.Consolidation
