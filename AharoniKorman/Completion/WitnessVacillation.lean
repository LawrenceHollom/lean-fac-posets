import AharoniKorman.Completion.WitnessChains
import AharoniKorman.Completion.VacillationWitness

/-! The simultaneous witness and alternating subsequence in `lem:witness-vacillation`. -/

namespace AharoniKorman.Completion.H

open Set

variable {α : Type*} [PartialOrder α]

/-- Move the given sequence into a common saturated witness chain and apply vacillation there. -/
theorem exists_decreasing_between_consecutive_increasing (hvac : IsVacillating α)
    (g : ℕ → IncreasingGerm α) (hg : StrictAnti (fun n => increasing (g n))) :
    ∃ (n : ℕ) (h : DecreasingGerm α), increasing (g (n + 1)) < decreasing h ∧
      decreasing h < increasing (g n) := by
  classical
  let f (n : ℕᵒᵈ) := increasing (g (OrderDual.ofDual n))
  have hf : StrictMono f := fun _ _ hij => hg hij
  have hgen (n : ℕᵒᵈ) : (f n).IsGenuineNonprincipal :=
    ⟨⟨.increasing, rfl⟩, increasing_ne_bot _, increasing_ne_top _⟩
  obtain ⟨C, hC⟩ := exists_witnesses_of_strictMono f hf hgen
  let : LinearOrder (C : Set α) := SaturatedChain.instLinearOrder C
  let incl : (C : Set α) ↪o α := OrderEmbedding.subtype _
  let hincl : SaturationPreserving incl := saturationPreserving_subtype_of_saturated C.saturated
  let emb := mapEmbedding incl hincl
  have preimage (n : ℕ) : ∃ x : IncreasingGerm (C : Set α),
      IncreasingGerm.map incl hincl x = g n := by
    obtain ⟨Y, hY, heq⟩ := (witnesses_iff_in_completion C _).mp (hC n)
    change emb Y = increasing (g n) at heq
    have hdir : Y.direction = some .increasing := by
      rw [← direction_map incl hincl Y]
      change (emb Y).direction = _
      rw [heq]
      rfl
    rcases (direction_eq_increasing_iff Y).mp hdir with ⟨x, rfl⟩ | htop
    · exact ⟨x, increasing.inj heq⟩
    · exact (hY.2.2 htop).elim
  choose x hx using preimage
  have hx' (n : ℕ) : emb (increasing (x n)) = increasing (g n) :=
    congrArg increasing (hx n)
  have hanti : StrictAnti (fun n => increasing (x n)) := by
    intro i j hij
    exact emb.lt_iff_lt.mp (by rw [hx', hx']; exact hg hij)
  obtain ⟨n, h, hlo, hhi⟩ := exists_negative_between_adjacent_positive
    (hvac.saturated_subtype C.saturated) x hanti
  refine ⟨n, DecreasingGerm.map incl hincl h, ?_, ?_⟩
  · have hlow := emb.strictMono hlo
    rw [hx'] at hlow
    exact hlow
  · have hhigh := emb.strictMono hhi
    rw [hx'] at hhigh
    exact hhigh

/-- Paper `lem:witness-vacillation`, decreasing sequence of increasing germs. -/
theorem exists_alternating_witness_of_strictAnti_increasing (hvac : IsVacillating α)
    (g : ℕ → IncreasingGerm α) (hg : StrictAnti (fun n => increasing (g n))) :
    ∃ e : ℕ → ℕ, ∃ h : ℕ → DecreasingGerm α, ∃ C : SaturatedChain α,
      StrictMono e ∧
      (∀ n, increasing (g (e (n + 1))) < decreasing (h n) ∧
        decreasing (h n) < increasing (g (e n))) ∧
      (∀ n, Witnesses C (increasing (g (e n)))) ∧
      (∀ n, Witnesses C (decreasing (h n))) := by
  classical
  have fromIndex (t : ℕ) : ∃ (k : ℕ) (Y : DecreasingGerm α), t ≤ k ∧
      increasing (g (k + 1)) < decreasing Y ∧ decreasing Y < increasing (g k) := by
    obtain ⟨k, Y, hlo, hhi⟩ := exists_decreasing_between_consecutive_increasing hvac
      (fun n => g (t+n)) (fun i j hij => hg (Nat.add_lt_add_left hij t))
    exact ⟨t+k, Y, Nat.le_add_right t k, hlo, hhi⟩
  choose k Y hgap using fromIndex
  let start (n : ℕ) : ℕ := Nat.rec 0 (fun _ t => k t + 1) n
  let e (n : ℕ) : ℕ := k (start n)
  let h (n : ℕ) : DecreasingGerm α := Y (start n)
  have heStep (n : ℕ) : e n < e (n+1) := (hgap (start (n+1))).1
  have halted (n : ℕ) : increasing (g (e (n+1))) < decreasing (h n) ∧
      decreasing (h n) < increasing (g (e n)) :=
    ⟨(hg.antitone (show e n + 1 ≤ e (n+1) from heStep n)).trans_lt (hgap (start n)).2.1,
      (hgap (start n)).2.2⟩
  let f (i : ℕ) : H α := if i % 2 = 0 then increasing (g (e (i/2))) else decreasing (h (i/2))
  have even (n : ℕ) : f (2*n) = increasing (g (e n)) := by
    have hmod : 2*n % 2 = 0 := by omega
    have hdiv : 2*n / 2 = n := by omega
    simp [f, hmod, hdiv]
  have odd (n : ℕ) : f (2*n+1) = decreasing (h n) := by
    have hdiv : (2*n+1) / 2 = n := by omega
    simp [f, hdiv]
  have hf : StrictAnti f := strictAnti_nat_of_succ_lt fun i => by
    by_cases hi : i % 2 = 0
    · have hi' : i = 2*(i/2) := by omega
      conv_rhs => rw [hi', even]
      conv_lhs => rw [show i+1 = 2*(i/2)+1 by omega, odd]
      exact (halted _).2
    · conv_rhs => rw [show i = 2*(i/2)+1 by omega, odd]
      conv_lhs => rw [show i+1 = 2*(i/2+1) by omega, even]
      exact (halted _).1
  have hgen (i : ℕ) : (f i).IsGenuineNonprincipal := by
    by_cases hi : i % 2 = 0
    · rw [show i = 2*(i/2) by omega, even]
      exact ⟨⟨.increasing, rfl⟩, increasing_ne_bot _, increasing_ne_top _⟩
    · rw [show i = 2*(i/2)+1 by omega, odd]
      exact ⟨⟨.decreasing, rfl⟩, decreasing_ne_bot _, decreasing_ne_top _⟩
  let f' (i : ℕᵒᵈ) := f (OrderDual.ofDual i)
  have hf' : StrictMono f' := fun _ _ hij => hf hij
  obtain ⟨C, hC⟩ := exists_witnesses_of_strictMono f' hf' (fun i => hgen (OrderDual.ofDual i))
  exact ⟨e, h, C, strictMono_nat_of_lt_succ heStep, halted,
    fun n => even n ▸ hC (OrderDual.toDual (2*n)),
    fun n => odd n ▸ hC (OrderDual.toDual (2*n+1))⟩

/-- The order-dual statement, for an increasing sequence of decreasing germs. -/
theorem exists_alternating_witness_of_strictMono_decreasing (hvac : IsVacillating α)
    (g : ℕ → DecreasingGerm α) (hg : StrictMono (fun n => decreasing (g n))) :
    ∃ e : ℕ → ℕ, ∃ h : ℕ → IncreasingGerm α, ∃ C : SaturatedChain α,
      StrictMono e ∧
      (∀ n, decreasing (g (e n)) < increasing (h n) ∧
        increasing (h n) < decreasing (g (e (n + 1)))) ∧
      (∀ n, Witnesses C (decreasing (g (e n)))) ∧
      (∀ n, Witnesses C (increasing (h n))) := by
  have hanti : StrictAnti (fun n => (decreasing (g n)).dual) :=
    fun i j hij => (dual_lt_dual _ _).mpr (hg hij)
  obtain ⟨e, h, C, he, hstep, hgWitness, hhWitness⟩ :=
    exists_alternating_witness_of_strictAnti_increasing hvac.orderDual (fun n => (g n).toDual) hanti
  refine ⟨e, fun n => (h n).toDual, C.dual, he, ?_, ?_, ?_⟩
  · intro n
    exact ⟨(dual_lt_dual _ _).mp (hstep n).2, (dual_lt_dual _ _).mp (hstep n).1⟩
  · intro n
    obtain ⟨A, hAC, hA⟩ := hgWitness n
    exact ⟨A.dual, hAC, hA.dual⟩
  · intro n
    obtain ⟨A, hAC, hA⟩ := hhWitness n
    exact ⟨A.dual, hAC, hA.dual⟩

end AharoniKorman.Completion.H
