import AharoniKorman.Completion.LinearOrder
import AharoniKorman.Completion.VacillationSuborder

/-! The forbidden-block step in `lem:witness-vacillation`. -/

namespace AharoniKorman.Completion.H

open Set

variable {α : Type*} [LinearOrder α]

/-- The principal points strictly between two completion points. -/
def principalInterval (L U : H α) : Set α := {p | L < principal p ∧ principal p < U}

theorem principalInterval_ordConnected (L U : H α) : (principalInterval L U).OrdConnected := by
  constructor
  intro a ha b hb c hc
  exact ⟨ha.1.trans_le ((principal_le_principal _ _).2 hc.1),
    ((principal_le_principal _ _).2 hc.2).trans_lt hb.2⟩

private theorem positive_interval_infinite {g h : IncreasingGerm α}
    (hgh : increasing g < increasing h) : (principalInterval (increasing g) (increasing h)).Infinite := by
  induction h using IncreasingGerm.inductionOn with
  | h D =>
    obtain ⟨p, hg, hh⟩ := exists_principal_between_increasing hgh
    obtain ⟨d, hpd⟩ := (principal_lt_increasing_ofChain p D).1 hh
    let d' : α := d.1
    have hd' : increasing g < principal d' := hg.trans ((principal_lt_principal p _).2 hpd)
    intro hfin
    have hex : ∃ m ∈ principalInterval (increasing g) (increasing (IncreasingGerm.ofChain D)),
        ∀ a ∈ principalInterval (increasing g) (increasing (IncreasingGerm.ofChain D)), a ≤ m := by
      have hm : d' ∈ principalInterval (increasing g) (increasing (IncreasingGerm.ofChain D)) := by
        refine ⟨hd', (principal_lt_increasing_ofChain _ D).2 ?_⟩
        exact D.2.exists_gt d
      obtain ⟨m, hm, hmax⟩ := hfin.exists_maximal ⟨d', hm⟩
      refine ⟨m, hm, fun a ha => ?_⟩
      exact (le_total a m).elim id (hmax ha)
    obtain ⟨m, hm, hmax⟩ := hex
    obtain ⟨e, hme⟩ := (principal_lt_increasing_ofChain m D).1 hm.2
    exact hme.not_ge (hmax e.1 ⟨hm.1.trans ((principal_lt_principal _ _).2 hme),
      (principal_lt_increasing_ofChain _ D).2 (D.2.exists_gt e)⟩)

private theorem gap_union_eq (g : ℕ → IncreasingGerm α)
    (hg : StrictAnti (fun n => increasing (g n))) :
    (⋃ n, principalInterval (increasing (g (n+1))) (increasing (g n))) =
      {p | principal p < increasing (g 0) ∧ ∃ n, increasing (g n) < principal p} := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hp
    exact ⟨hn.2.trans_le (hg.antitone (Nat.zero_le n)), n+1, hn.1⟩
  · rintro ⟨h0, hb⟩
    let n := Nat.find hb
    have hn : increasing (g n) < principal p := Nat.find_spec hb
    have hn0 : n ≠ 0 := fun heq => h0.not_ge (heq ▸ hn.le)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    refine Set.mem_iUnion.2 ⟨k, ?_, ?_⟩
    · simpa only [hk] using hn
    · rcases lt_trichotomy (principal p) (increasing (g k)) with hlt | heq | hgt
      · exact hlt
      · cases heq
      · exact (Nat.find_min hb (show k < Nat.find hb by change k < n; omega) hgt).elim

/-- A decreasing sequence of increasing germs has a principal gap with an infinite
descending sequence. The other alternative gives an explicit forbidden block sum. -/
theorem exists_non_wellFounded_positive_gap (hvac : IsVacillating α)
    (g : ℕ → IncreasingGerm α) (hg : StrictAnti (fun n => increasing (g n))) :
    ∃ n, ¬ WellFounded ((· < ·) : principalInterval (increasing (g (n+1)))
      (increasing (g n)) → _ → Prop) := by
  classical
  by_contra! hwf
  let B (n : ℕ) := principalInterval (increasing (g (n+1))) (increasing (g n))
  have hconv : (⋃ n, B n).OrdConnected := by
    change (⋃ n, principalInterval _ _).OrdConnected
    rw [gap_union_eq g hg]
    constructor
    intro a ha b hb c hc
    obtain ⟨n, hn⟩ := ha.2
    exact ⟨((principal_le_principal _ _).2 hc.2).trans_lt hb.1,
      n, hn.trans_le ((principal_le_principal _ _).2 hc.1)⟩
  have hsat : IsSaturatedChain (⋃ n, B n) := (isSaturatedChain_iff _).2 hconv
  apply (hvac _ hsat).2
  refine ⟨B, rfl, fun n => positive_interval_infinite (α := α) (hg (Nat.lt_succ_self n)),
    hwf, ?_⟩
  intro i j hij a ha b hb
  have hba : principal (α := α) b < principal (α := α) a :=
    hb.2.trans_le ((hg.antitone (Nat.succ_le_of_lt hij)).trans ha.1.le)
  exact (principal_lt_principal (α := α) _ _).1 hba

private theorem exists_decreasingChain_of_not_wellFounded {A : Set α} (hA : A.OrdConnected)
    (hwf : ¬ WellFounded ((· < ·) : A → A → Prop)) :
    ∃ D : DecreasingChain α, (D.1 : Set α) ⊆ A := by
  rw [RelEmbedding.wellFounded_iff_isEmpty, not_isEmpty_iff] at hwf
  obtain ⟨e⟩ := hwf
  let D := {x : α | x ≤ (e 0).1 ∧ ∃ n : ℕ, (e n).1 ≤ x}
  have hD (x : α) (hx : x ∈ D) : x ∈ A := by
    obtain ⟨n, hn⟩ := hx.2
    exact hA.out (e n).2 (e 0).2 ⟨hn, hx.1⟩
  have hconv : D.OrdConnected := by
    constructor
    intro x hx y hy z hz
    obtain ⟨n, hn⟩ := hx.2
    exact ⟨hz.2.trans hy.1, n, hn.trans hz.1⟩
  have hDne : D.Nonempty := ⟨(e 0).1, le_rfl, 0, le_rfl⟩
  let S : SaturatedChain α := ⟨D, hDne, (isSaturatedChain_iff _).2 hconv⟩
  have hstep (n : ℕ) : (e (n+1)).1 < (e n).1 := e.map_rel_iff.2 (Nat.lt_succ_self n)
  have he : StrictAnti (fun n : ℕ => (e n).1) := strictAnti_nat_of_succ_lt hstep
  have hmin : S.NoBottom := by
    rintro ⟨x, hmin⟩
    obtain ⟨n, hn⟩ := x.2.2
    have hyD : (e (n+1)).1 ∈ D := ⟨he.antitone (Nat.zero_le _), n+1, le_rfl⟩
    exact ((hstep n).trans_le hn).not_ge (hmin ⟨_, hyD⟩)
  exact ⟨⟨S, hmin⟩, fun _ hx => hD _ hx⟩

/-- The completion argument in `lem:witness-vacillation`, on a fixed linear order. -/
theorem exists_negative_between_adjacent_positive (hvac : IsVacillating α)
    (g : ℕ → IncreasingGerm α) (hg : StrictAnti (fun n => increasing (g n))) :
    ∃ (n : ℕ) (h : DecreasingGerm α), increasing (g (n+1)) < decreasing h ∧
      decreasing h < increasing (g n) := by
  obtain ⟨n, hn⟩ := exists_non_wellFounded_positive_gap hvac g hg
  obtain ⟨D, hD⟩ := exists_decreasingChain_of_not_wellFounded
    (principalInterval_ordConnected (increasing (g (n+1))) (increasing (g n))) hn
  refine ⟨n, DecreasingGerm.ofChain D, ?_, ?_⟩
  · generalize h : g (n+1) = a
    have hbound (d : D.1) : increasing a < principal d.1 := h ▸ (hD d.2).1
    induction a using IncreasingGerm.inductionOn with
    | h C =>
      exact (increasing_ofChain_lt_decreasing_ofChain C D).2
        (fun c d => (increasing_ofChain_lt_principal C d.1).1 (hbound d) c)
  · obtain ⟨d, hd⟩ := D.1.nonempty
    exact ((decreasing_ofChain_lt_principal D d).2 (D.2.exists_lt ⟨d, hd⟩)).trans
      (hD hd).2

end AharoniKorman.Completion.H
