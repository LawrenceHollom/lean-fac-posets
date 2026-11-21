import AharoniKorman.Consolidation.AtomicRepresentatives
import AharoniKorman.Completion.VacillationSuborder
import AharoniKorman.External.Hausdorff

/-! The Hausdorff/vacillation argument producing saturated omega rays. -/

namespace AharoniKorman.Consolidation

open Set Completion

section Linear

variable {β : Type*} [LinearOrder β]

theorem wellFoundedGT_Iio_of_no_omegaSucc
    (h : ¬Nonempty (WithTop ℕ ↪o β)) (b : β) :
    WellFounded (fun x y : Iio b => y < x) := by
  by_contra hnot
  rw [RelEmbedding.wellFounded_iff_isEmpty, not_isEmpty_iff] at hnot
  obtain ⟨e⟩ := hnot
  apply h
  exact omegaSucc_embedding_of_bounded_sequence
    (f := fun n => (e n).1) (fun m n hmn => e.map_rel_iff.2 hmn)
    (fun n => (e n).2)

/-- Locate the interval between successive values of a sequence. -/
theorem exists_sequence_interval {f : ℕ → β} {x : β}
    (h0 : f 0 ≤ x) (hb : ∃ n, x < f n) : ∃ n, f n ≤ x ∧ x < f (n + 1) := by
  classical
  let n := Nat.find hb
  have hn : x < f n := Nat.find_spec hb
  have hn0 : n ≠ 0 := by
    intro heq
    exact hn.not_ge (heq ▸ h0)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨k, le_of_not_gt ?_, by simpa only [hk] using hn⟩
  exact Nat.find_min hb (show k < Nat.find hb by change k < n; omega)

/-- Vacillation forces an omega tail in a no-maximum chain containing no
omega-plus-one. The excluded alternative gives explicit infinite blocks. -/
theorem exists_finite_initial_tail [Nonempty β] [NoMaxOrder β]
    (hvac : IsVacillating β) (hno : ¬Nonempty (WithTop ℕ ↪o β)) :
    ∃ a : β, ∀ b : β, (Icc a b).Finite := by
  classical
  by_contra hgood
  push Not at hgood
  have hnext (a : β) : ∃ b : β, a < b ∧ (Ico a b).Infinite := by
    obtain ⟨b, habinf⟩ := hgood a
    obtain ⟨x, hax, hxb⟩ := habinf.nonempty
    obtain ⟨c, hbc⟩ := exists_gt b
    exact ⟨c, hax.trans_lt (hxb.trans_lt hbc),
      habinf.mono (fun y hy => ⟨hy.1, hy.2.trans_lt hbc⟩)⟩
  choose next hnextlt hnextinf using hnext
  let f : ℕ → β := Nat.rec (Classical.arbitrary β) (fun _ x => next x)
  have hfstep (n : ℕ) : f n < f (n + 1) := hnextlt _
  have hf : StrictMono f := strictMono_nat_of_lt_succ hfstep
  let B : ℕ → Set β := fun n => Ico (f n) (f (n + 1))
  let M : Set β := ⋃ n, B n
  have hMmem (x : β) : x ∈ M ↔ f 0 ≤ x ∧ ∃ n, x < f n := by
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, hx⟩
      exact ⟨(hf.monotone (Nat.zero_le n)).trans hx.1, n + 1, hx.2⟩
    · rintro ⟨h0, hb⟩
      obtain ⟨n, hn⟩ := exists_sequence_interval h0 hb
      exact Set.mem_iUnion.2 ⟨n, hn⟩
  have hMconv : M.OrdConnected := by
    constructor
    intro x hx y hy z hz
    obtain ⟨hx0, _⟩ := (hMmem x).1 hx
    obtain ⟨_, n, hyn⟩ := (hMmem y).1 hy
    exact (hMmem z).2 ⟨hx0.trans hz.1, n, hz.2.trans_lt hyn⟩
  apply (hvac M (isSaturatedChain_iff M |>.2 hMconv)).1
  refine ⟨B, rfl, fun n => hnextinf (f n), ?_, ?_⟩
  · intro n
    let inc : B n → Iio (f (n + 1)) := fun x => ⟨x.1, x.2.2⟩
    exact (wellFoundedGT_Iio_of_no_omegaSucc hno _).onFun (f := inc)
  · intro i j hij x hx y hy
    exact hx.2.trans_le ((hf.monotone (Nat.succ_le_of_lt hij)).trans hy.1)

end Linear

variable {α : Type*} [PartialOrder α]

theorem IsOmegaRepresentative.map {C : IncreasingChain α}
    (hC : IsOmegaRepresentative C) {β : Type*} [PartialOrder β]
    (e : α ↪o β) (he : SaturationPreserving e) : IsOmegaRepresentative (C.map e he) := by
  intro x
  let iso := C.1.mapOrderIso e he
  apply ((hC (iso.symm x)).preimage iso.symm.injective.injOn).subset
  intro y hy
  exact iso.symm.monotone hy

/-- Atomic existence inside the actual saturated representative, with no
change to the surrounding maximal chain. -/
theorem exists_omega_subchain_of_embedding (hscattered : IsScattered α)
    (hvac : IsVacillating α) (C : SaturatedChain α) (homega : Nonempty (ℕ ↪o C)) :
    ∃ B : IncreasingChain α, (B.1 : Set α) ⊆ C ∧ IsOmegaRepresentative B := by
  classical
  obtain ⟨A, hAsat, hAne, hAup, _, hAno⟩ :=
    External.exists_saturated_omega_no_omegaSucc
      (hscattered.subtype (C : Set α)) homega
  have : Nonempty A := hAne.to_subtype
  have : NoMaxOrder A := ⟨fun a => by
    obtain ⟨b, hb, hab⟩ := hAup a.1 a.2
    exact ⟨⟨b, hb⟩, hab⟩⟩
  have hvacA : IsVacillating A :=
    (hvac.saturated_subtype C.saturated).saturated_subtype hAsat
  obtain ⟨a, ha⟩ := exists_finite_initial_tail hvacA hAno
  let T : IncreasingChain A :=
    ⟨⟨Ici a, ⟨a, le_rfl⟩, isSaturatedChain_iff _ |>.2 ordConnected_Ici⟩, by
      rintro ⟨m, hm⟩
      obtain ⟨b, hmb⟩ := exists_gt m.1
      exact hmb.not_ge (hm ⟨b, m.2.trans hmb.le⟩)⟩
  have hT : IsOmegaRepresentative T := by
    intro t
    apply ((ha t.1).preimage (f := fun x : T.1 => x.1) Subtype.val_injective.injOn).subset
    intro x hx
    exact ⟨x.2, hx⟩
  let eA : A ↪o C := OrderEmbedding.subtype A
  have heA : SaturationPreserving eA := saturationPreserving_subtype_of_saturated hAsat
  let eC : C ↪o α := OrderEmbedding.subtype (C : Set α)
  have heC : SaturationPreserving eC :=
    saturationPreserving_subtype_of_saturated C.saturated
  let B := (T.map eA heA).map eC heC
  refine ⟨B, ?_, (hT.map eA heA).map eC heC⟩
  rintro x ⟨y, hy, rfl⟩
  exact y.2

end AharoniKorman.Consolidation
