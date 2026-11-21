import AharoniKorman.External.HausdorffClassification

/-! The atomic-interval consequence of Hausdorff's classification. -/

namespace AharoniKorman.External

open Set

/-- The atomic-interval corollary of Hausdorff's classification.

Every scattered linear order which contains an increasing copy of `ω` has a nonempty convex
suborder which is increasing, still contains `ω`, and contains no copy of `ω + 1` (represented by
`WithTop ℕ`). In a linear ambient order, saturation is equivalent to convexity.
-/
theorem exists_saturated_omega_no_omegaSucc {α : Type*} [LinearOrder α]
    (hscattered : IsScattered α) (homega : Nonempty (ℕ ↪o α)) :
    ∃ C : Set α,
      IsSaturatedChain C ∧
      C.Nonempty ∧
      (∀ x ∈ C, ∃ y ∈ C, x < y) ∧
      Nonempty (ℕ ↪o C) ∧
      ¬Nonempty (WithTop ℕ ↪o C) := by
  obtain ⟨C, hC, ⟨e⟩, hnot⟩ := exists_atomic_convex_interval hscattered homega
  refine ⟨C, IsSaturatedChain.of_ordConnected (isChain_of_trichotomous _) hC,
    ⟨(e 0).1, (e 0).2⟩, ?_, ⟨e⟩, hnot⟩
  intro x hx
  by_contra h
  have bound (n : ℕ) : e n ≤ (⟨x, hx⟩ : C) :=
    le_of_not_gt fun hn => h ⟨(e n).1, (e n).2, hn⟩
  exact hnot (omegaSucc_embedding_of_bounded_sequence e.strictMono fun n =>
    (e.strictMono (Nat.lt_succ_self n)).trans_le (bound (n + 1)))

/-- The order-dual form of `exists_saturated_omega_no_omegaSucc`. -/
theorem exists_saturated_omegaStar_no_omegaSuccStar {α : Type*} [LinearOrder α]
    (hscattered : IsScattered α)
    (homega : Nonempty (ℕ ↪o (αᵒᵈ))) :
    ∃ C : Set α,
      @IsSaturatedChain αᵒᵈ inferInstance C ∧
      C.Nonempty ∧
      (∀ x ∈ C, ∃ y ∈ C, y < x) ∧
      Nonempty (ℕ ↪o {x : αᵒᵈ // x ∈ C}) ∧
      ¬Nonempty (WithTop ℕ ↪o {x : αᵒᵈ // x ∈ C}) := by
  exact exists_saturated_omega_no_omegaSucc hscattered.orderDual homega

end AharoniKorman.External
