import AharoniKorman.Completion.Scattering

/-! Phase D public-API gate and examples. No germ quotient or representative-level
domination definition is unfolded in this file. -/

namespace AharoniKorman.Completion.OrderAPI

open Set

variable {α : Type*} [PartialOrder α]

example (x y : α) : H.principal x ≤ H.principal y ↔ x ≤ y := H.principal_le_principal x y
example (x y : α) : Incomparable (H.principal x) (H.principal y) ↔ Incomparable x y :=
  H.incomparable_principal x y
example (X Y : H α) : X.dual < Y.dual ↔ Y < X := H.dual_lt_dual X Y
example (h : IsScattered α) : IsScattered (H α) := H.isScattered h

private theorem finite_hasTop [Finite α] (C : SaturatedChain α) : C.HasTop := by
  obtain ⟨m, hm, hmax⟩ := (Set.toFinite (C : Set α)).exists_maximal C.nonempty
  refine ⟨⟨m, hm⟩, ?_⟩
  intro c
  rcases C.isChain.total c.2 hm with hcm | hmc
  · exact hcm
  · exact hmax c.2 hmc

private theorem no_increasing_germ [Finite α] (g : IncreasingGerm α) : False := by
  induction g using IncreasingGerm.inductionOn with
  | h C => exact C.2 (finite_hasTop C.1)

/-- On any finite poset the only completion points are principal points and endpoints. -/
theorem finite_cases [Finite α] (X : H α) :
    (∃ x, X = H.principal x) ∨ X = ⊥ ∨ X = ⊤ := by
  cases X with
  | principal x => exact Or.inl ⟨x, rfl⟩
  | increasing g => exact (no_increasing_germ g).elim
  | decreasing g => exact (no_increasing_germ g.toDual).elim
  | bottom => exact Or.inr (Or.inl rfl)
  | top => exact Or.inr (Or.inr rfl)

example (X : H (Fin 4)) : (∃ x, X = H.principal x) ∨ X = ⊥ ∨ X = ⊤ := finite_cases X
example (X : H (Fin 4)ᵒᵈ) : (∃ x, X = H.principal x) ∨ X = ⊥ ∨ X = ⊤ := finite_cases X

private def univChain (β : Type*) [LinearOrder β] [Nonempty β] : SaturatedChain β :=
  ⟨Set.univ, Set.univ_nonempty, IsSaturatedChain.of_ordConnected
    (isChain_of_trichotomous _) Set.ordConnected_univ⟩

private def unboundedChain (β : Type*) [LinearOrder β] [Nonempty β] [NoMaxOrder β] :
    IncreasingChain β := by
  refine ⟨univChain β, ?_⟩
  rintro ⟨m, hm⟩
  obtain ⟨y, hmy⟩ := exists_gt m.1
  exact hmy.not_ge (hm ⟨y, Set.mem_univ y⟩)

private def natGerm : IncreasingGerm ℕ := IncreasingGerm.ofChain (unboundedChain ℕ)
private def intGerm : IncreasingGerm ℤ := IncreasingGerm.ofChain (unboundedChain ℤ)
private def intDualGerm : IncreasingGerm ℤᵒᵈ := IncreasingGerm.ofChain (unboundedChain ℤᵒᵈ)

example (n : ℕ) : H.principal n < H.increasing natGerm := by
  apply (H.principal_lt_increasing_ofChain n (unboundedChain ℕ)).2
  exact ⟨⟨n + 1, Set.mem_univ _⟩, Nat.lt_succ_self n⟩

example : H.increasing natGerm < (⊤ : H ℕ) := lt_top_iff_ne_top.2 (H.increasing_ne_top _)

example (z : ℤ) : H.principal z < H.increasing intGerm := by
  apply (H.principal_lt_increasing_ofChain z (unboundedChain ℤ)).2
  exact ⟨⟨z + 1, Set.mem_univ _⟩, lt_add_one z⟩

example (z : ℤ) : H.principal (OrderDual.toDual z) < H.increasing intDualGerm := by
  apply (H.principal_lt_increasing_ofChain _ (unboundedChain ℤᵒᵈ)).2
  exact ⟨⟨OrderDual.toDual (z - 1), Set.mem_univ _⟩, show z - 1 < z from sub_one_lt z⟩

example (n : ℕ) : H.decreasing natGerm.toDual < H.principal (OrderDual.toDual n) := by
  apply (H.dual_lt_dual (H.increasing natGerm) (H.principal n)).2
  apply (H.principal_lt_increasing_ofChain n (unboundedChain ℕ)).2
  exact ⟨⟨n + 1, Set.mem_univ _⟩, Nat.lt_succ_self n⟩

#print axioms H.strictLT_trans
#print axioms H.principalEmbedding
#print axioms H.dualOrderIso
#print axioms H.isScattered
#print axioms finite_cases

end AharoniKorman.Completion.OrderAPI
