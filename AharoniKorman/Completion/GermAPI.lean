import AharoniKorman.Completion.Germs

/-! Phase C public-API gate. No quotient or setoid implementation is unfolded. -/

namespace AharoniKorman.Completion.GermAPI

variable {α : Type*} [PartialOrder α]

/-- A semantic, set-valued invariant: the principal upper bounds of a germ. -/
def upperBounds : IncreasingGerm α → Set α :=
  IncreasingGerm.lift (fun C => {p | ∀ x : C.1, x.1 ≤ p})
    (fun _ _ h => Set.ext (fun p => h.upperBounds_iff p))

theorem upperBounds_of_representative {C : IncreasingChain α} {g : IncreasingGerm α}
    (h : g.Represents C) (p : α) : p ∈ upperBounds g ↔ ∀ x : C.1, x.1 ≤ p := by
  rw [← h]
  simp only [upperBounds, IncreasingGerm.lift_ofChain, Set.mem_ofPred_eq]

theorem chosen_representative_upperBounds (g : IncreasingGerm α) (p : α) :
    p ∈ upperBounds g ↔ ∀ x : g.representative.1, x.1 ≤ p :=
  upperBounds_of_representative g.representative_spec p

/-- A binary representative relation descends using transitivity in both slots. -/
def related : IncreasingGerm α → IncreasingGerm α → Prop :=
  IncreasingGerm.lift₂ IncreasingEquivalent (fun _ _ _ _ hC hD => propext
    ⟨fun h => hC.symm.trans (h.trans hD), fun h => hC.trans (h.trans hD.symm)⟩)

theorem related_iff_eq (g h : IncreasingGerm α) : related g h ↔ g = h := by
  induction g using IncreasingGerm.inductionOn with
  | h C =>
    induction h using IncreasingGerm.inductionOn with
    | h D => simp only [related, IncreasingGerm.lift₂_ofChain, IncreasingGerm.ofChain_eq_iff]

theorem dual_representative {C : IncreasingChain α} {g : IncreasingGerm α}
    (h : g.Represents C) : g.toDual.Represents C.toDual := by
  change DecreasingGerm.ofChain C.toDual = g.toDual
  rw [← IncreasingGerm.toDual_ofChain, h]

theorem decreasing_chosen_representative (g : DecreasingGerm α) :
    DecreasingGerm.ofChain g.representative = g := g.representative_spec

theorem dual_round_trip (g : IncreasingGerm α) : g.toDual.toDual = g :=
  IncreasingGerm.toDual_toDual g

#print axioms MutuallyFiniteIncomparability.transfer_finite_trace
#print axioms normalize_finite_cofinal
#print axioms IncreasingEquivalent.trans
#print axioms DecreasingEquivalent.trans
#print axioms IncreasingGerm.ofChain_eq_iff
#print axioms DecreasingGerm.ofChain_eq_iff
#print axioms related_iff_eq
#print axioms chosen_representative_upperBounds

end AharoniKorman.Completion.GermAPI
