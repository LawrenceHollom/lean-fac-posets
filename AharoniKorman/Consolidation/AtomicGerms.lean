import AharoniKorman.Consolidation.Genuine

/-! Atomic germs represented by saturated omega rays and their order duals. -/

namespace AharoniKorman.Consolidation

open Set Completion

variable {α : Type*} [PartialOrder α]

/-- A saturated increasing representative of order type omega. -/
def IsOmegaRepresentative (C : IncreasingChain α) : Prop :=
  ∀ c : C.1, (Set.Iic c).Finite

/-- The genuine positive atomic germs used in the proof. -/
def IsPositiveAtom (g : IncreasingGerm α) : Prop :=
  ∃ C : IncreasingChain α, g.Represents C ∧ IsOmegaRepresentative C

/-- Negative atomicity is positive atomicity in the order dual. -/
def IsNegativeAtom (g : DecreasingGerm α) : Prop :=
  @IsPositiveAtom αᵒᵈ inferInstance g.toDual

def IsAtomicGerm : H α → Prop
  | .increasing g => IsPositiveAtom g
  | .decreasing g => IsNegativeAtom g
  | _ => False

def atomicBoundaries (C : Set α) : Set (H α) := boundaries C ∩ {X | IsAtomicGerm X}

/-- A same-sign boundary improves a source if its directional profile is smaller. -/
def GermImproves (b a : H α) : Prop :=
  b.direction = a.direction ∧ boundaryProfile b ⊆ boundaryProfile a

theorem GermImproves.refl (a : H α) : GermImproves a a := ⟨rfl, Subset.rfl⟩

theorem GermImproves.trans {a b c : H α} (hcb : GermImproves c b) (hba : GermImproves b a) :
    GermImproves c a := ⟨hcb.1.trans hba.1, hcb.2.trans hba.2⟩

private theorem finite_trace_of_omega (D : IncreasingChain α)
    (hD : IsOmegaRepresentative D) {x : α} (hx : ∃ d : D.1, x < d.1) :
    (incomparabilityTrace D.1 x).Finite := by
  obtain ⟨d, hxd⟩ := hx
  apply (hD d).subset
  intro y hy
  change y ≤ d
  by_contra hyd
  have hdy : d ≤ y := le_of_not_ge hyd
  exact hy.not_ge (hxd.le.trans hdy)

/-- Equal predecessor cuts identify positive atoms, using finite traces of
omega representatives. No scatteredness or vacillation is needed for this step. -/
theorem positiveAtom_eq_of_lowerProfile_eq {g h : IncreasingGerm α}
    (hg : IsPositiveAtom g) (hh : IsPositiveAtom h)
    (heq : g.lowerProfile = h.lowerProfile) : g = h := by
  obtain ⟨C, hC, hComega⟩ := hg
  obtain ⟨D, hD, hDomega⟩ := hh
  rw [← hC, ← hD] at heq ⊢
  obtain ⟨hDC, hCD⟩ := (IncreasingGerm.bicomparable_ofChain_iff C D).1 heq
  apply IncreasingGerm.ofChain_eq_iff.2
  apply (IncreasingEquivalent.iff_finite_cofinal C D).2
  refine ⟨C.1, D.1, ⟨Subset.rfl, fun {_ _} _ hy _ => hy⟩,
    ⟨Subset.rfl, fun {_ _} _ hy _ => hy⟩, hCD, hDC, ?_, ?_⟩
  · intro d
    exact finite_trace_of_omega C hComega (hDC d)
  · intro c
    exact finite_trace_of_omega D hDomega (hCD c)

/-- The corresponding successor-cut assertion for negative atoms. -/
theorem negativeAtom_eq_of_upperProfile_eq {g h : DecreasingGerm α}
    (hg : IsNegativeAtom g) (hh : IsNegativeAtom h)
    (heq : g.upperProfile = h.upperProfile) : g = h :=
  positiveAtom_eq_of_lowerProfile_eq (α := αᵒᵈ) hg hh heq

/-- Paper `lem:atomic-consolidation-partial`, antisymmetry on omega atoms. -/
theorem atomic_eq_of_mutual_improvement {a b : H α}
    (ha : IsAtomicGerm a) (hb : IsAtomicGerm b)
    (hab : GermImproves a b) (hba : GermImproves b a) : a = b := by
  have hd := hab.1
  have hp := Subset.antisymm hab.2 hba.2
  cases a <;> cases b <;> simp_all [IsAtomicGerm, GermImproves, H.direction, boundaryProfile]
  · exact positiveAtom_eq_of_lowerProfile_eq ha hb hp
  · exact negativeAtom_eq_of_upperProfile_eq ha hb hp

end AharoniKorman.Consolidation
