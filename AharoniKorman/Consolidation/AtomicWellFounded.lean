import AharoniKorman.Consolidation.AtomicDescent
import AharoniKorman.Tube.Quasifounded

/-! Atomic consolidation is well founded in a quasifounded FAC poset. -/

namespace AharoniKorman.Consolidation

open Set Completion Completion.H

variable {α : Type*} [PartialOrder α]

abbrev PositiveAtom (α : Type*) [PartialOrder α] := {g : IncreasingGerm α // IsPositiveAtom g}

abbrev NegativeAtom (α : Type*) [PartialOrder α] := {g : DecreasingGerm α // IsNegativeAtom g}

/-- Paper `cor:consolidation-well-founded`, positive sign. The antichain
selection lemma and a Ramsey subsequence turn any descent into a domination descent. -/
theorem positive_consolidation_wellFounded (hfac : IsFAC α) (hq : IsQuasifounded α) :
    WellFounded (fun g h : PositiveAtom α => g.1.lowerProfile ⊂ h.1.lowerProfile) := by
  by_contra hwf
  rw [wellFounded_iff_isEmpty_descending_chain, not_isEmpty_iff] at hwf
  obtain ⟨g, hg⟩ := hwf
  have hcuts : StrictAnti (fun n => (g n).1.lowerProfile) := strictAnti_nat_of_succ_lt hg
  obtain ⟨e, he⟩ := exists_strictAnti_subsequence_of_positive_atomic_cut_descent hfac
    (fun n => (g n).1) (fun n => (g n).2) hcuts
  let f (n : ℕ) : NPlus α := ⟨H.increasing (g (e n)).1, rfl⟩
  have hf (n : ℕ) : f (n+1) < f n := he (Nat.lt_succ_self n)
  exact (wellFounded_iff_isEmpty_descending_chain.1 hq.1).false ⟨f, hf⟩

/-- Paper `cor:consolidation-well-founded`, negative sign. -/
theorem negative_consolidation_wellFounded (hfac : IsFAC α) (hq : IsQuasifounded α) :
    WellFounded (fun g h : NegativeAtom α => g.1.upperProfile ⊂ h.1.upperProfile) := by
  let toDual : NegativeAtom α → PositiveAtom αᵒᵈ := fun g => ⟨g.1.toDual, g.2⟩
  exact InvImage.wf toDual (positive_consolidation_wellFounded hfac.orderDual hq.orderDual)

end AharoniKorman.Consolidation
