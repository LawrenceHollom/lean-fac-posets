import AharoniKorman.Consolidation.GreedyConsolidation
import AharoniKorman.Final.AtomicHull

namespace AharoniKorman

variable {α : Type*} [PartialOrder α]

/-- The quasifounded case of the maximal-tube theorem. -/
theorem exists_maximalTube_of_quasifounded [Countable α]
    (hfac : IsFAC α) (hscattered : IsScattered α)
    (hqf : IsQuasifounded α) : ∃ T : Set α, IsMaximalTube T := by
  obtain ⟨C, hC⟩ := Consolidation.exists_atomicallyConsolidated hfac hqf
  exact ⟨_, (Consolidation.atomicallyConsolidated_hull_maximalTube
    hfac hscattered hqf.isVacillating C hC).2⟩

end AharoniKorman
