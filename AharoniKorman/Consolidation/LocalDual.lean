import AharoniKorman.Consolidation.BoundaryOrder

/-! Order duality for directional profiles and maximal chains. -/

namespace AharoniKorman.Consolidation

noncomputable section

open Completion

variable {α : Type*} [PartialOrder α]

@[simp] theorem boundaryProfile_dual (X : H α) :
    boundaryProfile (α := αᵒᵈ) X.dual = boundaryProfile X := by
  cases X <;> rfl

def MaximalChains.dual (C : MaximalChains α) : MaximalChains αᵒᵈ :=
  ⟨C.carrier, C.isMaximal.symm⟩

end

end AharoniKorman.Consolidation
