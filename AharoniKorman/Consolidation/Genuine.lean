import AharoniKorman.Completion

/-! The nonprincipal points witnessed by a chain and their directional profiles. -/

namespace AharoniKorman.Consolidation

noncomputable section

open Set Completion

variable {α : Type*} [PartialOrder α]

/-- The genuine nonprincipal points represented by subchains of `C`. -/
def boundaries (C : Set α) : Set (H α) :=
  {X | (∃ A : IncreasingChain α, (A.1 : Set α) ⊆ C ∧
          X = H.increasing (IncreasingGerm.ofChain A)) ∨
       (∃ A : DecreasingChain α, (A.1 : Set α) ⊆ C ∧
          X = H.decreasing (DecreasingGerm.ofChain A))}

abbrev Boundary (C : Set α) := boundaries C

theorem boundaries_mono {C D : Set α} (h : C ⊆ D) : boundaries C ⊆ boundaries D := by
  rintro X (⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩)
  · exact Or.inl ⟨A, hA.trans h, rfl⟩
  · exact Or.inr ⟨A, hA.trans h, rfl⟩

@[simp] theorem bot_not_mem_boundaries (C : Set α) : (⊥ : H α) ∉ boundaries C := by
  rintro (⟨A, _, h⟩ | ⟨A, _, h⟩) <;> cases h

@[simp] theorem top_not_mem_boundaries (C : Set α) : (⊤ : H α) ∉ boundaries C := by
  rintro (⟨A, _, h⟩ | ⟨A, _, h⟩) <;> cases h

@[simp] theorem principal_not_mem_boundaries (C : Set α) (p : α) :
    H.principal p ∉ boundaries C := by
  rintro (⟨A, _, h⟩ | ⟨A, _, h⟩) <;> cases h

/-- The lower profile of a positive point or upper profile of a negative point.
The other constructors are irrelevant on `Boundary C`. -/
def boundaryProfile : H α → Set α
  | .increasing g => g.lowerProfile
  | .decreasing g => g.upperProfile
  | _ => ∅

/-- Bundled inclusion-maximal chains. -/
structure MaximalChains (α : Type*) [PartialOrder α] where
  carrier : Set α
  isMaximal : IsMaximalChain carrier

end

end AharoniKorman.Consolidation
