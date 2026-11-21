import AharoniKorman.Consolidation.LocalDual
import AharoniKorman.Consolidation.PaperAtomic

/-! The consolidation relation on signed atomic profiles in vacillating posets. -/

namespace AharoniKorman.Consolidation

noncomputable section

open Set Completion

variable {α : Type*} [PartialOrder α]

abbrev AtomProfile (C : Set α) := atomicBoundaries C

/-- Witness data of `def:cofinal-comparability`, given the two signed atom sets. -/
structure ConsolidationWitness (A B : Set (H α)) where
  embedding : A ↪o B
  direction : ∀ X, (embedding X).1.direction = X.1.direction
  profile : ∀ X, boundaryProfile (embedding X).1 ⊆ boundaryProfile X.1

abbrev AtomicWitness (C D : Set α) := ConsolidationWitness (atomicBoundaries C) (atomicBoundaries D)

abbrev PaperAtomicWitness (C D : Set α) :=
  ConsolidationWitness (paperAtomicBoundaries C) (paperAtomicBoundaries D)

def AtomicallyConsolidates (C D : Set α) : Prop := Nonempty (AtomicWitness C D)

/-- Paper `def:consolidated`, using omega rays for the vacillating case. -/
def IsAtomicallyConsolidated (C : Set α) : Prop :=
  ∀ D : Set α, IsSaturatedChain D → AtomicallyConsolidates C D →
    atomicBoundaries D = atomicBoundaries C

def IsPaperAtomicallyConsolidated (C : Set α) : Prop :=
  ∀ D : Set α, IsSaturatedChain D → Nonempty (PaperAtomicWitness C D) →
    paperAtomicBoundaries D = paperAtomicBoundaries C

theorem isPaperAtomicallyConsolidated_iff (hvac : IsVacillating α) (C : Set α) :
    IsPaperAtomicallyConsolidated C ↔ IsAtomicallyConsolidated C := by
  simp only [IsPaperAtomicallyConsolidated, IsAtomicallyConsolidated, PaperAtomicWitness,
    AtomicallyConsolidates, AtomicWitness, paperAtomicBoundaries_eq hvac]

namespace AtomicWitness

def refl (C : Set α) : AtomicWitness C C where
  embedding := (OrderIso.refl _).toOrderEmbedding
  direction _ := rfl
  profile _ := Subset.rfl

def comp {C D E : Set α} (g : AtomicWitness D E) (f : AtomicWitness C D) :
    AtomicWitness C E where
  embedding := f.embedding.trans g.embedding
  direction X := (g.direction (f.embedding X)).trans (f.direction X)
  profile X := (g.profile (f.embedding X)).trans (f.profile X)

theorem improves {C D : Set α} (f : AtomicWitness C D) (X : AtomProfile C) :
    GermImproves (f.embedding X).1 X.1 := ⟨f.direction X, f.profile X⟩

theorem atomic_dual_mem {C : Set α} {X : H α} (hX : X ∈ atomicBoundaries C) :
    X.dual ∈ atomicBoundaries (α := αᵒᵈ) C := by
  refine ⟨boundary_dual_mem (α := α) hX.1, ?_⟩
  cases X with
  | increasing g => exact hX.2
  | decreasing g => exact hX.2
  | principal _ | bottom | top => exact hX.2.elim

private def atomDualOrderIso (C : Set α) : (AtomProfile C)ᵒᵈ ≃o AtomProfile (α := αᵒᵈ) C where
  toFun X := ⟨H.dual (α := α) X.1, atomic_dual_mem (α := α) X.2⟩
  invFun X := ⟨H.dual (α := αᵒᵈ) X.1, atomic_dual_mem (α := αᵒᵈ) X.2⟩
  left_inv X := Subtype.ext (H.dual_dual (α := α) X.1)
  right_inv X := Subtype.ext (H.dual_dual (α := αᵒᵈ) X.1)
  map_rel_iff' := fun {X Y} => H.dual_le_dual X.1 Y.1

def dual {C D : Set α} (f : AtomicWitness C D) : AtomicWitness (α := αᵒᵈ) C D where
  embedding := ((atomDualOrderIso C).symm.toOrderEmbedding.trans f.embedding.dual).trans
    (atomDualOrderIso D).toOrderEmbedding
  direction X := by
    let Y : AtomProfile C := ⟨H.dual (α := αᵒᵈ) X.1, atomic_dual_mem (α := αᵒᵈ) X.2⟩
    change H.direction (α := αᵒᵈ) (H.dual (α := α) (f.embedding Y).1) = X.1.direction
    rw [H.direction_dual, f.direction, ← H.direction_dual]
    exact congrArg H.direction (H.dual_dual (α := αᵒᵈ) X.1)
  profile X := by
    let Y : AtomProfile C := ⟨H.dual (α := αᵒᵈ) X.1, atomic_dual_mem (α := αᵒᵈ) X.2⟩
    change boundaryProfile (α := αᵒᵈ) (H.dual (α := α) (f.embedding Y).1) ⊆ boundaryProfile X.1
    exact (boundaryProfile_dual (f.embedding Y).1).subset.trans
      ((f.profile Y).trans (boundaryProfile_dual (α := αᵒᵈ) X.1).subset)

@[simp] theorem dual_apply {C D : Set α} (f : AtomicWitness C D) (X : AtomProfile C) :
    (f.dual.embedding ⟨X.1.dual, atomic_dual_mem (α := α) X.2⟩).1 = (f.embedding X).1.dual := by
  suffices h : (⟨H.dual (α := αᵒᵈ) (H.dual (α := α) X.1),
    atomic_dual_mem (α := αᵒᵈ) (atomic_dual_mem (α := α) X.2)⟩ : AtomProfile C) = X by
    exact congrArg (fun Y : AtomProfile C => (f.embedding Y).1.dual) h
  exact Subtype.ext (H.dual_dual X.1)

end AtomicWitness

theorem atomicallyConsolidates_refl (C : Set α) : AtomicallyConsolidates C C :=
  ⟨AtomicWitness.refl C⟩

/-- Paper `lem:chain-consolidation-transitive`. -/
theorem AtomicallyConsolidates.trans {C D E : Set α}
    (hCD : AtomicallyConsolidates C D) (hDE : AtomicallyConsolidates D E) :
    AtomicallyConsolidates C E := by
  obtain ⟨f⟩ := hCD
  obtain ⟨g⟩ := hDE
  exact ⟨g.comp f⟩

theorem atomicallyConsolidates_of_profile_eq {C D : Set α}
    (h : atomicBoundaries C = atomicBoundaries D) : AtomicallyConsolidates C D := by
  let e : AtomProfile C ↪o AtomProfile D :=
    ⟨⟨fun X => ⟨X.1, (show X.1 ∈ atomicBoundaries D from h ▸ X.2)⟩,
      fun _ _ heq => Subtype.ext (congrArg (fun X : AtomProfile D => X.1) heq)⟩,
      Iff.rfl⟩
  exact ⟨⟨e, fun _ => rfl, fun _ => Subset.rfl⟩⟩

end

end AharoniKorman.Consolidation
