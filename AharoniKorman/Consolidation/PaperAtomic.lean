import AharoniKorman.Consolidation.OmegaExistence
import AharoniKorman.Consolidation.BoundaryOrder
import Mathlib.Order.SuccPred.LinearLocallyFinite

/-! The paper's definition of atomicity before restricting to vacillating posets. -/

namespace AharoniKorman.Consolidation

open Set Completion

variable {α : Type*} [PartialOrder α]

/-- Paper `def:atomic`, positive sign. -/
def IsAtomicIncreasing (g : IncreasingGerm α) : Prop :=
  ∃ A : IncreasingChain α, g.Represents A ∧ ¬Nonempty (WithTop ℕ ↪o A.1)

/-- Paper `def:atomic`, negative sign. -/
def IsAtomicDecreasing (g : DecreasingGerm α) : Prop :=
  IsAtomicIncreasing (α := αᵒᵈ) g.toDual

theorem IsOmegaRepresentative.no_omegaSucc {A : IncreasingChain α}
    (hA : IsOmegaRepresentative A) : ¬Nonempty (WithTop ℕ ↪o A.1) := by
  rintro ⟨e⟩
  have hinj : Function.Injective (fun n : ℕ => e n) :=
    e.injective.comp (fun _ _ h => WithTop.coe_inj.1 h)
  exact (Set.infinite_range_of_injective hinj) ((hA (e ⊤)).subset (by
    rintro _ ⟨n, rfl⟩
    exact e.monotone le_top))

theorem IsPositiveAtom.isAtomicIncreasing {g : IncreasingGerm α} (hg : IsPositiveAtom g) :
    IsAtomicIncreasing g := by
  obtain ⟨A, hAg, hA⟩ := hg
  exact ⟨A, hAg, hA.no_omegaSucc⟩

theorem IsOmegaRepresentative.exists_orderIsoNat {A : IncreasingChain α}
    (hA : IsOmegaRepresentative A) : Nonempty (A.1 ≃o ℕ) := by
  classical
  have hne : Nonempty A.1 := A.1.nonempty.to_subtype
  letI : NoMaxOrder A.1 := ⟨A.2.exists_gt⟩
  letI : LocallyFiniteOrder A.1 := LocallyFiniteOrder.ofIcc _
    (fun a b => ((hA b).subset Set.Icc_subset_Iic_self).toFinset)
    (fun a b x => Set.Finite.mem_toFinset _)
  obtain ⟨p⟩ := hne
  obtain ⟨a, ha, hmin⟩ := (hA p).exists_minimal ⟨p, le_rfl⟩
  letI : Bot A.1 := ⟨a⟩
  letI : OrderBot A.1 := ⟨fun b => (le_total a b).elim id (fun h => hmin (h.trans ha) h)⟩
  letI : SuccOrder A.1 := LinearLocallyFiniteOrder.succOrder _
  letI : PredOrder A.1 := LinearLocallyFiniteOrder.predOrder _
  exact ⟨orderIsoNatOfLinearSuccPredArch⟩

/-- The omega-tail conclusion of `lem:atomic-is-omega`. The forbidden block
construction used by `exists_finite_initial_tail` works without scatteredness. -/
theorem IsAtomicIncreasing.isPositiveAtom (hvac : IsVacillating α)
    {g : IncreasingGerm α} (hg : IsAtomicIncreasing g) : IsPositiveAtom g := by
  obtain ⟨A, hAg, hA⟩ := hg
  letI : Nonempty A.1 := A.1.nonempty.to_subtype
  letI : NoMaxOrder A.1 := ⟨A.2.exists_gt⟩
  obtain ⟨a, ha⟩ := exists_finite_initial_tail (hvac.saturated_subtype A.1.saturated) hA
  let B : IncreasingChain α := ⟨A.1.tail a, A.1.tail_noTop a A.2⟩
  have hB : IsOmegaRepresentative B := by
    intro b
    let b' : A.1 := ⟨b.1, b.2.1⟩
    let inc : B.1 → A.1 := fun x => ⟨x.1, x.2.1⟩
    have hinc : Function.Injective inc := fun _ _ h => Subtype.ext (congrArg (fun y : A.1 => y.1) h)
    apply ((ha b').preimage hinc.injOn).subset
    intro x hx
    exact ⟨x.2.2, hx⟩
  refine ⟨B, Eq.trans ?_ hAg, hB⟩
  apply IncreasingGerm.ofChain_eq_iff.2
  exact ⟨B.1, B.1, ⟨Subset.rfl, fun _ _ _ hy _ => hy⟩, A.1.tail_final a,
    MutuallyFiniteIncomparability.refl _⟩

theorem isAtomicIncreasing_iff_isPositiveAtom (hvac : IsVacillating α) (g : IncreasingGerm α) :
    IsAtomicIncreasing g ↔ IsPositiveAtom g :=
  ⟨IsAtomicIncreasing.isPositiveAtom hvac, IsPositiveAtom.isAtomicIncreasing⟩

theorem isAtomicDecreasing_iff_isNegativeAtom (hvac : IsVacillating α) (g : DecreasingGerm α) :
    IsAtomicDecreasing g ↔ IsNegativeAtom g :=
  isAtomicIncreasing_iff_isPositiveAtom hvac.orderDual g.toDual

def IsPaperAtomicGerm : H α → Prop
  | .increasing g => IsAtomicIncreasing g
  | .decreasing g => IsAtomicDecreasing g
  | _ => False

/-- The exact atomic profile in `def:atomic`, also for nonvacillating posets. -/
def paperAtomicBoundaries (C : Set α) : Set (H α) := boundaries C ∩ {X | IsPaperAtomicGerm X}

theorem paperAtomicBoundaries_eq (hvac : IsVacillating α) (C : Set α) :
    paperAtomicBoundaries C = atomicBoundaries C := by
  ext X
  change _ ∧ IsPaperAtomicGerm X ↔ _ ∧ IsAtomicGerm X
  refine and_congr_right' ?_
  cases X with
  | increasing g => exact isAtomicIncreasing_iff_isPositiveAtom hvac g
  | decreasing g => exact isAtomicDecreasing_iff_isNegativeAtom hvac g
  | principal _ | bottom | top => exact Iff.rfl

theorem IsAtomicIncreasing.exists_omega_representative (hvac : IsVacillating α)
    {g : IncreasingGerm α} (hg : IsAtomicIncreasing g) :
    ∃ A : IncreasingChain α, g.Represents A ∧ Nonempty (A.1 ≃o ℕ) := by
  obtain ⟨A, hAg, hA⟩ := hg.isPositiveAtom hvac
  exact ⟨A, hAg, hA.exists_orderIsoNat⟩

/-- Paper `lem:exists-atomic`, applied inside a given saturated chain. -/
theorem exists_atomicIncreasing_of_chain (hscattered : IsScattered α)
    (C : SaturatedChain α) (homega : Nonempty (ℕ ↪o C)) :
    ∃ g : IncreasingGerm α, H.increasing g ∈ boundaries C ∧ IsAtomicIncreasing g := by
  obtain ⟨S, hSsat, hSne, hSup, _, hSno⟩ :=
    External.exists_saturated_omega_no_omegaSucc (hscattered.subtype (C : Set α)) homega
  let A : IncreasingChain C := ⟨⟨S, hSne, hSsat⟩, by
    rintro ⟨m, hm⟩
    obtain ⟨p, hp, hmp⟩ := hSup m.1 m.2
    exact hmp.not_ge (hm ⟨p, hp⟩)⟩
  let e : C ↪o α := OrderEmbedding.subtype (C : Set α)
  have he : SaturationPreserving e := saturationPreserving_subtype_of_saturated C.saturated
  let B := A.map e he
  have hBC : (B.1 : Set α) ⊆ C := by
    rintro _ ⟨c, _, rfl⟩
    exact c.2
  refine ⟨IncreasingGerm.ofChain B, Or.inl ⟨B, hBC, rfl⟩, B, rfl, ?_⟩
  rintro ⟨f⟩
  exact hSno ⟨f.trans (A.1.mapOrderIso e he).symm.toOrderEmbedding⟩

/-- Paper `lem:exists-atomic`, in the ambient poset. -/
theorem exists_atomicIncreasing (hscattered : IsScattered α) (homega : Nonempty (ℕ ↪o α)) :
    ∃ g : IncreasingGerm α, IsAtomicIncreasing g := by
  obtain ⟨e⟩ := homega
  have he : IsChain (· ≤ ·) (range e) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact (le_total i j).imp (fun h => e.monotone h) (fun h => e.monotone h)
  obtain ⟨C, hC, hsub⟩ := he.exists_maxChain
  let D : SaturatedChain α := ⟨C, ⟨e 0, hsub (mem_range_self 0)⟩,
    (MaximalChains.mk C hC).isSaturated⟩
  have hD : Nonempty (ℕ ↪o D) := ⟨OrderEmbedding.ofStrictMono
    (fun n => ⟨e n, hsub (mem_range_self n)⟩) e.strictMono⟩
  obtain ⟨g, _, hg⟩ := exists_atomicIncreasing_of_chain hscattered D hD
  exact ⟨g, hg⟩

end AharoniKorman.Consolidation
