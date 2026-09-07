import AharoniKorman.Preliminaries.FAC
import Mathlib.Order.WellFounded

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- A chain expressed as an omega-sum of infinite co-wellfounded blocks. -/
def IsOmegaSumOfInfiniteCowellfounded (C : Set α) : Prop :=
  ∃ B : ℕ → Set α,
    C = ⋃ n, B n ∧
    (∀ n, (B n).Infinite) ∧
    (∀ n, WellFounded (fun x y : B n => x > y)) ∧
    (∀ ⦃i j : ℕ⦄, i < j → SetStrictLT (B i) (B j))

/-- The paper's forbidden saturated-chain condition, in both order directions. -/
def IsVacillating (α : Type*) [PartialOrder α] : Prop :=
  ∀ C : Set α, IsSaturatedChain C →
    ¬ IsOmegaSumOfInfiniteCowellfounded C ∧
    ¬ @IsOmegaSumOfInfiniteCowellfounded αᵒᵈ inferInstance C

private theorem omegaSum_subtype_image {S : Set α} {C : Set S}
    (hC : IsOmegaSumOfInfiniteCowellfounded C) :
    IsOmegaSumOfInfiniteCowellfounded (Subtype.val '' C : Set α) := by
  classical
  obtain ⟨B, hCB, hBinf, hBwf, hBordered⟩ := hC
  let B' : ℕ → Set α := fun n => Subtype.val '' B n
  refine ⟨B', ?_, ?_, ?_, ?_⟩
  · simp only [B', hCB, Set.image_iUnion]
  · intro n
    exact (hBinf n).image Subtype.val_injective.injOn
  · intro n
    let f : B n → B' n := fun x => ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    exact (hf.wellFounded_iff (fun {_ _} => by rfl)).mp (hBwf n)
  · intro i j hij x hx y hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact hBordered hij hx' hy'

/-- Vacillation is inherited by convex induced subposets. -/
theorem IsVacillating.ordConnected_subtype (h : IsVacillating α) {S : Set α}
    (hS : S.OrdConnected) : IsVacillating S := by
  intro C hC
  let C' : Set α := Subtype.val '' C
  have hC'chain : IsChain (· ≤ ·) C' := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    exact hC.1 hx hy (fun h => hxy (congrArg Subtype.val h))
  have hC'convex : C'.OrdConnected := by
    refine ⟨fun x hx y hy z hz => ?_⟩
    obtain ⟨x', hxC, rfl⟩ := hx
    obtain ⟨y', hyC, rfl⟩ := hy
    have hzS : z ∈ S := hS.out x'.2 y'.2 hz
    let z' : S := ⟨z, hzS⟩
    have hzC : z' ∈ C := hC.2.out hxC hyC hz
    exact ⟨z', hzC, rfl⟩
  have hambient := h C' ⟨hC'chain, hC'convex⟩
  constructor
  · intro hbad
    exact hambient.1 (omegaSum_subtype_image hbad)
  · intro hbad
    letI : PartialOrder αᵒᵈ := inferInstance
    have hlift : @IsOmegaSumOfInfiniteCowellfounded αᵒᵈ inferInstance C' :=
      @omegaSum_subtype_image αᵒᵈ inferInstance (show Set αᵒᵈ from S) C hbad
    exact hambient.2 hlift

end AharoniKorman
