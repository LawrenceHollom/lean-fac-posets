import AharoniKorman.Completion.ChainSuborder
import AharoniKorman.Preliminaries.Vacillating

/-! Vacillation transfers through embeddings preserving saturation. -/

namespace AharoniKorman

open Set Completion

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

theorem IsVacillating.orderDual (h : IsVacillating α) : IsVacillating αᵒᵈ := by
  intro C hC
  have h' := h C hC.dual
  exact ⟨h'.2, h'.1⟩

theorem IsOmegaSumOfInfiniteCowellfounded.image {C : Set α}
    (h : IsOmegaSumOfInfiniteCowellfounded C) (e : α ↪o β) :
    IsOmegaSumOfInfiniteCowellfounded (e '' C) := by
  obtain ⟨B, hCB, hBinf, hBwf, hBorder⟩ := h
  refine ⟨fun n => e '' B n, ?_, ?_, ?_, ?_⟩
  · simp only [hCB, Set.image_iUnion]
  · intro n
    exact (hBinf n).image e.injective.injOn
  · intro n
    let f : B n → e '' B n := fun x => ⟨e x.1, x.1, x.2, rfl⟩
    have hf : Function.Surjective f := by
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    exact (hf.wellFounded_iff (fun {_ _} => e.lt_iff_lt.symm)).mp (hBwf n)
  · intro i j hij x hx y hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact e.strictMono (hBorder hij hx' hy')

theorem IsVacillating.of_saturationPreserving (hβ : IsVacillating β)
    (e : α ↪o β) (he : SaturationPreserving e) : IsVacillating α := by
  intro C hC
  have h := hβ (e '' C) (he C hC)
  constructor
  · intro hbad
    exact h.1 (hbad.image e)
  · intro hbad
    exact h.2 (hbad.image e.dual)

/-- Unlike arbitrary induced suborders, saturated subchains preserve vacillation. -/
theorem IsVacillating.saturated_subtype (h : IsVacillating α) {C : Set α}
    (hC : IsSaturatedChain C) : IsVacillating C :=
  h.of_saturationPreserving (OrderEmbedding.subtype C)
    (saturationPreserving_subtype_of_saturated hC)

end AharoniKorman
