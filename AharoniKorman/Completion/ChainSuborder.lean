import AharoniKorman.Completion

/-! Pulling a saturated representative into an induced suborder containing it.
These constructions retain the representative carrier and its actual germ. -/

namespace AharoniKorman.Completion

open Set

variable {α : Type*} [PartialOrder α]

def SaturatedChain.within (A : SaturatedChain α) {C : Set α}
    (hAC : (A : Set α) ⊆ C) : SaturatedChain C where
  carrier := {x | x.1 ∈ A}
  nonempty := by
    obtain ⟨a, ha⟩ := A.nonempty
    exact ⟨⟨a, hAC ha⟩, ha⟩
  saturated := by
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      exact A.isChain hx hy (fun h => hxy (Subtype.ext h))
    · intro a b x ha hb hax hxb hx
      exact A.saturated.2 ha hb hax hxb
        (fun c hc => hx ⟨c, hAC hc⟩ hc)

@[simp] theorem SaturatedChain.mem_within (A : SaturatedChain α) {C : Set α}
    (hAC : (A : Set α) ⊆ C) (x : C) : x ∈ A.within hAC ↔ x.1 ∈ A := Iff.rfl

def IncreasingChain.within (A : IncreasingChain α) {C : Set α}
    (hAC : (A.1 : Set α) ⊆ C) : IncreasingChain C :=
  ⟨A.1.within hAC, by
    rintro ⟨m, hm⟩
    obtain ⟨a, hma⟩ := A.2.exists_gt ⟨m.1.1, m.2⟩
    exact hma.not_ge (hm ⟨⟨a.1, hAC a.2⟩, a.2⟩)⟩

def DecreasingChain.within (A : DecreasingChain α) {C : Set α}
    (hAC : (A.1 : Set α) ⊆ C) : DecreasingChain C :=
  ⟨A.1.within hAC, by
    rintro ⟨m, hm⟩
    obtain ⟨a, ham⟩ := A.2.exists_lt ⟨m.1.1, m.2⟩
    exact ham.not_ge (hm ⟨⟨a.1, hAC a.2⟩, a.2⟩)⟩

theorem SaturatedChain.map_within (A : SaturatedChain α) {C : Set α}
    (hAC : (A : Set α) ⊆ C)
    (hC : SaturationPreserving (α := C) (β := α) (OrderEmbedding.subtype C)) :
    (A.within hAC).map (OrderEmbedding.subtype C) hC = A := by
  apply SetLike.coe_injective
  ext a
  change (∃ x : C, x.1 ∈ A ∧ x.1 = a) ↔ a ∈ A
  exact ⟨fun ⟨x, hx, hxa⟩ => hxa ▸ hx, fun ha => ⟨⟨a, hAC ha⟩, ha, rfl⟩⟩

theorem IncreasingChain.map_within (A : IncreasingChain α) {C : Set α}
    (hAC : (A.1 : Set α) ⊆ C)
    (hC : SaturationPreserving (α := C) (β := α) (OrderEmbedding.subtype C)) :
    (A.within hAC).map (OrderEmbedding.subtype C) hC = A := by
  apply Subtype.ext
  exact A.1.map_within hAC hC

theorem DecreasingChain.map_within (A : DecreasingChain α) {C : Set α}
    (hAC : (A.1 : Set α) ⊆ C)
    (hC : SaturationPreserving (α := C) (β := α) (OrderEmbedding.subtype C)) :
    (A.within hAC).map (OrderEmbedding.subtype C) hC = A := by
  apply Subtype.ext
  rw [DecreasingChain.map_val]
  exact A.1.map_within hAC hC

end AharoniKorman.Completion
