import AharoniKorman.Preliminaries.Scattered

/-! A scattered linear order with no two consecutive covers has at most two points.
This avoids a further finite-distance quotient in principal-cut realization. -/

namespace AharoniKorman

open Set

variable {α : Type*} [LinearOrder α]

theorem IsScattered.no_three_of_no_consecutive_covers (h : IsScattered α)
    (hc : ∀ x y z : α, x ⋖ y → y ⋖ z → False)
    {a b c : α} (hab : a < b) (hbc : b < c) : False := by
  classical
  let S : Set α := {x | ∃ y, x ⋖ y}
  have hbetween {x y : S} (hxy : x < y) : ∃ z : S, x < z ∧ z < y := by
    obtain ⟨x', hxx'⟩ := x.2
    have hx'y : x' < y.1 := by
      have hle : x' ≤ y.1 := hxx'.ge_of_gt hxy
      apply lt_of_le_of_ne hle
      intro heq
      obtain ⟨y', hyy'⟩ := y.2
      exact hc x.1 y.1 y' (heq ▸ hxx') hyy'
    obtain ⟨z, z', hx'z, hzz', hz'y, hcov⟩ := h.exists_covBy_between hx'y
    exact ⟨⟨z, z', hcov⟩, hxx'.lt.trans_le hx'z, hzz'.trans_le hz'y⟩
  let : DenselyOrdered S := ⟨fun _ _ hxy => hbetween hxy⟩
  obtain ⟨x, x', hax, hxx', hx'b, hcovx⟩ := h.exists_covBy_between hab
  obtain ⟨y, y', hby, hyy', hy'c, hcovy⟩ := h.exists_covBy_between hbc
  have hxy : x < y := hxx'.trans_le (hx'b.trans hby)
  let : Nontrivial S := ⟨⟨⟨x, x', hcovx⟩, ⟨y, y', hcovy⟩, ne_of_lt hxy⟩⟩
  obtain ⟨e⟩ := Order.embedding_from_countable_to_dense (α := ℚ) (β := S)
  exact h ⟨e.trans (OrderEmbedding.subtype S)⟩

end AharoniKorman
