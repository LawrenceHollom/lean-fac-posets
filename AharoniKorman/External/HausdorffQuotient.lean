import AharoniKorman.Preliminaries.Scattered
import Mathlib.Order.Quotient

namespace AharoniKorman

variable {α : Type*} [LinearOrder α]

/-- The quotient by a partition into convex classes is scattered if the original order is
scattered. Choosing one representative of each class gives a strictly increasing section. -/
theorem IsScattered.quotient (h : IsScattered α) (s : Setoid α)
    [∀ q : Quotient s, Set.OrdConnected (Quotient.mk s ⁻¹' ({q} : Set (Quotient s)))]
    [DecidableRel s.r] : IsScattered (Quotient s) := by
  rintro ⟨e⟩
  have hout : StrictMono (Quotient.out (s := s)) := by
    intro x y hxy
    apply Quotient.lt_of_mk_lt_mk (s := s)
    simpa only [Quotient.out_eq] using hxy
  exact h ⟨e.trans (OrderEmbedding.ofStrictMono _ hout)⟩

end AharoniKorman
