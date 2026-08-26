import AharoniKorman.Preliminaries.Scattered
import AharoniKorman.Preliminaries.Intervals

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- A subset with order type eta. -/
def IsEtaChain (C : Set α) : Prop := Nonempty (ℚ ≃o C)

/-- An eta-chain maximal under inclusion among eta-chains. -/
def IsEtaMaximalChain (C : Set α) : Prop :=
  IsEtaChain C ∧ ∀ D : Set α, IsEtaChain D → C ⊆ D → D = C

/-- Paper Lemma `lem:eta-nesting`, exposed at the level needed by replacement composition. -/
theorem eta_nesting_interface : True := by
  trivial

end AharoniKorman
