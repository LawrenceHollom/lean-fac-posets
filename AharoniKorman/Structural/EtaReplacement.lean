import AharoniKorman.Structural.EtaChains
import AharoniKorman.Preliminaries.FAC
import Mathlib.Order.Zorn

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- Witness data for replacing points of one eta-maximal chain by singleton or eta intervals. -/
structure EtaReplacement (C D : Set α) where
  source : IsEtaMaximalChain C
  target : IsEtaMaximalChain D
  image : C → Set α
  image_subset : ∀ x, image x ⊆ D
  image_nonempty : ∀ x, (image x).Nonempty
  image_shape : ∀ x, image x = {x.1} ∨ IsEtaChain (image x)
  compatible : ∀ x y : C, x.1 < y.1 → SetStrictLT (image x) (image y)

def EtaReplacement.Trivial {C D : Set α} (f : EtaReplacement C D) : Prop :=
  ∀ x, f.image x = {x.1}

/-- A chain admitting no nontrivial eta replacement. -/
def IsEtaStronglyMaximal (C : Set α) : Prop :=
  IsEtaMaximalChain C ∧
    ∀ (D : Set α) (f : EtaReplacement C D), f.Trivial

theorem exists_etaStronglyMaximal [Countable α] (hfac : IsFAC α)
    (hns : ¬ IsScattered α) : ∃ C : Set α, IsEtaStronglyMaximal C := by
  sorry

end AharoniKorman
