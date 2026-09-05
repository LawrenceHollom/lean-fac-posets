import AharoniKorman.Preliminaries.Chains

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- A nonempty convex subset, used as the codomain object of replacement witnesses. -/
structure NonemptyInterval (α : Type*) [PartialOrder α] where
  carrier : Set α
  nonempty : carrier.Nonempty
  ordConnected : carrier.OrdConnected

instance : SetLike (NonemptyInterval α) α where
  coe I := I.carrier
  coe_injective := by intro I J h; cases I; cases J; cases h; rfl

/-- Convex hull in a partial order, following the manuscript's definition. -/
def convexHull (S : Set α) : Set α := {x | ∃ y ∈ S, ∃ z ∈ S, y ≤ x ∧ x ≤ z}

/-- `I` is an interval in the induced order on `D`.  This differs from ambient
`Set.OrdConnected`: points lying between two members of `I` are required to belong to `I` only
when they also belong to `D`. -/
def IsIntervalIn (I D : Set α) : Prop :=
  I ⊆ D ∧ ∀ ⦃x⦄, x ∈ I → ∀ ⦃y⦄, y ∈ I → x ≤ y →
    ∀ ⦃z⦄, z ∈ D → x ≤ z → z ≤ y → z ∈ I

/-- Convex hull inside an induced suborder. -/
def convexHullIn (D S : Set α) : Set α :=
  {x | x ∈ D ∧ ∃ y ∈ S, ∃ z ∈ S, y ≤ x ∧ x ≤ z}

theorem convexHullIn_subset (D S : Set α) : convexHullIn D S ⊆ D := fun _ hx => hx.1

theorem subset_convexHullIn {D S : Set α} (hSD : S ⊆ D) : S ⊆ convexHullIn D S := by
  intro x hx
  exact ⟨hSD hx, x, hx, x, hx, le_rfl, le_rfl⟩

theorem convexHullIn_interval (D S : Set α) : IsIntervalIn (convexHullIn D S) D := by
  refine ⟨convexHullIn_subset D S, ?_⟩
  rintro x ⟨hxD, a, ha, b, hb, hax, hxb⟩ y ⟨hyD, c, hc, d, hd, hcy, hyd⟩ hxy z hzD hxz hzy
  exact ⟨hzD, a, ha, d, hd, hax.trans hxz, hzy.trans hyd⟩

theorem convexHullIn_eq_self {D S : Set α} (hS : IsIntervalIn S D) :
    convexHullIn D S = S := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxD, a, ha, b, hb, hax, hxb⟩
    exact hS.2 ha hb (hax.trans hxb) hxD hax hxb
  · exact subset_convexHullIn hS.1

end AharoniKorman
