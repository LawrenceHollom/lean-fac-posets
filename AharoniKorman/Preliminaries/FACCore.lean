import AharoniKorman.Preliminaries.FAC
import AharoniKorman.Preliminaries.Relations
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Zorn

/-!
A localization principle for the finite antichain condition.

For any property of subsets holding of the whole poset, there is a region
obtained by imposing finitely many incomparability constraints where the
property holds but imposing one further constraint destroys it. No monotonicity
or finite-union assumption on the property is required.

The region is order convex. This is the combinatorial localization step used
in the informal proofs of rank attainment and minimal top-rank profiles.
-/

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- Points incomparable with every member of `A`. -/
def commonIncomparables (A : Set α) : Set α :=
  {x | ∀ a ∈ A, Incomparable a x}

@[simp] theorem commonIncomparables_empty :
    commonIncomparables (∅ : Set α) = univ := by
  ext x
  simp [commonIncomparables]

@[simp] theorem commonIncomparables_insert (A : Set α) (p : α) :
    commonIncomparables (insert p A) = commonIncomparables A ∩ incomparableSet p := by
  ext x
  simp only [commonIncomparables, mem_ofPred_eq, forall_mem_insert, mem_inter_iff,
    mem_incomparableSet]
  exact and_comm

theorem commonIncomparables_ordConnected (A : Set α) :
    OrdConnected (commonIncomparables A) := by
  constructor
  intro x hx y hy z hz a ha
  exact ⟨fun haz => (hy a ha).1 (haz.trans hz.2),
    fun hza => (hx a ha).2 (hz.1.trans hza)⟩

/-- FAC prevents an endless sequence of new incomparability constraints,
even when the property being preserved is not monotone. -/
theorem IsFAC.exists_commonIncomparables_core (hfac : IsFAC α)
    (Rich : Set α → Prop) (hRich : Rich univ) :
    ∃ A : Set α, IsAntichain (· ≤ ·) A ∧ A.Finite ∧
      Rich (commonIncomparables A) ∧
      ∀ p ∈ commonIncomparables A,
        ¬ Rich (commonIncomparables A ∩ incomparableSet p) := by
  classical
  let S : Set (Set α) := {A | IsAntichain (· ≤ ·) A ∧ Rich (commonIncomparables A)}
  have hEmpty : (∅ : Set α) ∈ S := ⟨IsAntichain.empty, by simpa using hRich⟩
  have hBound : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ B ∈ S, ∀ D ∈ c, D ⊆ B := by
    intro c hcs hc hcn
    have hUnion : IsAntichain (· ≤ ·) (⋃₀ c) := by
      rintro x ⟨B, hBc, hxB⟩ y ⟨D, hDc, hyD⟩ hxy hle
      rcases hc.total hBc hDc with hBD | hDB
      · exact (hcs hDc).1 (hBD hxB) hyD hxy hle
      · exact (hcs hBc).1 hxB (hDB hyD) hxy hle
    obtain ⟨B, hBc, hUB⟩ :=
      hc.directedOn.exists_mem_subset_of_finite_of_subset_sUnion
        hcn (hfac _ hUnion) (Subset.refl _)
    exact ⟨B, hcs hBc, fun D hDc => (subset_sUnion_of_mem hDc).trans hUB⟩
  obtain ⟨A, _, hA⟩ := zorn_subset_nonempty S hBound ∅ hEmpty
  refine ⟨A, hA.1.1, hfac A hA.1.1, hA.1.2, ?_⟩
  intro p hp hNext
  have hInsert : insert p A ∈ S := by
    constructor
    · intro x hx y hy hxy hle
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact hxy rfl
        · exact (hp y hy).2 hle
      · rcases hy with rfl | hy
        · exact (hp x hx).1 hle
        · exact hA.1.1 hx hy hxy hle
    · simpa only [commonIncomparables_insert] using hNext
  have hpA : p ∈ A := hA.2 hInsert (subset_insert p A) (mem_insert p A)
  exact (hp p hpA).1 le_rfl

/-- A convenient convex-region form of the localization principle. -/
theorem IsFAC.exists_convex_core (hfac : IsFAC α)
    (Rich : Set α → Prop) (hRich : Rich univ) :
    ∃ Q : Set α, OrdConnected Q ∧ Rich Q ∧
      ∀ p ∈ Q, ¬ Rich (Q ∩ incomparableSet p) := by
  obtain ⟨A, _, _, hA, hcore⟩ := hfac.exists_commonIncomparables_core Rich hRich
  exact ⟨commonIncomparables A, commonIncomparables_ordConnected A, hA, hcore⟩

end AharoniKorman
