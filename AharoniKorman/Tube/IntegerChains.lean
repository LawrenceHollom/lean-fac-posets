import AharoniKorman.Completion.Embedding
import Mathlib.Data.Int.Interval

/-! Saturated integer chains and their convex hulls. -/

namespace AharoniKorman.Illfounded

open Set Completion

variable {α : Type*} [PartialOrder α]

/-- A copy of the integers saturated in the ambient poset, contained in `S`. -/
def HasSaturatedZeta (S : Set α) : Prop :=
  ∃ e : ℤ ↪o α, range e ⊆ S ∧ IsSaturatedChain (range e)

theorem HasSaturatedZeta.mono {S T : Set α} (h : HasSaturatedZeta S)
    (hST : S ⊆ T) : HasSaturatedZeta T := by
  obtain ⟨e, he, hs⟩ := h
  exact ⟨e, he.trans hST, hs⟩

theorem not_hasSaturatedZeta_singleton (a : α) : ¬HasSaturatedZeta ({a} : Set α) := by
  rintro ⟨e, he, _⟩
  have h0 : e 0 = a := he ⟨0, rfl⟩
  have h1 : e 1 = a := he ⟨1, rfl⟩
  have : (0 : ℤ) = 1 := e.injective (h0.trans h1.symm)
  omega

theorem convexHull_ordConnected (C : Set α) : OrdConnected (convexHull C) := by
  constructor
  rintro x ⟨a, ha, b, hb, hax, hxb⟩ y ⟨c, hc, d, hd, hcy, hyd⟩ z hz
  exact ⟨a, ha, d, hd, hax.trans hz.1, hz.2.trans hyd⟩

theorem convexHull_subset_of_ordConnected {C Q : Set α} (hQ : OrdConnected Q)
    (hCQ : C ⊆ Q) : convexHull C ⊆ Q := by
  rintro x ⟨a, ha, b, hb, hax, hxb⟩
  exact hQ.out (hCQ ha) (hCQ hb) ⟨hax, hxb⟩

/-- The convex hull of an integer chain has neither minimal nor maximal points. -/
theorem zetaHull_no_endpoints (e : ℤ ↪o α) :
    (convexHull (range e)).Nonempty ∧
    (∀ x ∈ convexHull (range e), ∃ y ∈ convexHull (range e), y < x) ∧
    (∀ x ∈ convexHull (range e), ∃ y ∈ convexHull (range e), x < y) := by
  have hmem (i : ℤ) : e i ∈ convexHull (range e) :=
    ⟨e i, ⟨i, rfl⟩, e i, ⟨i, rfl⟩, le_rfl, le_rfl⟩
  refine ⟨⟨e 0, hmem 0⟩, ?_, ?_⟩
  · rintro x ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, hix, _⟩
    exact ⟨e (i - 1), hmem _, (e.strictMono (by omega)).trans_le hix⟩
  · rintro x ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, _, hxj⟩
    exact ⟨e (j + 1), hmem _, hxj.trans_lt (e.strictMono (by omega))⟩

/-- Saturation gives the finite cover of each bounded integer interval. -/
theorem zeta_interval_cover (e : ℤ ↪o α) (he : IsSaturatedChain (range e))
    (m n : ℤ) {x : α} (hx : x ∈ Icc (e m) (e n)) :
    ∃ i ∈ Finset.Icc m n, x = e i ∨ Incomparable (e i) x := by
  classical
  by_contra! h
  have hcomp (i : ℤ) : x ≤ e i ∨ e i ≤ x := by
    by_cases hmi : i < m
    · exact Or.inr ((e.monotone hmi.le).trans hx.1)
    by_cases hni : n < i
    · exact Or.inl (hx.2.trans (e.monotone hni.le))
    have hi : i ∈ Finset.Icc m n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hh := (h i hi).2
    simp only [Incomparable, IncompRel, not_and_or, not_not] at hh
    exact hh.symm
  have hxC : x ∈ range e := he.2 ⟨m, rfl⟩ ⟨n, rfl⟩ hx.1 hx.2 (by
    rintro _ ⟨i, rfl⟩
    exact hcomp i)
  obtain ⟨i, rfl⟩ := hxC
  exact (h i (Finset.mem_Icc.2 ⟨e.le_iff_le.1 hx.1, e.le_iff_le.1 hx.2⟩)).1 rfl

theorem incomparableSet_ordConnected (p : α) : OrdConnected (incomparableSet p) := by
  constructor
  intro x hx y hy z hz
  exact ⟨fun hpz => hy.1 (hpz.trans hz.2), fun hzp => hx.2 (hz.1.trans hzp)⟩

/-- A convex integer range in the induced order on a saturated chain
is still saturated in the ambient partial order. -/
theorem hasSaturatedZeta_of_convex_int_in_subtype {C : Set α}
    (hC : IsSaturatedChain C) (e : ℤ ↪o C) (he : OrdConnected (range e)) :
    HasSaturatedZeta C := by
  let f : ℤ ↪o α := e.trans (OrderEmbedding.subtype C)
  have hrange : range f = Subtype.val '' range e := by
    ext x
    exact ⟨fun ⟨n, hn⟩ => ⟨e n, ⟨n, rfl⟩, hn⟩,
      fun ⟨y, ⟨n, hn⟩, hy⟩ => ⟨n, by
        change (e n).val = x
        simpa only [← hn] using hy⟩⟩
  have hsat : IsSaturatedChain (range e) :=
    IsSaturatedChain.of_ordConnected e.monotone.isChain_range he
  refine ⟨f, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (e n).2
  · rw [hrange]
    exact saturationPreserving_subtype_of_saturated hC (range e) hsat

end AharoniKorman.Illfounded
