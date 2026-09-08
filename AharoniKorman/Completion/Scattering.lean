import AharoniKorman.Completion.Order
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases

/-! Scattering of the completion (paper `lem:h-scattered`). The only combinatorial
inputs are finite-colouring indivisibility of the rationals and the standard
embedding of a countable linear order into a dense linear order. -/

namespace AharoniKorman.Completion

variable {α : Type*} [PartialOrder α]

namespace H

/-- If each interval of a rational copy contains a principal separator, then the
original poset contains a rational copy. Disjoint intervals are indexed by
`ℚ ×ₗ Fin 2`, avoiding a separate recursion on dyadic rationals. -/
theorem rational_embedding_of_separators (f : ℚ ↪o H α)
    (hsep : ∀ p q : ℚ, p < q → ∃ x : α, f p < principal x ∧ principal x < f q) :
    Nonempty (ℚ ↪o α) := by
  classical
  let : Countable (ℚ ×ₗ Fin 2) := ofLex.injective.countable
  obtain ⟨e⟩ := Order.embedding_from_countable_to_dense (α := ℚ ×ₗ Fin 2) (β := ℚ)
  have hpairs (q : ℚ) : e (toLex (q, 0)) < e (toLex (q, 1)) :=
    e.strictMono (Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, show (0 : Fin 2) < 1 from by decide⟩))
  choose x hx using fun q => hsep _ _ (hpairs q)
  refine ⟨OrderEmbedding.ofStrictMono x ?_⟩
  intro p q hpq
  have hpq' : e (toLex (p, 1)) < e (toLex (q, 0)) :=
    e.strictMono (Prod.Lex.toLex_lt_toLex.2 (Or.inl hpq))
  exact (principal_lt_principal _ _).1
    ((hx p).2.trans ((f.strictMono hpq').trans (hx q).1))

private def colour : H α → Fin 5
  | principal _ => 0
  | increasing _ => 1
  | decreasing _ => 2
  | bottom => 3
  | top => 4

private theorem colour_principal (X : H α) (h : colour X = 0) : ∃ x, X = principal x := by
  cases X <;> simp_all [colour]

private theorem colour_increasing (X : H α) (h : colour X = 1) : ∃ g, X = increasing g := by
  cases X <;> simp_all [colour]

private theorem colour_decreasing (X : H α) (h : colour X = 2) : ∃ g, X = decreasing g := by
  cases X <;> simp_all [colour]

private theorem colour_bottom (X : H α) (h : colour X = 3) : X = ⊥ := by
  cases X <;> simp_all [colour, Bot.bot]

private theorem colour_top (X : H α) (h : colour X = 4) : X = ⊤ := by
  cases X <;> simp_all [colour, Top.top]

/-- Paper `lem:h-scattered`: completion preserves scatteredness. -/
theorem isScattered (hα : IsScattered α) : IsScattered (H α) := by
  classical
  rintro ⟨f⟩
  obtain ⟨i, ⟨e⟩⟩ := finite_coloring_rat_exists_monochromatic_embedding (fun q => colour (f q))
  let g : ℚ ↪o H α := e.trans ((OrderEmbedding.subtype _).trans f)
  have hg (q : ℚ) : colour (g q) = i := (e q).2
  fin_cases i
  · choose x hx using fun q => colour_principal (g q) (hg q)
    apply hα
    refine ⟨OrderEmbedding.ofStrictMono x ?_⟩
    intro p q hpq
    exact (principal_lt_principal _ _).1 (by simpa only [hx] using g.strictMono hpq)
  · apply hα
    apply rational_embedding_of_separators g
    intro p q hpq
    obtain ⟨a, ha⟩ := colour_increasing (g p) (hg p)
    obtain ⟨b, hb⟩ := colour_increasing (g q) (hg q)
    have hlt := g.strictMono hpq
    rw [ha, hb] at hlt ⊢
    exact exists_principal_between_increasing hlt
  · apply hα
    apply rational_embedding_of_separators g
    intro p q hpq
    obtain ⟨a, ha⟩ := colour_decreasing (g p) (hg p)
    obtain ⟨b, hb⟩ := colour_decreasing (g q) (hg q)
    have hlt := g.strictMono hpq
    rw [ha, hb] at hlt ⊢
    exact exists_principal_between_decreasing hlt
  · have he : g 0 = g 1 := (colour_bottom _ (hg 0)).trans (colour_bottom _ (hg 1)).symm
    exact (zero_ne_one : (0 : ℚ) ≠ 1) (g.injective he)
  · have he : g 0 = g 1 := (colour_top _ (hg 0)).trans (colour_top _ (hg 1)).symm
    exact (zero_ne_one : (0 : ℚ) ≠ 1) (g.injective he)

end H

end AharoniKorman.Completion
