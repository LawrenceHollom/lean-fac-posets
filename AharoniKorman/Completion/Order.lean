import AharoniKorman.Completion.Domination
import AharoniKorman.Preliminaries.Scattered

/-! The domination order on `H(P)` and scattering/chain results. -/

namespace AharoniKorman.Completion

variable {α : Type*} [PartialOrder α]

namespace H

open Domination

/-- Strict domination on normalized points (paper `def:domination`). The public
representative formulas below justify the use of chosen representatives here. -/
noncomputable def StrictLT : H α → H α → Prop
  | bottom, bottom => False
  | top, _ => False
  | _, top => True
  | bottom, _ => True
  | _, bottom => False
  | principal x, principal y => x < y
  | principal x, increasing h => principalIncreasing x h.representative
  | principal x, decreasing h => principalDecreasing x h.representative
  | increasing g, principal y => increasingPrincipal g.representative y
  | decreasing g, principal y => decreasingPrincipal g.representative y
  | increasing g, increasing h => increasingIncreasing g.representative h.representative
  | increasing g, decreasing h => increasingDecreasing g.representative h.representative
  | decreasing g, increasing h => decreasingIncreasing g.representative h.representative
  | decreasing g, decreasing h => decreasingDecreasing g.representative h.representative

private theorem increasing_rep_equiv {g : IncreasingGerm α} {C : IncreasingChain α}
    (h : g.Represents C) : IncreasingEquivalent g.representative C :=
  (IncreasingGerm.eq_iff_of_representatives g.representative_spec h).1 rfl

private theorem decreasing_rep_equiv {g : DecreasingGerm α} {C : DecreasingChain α}
    (h : g.Represents C) : DecreasingEquivalent g.representative C :=
  (DecreasingGerm.eq_iff_of_representatives g.representative_spec h).1 rfl

theorem strictLT_principal_increasing {g : IncreasingGerm α} {C : IncreasingChain α}
    (h : g.Represents C) (x : α) :
    StrictLT (principal x) (increasing g) ↔ ∃ c : C.1, x < c.1 :=
  principalIncreasing_congr x (increasing_rep_equiv h)

theorem strictLT_increasing_principal {g : IncreasingGerm α} {C : IncreasingChain α}
    (h : g.Represents C) (x : α) :
    StrictLT (increasing g) (principal x) ↔ ∀ c : C.1, c.1 < x :=
  increasingPrincipal_congr x (increasing_rep_equiv h)

theorem strictLT_principal_decreasing {g : DecreasingGerm α} {C : DecreasingChain α}
    (h : g.Represents C) (x : α) :
    StrictLT (principal x) (decreasing g) ↔ ∀ c : C.1, x < c.1 :=
  principalDecreasing_congr x (decreasing_rep_equiv h)

theorem strictLT_decreasing_principal {g : DecreasingGerm α} {C : DecreasingChain α}
    (h : g.Represents C) (x : α) :
    StrictLT (decreasing g) (principal x) ↔ ∃ c : C.1, c.1 < x :=
  decreasingPrincipal_congr x (decreasing_rep_equiv h)

theorem strictLT_increasing_increasing {g h : IncreasingGerm α} {C D : IncreasingChain α}
    (hC : g.Represents C) (hD : h.Represents D) :
    StrictLT (increasing g) (increasing h) ↔ ∃ d : D.1, ∀ c : C.1, c.1 < d.1 :=
  increasingIncreasing_congr (increasing_rep_equiv hC) (increasing_rep_equiv hD)

theorem strictLT_increasing_decreasing {g : IncreasingGerm α} {h : DecreasingGerm α}
    {C : IncreasingChain α} {D : DecreasingChain α}
    (hC : g.Represents C) (hD : h.Represents D) :
    StrictLT (increasing g) (decreasing h) ↔ ∀ c : C.1, ∀ d : D.1, c.1 < d.1 :=
  increasingDecreasing_congr (increasing_rep_equiv hC) (decreasing_rep_equiv hD)

theorem strictLT_decreasing_increasing {g : DecreasingGerm α} {h : IncreasingGerm α}
    {C : DecreasingChain α} {D : IncreasingChain α}
    (hC : g.Represents C) (hD : h.Represents D) :
    StrictLT (decreasing g) (increasing h) ↔ ∃ c : C.1, ∃ d : D.1, c.1 < d.1 :=
  decreasingIncreasing_congr (decreasing_rep_equiv hC) (increasing_rep_equiv hD)

theorem strictLT_decreasing_decreasing {g h : DecreasingGerm α} {C D : DecreasingChain α}
    (hC : g.Represents C) (hD : h.Represents D) :
    StrictLT (decreasing g) (decreasing h) ↔ ∃ c : C.1, ∀ d : D.1, c.1 < d.1 :=
  decreasingDecreasing_congr (decreasing_rep_equiv hC) (decreasing_rep_equiv hD)

theorem strictLT_irrefl (X : H α) : ¬StrictLT X X := by
  cases X <;> simp only [StrictLT, increasingIncreasing, decreasingDecreasing]
  · exact lt_irrefl _
  · rintro ⟨c, hc⟩; exact (hc c).false
  · rintro ⟨c, hc⟩; exact (hc c).false
  · exact not_false
  · exact not_false

theorem strictLT_trans {X Y Z : H α} (hXY : StrictLT X Y) (hYZ : StrictLT Y Z) :
    StrictLT X Z := by
  cases X <;> cases Y <;> cases Z <;>
    simp only [StrictLT, principalIncreasing, increasingPrincipal, principalDecreasing,
      decreasingPrincipal, increasingIncreasing, increasingDecreasing, decreasingIncreasing,
      decreasingDecreasing] at *
  all_goals first | contradiction | trivial | aesop (add unsafe apply lt_trans)

noncomputable instance : PartialOrder (H α) where
  le X Y := X = Y ∨ StrictLT X Y
  lt := StrictLT
  le_refl _ := Or.inl rfl
  le_trans X Y Z hXY hYZ := by
    rcases hXY with rfl | hXY
    · exact hYZ
    rcases hYZ with rfl | hYZ
    · exact Or.inr hXY
    exact Or.inr (strictLT_trans hXY hYZ)
  le_antisymm X Y hXY hYX := by
    rcases hXY with h | h
    · exact h
    rcases hYX with h' | h'
    · exact h'.symm
    exact (strictLT_irrefl X (strictLT_trans h h')).elim
  lt_iff_le_not_ge X Y := by
    constructor
    · intro h
      refine ⟨Or.inr h, ?_⟩
      rintro (rfl | h')
      · exact strictLT_irrefl _ h
      · exact strictLT_irrefl _ (strictLT_trans h h')
    · rintro ⟨h, hn⟩
      exact h.resolve_left (fun he => hn (Or.inl he.symm))

theorem le_iff_eq_or_strictLT (X Y : H α) : X ≤ Y ↔ X = Y ∨ StrictLT X Y := Iff.rfl
theorem lt_iff_strictLT (X Y : H α) : X < Y ↔ StrictLT X Y := Iff.rfl

@[simp] theorem principal_lt_principal (x y : α) : principal x < principal y ↔ x < y := Iff.rfl

@[simp] theorem principal_le_principal (x y : α) : principal x ≤ principal y ↔ x ≤ y := by
  change (principal x = principal y ∨ x < y) ↔ x ≤ y
  rw [principal_inj]
  exact ⟨le_of_eq_or_lt, fun h => (lt_or_eq_of_le h).symm⟩

noncomputable instance : OrderBot (H α) where
  bot_le X := by cases X <;> first | exact Or.inl rfl | exact Or.inr trivial

noncomputable instance : OrderTop (H α) where
  le_top X := by cases X <;> first | exact Or.inl rfl | exact Or.inr trivial

/-- The original poset sits in its completion with exactly its original order. -/
noncomputable def principalEmbedding : α ↪o H α :=
  OrderEmbedding.ofMapLEIff principal (by intro x y; exact principal_le_principal x y)

@[simp] theorem principalEmbedding_apply (x : α) : principalEmbedding x = principal x := rfl

@[simp] theorem comparable_principal (x y : α) :
    Comparable (principal x) (principal y) ↔ Comparable x y := by
  simp only [Comparable, Relation.SymmGen, principal_le_principal]

@[simp] theorem incomparable_principal (x y : α) :
    Incomparable (principal x) (principal y) ↔ Incomparable x y := by
  simp only [Incomparable, IncompRel, principal_le_principal]

@[simp] theorem principal_lt_increasing_ofChain (x : α) (C : IncreasingChain α) :
    principal x < increasing (IncreasingGerm.ofChain C) ↔ ∃ c : C.1, x < c.1 :=
  strictLT_principal_increasing rfl x

@[simp] theorem increasing_ofChain_lt_principal (C : IncreasingChain α) (x : α) :
    increasing (IncreasingGerm.ofChain C) < principal x ↔ ∀ c : C.1, c.1 < x :=
  strictLT_increasing_principal rfl x

@[simp] theorem principal_lt_decreasing_ofChain (x : α) (C : DecreasingChain α) :
    principal x < decreasing (DecreasingGerm.ofChain C) ↔ ∀ c : C.1, x < c.1 :=
  strictLT_principal_decreasing rfl x

@[simp] theorem decreasing_ofChain_lt_principal (C : DecreasingChain α) (x : α) :
    decreasing (DecreasingGerm.ofChain C) < principal x ↔ ∃ c : C.1, c.1 < x :=
  strictLT_decreasing_principal rfl x

@[simp] theorem increasing_ofChain_lt_increasing_ofChain (C D : IncreasingChain α) :
    increasing (IncreasingGerm.ofChain C) < increasing (IncreasingGerm.ofChain D) ↔
      ∃ d : D.1, ∀ c : C.1, c.1 < d.1 := strictLT_increasing_increasing rfl rfl

@[simp] theorem increasing_ofChain_lt_decreasing_ofChain
    (C : IncreasingChain α) (D : DecreasingChain α) :
    increasing (IncreasingGerm.ofChain C) < decreasing (DecreasingGerm.ofChain D) ↔
      ∀ c : C.1, ∀ d : D.1, c.1 < d.1 := strictLT_increasing_decreasing rfl rfl

@[simp] theorem decreasing_ofChain_lt_increasing_ofChain
    (C : DecreasingChain α) (D : IncreasingChain α) :
    decreasing (DecreasingGerm.ofChain C) < increasing (IncreasingGerm.ofChain D) ↔
      ∃ c : C.1, ∃ d : D.1, c.1 < d.1 := strictLT_decreasing_increasing rfl rfl

@[simp] theorem decreasing_ofChain_lt_decreasing_ofChain (C D : DecreasingChain α) :
    decreasing (DecreasingGerm.ofChain C) < decreasing (DecreasingGerm.ofChain D) ↔
      ∃ c : C.1, ∀ d : D.1, c.1 < d.1 := strictLT_decreasing_decreasing rfl rfl

/-- Representative induction for completion points, with no quotient internals exposed. -/
@[elab_as_elim] theorem inductionOnRepresentatives {motive : H α → Prop} (X : H α)
    (hp : ∀ x, motive (principal x))
    (hi : ∀ C, motive (increasing (IncreasingGerm.ofChain C)))
    (hd : ∀ C, motive (decreasing (DecreasingGerm.ofChain C)))
    (hb : motive ⊥) (ht : motive ⊤) : motive X := by
  cases X with
  | principal x => exact hp x
  | increasing g => exact IncreasingGerm.inductionOn g hi
  | decreasing g => exact DecreasingGerm.inductionOn g hd
  | bottom => exact hb
  | top => exact ht

@[simp] theorem dual_lt_dual (X Y : H α) : X.dual < Y.dual ↔ Y < X := by
  induction X using inductionOnRepresentatives <;>
    induction Y using inductionOnRepresentatives <;>
    simp only [dual, IncreasingGerm.toDual_ofChain, DecreasingGerm.toDual_ofChain,
      principal_lt_principal, principal_lt_increasing_ofChain, increasing_ofChain_lt_principal,
      principal_lt_decreasing_ofChain, decreasing_ofChain_lt_principal,
      increasing_ofChain_lt_increasing_ofChain, increasing_ofChain_lt_decreasing_ofChain,
      decreasing_ofChain_lt_increasing_ofChain, decreasing_ofChain_lt_decreasing_ofChain]
  all_goals first | rfl | exact forall_comm | exact exists_comm | skip
  all_goals first
    | exact principal_lt_increasing_ofChain (α := αᵒᵈ) _ _
    | exact principal_lt_decreasing_ofChain (α := αᵒᵈ) _ _
    | exact increasing_ofChain_lt_principal (α := αᵒᵈ) _ _
    | exact decreasing_ofChain_lt_principal (α := αᵒᵈ) _ _

@[simp] theorem dual_le_dual (X Y : H α) : X.dual ≤ Y.dual ↔ Y ≤ X := by
  rw [le_iff_eq_or_lt, le_iff_eq_or_lt, dual_lt_dual]
  have he : X.dual = Y.dual ↔ Y = X := by
    constructor
    · exact fun h => (dual_injective h).symm
    · rintro rfl; rfl
  rw [he]

/-- The completion construction commutes with order duality. -/
noncomputable def dualOrderIso : (H α)ᵒᵈ ≃o H αᵒᵈ where
  toFun := dual
  invFun := dual
  left_inv := dual_dual
  right_inv := dual_dual
  map_rel_iff' := dual_le_dual _ _

theorem exists_principal_between_increasing {g h : IncreasingGerm α}
    (hgh : increasing g < increasing h) :
    ∃ x : α, increasing g < principal x ∧ principal x < increasing h := by
  obtain ⟨d, hd⟩ := (strictLT_increasing_increasing
    g.representative_spec h.representative_spec).1 hgh
  obtain ⟨d', hdd'⟩ := h.representative.2.exists_gt d
  exact ⟨d.1, (strictLT_increasing_principal g.representative_spec _).2 hd,
    (strictLT_principal_increasing h.representative_spec _).2 ⟨d', hdd'⟩⟩

theorem exists_principal_between_decreasing {g h : DecreasingGerm α}
    (hgh : decreasing g < decreasing h) :
    ∃ x : α, decreasing g < principal x ∧ principal x < decreasing h := by
  have hd : increasing h.toDual < increasing g.toDual :=
    (dual_lt_dual (decreasing h) (decreasing g)).2 hgh
  obtain ⟨x, hhx, hxg⟩ := exists_principal_between_increasing hd
  exact ⟨x, (dual_lt_dual (principal (show α from x)) (decreasing g)).1 hxg,
    (dual_lt_dual (decreasing h) (principal (show α from x))).1 hhx⟩

end H

end AharoniKorman.Completion
