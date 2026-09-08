import AharoniKorman.Completion.Sequences

/-! Accumulation and isolated points (`def:accumulation-and-isolated-points`).

Accumulation is relative to the nonprincipal order, with the direction of approach
specified by the point. Sequential characterizations use a countable underlying linear
order. Formal endpoints are included in `N`, but are isolated in a chain completion.
-/

namespace AharoniKorman.Completion

open Set

namespace H

variable {α : Type*} [PartialOrder α]

@[simp] theorem isNonprincipal_dual (X : H α) : X.dual.IsNonprincipal ↔ X.IsNonprincipal := by
  cases X <;> simp [IsNonprincipal, direction, dual]

/-- There is no last nonprincipal point strictly below `X`. -/
def AccumulatesBelow (X : H α) : Prop :=
  ∀ Y : H α, Y.IsNonprincipal → Y < X →
    ∃ Z : H α, Z.IsNonprincipal ∧ Y < Z ∧ Z < X

/-- There is no first nonprincipal point strictly above `X`. -/
def AccumulatesAbove (X : H α) : Prop :=
  ∀ Y : H α, Y.IsNonprincipal → X < Y →
    ∃ Z : H α, Z.IsNonprincipal ∧ X < Z ∧ Z < Y

theorem accumulatesAbove_iff (X : H α) : AccumulatesAbove X ↔
    ∀ Y : H α, Y.IsNonprincipal → X < Y →
      ∃ Z : H α, Z.IsNonprincipal ∧ X < Z ∧ Z < Y := Iff.rfl

@[simp] theorem accumulatesBelow_dual (X : H α) :
    AccumulatesBelow X.dual ↔ AccumulatesAbove X := by
  constructor
  · intro h Y hY hXY
    obtain ⟨Z, hZ, hYZ, hZX⟩ := h Y.dual ((isNonprincipal_dual Y).2 hY)
      ((dual_lt_dual Y X).2 hXY)
    obtain ⟨Z, rfl⟩ := (dualOrderIso (α := α)).surjective Z
    exact ⟨Z, (isNonprincipal_dual Z).1 hZ,
      (dual_lt_dual Z X).1 hZX, (dual_lt_dual Y Z).1 hYZ⟩
  · intro h Y hY hYX
    obtain ⟨Y, rfl⟩ := (dualOrderIso (α := α)).surjective Y
    obtain ⟨Z, hZ, hXZ, hZY⟩ := h Y ((isNonprincipal_dual Y).1 hY)
      ((dual_lt_dual Y X).1 hYX)
    exact ⟨Z.dual, (isNonprincipal_dual Z).2 hZ,
      (dual_lt_dual Y Z).2 hZY,
      (dual_lt_dual Z X).2 hXZ⟩

@[simp] theorem accumulatesAbove_dual (X : H α) :
    AccumulatesAbove X.dual ↔ AccumulatesBelow X := by
  constructor
  · intro h Y hY hYX
    obtain ⟨Z, hZ, hXZ, hZY⟩ := h Y.dual ((isNonprincipal_dual Y).2 hY)
      ((dual_lt_dual X Y).2 hYX)
    obtain ⟨Z, rfl⟩ := (dualOrderIso (α := α)).surjective Z
    exact ⟨Z, (isNonprincipal_dual Z).1 hZ,
      (dual_lt_dual Z Y).1 hZY, (dual_lt_dual X Z).1 hXZ⟩
  · intro h Y hY hXY
    obtain ⟨Y, rfl⟩ := (dualOrderIso (α := α)).surjective Y
    obtain ⟨Z, hZ, hYZ, hZX⟩ := h Y ((isNonprincipal_dual Y).1 hY)
      ((dual_lt_dual X Y).1 hXY)
    exact ⟨Z.dual, (isNonprincipal_dual Z).2 hZ,
      (dual_lt_dual X Z).2 hZX, (dual_lt_dual Z Y).2 hYZ⟩

/-- Accumulation from the side specified by the nonprincipal point's direction. -/
def IsAccumulation (X : H α) : Prop :=
  (X.direction = some .increasing ∧ AccumulatesBelow X) ∨
    (X.direction = some .decreasing ∧ AccumulatesAbove X)

/-- Isolation is defined only for nonprincipal points. -/
def IsIsolated (X : H α) : Prop := X.IsNonprincipal ∧ ¬X.IsAccumulation

theorem isAccumulation_of_direction_increasing {X : H α}
    (hX : X.direction = some .increasing) : X.IsAccumulation ↔ AccumulatesBelow X := by
  simp [IsAccumulation, hX]

theorem isAccumulation_of_direction_decreasing {X : H α}
    (hX : X.direction = some .decreasing) : X.IsAccumulation ↔ AccumulatesAbove X := by
  simp [IsAccumulation, hX]

@[simp] theorem isAccumulation_increasing (g : IncreasingGerm α) :
    (increasing g).IsAccumulation ↔ AccumulatesBelow (increasing g) :=
  isAccumulation_of_direction_increasing rfl

@[simp] theorem isAccumulation_decreasing (g : DecreasingGerm α) :
    (decreasing g).IsAccumulation ↔ AccumulatesAbove (decreasing g) :=
  isAccumulation_of_direction_decreasing rfl

@[simp] theorem not_isAccumulation_principal (x : α) : ¬(principal x).IsAccumulation := by
  simp [IsAccumulation]

@[simp] theorem not_isIsolated_principal (x : α) : ¬(principal x).IsIsolated := by
  simp [IsIsolated, IsNonprincipal]

theorem IsAccumulation.isNonprincipal {X : H α} (h : X.IsAccumulation) : X.IsNonprincipal := by
  rcases h with ⟨hd, _⟩ | ⟨hd, _⟩
  · exact ⟨.increasing, hd⟩
  · exact ⟨.decreasing, hd⟩

@[simp] theorem isAccumulation_dual (X : H α) : X.dual.IsAccumulation ↔ X.IsAccumulation := by
  simp only [IsAccumulation, direction_dual, accumulatesBelow_dual, accumulatesAbove_dual]
  cases hd : X.direction with
  | none => simp
  | some d => cases d <;> simp

@[simp] theorem isIsolated_dual (X : H α) : X.dual.IsIsolated ↔ X.IsIsolated := by
  simp [IsIsolated]

/-- An isolated increasing point has a predecessor in the nonprincipal order. -/
theorem not_accumulatesBelow_iff_covBy {X : H α} (hX : X.IsNonprincipal) :
    ¬AccumulatesBelow X ↔ ∃ Y : N α, Y ⋖ (⟨X, hX⟩ : N α) := by
  classical
  constructor
  · intro h
    simp only [AccumulatesBelow, not_forall, not_exists, not_and] at h
    obtain ⟨Y, hY, hYX, hgap⟩ := h
    exact ⟨⟨Y, hY⟩, hYX, fun Z hYZ hZX => hgap Z.1 Z.2 hYZ hZX⟩
  · rintro ⟨Y, hY⟩ h
    obtain ⟨Z, hZ, hYZ, hZX⟩ := h Y.1 Y.2 hY.1
    exact hY.2 (c := ⟨Z, hZ⟩) hYZ hZX

theorem not_accumulatesAbove_iff_covBy {X : H α} (hX : X.IsNonprincipal) :
    ¬AccumulatesAbove X ↔ ∃ Y : N α, (⟨X, hX⟩ : N α) ⋖ Y := by
  classical
  rw [accumulatesAbove_iff]
  constructor
  · intro h
    simp only [not_forall, not_exists, not_and] at h
    obtain ⟨Y, hY, hXY, hgap⟩ := h
    exact ⟨⟨Y, hY⟩, hXY, fun Z hXZ hZY => hgap Z.1 Z.2 hXZ hZY⟩
  · rintro ⟨Y, hY⟩ h
    obtain ⟨Z, hZ, hXZ, hZY⟩ := h Y.1 Y.2 hY.1
    exact hY.2 (c := ⟨Z, hZ⟩) hXZ hZY

theorem isIsolated_increasing_iff (g : IncreasingGerm α) :
    (increasing g).IsIsolated ↔
      ∃ Y : N α, Y ⋖ (⟨increasing g, ⟨.increasing, rfl⟩⟩ : N α) := by
  rw [IsIsolated, isAccumulation_increasing]
  exact (and_iff_right (show (increasing g).IsNonprincipal from ⟨.increasing, rfl⟩)).trans
    (not_accumulatesBelow_iff_covBy _)

theorem isIsolated_decreasing_iff (g : DecreasingGerm α) :
    (decreasing g).IsIsolated ↔
      ∃ Y : N α, (⟨decreasing g, ⟨.decreasing, rfl⟩⟩ : N α) ⋖ Y := by
  rw [IsIsolated, isAccumulation_decreasing]
  exact (and_iff_right (show (decreasing g).IsNonprincipal from ⟨.decreasing, rfl⟩)).trans
    (not_accumulatesAbove_iff_covBy _)

end H

namespace H

variable {α : Type*} [LinearOrder α]

/-- The nonprincipal points strictly below a proposed boundary. -/
def lowerNonprincipal (X : H α) : Set (H α) := {Y | Y.IsNonprincipal ∧ Y < X}

theorem lowerNonprincipal_nonempty {X : H α} (hX : X ≠ ⊥) :
    (lowerNonprincipal X).Nonempty :=
  ⟨⊥, ⟨.decreasing, rfl⟩, bot_lt_iff_ne_bot.2 hX⟩

theorem AccumulatesBelow.no_greatest {X : H α} (h : AccumulatesBelow X) :
    ∀ Y ∈ lowerNonprincipal X, ∃ Z ∈ lowerNonprincipal X, Y < Z := by
  intro Y hY
  obtain ⟨Z, hZ, hYZ, hZX⟩ := h Y hY.1 hY.2
  exact ⟨Z, ⟨hZ, hZX⟩, hYZ⟩

private theorem accumulatesBelow_sup_not_mem {X : H α} (h : AccumulatesBelow X) :
    sSup (lowerNonprincipal X) ∉ lowerNonprincipal X := by
  intro hm
  obtain ⟨Y, hY, hlt⟩ := h.no_greatest _ hm
  exact hlt.not_ge (le_sSup hY)

/-- Accumulation means that the smaller nonprincipal points have the claimed boundary
as their supremum in the full completion, not merely in its nonprincipal subtype. -/
theorem accumulatesBelow_iff_isLUB {X : H α} (hX : X ≠ ⊥) :
    AccumulatesBelow X ↔ IsLUB (lowerNonprincipal X) X := by
  constructor
  · intro h
    have hnot := accumulatesBelow_sup_not_mem h
    have hdir := sSup_direction_of_not_mem (lowerNonprincipal_nonempty hX) hnot
    have heq : sSup (lowerNonprincipal X) = X := by
      apply le_antisymm (sSup_le (fun Y hY => hY.2.le))
      apply le_of_not_gt
      intro hlt
      exact hnot ⟨⟨.increasing, hdir⟩, hlt⟩
    simpa only [heq] using isLUB_sSup (lowerNonprincipal X)
  · intro h Y hY hYX
    by_contra hno
    have hbound : Y ∈ upperBounds (lowerNonprincipal X) := by
      intro Z hZ
      exact le_of_not_gt (fun hYZ => hno ⟨Z, hZ.1, hYZ, hZ.2⟩)
    exact hYX.not_ge (h.2 hbound)

/-- In a chain completion, the same cofinal approximation works above principal
points as well as above nonprincipal points. -/
theorem accumulatesBelow_iff_cofinal {X : H α} (hX : X ≠ ⊥) :
    AccumulatesBelow X ↔ ∀ Y : H α, Y < X →
      ∃ Z : H α, Z.IsNonprincipal ∧ Y < Z ∧ Z < X := by
  constructor
  · intro h Y hYX
    have hlub := (accumulatesBelow_iff_isLUB hX).1 h
    by_contra hno
    apply hYX.not_ge
    apply hlub.2
    intro Z hZ
    exact le_of_not_gt (fun hYZ => hno ⟨Z, hZ.1, hYZ, hZ.2⟩)
  · intro h Y _ hYX
    exact h Y hYX

/-- The dual coinitial characterization. -/
theorem accumulatesAbove_iff_coinitial {X : H α} (hX : X ≠ ⊤) :
    AccumulatesAbove X ↔ ∀ Y : H α, X < Y →
      ∃ Z : H α, Z.IsNonprincipal ∧ X < Z ∧ Z < Y := by
  have hXd : X.dual ≠ ⊥ := fun heq => hX (dual_injective heq)
  rw [← accumulatesBelow_dual, accumulatesBelow_iff_cofinal hXd]
  constructor
  · intro h Y hXY
    obtain ⟨Z, hZ, hYZ, hZX⟩ := h Y.dual ((dual_lt_dual Y X).2 hXY)
    obtain ⟨Z, rfl⟩ := (dualOrderIso (α := α)).surjective Z
    exact ⟨Z, (isNonprincipal_dual Z).1 hZ,
      (dual_lt_dual Z X).1 hZX, (dual_lt_dual Y Z).1 hYZ⟩
  · intro h Y hYX
    obtain ⟨Y, rfl⟩ := (dualOrderIso (α := α)).surjective Y
    obtain ⟨Z, hZ, hXZ, hZY⟩ := h Y ((dual_lt_dual Y X).1 hYX)
    exact ⟨Z.dual, (isNonprincipal_dual Z).2 hZ,
      (dual_lt_dual Y Z).2 hZY, (dual_lt_dual Z X).2 hXZ⟩

def upperNonprincipal (X : H α) : Set (H α) := {Y | Y.IsNonprincipal ∧ X < Y}

/-- Infimum characterization obtained by transport from the supremum theorem. -/
theorem accumulatesAbove_iff_isGLB {X : H α} (hX : X ≠ ⊤) :
    AccumulatesAbove X ↔ IsGLB (upperNonprincipal X) X := by
  have hXd : X.dual ≠ ⊥ := fun heq => hX (dual_injective heq)
  have himg : dual '' upperNonprincipal X = lowerNonprincipal X.dual := by
    ext Y
    constructor
    · rintro ⟨Z, hZ, rfl⟩
      exact ⟨(isNonprincipal_dual Z).2 hZ.1, (dual_lt_dual Z X).2 hZ.2⟩
    · intro hY
      obtain ⟨Z, rfl⟩ := (dualOrderIso (α := α)).surjective Y
      exact ⟨Z, ⟨(isNonprincipal_dual Z).1 hY.1, (dual_lt_dual Z X).1 hY.2⟩, rfl⟩
  rw [← accumulatesBelow_dual, accumulatesBelow_iff_isLUB hXd]
  change IsLUB (lowerNonprincipal X.dual) X.dual ↔
    IsLUB (show Set (H α)ᵒᵈ from upperNonprincipal X) X
  rw [← himg]
  exact (dualOrderIso (α := α)).isLUB_image'

/-- The formal top has an immediate predecessor in the nonprincipal order. -/
theorem isIsolated_top : (⊤ : H α).IsIsolated := by
  refine ⟨⟨.increasing, rfl⟩, ?_⟩
  intro h
  have ha := (isAccumulation_of_direction_increasing rfl).1 h
  have hne := lowerNonprincipal_nonempty (α := α) bot_ne_top.symm
  obtain ⟨g, hg⟩ := sSup_eq_increasing_of_not_mem hne (accumulatesBelow_sup_not_mem ha)
  have heq := ((accumulatesBelow_iff_isLUB bot_ne_top.symm).1 ha).sSup_eq
  exact increasing_ne_top g (hg.symm.trans heq)

theorem isIsolated_bot : (⊥ : H α).IsIsolated := by
  exact (isIsolated_dual (⊥ : H α)).1 (isIsolated_top (α := αᵒᵈ))

/-- Any strict increasing cofinal nonprincipal sequence witnesses accumulation. -/
theorem accumulatesBelow_of_isLUB_sequence {X : H α} (f : ℕ → H α)
    (hf : ∀ n, (f n).IsNonprincipal ∧ f n < X) (hlub : IsLUB (range f) X) :
    AccumulatesBelow X := by
  intro Y _ hYX
  by_contra hno
  apply hYX.not_ge
  apply hlub.2
  rintro _ ⟨n, rfl⟩
  exact le_of_not_gt (fun hYf => hno ⟨f n, (hf n).1, hYf, (hf n).2⟩)

/-- Sequential characterization under countability of the original chain. -/
theorem accumulatesBelow_iff_sequence [Countable α] {X : H α} (hX : X ≠ ⊥) :
    AccumulatesBelow X ↔ ∃ f : ℕ → H α, StrictMono f ∧
      (∀ n, (f n).IsNonprincipal ∧ f n < X) ∧ IsLUB (range f) X := by
  constructor
  · intro h
    obtain ⟨f, hfD, hf, _, hfLub⟩ := exists_strictMono_isLUB
      (lowerNonprincipal_nonempty hX) h.no_greatest
    have heq := ((accumulatesBelow_iff_isLUB hX).1 h).sSup_eq
    exact ⟨f, hf, hfD, heq ▸ hfLub⟩
  · rintro ⟨f, _, hf, hlub⟩
    exact accumulatesBelow_of_isLUB_sequence f hf hlub

/-- Dual sequential characterization, with an infimum in the full completion. -/
theorem accumulatesAbove_iff_sequence [Countable α] {X : H α} (hX : X ≠ ⊤) :
    AccumulatesAbove X ↔ ∃ f : ℕ → H α, StrictAnti f ∧
      (∀ n, (f n).IsNonprincipal ∧ X < f n) ∧ IsGLB (range f) X := by
  let : Countable αᵒᵈ := ‹Countable α›
  have hXd : X.dual ≠ ⊥ := fun heq => hX (dual_injective heq)
  rw [← accumulatesBelow_dual, accumulatesBelow_iff_sequence hXd]
  constructor
  · rintro ⟨f, hf, hfn, hlub⟩
    let g : ℕ → H α := fun n => (dualOrderIso (α := α)).symm (f n)
    have hgd (n : ℕ) : (g n).dual = f n := (dualOrderIso (α := α)).apply_symm_apply _
    refine ⟨g, ?_, ?_, ?_⟩
    · intro i j hij
      exact (dual_lt_dual (g i) (g j)).1 (by simpa only [hgd] using hf hij)
    · intro n
      exact ⟨(isNonprincipal_dual (g n)).1 (by simpa only [hgd] using (hfn n).1),
        (dual_lt_dual (g n) X).1 (by simpa only [hgd] using (hfn n).2)⟩
    · have himg : dual '' range g = range f := by
        ext Y
        simp only [mem_image, mem_range, exists_exists_eq_and, hgd]
      apply (dualOrderIso (α := α)).isLUB_image'.1
      change IsLUB (dual '' range g) X.dual
      rw [himg]
      exact hlub
  · rintro ⟨f, hf, hfn, hglb⟩
    refine ⟨fun n => (f n).dual, fun i j hij => (dual_lt_dual _ _).2 (hf hij),
      fun n => ⟨(isNonprincipal_dual _).2 (hfn n).1,
        (dual_lt_dual _ _).2 (hfn n).2⟩, ?_⟩
    have h := (dualOrderIso (α := α)).isLUB_image'.2 hglb
    change IsLUB (dual '' range f) X.dual at h
    simpa only [← Set.range_comp, Function.comp_def] using h

theorem isAccumulation_increasing_iff_sequence [Countable α] (g : IncreasingGerm α) :
    (increasing g).IsAccumulation ↔ ∃ f : ℕ → H α, StrictMono f ∧
      (∀ n, (f n).IsNonprincipal ∧ f n < increasing g) ∧ IsLUB (range f) (increasing g) := by
  rw [isAccumulation_increasing, accumulatesBelow_iff_sequence (increasing_ne_bot g)]

theorem isAccumulation_decreasing_iff_sequence [Countable α] (g : DecreasingGerm α) :
    (decreasing g).IsAccumulation ↔ ∃ f : ℕ → H α, StrictAnti f ∧
      (∀ n, (f n).IsNonprincipal ∧ decreasing g < f n) ∧ IsGLB (range f) (decreasing g) := by
  rw [isAccumulation_decreasing, accumulatesAbove_iff_sequence (decreasing_ne_top g)]

end H

end AharoniKorman.Completion
