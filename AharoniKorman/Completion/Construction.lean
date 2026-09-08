import AharoniKorman.Completion.Germs

/-! The normalized completion carrier (paper `def:h-p`). Principal chains have
already been removed from the germ types, so no gluing quotient is needed. -/

namespace AharoniKorman.Completion

variable {α : Type*} [PartialOrder α]

/-- The five disjoint kinds of completion point. -/
inductive H (α : Type*) [PartialOrder α]
  | principal (x : α)
  | increasing (g : IncreasingGerm α)
  | decreasing (g : DecreasingGerm α)
  | bottom
  | top

namespace H

instance : Bot (H α) := ⟨bottom⟩
instance : Top (H α) := ⟨top⟩

/-- Principal points have no direction; the formal endpoints have the paper's signs. -/
def direction : H α → Option OrderDirection
  | principal _ => none
  | increasing _ => some .increasing
  | decreasing _ => some .decreasing
  | bottom => some .decreasing
  | top => some .increasing

@[simp] theorem direction_principal (x : α) : (principal x).direction = none := rfl
@[simp] theorem direction_increasing (g : IncreasingGerm α) :
    (increasing g).direction = some .increasing := rfl
@[simp] theorem direction_decreasing (g : DecreasingGerm α) :
    (decreasing g).direction = some .decreasing := rfl
@[simp] theorem direction_bot : (⊥ : H α).direction = some .decreasing := rfl
@[simp] theorem direction_top : (⊤ : H α).direction = some .increasing := rfl

def IsNonprincipal (X : H α) : Prop := ∃ d, X.direction = some d

/-- Nonprincipal points, including the formal endpoints. -/
abbrev N (α : Type*) [PartialOrder α] := {X : H α // X.IsNonprincipal}

/-- The direction-tagged nonprincipal subtypes `N+` and `N-`. -/
abbrev NDirection (d : OrderDirection) (α : Type*) [PartialOrder α] :=
  {X : H α // X.direction = some d}

abbrev NPlus (α : Type*) [PartialOrder α] := NDirection .increasing α
abbrev NMinus (α : Type*) [PartialOrder α] := NDirection .decreasing α

@[simp] theorem principal_inj {x y : α} : principal x = principal y ↔ x = y :=
  ⟨principal.inj, congrArg principal⟩

theorem principal_injective : Function.Injective (principal : α → H α) :=
  fun _ _ => principal.inj

@[simp] theorem principal_ne_increasing (x : α) (g : IncreasingGerm α) :
    principal x ≠ increasing g := by intro h; cases h
@[simp] theorem principal_ne_decreasing (x : α) (g : DecreasingGerm α) :
    principal x ≠ decreasing g := by intro h; cases h
@[simp] theorem principal_ne_bot (x : α) : principal x ≠ (⊥ : H α) := by intro h; cases h
@[simp] theorem principal_ne_top (x : α) : principal x ≠ (⊤ : H α) := by intro h; cases h
@[simp] theorem increasing_ne_decreasing (g : IncreasingGerm α) (h : DecreasingGerm α) :
    increasing g ≠ decreasing h := by intro he; cases he
@[simp] theorem increasing_ne_bot (g : IncreasingGerm α) :
    increasing g ≠ (⊥ : H α) := by intro h; cases h
@[simp] theorem increasing_ne_top (g : IncreasingGerm α) :
    increasing g ≠ (⊤ : H α) := by intro h; cases h
@[simp] theorem decreasing_ne_bot (g : DecreasingGerm α) :
    decreasing g ≠ (⊥ : H α) := by intro h; cases h
@[simp] theorem decreasing_ne_top (g : DecreasingGerm α) :
    decreasing g ≠ (⊤ : H α) := by intro h; cases h
@[simp] theorem bot_ne_top : (⊥ : H α) ≠ ⊤ := by intro h; cases h

theorem direction_eq_none_iff (X : H α) : X.direction = none ↔ ∃ x, X = principal x := by
  cases X <;> simp [direction]

theorem direction_eq_increasing_iff (X : H α) :
    X.direction = some .increasing ↔ (∃ g, X = increasing g) ∨ X = ⊤ := by
  cases X <;> simp [direction, Top.top]

theorem direction_eq_decreasing_iff (X : H α) :
    X.direction = some .decreasing ↔ (∃ g, X = decreasing g) ∨ X = ⊥ := by
  cases X <;> simp [direction, Bot.bot]

theorem principal_or_direction (X : H α) :
    (∃ x, X = principal x) ∨ X.direction = some .increasing ∨
      X.direction = some .decreasing := by
  cases X <;> simp [direction]

theorem directions_disjoint (X : H α) :
    ¬(X.direction = some .increasing ∧ X.direction = some .decreasing) := by
  rintro ⟨hi, hd⟩
  rw [hi] at hd
  cases hd

/-- Reverse the ambient order and exchange the signs and formal endpoints. -/
def dual : H α → H αᵒᵈ
  | principal x => principal x
  | increasing g => decreasing g.toDual
  | decreasing g => increasing g.toDual
  | bottom => top
  | top => bottom

@[simp] theorem dual_dual (X : H α) : X.dual.dual = X := by
  cases X <;> rfl

theorem dual_injective : Function.Injective (dual : H α → H αᵒᵈ) :=
  Function.LeftInverse.injective dual_dual

@[simp] theorem direction_dual (X : H α) :
    X.dual.direction = X.direction.map OrderDirection.dual := by
  cases X <;> rfl

end H

end AharoniKorman.Completion
