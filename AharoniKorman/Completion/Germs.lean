import AharoniKorman.Completion.ChainTransitivity

/-! Nonprincipal germs. The quotient implementation is private; clients use
`ofChain`, equality, induction, representatives, and the invariant lift API. -/

namespace AharoniKorman.Completion

variable {α : Type*} [PartialOrder α]

private def increasingChainSetoid (α : Type*) [PartialOrder α] : Setoid (IncreasingChain α) where
  r := IncreasingEquivalent
  iseqv := ⟨IncreasingEquivalent.refl, IncreasingEquivalent.symm, IncreasingEquivalent.trans⟩

/-- An increasing germ has no principal representative. -/
structure IncreasingGerm (α : Type*) [PartialOrder α] where
  private mk ::
  private quotient : Quotient (increasingChainSetoid α)

/-- The germ represented by an increasing chain. -/
def IncreasingGerm.ofChain (C : IncreasingChain α) : IncreasingGerm α :=
  ⟨Quotient.mk _ C⟩

@[simp] theorem IncreasingGerm.ofChain_eq_iff {C D : IncreasingChain α} :
    IncreasingGerm.ofChain C = IncreasingGerm.ofChain D ↔ IncreasingEquivalent C D := by
  constructor
  · intro h
    exact Quotient.exact (congrArg IncreasingGerm.quotient h)
  · intro h
    exact congrArg IncreasingGerm.mk (Quotient.sound h)

/-- Public induction without exposing the quotient carrier. -/
@[elab_as_elim] theorem IncreasingGerm.inductionOn {motive : IncreasingGerm α → Prop}
    (g : IncreasingGerm α) (h : ∀ C, motive (IncreasingGerm.ofChain C)) : motive g := by
  rcases g with ⟨q⟩
  exact Quotient.inductionOn q h

def IncreasingGerm.Represents (C : IncreasingChain α) (g : IncreasingGerm α) : Prop :=
  IncreasingGerm.ofChain C = g

theorem IncreasingGerm.exists_representative (g : IncreasingGerm α) :
    ∃ C, g.Represents C := by
  induction g using IncreasingGerm.inductionOn with
  | h C => exact ⟨C, rfl⟩

noncomputable def IncreasingGerm.representative (g : IncreasingGerm α) : IncreasingChain α :=
  Classical.choose g.exists_representative

theorem IncreasingGerm.representative_spec (g : IncreasingGerm α) :
    g.Represents g.representative := Classical.choose_spec g.exists_representative

theorem IncreasingGerm.represents_iff {C D : IncreasingChain α} {g : IncreasingGerm α}
    (hC : g.Represents C) : g.Represents D ↔ IncreasingEquivalent D C := by
  change IncreasingGerm.ofChain D = g ↔ _
  rw [← hC, IncreasingGerm.ofChain_eq_iff]

theorem IncreasingGerm.eq_iff_of_representatives {C D : IncreasingChain α}
    {g h : IncreasingGerm α} (hC : g.Represents C) (hD : h.Represents D) :
    g = h ↔ IncreasingEquivalent C D := by
  rw [← hC, ← hD, IncreasingGerm.ofChain_eq_iff]

/-- Descend any representative-independent function to increasing germs. -/
def IncreasingGerm.lift {β : Sort*} (f : IncreasingChain α → β)
    (hf : ∀ C D, IncreasingEquivalent C D → f C = f D) (g : IncreasingGerm α) : β :=
  Quotient.lift f hf g.quotient

@[simp] theorem IncreasingGerm.lift_ofChain {β : Sort*} (f : IncreasingChain α → β)
    (hf : ∀ C D, IncreasingEquivalent C D → f C = f D) (C : IncreasingChain α) :
    IncreasingGerm.lift f hf (IncreasingGerm.ofChain C) = f C := rfl

/-- Descend a binary function (including a proposition via `propext`). -/
def IncreasingGerm.lift₂ {β : Sort*} (f : IncreasingChain α → IncreasingChain α → β)
    (hf : ∀ C C' D D', IncreasingEquivalent C C' → IncreasingEquivalent D D' →
      f C D = f C' D') (g h : IncreasingGerm α) : β :=
  Quotient.liftOn₂ g.quotient h.quotient f (fun C D C' D' => hf C C' D D')

@[simp] theorem IncreasingGerm.lift₂_ofChain {β : Sort*}
    (f : IncreasingChain α → IncreasingChain α → β)
    (hf : ∀ C C' D D', IncreasingEquivalent C C' → IncreasingEquivalent D D' →
      f C D = f C' D') (C D : IncreasingChain α) :
    IncreasingGerm.lift₂ f hf (IncreasingGerm.ofChain C) (IncreasingGerm.ofChain D) = f C D := rfl

/-- Reverse the direction of a nonprincipal increasing representative. -/
def IncreasingChain.toDual (C : IncreasingChain α) : DecreasingChain αᵒᵈ :=
  ⟨C.1.dual, (SaturatedChain.dual_noBottom_iff C.1).2 C.2⟩

@[simp] theorem IncreasingChain.toDual_toDual (C : IncreasingChain α) :
    C.toDual.toDual = C := by
  apply Subtype.ext
  exact SaturatedChain.dual_dual C.1

@[simp] theorem DecreasingChain.toDual_toDual (C : DecreasingChain α) :
    C.toDual.toDual = C := by
  apply Subtype.ext
  exact SaturatedChain.dual_dual C.1

/-- Decreasing germs are increasing germs of the dual poset. -/
def DecreasingGerm (α : Type*) [PartialOrder α] := IncreasingGerm αᵒᵈ

def DecreasingGerm.ofChain (C : DecreasingChain α) : DecreasingGerm α :=
  IncreasingGerm.ofChain C.toDual

@[simp] theorem DecreasingGerm.ofChain_eq_iff {C D : DecreasingChain α} :
    DecreasingGerm.ofChain C = DecreasingGerm.ofChain D ↔ DecreasingEquivalent C D :=
  IncreasingGerm.ofChain_eq_iff

@[elab_as_elim] theorem DecreasingGerm.inductionOn {motive : DecreasingGerm α → Prop}
    (g : DecreasingGerm α) (h : ∀ C, motive (DecreasingGerm.ofChain C)) : motive g := by
  refine IncreasingGerm.inductionOn (α := αᵒᵈ) g ?_
  intro C
  have hC := h C.toDual
  change motive (IncreasingGerm.ofChain C.toDual.toDual) at hC
  rw [IncreasingChain.toDual_toDual C] at hC
  exact hC

def DecreasingGerm.Represents (C : DecreasingChain α) (g : DecreasingGerm α) : Prop :=
  DecreasingGerm.ofChain C = g

theorem DecreasingGerm.exists_representative (g : DecreasingGerm α) :
    ∃ C, g.Represents C := by
  induction g using DecreasingGerm.inductionOn with
  | h C => exact ⟨C, rfl⟩

noncomputable def DecreasingGerm.representative (g : DecreasingGerm α) : DecreasingChain α :=
  Classical.choose g.exists_representative

theorem DecreasingGerm.representative_spec (g : DecreasingGerm α) :
    g.Represents g.representative := Classical.choose_spec g.exists_representative

theorem DecreasingGerm.represents_iff {C D : DecreasingChain α} {g : DecreasingGerm α}
    (hC : g.Represents C) : g.Represents D ↔ DecreasingEquivalent D C := by
  change DecreasingGerm.ofChain D = g ↔ _
  rw [← hC, DecreasingGerm.ofChain_eq_iff]

theorem DecreasingGerm.eq_iff_of_representatives {C D : DecreasingChain α}
    {g h : DecreasingGerm α} (hC : g.Represents C) (hD : h.Represents D) :
    g = h ↔ DecreasingEquivalent C D := by
  rw [← hC, ← hD, DecreasingGerm.ofChain_eq_iff]

def DecreasingGerm.lift {β : Sort*} (f : DecreasingChain α → β)
    (hf : ∀ C D, DecreasingEquivalent C D → f C = f D) (g : DecreasingGerm α) : β :=
  IncreasingGerm.lift (α := αᵒᵈ) (fun C => f C.toDual) (fun C D h => hf C.toDual D.toDual (by
    change IncreasingEquivalent C.toDual.toDual D.toDual.toDual
    rw [IncreasingChain.toDual_toDual C, IncreasingChain.toDual_toDual D]
    exact h)) g

@[simp] theorem DecreasingGerm.lift_ofChain {β : Sort*} (f : DecreasingChain α → β)
    (hf : ∀ C D, DecreasingEquivalent C D → f C = f D) (C : DecreasingChain α) :
    DecreasingGerm.lift f hf (DecreasingGerm.ofChain C) = f C := by
  simp only [DecreasingGerm.lift, DecreasingGerm.ofChain, IncreasingGerm.lift_ofChain,
    DecreasingChain.toDual_toDual]

def DecreasingGerm.lift₂ {β : Sort*} (f : DecreasingChain α → DecreasingChain α → β)
    (hf : ∀ C C' D D', DecreasingEquivalent C C' → DecreasingEquivalent D D' →
      f C D = f C' D') (g h : DecreasingGerm α) : β :=
  IncreasingGerm.lift₂ (α := αᵒᵈ) (fun C D => f C.toDual D.toDual) (fun C C' D D' hC hD =>
    hf C.toDual C'.toDual D.toDual D'.toDual
      (by
        change IncreasingEquivalent C.toDual.toDual C'.toDual.toDual
        rw [IncreasingChain.toDual_toDual C, IncreasingChain.toDual_toDual C']
        exact hC)
      (by
        change IncreasingEquivalent D.toDual.toDual D'.toDual.toDual
        rw [IncreasingChain.toDual_toDual D, IncreasingChain.toDual_toDual D']
        exact hD)) g h

@[simp] theorem DecreasingGerm.lift₂_ofChain {β : Sort*}
    (f : DecreasingChain α → DecreasingChain α → β)
    (hf : ∀ C C' D D', DecreasingEquivalent C C' → DecreasingEquivalent D D' →
      f C D = f C' D') (C D : DecreasingChain α) :
    DecreasingGerm.lift₂ f hf (DecreasingGerm.ofChain C) (DecreasingGerm.ofChain D) = f C D := by
  simp only [DecreasingGerm.lift₂, DecreasingGerm.ofChain, IncreasingGerm.lift₂_ofChain,
    DecreasingChain.toDual_toDual]

def IncreasingGerm.toDual (g : IncreasingGerm α) : DecreasingGerm αᵒᵈ := g

def DecreasingGerm.toDual (g : DecreasingGerm α) : IncreasingGerm αᵒᵈ := g

@[simp] theorem IncreasingGerm.toDual_ofChain (C : IncreasingChain α) :
    (IncreasingGerm.ofChain C).toDual = DecreasingGerm.ofChain C.toDual := by
  change IncreasingGerm.ofChain C = IncreasingGerm.ofChain C.toDual.toDual
  rw [IncreasingChain.toDual_toDual C]
  rfl

@[simp] theorem DecreasingGerm.toDual_ofChain (C : DecreasingChain α) :
    (DecreasingGerm.ofChain C).toDual = IncreasingGerm.ofChain C.toDual := rfl

@[simp] theorem IncreasingGerm.toDual_toDual (g : IncreasingGerm α) : g.toDual.toDual = g := rfl

@[simp] theorem DecreasingGerm.toDual_toDual (g : DecreasingGerm α) : g.toDual.toDual = g := rfl

def IncreasingGerm.direction (_ : IncreasingGerm α) : OrderDirection := .increasing

def DecreasingGerm.direction (_ : DecreasingGerm α) : OrderDirection := .decreasing

@[simp] theorem IncreasingGerm.direction_toDual (g : IncreasingGerm α) :
    g.toDual.direction = g.direction.dual := rfl

@[simp] theorem DecreasingGerm.direction_toDual (g : DecreasingGerm α) :
    g.toDual.direction = g.direction.dual := rfl

end AharoniKorman.Completion
