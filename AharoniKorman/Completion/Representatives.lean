import AharoniKorman.Completion.Construction

/-! Representatives of genuine nonprincipal points (paper `def:h-p`).
The formal endpoints have no representative; every other nonprincipal point does.
All germ operations here use the public Phase C API. -/

namespace AharoniKorman.Completion

variable {α : Type*} [PartialOrder α]

namespace H

/-- A saturated chain represents a genuine germ, with its direction determined by the point. -/
def Represents (C : SaturatedChain α) : H α → Prop
  | increasing g => ∃ h : C.NoTop, g.Represents ⟨C, h⟩
  | decreasing g => ∃ h : C.NoBottom, g.Represents ⟨C, h⟩
  | _ => False

@[simp] theorem represents_principal (C : SaturatedChain α) (x : α) :
    ¬Represents C (principal x) := id
@[simp] theorem represents_bot (C : SaturatedChain α) : ¬Represents C (⊥ : H α) := id
@[simp] theorem represents_top (C : SaturatedChain α) : ¬Represents C (⊤ : H α) := id

@[simp] theorem represents_increasing (C : IncreasingChain α) (g : IncreasingGerm α) :
    Represents C.1 (increasing g) ↔ g.Represents C := by
  constructor
  · rintro ⟨_, h⟩; exact h
  · exact fun h => ⟨C.2, h⟩

@[simp] theorem represents_decreasing (C : DecreasingChain α) (g : DecreasingGerm α) :
    Represents C.1 (decreasing g) ↔ g.Represents C := by
  constructor
  · rintro ⟨_, h⟩; exact h
  · exact fun h => ⟨C.2, h⟩

theorem change_increasing_representative {C D : IncreasingChain α} {g : IncreasingGerm α}
    (hC : Represents C.1 (increasing g)) :
    Represents D.1 (increasing g) ↔ IncreasingEquivalent D C := by
  rw [represents_increasing] at hC ⊢
  exact IncreasingGerm.represents_iff hC

theorem change_decreasing_representative {C D : DecreasingChain α} {g : DecreasingGerm α}
    (hC : Represents C.1 (decreasing g)) :
    Represents D.1 (decreasing g) ↔ DecreasingEquivalent D C := by
  rw [represents_decreasing] at hC ⊢
  exact DecreasingGerm.represents_iff hC

theorem exists_representative {X : H α} (hX : X.IsNonprincipal)
    (hb : X ≠ ⊥) (ht : X ≠ ⊤) : ∃ C, Represents C X := by
  cases X with
  | principal x => rcases hX with ⟨d, hd⟩; cases hd
  | increasing g =>
      obtain ⟨C, hC⟩ := g.exists_representative
      exact ⟨C.1, C.2, hC⟩
  | decreasing g =>
      obtain ⟨C, hC⟩ := g.exists_representative
      exact ⟨C.1, C.2, hC⟩
  | bottom => exact (hb rfl).elim
  | top => exact (ht rfl).elim

noncomputable def representative (X : H α) (hX : X.IsNonprincipal)
    (hb : X ≠ ⊥) (ht : X ≠ ⊤) : SaturatedChain α :=
  Classical.choose (exists_representative hX hb ht)

theorem representative_spec (X : H α) (hX : X.IsNonprincipal)
    (hb : X ≠ ⊥) (ht : X ≠ ⊤) : Represents (representative X hX hb ht) X :=
  Classical.choose_spec (exists_representative hX hb ht)

theorem Represents.dual {C : SaturatedChain α} {X : H α} (h : Represents C X) :
    Represents C.dual X.dual := by
  cases X with
  | principal x => exact h.elim
  | bottom => exact h.elim
  | top => exact h.elim
  | increasing g =>
      obtain ⟨hn, hC⟩ := h
      refine ⟨(SaturatedChain.dual_noBottom_iff C).2 hn, ?_⟩
      exact (IncreasingGerm.toDual_ofChain (show IncreasingChain α from ⟨C, hn⟩)).symm.trans
        (congrArg IncreasingGerm.toDual hC)
  | decreasing g =>
      obtain ⟨hn, hC⟩ := h
      refine ⟨(SaturatedChain.dual_noTop_iff C).2 hn, ?_⟩
      exact (DecreasingGerm.toDual_ofChain (show DecreasingChain α from ⟨C, hn⟩)).symm.trans
        (congrArg DecreasingGerm.toDual hC)

end H

end AharoniKorman.Completion
