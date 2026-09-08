import AharoniKorman.Completion.Order

/-! Representative-independent lower and upper profiles of genuine germs.

Local cofinality for consolidation is inclusion of these profiles. Bicomparability is
equality of profiles; it does not assert equality of germs. This distinction permits a
stable atomic source to acquire a different, non-atomic boundary in a limit chain.
-/

namespace AharoniKorman.Completion

open Set

variable {α : Type*} [PartialOrder α]

namespace IncreasingGerm

/-- The original points strictly below an increasing germ. -/
def lowerProfile (g : IncreasingGerm α) : Set α :=
  {x | H.principal x < H.increasing g}

@[simp] theorem mem_lowerProfile_ofChain (C : IncreasingChain α) (x : α) :
    x ∈ (ofChain C).lowerProfile ↔ ∃ c : C.1, x < c.1 :=
  H.principal_lt_increasing_ofChain x C

theorem representative_mem_lowerProfile (C : IncreasingChain α) (c : C.1) :
    c.1 ∈ (ofChain C).lowerProfile :=
  (mem_lowerProfile_ofChain C c.1).2 (C.2.exists_gt c)

theorem lowerProfile_isLowerSet (g : IncreasingGerm α) : IsLowerSet g.lowerProfile := by
  intro a b hab hb
  exact ((H.principal_le_principal b a).2 hab).trans_lt
    (show H.principal a < H.increasing g from hb)

theorem lowerProfile_nonempty (g : IncreasingGerm α) : g.lowerProfile.Nonempty := by
  induction g using IncreasingGerm.inductionOn with
  | h C =>
    obtain ⟨c, hc⟩ := C.1.nonempty
    exact ⟨c, representative_mem_lowerProfile C ⟨c, hc⟩⟩

/-- The local increasing consolidation condition, without an atomicity restriction. -/
def CofinalAbove (g h : IncreasingGerm α) : Prop := h.lowerProfile ⊆ g.lowerProfile

theorem cofinalAbove_refl (g : IncreasingGerm α) : CofinalAbove g g := Subset.rfl

theorem CofinalAbove.trans {g h k : IncreasingGerm α}
    (hgh : CofinalAbove g h) (hhk : CofinalAbove h k) : CofinalAbove g k :=
  Set.Subset.trans hhk hgh

theorem cofinalAbove_ofChain_iff (C D : IncreasingChain α) :
    CofinalAbove (ofChain C) (ofChain D) ↔ ∀ d : D.1, ∃ c : C.1, d.1 < c.1 := by
  constructor
  · intro h d
    exact (mem_lowerProfile_ofChain C d.1).1 (h (representative_mem_lowerProfile D d))
  · intro h x hx
    obtain ⟨d, hxd⟩ := (mem_lowerProfile_ofChain D x).1 hx
    obtain ⟨c, hdc⟩ := h d
    exact (mem_lowerProfile_ofChain C x).2 ⟨c, hxd.trans hdc⟩

theorem cofinalAbove_of_le {g h : IncreasingGerm α}
    (hgh : H.increasing g ≤ H.increasing h) : CofinalAbove h g := by
  intro x hx
  exact (show H.principal x < H.increasing g from hx).trans_le hgh

/-- The cofinal notion of bicomparability from `def:bicomparable`. -/
def Bicomparable (g h : IncreasingGerm α) : Prop := g.lowerProfile = h.lowerProfile

theorem bicomparable_iff (g h : IncreasingGerm α) :
    Bicomparable g h ↔ CofinalAbove g h ∧ CofinalAbove h g := by
  change g.lowerProfile = h.lowerProfile ↔
    h.lowerProfile ⊆ g.lowerProfile ∧ g.lowerProfile ⊆ h.lowerProfile
  constructor
  · intro heq
    rw [heq]
    exact ⟨Subset.rfl, Subset.rfl⟩
  · exact fun h => Set.Subset.antisymm h.2 h.1

theorem bicomparable_refl (g : IncreasingGerm α) : Bicomparable g g := rfl

theorem Bicomparable.symm {g h : IncreasingGerm α} (hgh : Bicomparable g h) :
    Bicomparable h g := Eq.symm hgh

theorem Bicomparable.trans {g h k : IncreasingGerm α}
    (hgh : Bicomparable g h) (hhk : Bicomparable h k) : Bicomparable g k :=
  Eq.trans hgh hhk

theorem bicomparable_ofChain_iff (C D : IncreasingChain α) :
    Bicomparable (ofChain C) (ofChain D) ↔
      (∀ d : D.1, ∃ c : C.1, d.1 < c.1) ∧ (∀ c : C.1, ∃ d : D.1, c.1 < d.1) := by
  rw [bicomparable_iff, cofinalAbove_ofChain_iff, cofinalAbove_ofChain_iff]

/-- A principal upper bound controls the whole lower profile, not just one representative. -/
theorem lt_principal_iff_profile_bounded (g : IncreasingGerm α) (p : α) :
    H.increasing g < H.principal p ↔ ∀ x ∈ g.lowerProfile, x < p := by
  constructor
  · intro h x hx
    exact (H.principal_lt_principal x p).1 (hx.trans h)
  · induction g using IncreasingGerm.inductionOn with
    | h C =>
      intro h
      exact (H.increasing_ofChain_lt_principal C p).2
        (fun c => h c.1 (representative_mem_lowerProfile C c))

/-- The uniform bound used to keep two images distinct in a sequential limit. -/
theorem lt_principal_of_cofinalAbove {g h : IncreasingGerm α} (hgh : CofinalAbove g h)
    {p : α} (hgp : H.increasing g < H.principal p) : H.increasing h < H.principal p := by
  apply (lt_principal_iff_profile_bounded h p).2
  intro x hx
  exact (lt_principal_iff_profile_bounded g p).1 hgp x (hgh hx)

end IncreasingGerm

namespace DecreasingGerm

/-- The upper profile, obtained from the increasing profile by order duality. -/
def upperProfile (g : DecreasingGerm α) : Set α :=
  IncreasingGerm.lowerProfile (α := αᵒᵈ) g.toDual

/-- The local decreasing consolidation condition. -/
def CoinitialBelow (g h : DecreasingGerm α) : Prop :=
  IncreasingGerm.CofinalAbove (α := αᵒᵈ) g.toDual h.toDual

theorem coinitialBelow_refl (g : DecreasingGerm α) : CoinitialBelow g g :=
  IncreasingGerm.cofinalAbove_refl g.toDual

theorem CoinitialBelow.trans {g h k : DecreasingGerm α}
    (hgh : CoinitialBelow g h) (hhk : CoinitialBelow h k) : CoinitialBelow g k :=
  IncreasingGerm.CofinalAbove.trans hgh hhk

theorem coinitialBelow_ofChain_iff (C D : DecreasingChain α) :
    CoinitialBelow (ofChain C) (ofChain D) ↔ ∀ d : D.1, ∃ c : C.1, c.1 < d.1 :=
  IncreasingGerm.cofinalAbove_ofChain_iff (α := αᵒᵈ) C.toDual D.toDual

/-- Decreasing bicomparability is the dual of increasing bicomparability. -/
def Bicomparable (g h : DecreasingGerm α) : Prop :=
  IncreasingGerm.Bicomparable (α := αᵒᵈ) g.toDual h.toDual

theorem bicomparable_iff (g h : DecreasingGerm α) :
    Bicomparable g h ↔ CoinitialBelow g h ∧ CoinitialBelow h g :=
  IncreasingGerm.bicomparable_iff g.toDual h.toDual

theorem bicomparable_refl (g : DecreasingGerm α) : Bicomparable g g :=
  IncreasingGerm.bicomparable_refl g.toDual

theorem Bicomparable.symm {g h : DecreasingGerm α} (hgh : Bicomparable g h) :
    Bicomparable h g := IncreasingGerm.Bicomparable.symm hgh

theorem Bicomparable.trans {g h k : DecreasingGerm α}
    (hgh : Bicomparable g h) (hhk : Bicomparable h k) : Bicomparable g k :=
  IncreasingGerm.Bicomparable.trans hgh hhk

theorem bicomparable_ofChain_iff (C D : DecreasingChain α) :
    Bicomparable (ofChain C) (ofChain D) ↔
      (∀ d : D.1, ∃ c : C.1, c.1 < d.1) ∧ (∀ c : C.1, ∃ d : D.1, d.1 < c.1) :=
  IncreasingGerm.bicomparable_ofChain_iff (α := αᵒᵈ) C.toDual D.toDual

end DecreasingGerm

end AharoniKorman.Completion
