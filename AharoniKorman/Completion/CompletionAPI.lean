import AharoniKorman.Completion

/-! The Phase E public-API and axiom gate, including the principal-cut repair.
Only the frozen aggregate interface is imported. The examples use no germ setoid,
quotient constructor, or representative-level domination implementation.
See `COMPLETION_API.md` for assumptions and endpoint conventions. -/

namespace AharoniKorman.Completion.CompletionAPI

noncomputable section

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

example (S : Set α) (hS : S.OrdConnected) : H S ↪o H α :=
  H.mapEmbedding (OrderEmbedding.subtype S) (saturationPreserving_subtype_of_ordConnected hS)

example (C : SaturatedChain α) : H C ↪o H α :=
  H.mapEmbedding (OrderEmbedding.subtype (C : Set α))
    (saturationPreserving_subtype_of_saturated C.saturated)

example (e : α ↪o β) (he : SaturationPreserving e) (X Y : H α) :
    H.mapEmbedding e he X ≤ H.mapEmbedding e he Y ↔ X ≤ Y := H.map_le_map e he X Y

example (e : α ↪o β) (he : SaturationPreserving e) (C : IncreasingChain α) :
    H.map e he (H.increasing (IncreasingGerm.ofChain C)) =
      H.increasing (IncreasingGerm.ofChain (C.map e he)) := rfl

section Linear

variable {γ : Type*} [LinearOrder γ]

example : CompleteLinearOrder (H γ) := inferInstance
example (D : Set (H γ)) : IsLUB D (sSup D) := isLUB_sSup D
example (D : Set (H γ)) : IsGLB D (sInf D) := isGLB_sInf D
example : sSup (∅ : Set (H γ)) = ⊥ := sSup_empty
example : sInf (∅ : Set (H γ)) = ⊤ := sInf_empty
example {D : Set (H γ)} (hne : D.Nonempty) (hnot : sSup D ∉ D) :
    (sSup D).direction = some .increasing := H.sSup_direction_of_not_mem hne hnot
example (f : ℕ → H γ) (hf : StrictMono f) :
    (⨆ n, f n).direction = some .increasing := H.iSup_direction_of_strictMono f hf
example (f : ℕ → H γ) (hf : StrictAnti f) :
    (⨅ n, f n).direction = some .decreasing := H.iInf_direction_of_strictAnti f hf

example (g : IncreasingGerm γ) : (H.increasing g).IsAccumulation ↔
    IsLUB (H.lowerNonprincipal (H.increasing g)) (H.increasing g) := by
  rw [H.isAccumulation_increasing, H.accumulatesBelow_iff_isLUB (H.increasing_ne_bot g)]

example (g : DecreasingGerm γ) : (H.decreasing g).IsAccumulation ↔
    IsGLB (H.upperNonprincipal (H.decreasing g)) (H.decreasing g) := by
  rw [H.isAccumulation_decreasing, H.accumulatesAbove_iff_isGLB (H.decreasing_ne_top g)]

example [Countable γ] (g : IncreasingGerm γ)
    (hg : (H.increasing g).IsAccumulation) :
    ∃ f : ℕ → H γ, StrictMono f ∧
      (∀ n, (f n).IsNonprincipal ∧ f n < H.increasing g) ∧
      IsLUB (Set.range f) (H.increasing g) :=
  (H.isAccumulation_increasing_iff_sequence g).1 hg

example [Countable γ] (g : DecreasingGerm γ)
    (hg : (H.decreasing g).IsAccumulation) :
    ∃ f : ℕ → H γ, StrictAnti f ∧
      (∀ n, (f n).IsNonprincipal ∧ H.decreasing g < f n) ∧
      IsGLB (Set.range f) (H.decreasing g) :=
  (H.isAccumulation_decreasing_iff_sequence g).1 hg

example : (⊤ : H γ).IsIsolated := H.isIsolated_top
example : (⊥ : H γ).IsIsolated := H.isIsolated_bot

end Linear

example (f : SupInfEmbedding α β) (g : SupInfEmbedding β α) (x : α) :
    g.comp f x = g (f x) := SupInfEmbedding.comp_apply g f x

example (f : SupInfEmbedding α β) (T : Set β) (hf : ∀ x, f x ∈ T) :
    (f.codRestrict T hf).HasCofinalRange ↔ ∀ y ∈ T, ∃ x, y ≤ f x :=
  f.codRestrict_cofinal_iff T hf

example {γ : Type*} [LinearOrder γ] (f : SupInfEmbedding γ β)
    (S : Set γ) (hS : S.OrdConnected) {s : Set S} {x : S}
    (hs : s.Nonempty) (hx : IsLUB s x) :
    IsLUB (f.restrictDomain S hS '' s) (f.restrictDomain S hS x) :=
  (f.restrictDomain S hS).map_isLUB hs hx

example (g h k : IncreasingGerm α) (hgh : g.CofinalAbove h) (hhk : h.CofinalAbove k) :
    g.CofinalAbove k := hgh.trans hhk

example (g h : DecreasingGerm α) :
    g.Bicomparable h ↔ g.CoinitialBelow h ∧ h.CoinitialBelow g :=
  DecreasingGerm.bicomparable_iff g h

example [Countable α] (C : IncreasingChain α) :
    ∃ f : ℕ → C.1, StrictMono f ∧ ∀ c : C.1, ∃ n, c < f n :=
  C.exists_cofinal_sequence

example [Countable α] (C : DecreasingChain α) :
    ∃ f : ℕ → C.1, StrictAnti f ∧ ∀ c : C.1, ∃ n, f n < c :=
  C.exists_coinitial_sequence

example (C D : IncreasingChain α) (c : ℕ → C.1) (d : ℕ → D.1)
    (hc : ∀ x : C.1, ∃ n, x < c n) (hd : ∀ y : D.1, ∃ n, y < d n) :
    (IncreasingGerm.ofChain C).Bicomparable (IncreasingGerm.ofChain D) ↔
      (∀ n, ∃ m, (d n).1 < (c m).1) ∧ (∀ n, ∃ m, (c n).1 < (d m).1) :=
  IncreasingChain.bicomparable_iff_sequences C D c d hc hd

example (hα : IsScattered α) {K : Set (H α)} (hK : IsMaxChain (· ≤ ·) K)
    (g : IncreasingGerm α) (hg : H.increasing g ∈ K) :
    H.PrincipalInterpolationBelow K (H.increasing g) :=
  H.principalInterpolationBelow_of_maxChain hα hK g hg

example (hα : IsScattered α) {K : Set (H α)} (hK : IsMaxChain (· ≤ ·) K)
    (g : DecreasingGerm α) (hg : H.decreasing g ∈ K) :
    H.PrincipalInterpolationAbove K (H.decreasing g) :=
  H.principalInterpolationAbove_of_maxChain hα hK g hg

/-- Cofinality in a completion with the formal top imposes no cofinality
condition on the original inclusion: every admissible inclusion satisfies it. -/
theorem map_has_cofinal_image (e : α ↪o β) (he : SaturationPreserving e) :
    ∀ Y : H β, ∃ X : H α, Y ≤ H.map e he X := by
  intro Y
  exact ⟨⊤, by rw [H.map_top]; exact le_top⟩

/-- The same problem occurs dually at the formal bottom. -/
theorem map_has_coinitial_image (e : α ↪o β) (he : SaturationPreserving e) :
    ∀ Y : H β, ∃ X : H α, H.map e he X ≤ Y := by
  intro Y
  exact ⟨⊥, by rw [H.map_bot]; exact bot_le⟩

/-- The vacuity persists when restricted to the paper's nonprincipal subtypes. -/
theorem nonprincipal_cofinal_of_top
    (f : H.N α → H.N β)
    (htop : f ⟨⊤, ⟨.increasing, rfl⟩⟩ = ⟨⊤, ⟨.increasing, rfl⟩⟩) :
    ∀ Y : H.N β, ∃ X : H.N α, Y.1 ≤ (f X).1 := by
  intro Y
  refine ⟨⟨⊤, ⟨.increasing, rfl⟩⟩, ?_⟩
  rw [htop]
  exact le_top

#print axioms H.mapEmbedding
#print axioms H.total
#print axioms H.isLUB_supChain
#print axioms H.instCompleteLinearOrder
#print axioms H.iSup_direction_of_strictMono
#print axioms H.iInf_direction_of_strictAnti
#print axioms nonprincipal_cofinal_of_top
#print axioms SupInfEmbedding.comp
#print axioms SupInfEmbedding.codRestrict
#print axioms SupInfEmbedding.restrictDomain
#print axioms SupInfEmbedding.map_sSup
#print axioms SupInfEmbedding.map_sInf
#print axioms IncreasingGerm.cofinalAbove_ofChain_iff
#print axioms DecreasingGerm.bicomparable_ofChain_iff
#print axioms H.principalInterpolationBelow_of_maxChain
#print axioms H.principalInterpolationAbove_of_maxChain
#print axioms H.principalTrace_nonempty
#print axioms H.exists_principalTrace_extension
#print axioms H.realizeIncreasing_cofinalAbove
#print axioms H.realizeIncreasing_strict_of_principal_bound
#print axioms H.realizeMaxChainIncreasing_cofinalAbove
#print axioms H.realizeMaxChainIncreasing_lt
#print axioms H.sSup_eq_increasing_of_not_mem
#print axioms H.sInf_eq_decreasing_of_not_mem
#print axioms IncreasingChain.exists_cofinal_sequence
#print axioms DecreasingChain.exists_coinitial_sequence
#print axioms IncreasingChain.bicomparable_iff_sequences
#print axioms DecreasingChain.bicomparable_iff_sequences
#print axioms H.exists_strictMono_isLUB
#print axioms H.isAccumulation_dual
#print axioms H.isIsolated_increasing_iff
#print axioms H.isIsolated_decreasing_iff
#print axioms H.accumulatesBelow_iff_isLUB
#print axioms H.accumulatesAbove_iff_isGLB
#print axioms H.accumulatesBelow_iff_cofinal
#print axioms H.accumulatesAbove_iff_coinitial
#print axioms H.isAccumulation_increasing_iff_sequence
#print axioms H.isAccumulation_decreasing_iff_sequence
#print axioms H.isIsolated_top
#print axioms H.isIsolated_bot

end

end AharoniKorman.Completion.CompletionAPI
