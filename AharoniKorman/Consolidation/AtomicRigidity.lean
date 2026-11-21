import AharoniKorman.Consolidation.AtomicOrder
import AharoniKorman.Completion.VacillationWitness

/-! Rigidity of self-consolidations, by iterating a moved atom. -/

namespace AharoniKorman.Consolidation

open Set Completion

variable {α : Type*} [PartialOrder α]

private theorem exists_negativeAtom_between_adjacent_positive
    (hsc : IsScattered α) (hvac : IsVacillating α) {C : Set α} (hC : IsSaturatedChain C)
    (g : ℕ → IncreasingGerm α) (hgC : ∀ n, H.increasing (g n) ∈ boundaries C)
    (hg : StrictAnti (fun n => H.increasing (g n))) :
    ∃ (n : ℕ) (Y : AtomProfile C), Y.1.direction = some .decreasing ∧
      H.increasing (g (n+1)) < Y.1 ∧ Y.1 < H.increasing (g n) := by
  classical
  letI : LinearOrder C := hC.1.linearOrder
  let e : C ↪o α := OrderEmbedding.subtype C
  have he : SaturationPreserving e := saturationPreserving_subtype_of_saturated hC
  let mapH := H.mapEmbedding e he
  have preimage (n : ℕ) : ∃ z : IncreasingGerm C, mapH (H.increasing z) = H.increasing (g n) := by
    rcases hgC n with ⟨A, hAC, hA⟩ | ⟨A, hAC, hA⟩
    · refine ⟨IncreasingGerm.ofChain (A.within hAC), ?_⟩
      change H.map e he (H.increasing (IncreasingGerm.ofChain (A.within hAC))) = _
      rw [H.map, IncreasingGerm.map_ofChain,
        show (A.within hAC).map e he = A from A.map_within hAC he]
      exact hA.symm
    · cases hA
  choose r hr using preimage
  have hanti : StrictAnti (fun n => H.increasing (r n)) := by
    intro i j hij
    exact mapH.lt_iff_lt.1 (by simpa only [hr] using hg hij)
  obtain ⟨n, hn⟩ := H.exists_non_wellFounded_positive_gap (hvac.saturated_subtype hC) r hanti
  let J := H.principalInterval (H.increasing (r (n+1))) (H.increasing (r n))
  change ¬ WellFounded ((· < ·) : J → J → Prop) at hn
  rw [RelEmbedding.wellFounded_iff_isEmpty, not_isEmpty_iff] at hn
  obtain ⟨k⟩ := hn
  have hJne : J.Nonempty := ⟨(k 0).1, (k 0).2⟩
  have hJconv : J.OrdConnected := H.principalInterval_ordConnected _ _
  let J' : SaturatedChain Cᵒᵈ := ⟨J, hJne, ((isSaturatedChain_iff _).2 hJconv).dual⟩
  have hk : Nonempty (ℕ ↪o J') := ⟨OrderEmbedding.ofStrictMono
    (fun i => (⟨(k i).1, (k i).2⟩ : J')) (fun i j hij => k.map_rel_iff.2 hij)⟩
  obtain ⟨A, hAJ, hA⟩ := exists_omega_subchain_of_embedding
    (hsc.subtype C).orderDual (hvac.saturated_subtype hC).orderDual J' hk
  let B := A.map e.dual (saturationPreserving_subtype_of_saturated hC.dual)
  have hBC : B.1.carrier ⊆ C := by
    rintro _ ⟨p, _, rfl⟩
    exact p.2
  let b := DecreasingGerm.ofChain A.toDual
  have hrb : H.increasing (r (n+1)) < H.decreasing b := by
    generalize heq : r (n+1) = a
    have hb (p : A.1) : H.increasing a < H.principal (α := C) p.1 :=
      heq ▸ (hAJ p.2).1
    induction a using IncreasingGerm.inductionOn with
    | h D =>
      exact (H.increasing_ofChain_lt_decreasing_ofChain D A.toDual).2
        (fun d p => (H.increasing_ofChain_lt_principal D p.1).1 (hb p) d)
  have hbr : H.decreasing b < H.increasing (r n) := by
    obtain ⟨p, hp⟩ := A.1.nonempty
    have hbp := (H.decreasing_ofChain_lt_principal A.toDual p).2 (A.toDual.2.exists_lt ⟨p, hp⟩)
    exact hbp.trans (hAJ hp).2
  have hmap : mapH (H.decreasing b) = H.decreasing (DecreasingGerm.ofChain B.toDual) := by
    change H.map e he (H.decreasing (DecreasingGerm.ofChain A.toDual)) = _
    simp only [H.map]
    rfl
  have hB : IsNegativeAtom (DecreasingGerm.ofChain B.toDual) := by
    refine ⟨B, ?_, hA.map e.dual (saturationPreserving_subtype_of_saturated hC.dual)⟩
    exact IncreasingGerm.toDual_ofChain B
  refine ⟨n, ⟨_, ⟨Or.inr ⟨B.toDual, hBC, rfl⟩, hB⟩⟩, rfl, ?_, ?_⟩
  · have hlt : mapH (H.increasing (r (n+1))) < mapH (H.decreasing b) := mapH.strictMono hrb
    rwa [hr, hmap] at hlt
  · have hlt : mapH (H.decreasing b) < mapH (H.increasing (r n)) := mapH.strictMono hbr
    rwa [hr, hmap] at hlt

private theorem atomicWitness_positive_le {C : Set α} (hC : IsSaturatedChain C)
    (f : AtomicWitness C C) (X : AtomProfile C) (hX : X.1.direction = some .increasing) :
    f.embedding X ≤ X := by
  have hY := (f.direction X).trans hX
  have hP := f.profile X
  have hXC := X.2.1
  have hYC := (f.embedding X).2.1
  change (f.embedding X).1 ≤ X.1
  rcases (H.direction_eq_increasing_iff _).1 hX with ⟨g, hg⟩ | ht
  · rcases (H.direction_eq_increasing_iff _).1 hY with ⟨d, hd⟩ | ht
    · rw [hg] at hXC hP ⊢
      rw [hd] at hYC hP ⊢
      exact (positive_profile_subset_iff hC hYC hXC).1 hP
    · exact (top_not_mem_boundaries C (ht ▸ hYC)).elim
  · exact (top_not_mem_boundaries C (ht ▸ hXC)).elim

private theorem atomicWitness_negative_ge {C : Set α} (hC : IsSaturatedChain C)
    (f : AtomicWitness C C) (X : AtomProfile C) (hX : X.1.direction = some .decreasing) :
    X ≤ f.embedding X := by
  let Y : AtomProfile (α := αᵒᵈ) C := ⟨X.1.dual, AtomicWitness.atomic_dual_mem (α := α) X.2⟩
  have hY : Y.1.direction = some .increasing := by
    change (H.dual (α := α) X.1).direction = _
    rw [H.direction_dual, hX]
    rfl
  have hle := atomicWitness_positive_le hC.dual f.dual Y hY
  change (f.dual.embedding Y).1 ≤ Y.1 at hle
  rw [show (f.dual.embedding Y).1 = (f.embedding X).1.dual from f.dual_apply X] at hle
  exact (H.dual_le_dual (f.embedding X).1 X.1).1 hle

private theorem atomicWitness_fixes_positive (hsc : IsScattered α) (hvac : IsVacillating α)
    {C : Set α} (hC : IsSaturatedChain C) (f : AtomicWitness C C)
    (X : AtomProfile C) (hX : X.1.direction = some .increasing) : f.embedding X = X := by
  classical
  by_contra hmove
  let x : ℕ → AtomProfile C := Nat.rec X (fun _ y => f.embedding y)
  have hx0 : x 0 = X := rfl
  have hxstep (n : ℕ) : x (n+1) = f.embedding (x n) := rfl
  have hpos (n : ℕ) : (x n).1.direction = some .increasing := by
    induction n with
    | zero => simpa only [hx0] using hX
    | succ n ih => exact (f.direction (x n)).trans ih
  have hne (n : ℕ) : x (n+1) ≠ x n := by
    induction n with
    | zero => exact hmove
    | succ n ih => exact fun heq => ih (f.embedding.injective heq)
  have hanti : StrictAnti x := strictAnti_nat_of_succ_lt (fun n =>
    lt_of_le_of_ne ((hxstep n).symm ▸ atomicWitness_positive_le hC f (x n) (hpos n)) (hne n))
  have hxg (n : ℕ) : ∃ g : IncreasingGerm α, (x n).1 = H.increasing g := by
    rcases (H.direction_eq_increasing_iff _).1 (hpos n) with hg | ht
    · exact hg
    · exact (top_not_mem_boundaries C (ht ▸ (x n).2.1)).elim
  choose g hg using hxg
  have hgC (n : ℕ) : H.increasing (g n) ∈ boundaries C := hg n ▸ (x n).2.1
  have hanti' : StrictAnti (fun n => H.increasing (g n)) := by
    intro i j hij
    change H.increasing (g j) < H.increasing (g i)
    rw [← hg i, ← hg j]
    exact hanti hij
  obtain ⟨n, Y, hY, hlow, hhigh⟩ := exists_negativeAtom_between_adjacent_positive hsc hvac hC g hgC hanti'
  have hYx : Y < x n := by
    change Y.1 < (x n).1
    rwa [hg n]
  have hxY : x (n+1) < Y := by
    change (x (n+1)).1 < Y.1
    rwa [hg (n+1)]
  exact hxY.not_ge ((atomicWitness_negative_ge hC f Y hY).trans
    ((hxstep n).symm ▸ (f.embedding.strictMono hYx).le))

/-- Paper `lem:self-consolidation-trivial`. -/
theorem AtomicWitness.self_eq (hsc : IsScattered α) (hvac : IsVacillating α)
    {C : Set α} (hC : IsSaturatedChain C) (f : AtomicWitness C C) (X : AtomProfile C) :
    f.embedding X = X := by
  obtain ⟨X, hX⟩ := X
  cases X with
  | increasing g => exact atomicWitness_fixes_positive hsc hvac hC f ⟨_, hX⟩ rfl
  | decreasing g =>
    let Y : AtomProfile (α := αᵒᵈ) C :=
      ⟨(H.decreasing g).dual, AtomicWitness.atomic_dual_mem (α := α) hX⟩
    have heq := atomicWitness_fixes_positive hsc.orderDual hvac.orderDual hC.dual f.dual Y rfl
    have hv := congrArg (fun a : AtomProfile (α := αᵒᵈ) C => a.1) heq
    rw [show (f.dual.embedding Y).1 = (f.embedding ⟨_, hX⟩).1.dual from f.dual_apply ⟨_, hX⟩] at hv
    apply Subtype.ext
    exact (H.dualOrderIso (α := α)).injective hv
  | principal _ | bottom | top => exact hX.2.elim

/-- Paper `prop:consolidation-partial`, antisymmetry on atomic profiles. -/
theorem atomicProfiles_eq_of_mutual_consolidation (hsc : IsScattered α) (hvac : IsVacillating α)
    {C D : Set α} (hC : IsSaturatedChain C) (hD : IsSaturatedChain D)
    (hCD : AtomicallyConsolidates C D) (hDC : AtomicallyConsolidates D C) :
    atomicBoundaries C = atomicBoundaries D := by
  obtain ⟨f⟩ := hCD
  obtain ⟨g⟩ := hDC
  have incl {C D : Set α} (hC : IsSaturatedChain C)
      (f : AtomicWitness C D) (g : AtomicWitness D C) : atomicBoundaries C ⊆ atomicBoundaries D := by
    intro a ha
    let X : AtomProfile C := ⟨a, ha⟩
    have hX : g.embedding (f.embedding X) = X := (g.comp f).self_eq hsc hvac hC X
    have hrev := g.improves (f.embedding X)
    rw [hX] at hrev
    have heq : (f.embedding X).1 = X.1 := atomic_eq_of_mutual_improvement
      (f.embedding X).2.2 X.2.2 (f.improves X) hrev
    change X.1 ∈ atomicBoundaries D
    rw [← heq]
    exact (f.embedding X).2
  exact Set.Subset.antisymm (incl hC f g) (incl hD g f)

/-- The atomic profiles realized by saturated chains, using the paper's definition of atomicity. -/
@[ext] structure RealizedAtomicProfile (α : Type*) [PartialOrder α] where
  atoms : Set (H α)
  realized : ∃ C : Set α, IsSaturatedChain C ∧ paperAtomicBoundaries C = atoms

/-- Paper `prop:consolidation-partial` as a partial order on the realized profiles. -/
instance [Fact (IsScattered α)] [Fact (IsVacillating α)] :
    PartialOrder (RealizedAtomicProfile α) where
  le A B := Nonempty (ConsolidationWitness A.1 B.1)
  le_refl _ := ⟨⟨(OrderIso.refl _).toOrderEmbedding, fun _ => rfl, fun _ => Subset.rfl⟩⟩
  le_trans A B C hAB hBC := by
    obtain ⟨f⟩ := hAB
    obtain ⟨g⟩ := hBC
    exact ⟨⟨f.embedding.trans g.embedding, fun x => (g.direction _).trans (f.direction x),
      fun x => (g.profile _).trans (f.profile x)⟩⟩
  le_antisymm A B hAB hBA := by
    obtain ⟨C, hC, hCA⟩ := A.2
    obtain ⟨D, hD, hDB⟩ := B.2
    have hAC : A.1 = atomicBoundaries C := hCA.symm.trans (paperAtomicBoundaries_eq Fact.out C)
    have hBD : B.1 = atomicBoundaries D := hDB.symm.trans (paperAtomicBoundaries_eq Fact.out D)
    change Nonempty (ConsolidationWitness A.1 B.1) at hAB
    change Nonempty (ConsolidationWitness B.1 A.1) at hBA
    rw [hAC, hBD] at hAB hBA
    exact RealizedAtomicProfile.ext (hAC.trans ((atomicProfiles_eq_of_mutual_consolidation Fact.out Fact.out
      hC hD hAB hBA).trans hBD.symm))

end AharoniKorman.Consolidation
