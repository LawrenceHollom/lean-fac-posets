import AharoniKorman.Completion.PrincipalInterpolation

/-! Principal-cut realization for consolidation limits.

The interpolation hypothesis is stated explicitly and supplied by
`principalInterpolationBelow_of_maxChain`. These lemmas check the ensuing construction
and the strict-separation safeguard without assuming that the old germ has a
representative in the final chain. See `CONSOLIDATION_LIMIT_REPAIR.md`, Section 4.
-/

namespace AharoniKorman.Completion

open Set

variable {α : Type*} [PartialOrder α]

namespace H

/-- Extend the principal trace, after proving that it is a nonempty chain. -/
theorem exists_principalTrace_extension [Nonempty α] (hα : IsScattered α)
    {K : Set (H α)} (hK : IsMaxChain (· ≤ ·) K) :
    ∃ C : SaturatedChain α, IsMaxChain (· ≤ ·) (C : Set α) ∧
      ∀ e : α, principal e ∈ K → e ∈ C := by
  let E : Set α := {e | principal e ∈ K}
  have hE : IsChain (· ≤ ·) E := by
    intro x hx y hy _
    exact (hK.1.total hx hy).imp ((principal_le_principal x y).1)
      ((principal_le_principal y x).1)
  obtain ⟨C, hC, hEC⟩ := hE.exists_maxChain
  obtain ⟨e, he⟩ := principalTrace_nonempty hα hK
  have hsat : IsSaturatedChain C := by
    refine ⟨hC.1, ?_⟩
    intro a b x _ _ _ _ hx
    have heq : insert x C = C :=
      (hC.2 (hC.1.insert (fun c hc _ => hx c hc)) (Set.subset_insert _ _)).symm
    exact heq ▸ Set.mem_insert _ _
  exact ⟨⟨C, ⟨e, hEC he⟩, hsat⟩, hC, fun p hp => hEC hp⟩

/-- A maximal completion chain's principal trace cannot be bounded by a principal
point lying strictly below a boundary with principal interpolation. -/
theorem principalTrace_escape_bound {K : Set (H α)} (hK : IsMaxChain (· ≤ ·) K)
    {g : H α} (hg : g ∈ K) (hi : PrincipalInterpolationBelow K g)
    {p : α} (hpg : principal p < g) :
    ∃ e : α, principal e ∈ K ∧ principal e < g ∧ ¬ e ≤ p := by
  classical
  by_contra hno
  have hb : ∀ e : α, principal e ∈ K → principal e < g → e ≤ p := by
    intro e he heg
    by_contra hep
    exact hno ⟨e, he, heg, hep⟩
  have hcomp : ∀ a ∈ K, principal p ≠ a → principal p ≤ a ∨ a ≤ principal p := by
    intro a ha _
    rcases hK.1.total ha hg with hag | hga
    · by_cases heq : a = g
      · exact Or.inl (heq ▸ hpg.le)
      obtain ⟨e, he, hae, heg⟩ := hi a ha (lt_of_le_of_ne hag heq)
      exact Or.inr (hae.le.trans ((principal_le_principal e p).2 (hb e he heg)))
    · exact Or.inl (hpg.le.trans hga)
  have hpK : principal p ∈ K := by
    have heq : insert (principal p) K = K :=
      (hK.2 (hK.1.insert hcomp) (Set.subset_insert _ _)).symm
    exact heq ▸ Set.mem_insert _ _
  obtain ⟨e, he, hpe, heg⟩ := hi (principal p) hpK hpg
  exact ((principal_lt_principal p e).1 hpe).not_ge (hb e he heg)

/-- The initial segment generated in the final chain by trace points below a boundary. -/
def lowerTraceCut (K : Set (H α)) (C : SaturatedChain α) (g : H α) : Set α :=
  {x | x ∈ C ∧ ∃ e : α, principal e ∈ K ∧ principal e < g ∧ x ≤ e}

theorem lowerTraceCut_initial (K : Set (H α)) (C : SaturatedChain α) (g : H α) :
    IsInitialSegment (lowerTraceCut K C g) C := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  rintro x y ⟨hx, e, he, heg, hxe⟩ hy hyx
  exact ⟨hy, e, he, heg, hyx.trans hxe⟩

theorem lowerTraceCut_nonempty {K : Set (H α)} {C : SaturatedChain α} {g : H α}
    (hEC : ∀ e : α, principal e ∈ K → e ∈ C)
    (hne : ∃ e : α, principal e ∈ K ∧ principal e < g) :
    (lowerTraceCut K C g).Nonempty := by
  obtain ⟨e, he, heg⟩ := hne
  exact ⟨e, hEC e he, e, he, heg, le_rfl⟩

/-- Realize an increasing boundary by an initial segment of the final chain. -/
def realizeIncreasing (K : Set (H α)) (C : SaturatedChain α) (g : H α)
    (hEC : ∀ e : α, principal e ∈ K → e ∈ C)
    (hne : ∃ e : α, principal e ∈ K ∧ principal e < g)
    (hi : PrincipalInterpolationBelow K g) : IncreasingChain α := by
  let T := C.restrict .decreasing (lowerTraceCut K C g)
    (lowerTraceCut_initial K C g) (lowerTraceCut_nonempty hEC hne)
  refine ⟨T, ?_⟩
  rintro ⟨m, hm⟩
  obtain ⟨hmC, e, he, heg, hme⟩ := m.2
  obtain ⟨d, hd, hed, hdg⟩ := hi (principal e) he heg
  have hdT : d ∈ T := ⟨hEC d hd, d, hd, hdg, le_rfl⟩
  have hmd : m.1 < d := hme.trans_lt ((principal_lt_principal e d).1 hed)
  exact hmd.not_ge (hm ⟨d, hdT⟩)

@[simp] theorem mem_realizeIncreasing (K : Set (H α)) (C : SaturatedChain α) (g : H α)
    (hEC : ∀ e : α, principal e ∈ K → e ∈ C)
    (hne : ∃ e : α, principal e ∈ K ∧ principal e < g)
    (hi : PrincipalInterpolationBelow K g) (x : α) :
    x ∈ (realizeIncreasing K C g hEC hne hi).1 ↔ x ∈ lowerTraceCut K C g := Iff.rfl

theorem realizeIncreasing_cofinalAbove {K : Set (H α)} {C : SaturatedChain α}
    (g : IncreasingGerm α)
    (hEC : ∀ e : α, principal e ∈ K → e ∈ C)
    (hne : ∃ e : α, principal e ∈ K ∧ principal e < increasing g)
    (hi : PrincipalInterpolationBelow K (increasing g)) :
    g.CofinalAbove (IncreasingGerm.ofChain
      (realizeIncreasing K C (increasing g) hEC hne hi)) := by
  intro x hx
  obtain ⟨c, hxc⟩ := (IncreasingGerm.mem_lowerProfile_ofChain _ x).1 hx
  obtain ⟨_, e, _, heg, hce⟩ := c.2
  exact ((principal_lt_principal x e).2 (hxc.trans_le hce)).trans heg

/-- Uniform principal bounds prevent distinct limit images from merging, even if
the boundary being realized was atomic and its new realization is non-atomic. -/
theorem realizeIncreasing_strict_of_principal_bound
    {K : Set (H α)} (hK : IsMaxChain (· ≤ ·) K) {C : SaturatedChain α}
    {g : H α} (hg : g ∈ K)
    (hEC : ∀ e : α, principal e ∈ K → e ∈ C)
    (hne : ∃ e : α, principal e ∈ K ∧ principal e < g)
    (hi : PrincipalInterpolationBelow K g)
    (T : IncreasingChain α) (hTC : (T.1 : Set α) ⊆ C)
    {p : α} (hTp : increasing (IncreasingGerm.ofChain T) < principal p)
    (hpg : principal p < g) :
    increasing (IncreasingGerm.ofChain T) <
      increasing (IncreasingGerm.ofChain (realizeIncreasing K C g hEC hne hi)) := by
  obtain ⟨e, he, heg, hep⟩ := principalTrace_escape_bound hK hg hi hpg
  have hTe : increasing (IncreasingGerm.ofChain T) < principal e := by
    apply (increasing_ofChain_lt_principal T e).2
    intro t
    have htp := (increasing_ofChain_lt_principal T p).1 hTp t
    rcases C.isChain.total (hTC t.2) (hEC e he) with hte | het
    · exact lt_of_le_of_ne hte (fun heq => hep (heq ▸ htp.le))
    · exact False.elim (hep (het.trans htp.le))
  apply hTe.trans
  apply (principal_lt_increasing_ofChain _ _).2
  let eT : (realizeIncreasing K C g hEC hne hi).1 :=
    ⟨e, hEC e he, e, he, heg, le_rfl⟩
  exact (realizeIncreasing K C g hEC hne hi).2.exists_gt eT

/-- The increasing realization with its interpolation obligations discharged. -/
def realizeMaxChainIncreasing (hα : IsScattered α)
    {K : Set (H α)} (hK : IsMaxChain (· ≤ ·) K) (C : SaturatedChain α)
    (hEC : ∀ e : α, principal e ∈ K → e ∈ C)
    (g : IncreasingGerm α) (hg : increasing g ∈ K) : IncreasingChain α :=
  realizeIncreasing K C (increasing g) hEC
    (by
      obtain ⟨e, he, _, heg⟩ := principalInterpolationBelow_of_maxChain hα hK g hg
        ⊥ hK.bot_mem (bot_lt_iff_ne_bot.2 (increasing_ne_bot g))
      exact ⟨e, he, heg⟩)
    (principalInterpolationBelow_of_maxChain hα hK g hg)

theorem realizeMaxChainIncreasing_cofinalAbove (hα : IsScattered α)
    {K : Set (H α)} (hK : IsMaxChain (· ≤ ·) K) (C : SaturatedChain α)
    (hEC : ∀ e : α, principal e ∈ K → e ∈ C)
    (g : IncreasingGerm α) (hg : increasing g ∈ K) :
    g.CofinalAbove (IncreasingGerm.ofChain (realizeMaxChainIncreasing hα hK C hEC g hg)) :=
  realizeIncreasing_cofinalAbove g hEC _ _

/-- Ordered increasing constraints remain strictly ordered after realization. -/
theorem realizeMaxChainIncreasing_lt (hα : IsScattered α)
    {K : Set (H α)} (hK : IsMaxChain (· ≤ ·) K) (C : SaturatedChain α)
    (hEC : ∀ e : α, principal e ∈ K → e ∈ C)
    (g h : IncreasingGerm α) (hg : increasing g ∈ K) (hh : increasing h ∈ K)
    (hgh : increasing g < increasing h) :
    increasing (IncreasingGerm.ofChain (realizeMaxChainIncreasing hα hK C hEC g hg)) <
      increasing (IncreasingGerm.ofChain (realizeMaxChainIncreasing hα hK C hEC h hh)) := by
  obtain ⟨p, hgp, hph⟩ := exists_principal_between_increasing hgh
  have hcutp := IncreasingGerm.lt_principal_of_cofinalAbove
    (realizeMaxChainIncreasing_cofinalAbove hα hK C hEC g hg) hgp
  apply realizeIncreasing_strict_of_principal_bound hK hh hEC _ _
    (realizeMaxChainIncreasing hα hK C hEC g hg) (fun _ hx => hx.1) hcutp hph

end H

end AharoniKorman.Completion
