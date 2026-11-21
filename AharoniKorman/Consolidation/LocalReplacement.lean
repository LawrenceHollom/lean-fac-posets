import AharoniKorman.Consolidation.OrderedBoundaries

namespace AharoniKorman.Consolidation

noncomputable section

open Set Completion

variable {α : Type*} [PartialOrder α]

/-- The concrete replacement geometry; no existence assumption is hidden here. -/
structure LocalReplacement (C : MaximalChains α) where
  target : MaximalChains α
  left : Set α
  middle : SaturatedChain α
  right : Set α
  decomposition : C.carrier = (left ∪ (middle : Set α)) ∪ right
  left_middle : SetStrictLT left (middle : Set α)
  middle_right : SetStrictLT (middle : Set α) right
  finite_initial : FiniteInitialIntervals (middle : Set α)
  replacement : IncreasingChain α
  left_replacement : SetStrictLT left (replacement.1 : Set α)
  replacement_right : SetStrictLT (replacement.1 : Set α) right
  left_target : left ⊆ target.carrier
  right_target : right ⊆ target.carrier
  replacement_target : (replacement.1 : Set α) ⊆ target.carrier
  profile_control : (middle : Set α).Infinite → ∀ y ∈ replacement.1, ∃ j ∈ middle, y < j
  separating_point : ∃ k ∈ C.carrier, (replacement.1 : Set α) ⊆ incomparableSet k

namespace LocalReplacement

variable {C : MaximalChains α} (Q : LocalReplacement C)

theorem left_right : SetStrictLT Q.left Q.right := by
  obtain ⟨j, hj⟩ := Q.middle.nonempty
  exact fun _ hl _ hr => (Q.left_middle hl hj).trans (Q.middle_right hj hr)

theorem boundary_split : boundaries C.carrier =
    (boundaries Q.left ∪ boundaries (Q.middle : Set α)) ∪ boundaries Q.right := by
  rw [Q.decomposition, boundaries_ordered_union, boundaries_ordered_union Q.left_middle]
  rintro x (hx | hx) y hy
  · exact Q.left_right hx hy
  · exact Q.middle_right hx hy

def newBoundary : Boundary Q.target.carrier :=
  ⟨H.increasing (IncreasingGerm.ofChain Q.replacement), Or.inl ⟨Q.replacement, Q.replacement_target, rfl⟩⟩

theorem middle_properties : (boundaries (Q.middle : Set α)).Subsingleton ∧
    (∀ X ∈ boundaries (Q.middle : Set α), IsAtomicGerm X) ∧
    ∀ X ∈ boundaries (Q.middle : Set α), GermImproves Q.newBoundary.1 X := by
  classical
  by_cases hfin : (Q.middle : Set α).Finite
  · rw [boundaries_eq_empty_of_finite hfin]
    exact ⟨Set.subsingleton_empty, fun _ h => h.elim, fun _ h => h.elim⟩
  · have hinf : (Q.middle : Set α).Infinite := hfin
    obtain ⟨htop, homega⟩ := Q.finite_initial.omega hinf
    let A : IncreasingChain α := ⟨Q.middle, htop⟩
    have heq : boundaries (Q.middle : Set α) = {H.increasing (IncreasingGerm.ofChain A)} :=
      omega_boundaries_singleton A Q.finite_initial
    rw [heq]
    refine ⟨Set.subsingleton_singleton, ?_, ?_⟩
    · rintro X rfl
      exact ⟨A, rfl, homega⟩
    · rintro X rfl
      refine ⟨rfl, ?_⟩
      intro p hp
      obtain ⟨y, hpy⟩ := (IncreasingGerm.mem_lowerProfile_ofChain Q.replacement p).1 hp
      obtain ⟨j, hj, hyj⟩ := Q.profile_control hinf y.1 y.2
      exact (IncreasingGerm.mem_lowerProfile_ofChain A p).2 ⟨⟨j, hj⟩, hpy.trans hyj⟩

def mapBoundary (X : Boundary C.carrier) : Boundary Q.target.carrier := by
  classical
  by_cases hmid : X.1 ∈ boundaries (Q.middle : Set α)
  · exact Q.newBoundary
  · refine ⟨X.1, ?_⟩
    have hX := X.2
    change X.1 ∈ boundaries C.carrier at hX
    rw [Q.boundary_split] at hX
    rcases hX with (hl | hm) | hr
    · exact boundaries_mono Q.left_target hl
    · exact False.elim (hmid hm)
    · exact boundaries_mono Q.right_target hr

theorem mapBoundary_eq_new {X : Boundary C.carrier} (hX : X.1 ∈ boundaries (Q.middle : Set α)) :
    Q.mapBoundary X = Q.newBoundary := by simp only [mapBoundary, dif_pos hX]

theorem mapBoundary_eq_self {X : Boundary C.carrier} (hX : X.1 ∉ boundaries (Q.middle : Set α)) :
    (Q.mapBoundary X).1 = X.1 := by simp only [mapBoundary, dif_neg hX]

theorem mapBoundary_strict : StrictMono Q.mapBoundary := by
  classical
  intro X Y hXY
  change (Q.mapBoundary X).1 < (Q.mapBoundary Y).1
  by_cases hx : X.1 ∈ boundaries (Q.middle : Set α) <;>
    by_cases hy : Y.1 ∈ boundaries (Q.middle : Set α)
  · exact False.elim (hXY.ne (Subtype.ext (Q.middle_properties.1 hx hy)))
  · rw [Q.mapBoundary_eq_new hx, Q.mapBoundary_eq_self hy]
    have hY := Y.2
    change Y.1 ∈ boundaries C.carrier at hY
    rw [Q.boundary_split] at hY
    rcases hY with (hyl | hym) | hyr
    · exact False.elim (hXY.not_gt (boundaries_strictLT Q.left_middle hyl hx))
    · exact False.elim (hy hym)
    · exact boundaries_strictLT Q.replacement_right (Or.inl ⟨Q.replacement, Subset.rfl, rfl⟩) hyr
  · rw [Q.mapBoundary_eq_self hx, Q.mapBoundary_eq_new hy]
    have hX := X.2
    change X.1 ∈ boundaries C.carrier at hX
    rw [Q.boundary_split] at hX
    rcases hX with (hxl | hxm) | hxr
    · exact boundaries_strictLT Q.left_replacement hxl (Or.inl ⟨Q.replacement, Subset.rfl, rfl⟩)
    · exact False.elim (hx hxm)
    · exact False.elim (hXY.not_gt (boundaries_strictLT Q.middle_right hy hxr))
  · rw [Q.mapBoundary_eq_self hx, Q.mapBoundary_eq_self hy]
    exact hXY

theorem newBoundary_not_old : Q.newBoundary.1 ∉ boundaries C.carrier := by
  intro hOld
  obtain ⟨k, hkC, hinc⟩ := Q.separating_point
  have hbinc : Incomparable Q.newBoundary.1 (H.principal k) :=
    boundary_incomparable_principal hinc (Or.inl ⟨Q.replacement, Subset.rfl, rfl⟩)
  exact (boundary_comparable_principal C.isSaturated hOld hkC).elim hbinc.not_le hbinc.not_ge

end LocalReplacement

end

end AharoniKorman.Consolidation
