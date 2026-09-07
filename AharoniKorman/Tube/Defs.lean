import AharoniKorman.Preliminaries.Spine
import AharoniKorman.Preliminaries.Relations

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- Every point of `T` is incomparable with only finitely many points of `T`. -/
def IsTube (T : Set α) : Prop :=
  ∀ x ∈ T, (T ∩ incomparableSet x).Finite

/-- Inclusion-maximality among tubes, written in the one-point form used in the paper. -/
def IsMaximalTube (T : Set α) : Prop :=
  IsTube T ∧ ∀ x ∉ T, ¬ IsTube (insert x T)

theorem IsTube.mono {S T : Set α} (hT : IsTube T) (hST : S ⊆ T) : IsTube S := by
  intro x hx
  exact (hT x (hST hx)).subset (inter_subset_inter_left _ hST)

/-- Every chain is a tube. -/
theorem IsChain.isTube {C : Set α} (hC : IsChain (· ≤ ·) C) : IsTube C := by
  intro x hx
  have hEmpty : C ∩ incomparableSet x = ∅ := by
    ext y
    constructor
    · rintro ⟨hy, hinc⟩
      have hne : y ≠ x := (show Incomparable x y from hinc).symm.ne
      rcases hC hx hy hne.symm with hxy | hyx
      · exact False.elim ((show Incomparable x y from hinc).not_le hxy)
      · exact False.elim ((show Incomparable x y from hinc).not_ge hyx)
    · simp
  rw [hEmpty]
  exact Set.finite_empty

/-- A point can be adjoined to a tube when it has finite incomparability inside the tube. -/
theorem IsTube.insert {T : Set α} (hT : IsTube T) {x : α}
    (hx : (T ∩ incomparableSet x).Finite) : IsTube (insert x T) := by
  intro y hy
  rcases hy with rfl | hy
  · apply hx.subset
    rintro z ⟨hz, hinc⟩
    refine ⟨?_, hinc⟩
    rcases hz with rfl | hz
    · exact False.elim (hinc.not_le le_rfl)
    · exact hz
  · apply ((hT y hy).insert x).subset
    rintro z ⟨hz, hinc⟩
    rcases hz with rfl | hz
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem x ⟨hz, hinc⟩

/-- The useful outside-point characterization of maximal tubes. -/
theorem isMaximalTube_iff (T : Set α) :
    IsMaximalTube T ↔ IsTube T ∧ ∀ x ∉ T, (T ∩ incomparableSet x).Infinite := by
  constructor
  · rintro ⟨hT, hmax⟩
    refine ⟨hT, fun x hx => ?_⟩
    intro hfinite
    exact hmax x hx (hT.insert hfinite)
  · rintro ⟨hT, hout⟩
    refine ⟨hT, fun x hx hinsert => ?_⟩
    apply hout x hx
    exact (hinsert x (Set.mem_insert x T)).subset fun z hz =>
      ⟨Set.mem_insert_of_mem x hz.1, hz.2⟩

theorem IsMaximalTube.nonempty [Nonempty α] {T : Set α} (hT : IsMaximalTube T) :
    T.Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty α›
  by_contra hne
  have hx : x ∉ T := fun hx => hne ⟨x, hx⟩
  have hinfinite := (isMaximalTube_iff T).mp hT |>.2 x hx
  apply hinfinite
  have hempty : T ∩ incomparableSet x = ∅ := Set.not_nonempty_iff_eq_empty.mp
    (fun ⟨y, hy⟩ => hne ⟨y, hy.1⟩)
  rw [hempty]
  exact Set.finite_empty

end AharoniKorman
