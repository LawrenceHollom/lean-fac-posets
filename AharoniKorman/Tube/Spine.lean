import AharoniKorman.Tube.LimitPoints
import AharoniKorman.Preliminaries.FiniteIntervals
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.Ultrafilter.Basic

/-! The finite height construction and the compactness step in `thm:zaguia-spine-reformed`. -/

namespace AharoniKorman

open Set Filter Completion

variable {α : Type*} [PartialOrder α]

/-- Assign each point to the representative of its antichain. -/
structure SpineAssignment (f : α → α) : Prop where
  fixed : ∀ x, f (f x) = f x
  comparable : ∀ x y, Comparable (f x) (f y)
  separates : ∀ ⦃x y⦄, x < y → f x ≠ f y

theorem SpineAssignment.spineData {f : α → α} (h : SpineAssignment f) :
    Nonempty (SpineData univ (range f)) := by
  refine ⟨⟨?_, subset_univ _, fun x => f ⁻¹' {x.1}, ?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _
    exact h.comparable x y
  · intro c x hx y hy hne hle
    exact h.separates (lt_of_le_of_ne hle hne) ((mem_singleton_iff.mp hx).trans
      (mem_singleton_iff.mp hy).symm)
  · intro c
    obtain ⟨x, hx⟩ := c.2
    exact mem_singleton_iff.mpr (hx ▸ h.fixed x)
  · intro x y hne
    exact disjoint_left.mpr fun a ha hb => hne (Subtype.ext
      ((mem_singleton_iff.mp ha).symm.trans (mem_singleton_iff.mp hb)))
  · apply eq_univ_of_forall
    intro x
    exact mem_iUnion_of_mem ⟨f x, mem_range_self x⟩ rfl

private theorem SpineAssignment.hasSpine {f : α → α} (h : SpineAssignment f) :
    HasSpine α := ⟨range f, h.spineData⟩

/-- The height of a point in a finite partial order is the largest cardinality of a chain
below it. A longest chain contains a representative of every height. -/
private theorem exists_finiteSpineAssignment [Finite α] : ∃ f : α → α, SpineAssignment f := by
  classical
  let := Fintype.ofFinite α
  let chains := (Finset.univ : Finset α).powerset.filter
    (fun S : Finset α => IsChain (· ≤ ·) (S : Set α))
  have mem_chains (S : Finset α) : S ∈ chains ↔ IsChain (· ≤ ·) (S : Set α) := by
    simp [chains]
  obtain ⟨C, hCmem, hCmax⟩ := chains.exists_max_image Finset.card
    ⟨∅, (mem_chains ∅).2 (by simp)⟩
  have hC := (mem_chains C).1 hCmem
  let below (x : α) := chains.filter (fun S => ∀ y ∈ S, y ≤ x)
  have below_nonempty (x : α) : (below x).Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨(mem_chains ∅).2 (by simp), by simp⟩⟩
  let height (x : α) := (below x).sup Finset.card
  have exists_height_chain (x : α) : ∃ S ∈ below x, height x = S.card :=
    Finset.exists_mem_eq_sup _ (below_nonempty x) _
  have height_strict : StrictMono height := by
    intro x y hxy
    obtain ⟨S, hS, hheight⟩ := exists_height_chain x
    obtain ⟨hSchain, hSle⟩ := Finset.mem_filter.mp hS
    have hyS : y ∉ S := fun hy => hxy.not_ge (hSle y hy)
    have hins : insert y S ∈ below y := by
      refine Finset.mem_filter.mpr ⟨(mem_chains _).2 ?_, ?_⟩
      · rw [Finset.coe_insert]
        exact ((mem_chains S).1 hSchain).insert fun b hb _ =>
          Or.inr ((hSle b hb).trans hxy.le)
      · intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact le_rfl
        · exact (hSle b hb).trans hxy.le
    have hcard : (insert y S).card ≤ height y := Finset.le_sup hins
    rw [Finset.card_insert_of_notMem hyS, ← hheight] at hcard
    exact hcard
  have height_bounds (x : α) : 1 ≤ height x ∧ height x ≤ C.card := by
    refine ⟨?_, Finset.sup_le fun S hS => hCmax S (Finset.mem_filter.mp hS).1⟩
    have hsingle : {x} ∈ below x := by simp [below, mem_chains]
    simpa only [Finset.card_singleton] using (Finset.le_sup (f := Finset.card) hsingle)
  have height_inj : Set.InjOn height (C : Set α) := by
    intro a ha b hb hab
    by_contra hne
    rcases hC.lt_of_le ha hb hne with h | h
    · exact (height_strict h).ne hab
    · exact (height_strict h).ne hab.symm
  let levels := (Finset.range (C.card + 1)).erase 0
  have hlevels : C.image height = levels := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro n hn
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨hlow, hhigh⟩ := height_bounds x
      simp [levels, Nat.ne_of_gt hlow, Nat.lt_succ_of_le hhigh]
    · rw [Finset.card_image_of_injOn height_inj]
      simp [levels]
  have choose_rep (x : α) : ∃ y ∈ C, height y = height x := by
    apply Finset.mem_image.mp
    rw [hlevels]
    obtain ⟨hlow, hhigh⟩ := height_bounds x
    simp [levels, Nat.ne_of_gt hlow, Nat.lt_succ_of_le hhigh]
  choose f hfC hfheight using choose_rep
  refine ⟨f, ⟨fun x => height_inj (hfC (f x)) (hfC x) (hfheight (f x)),
    fun x y => hC.total (hfC x) (hfC y), ?_⟩⟩
  intro x y hxy heq
  exact (height_strict hxy).ne ((hfheight x).symm.trans (heq ▸ hfheight y))

/-- If every point has finitely many incomparable points, finite spine assignments have a
compatible limit. Each point's representative is chosen from itself and its incomparable points. -/
private theorem spine_of_finite_stages {ι : Type*} (l : Filter ι) [l.NeBot]
    (stage : ι → Finset α) (covers : ∀ x : α, ∀ᶠ n in l, x ∈ stage n)
    (hT : IsTube (univ : Set α)) : HasSpine α := by
  classical
  let localAssignment (s : Finset α) : (↑s : Set α) → (↑s : Set α) :=
    (exists_finiteSpineAssignment (α := (↑s : Set α))).choose
  have localSpec (s : Finset α) : SpineAssignment (localAssignment s) :=
    (exists_finiteSpineAssignment (α := (↑s : Set α))).choose_spec
  let assign (s : Finset α) (x : α) : α :=
    if hx : x ∈ s then (localAssignment s ⟨x, hx⟩).1 else x
  have assign_of_mem {s : Finset α} {x : α} (hx : x ∈ s) :
      assign s x = (localAssignment s ⟨x, hx⟩).1 := dif_pos hx
  obtain ⟨u, hu⟩ := l.exists_ultrafilter_le
  have eventually_mem (x : α) : ∀ᶠ n in (u : Filter ι), x ∈ stage n := hu (covers x)
  have possible (x : α) : ∃ y, ∀ᶠ n in (u : Filter ι), assign (stage n) x = y := by
    have hfinite : (Insert.insert x (univ ∩ incomparableSet x)).Finite :=
      (hT x (mem_univ x)).insert x
    refine ((u.eventually_exists_mem_iff hfinite).mp ?_).imp fun y hy => hy.2
    filter_upwards [eventually_mem x] with n hx
    let s := stage n
    refine ⟨assign s x, ?_, rfl⟩
    rw [assign_of_mem hx, mem_insert_iff]
    by_cases h : (localAssignment s ⟨x, hx⟩).1 = x
    · exact Or.inl h
    · refine Or.inr ⟨mem_univ _, ⟨fun hxy => ?_, fun hyx => ?_⟩⟩
      · have hlt : (⟨x, hx⟩ : (↑s : Set α)) < localAssignment s ⟨x, hx⟩ :=
          lt_of_le_of_ne hxy fun he => h (congrArg Subtype.val he.symm)
        exact (localSpec s).separates hlt ((localSpec s).fixed _).symm
      · have hlt : localAssignment s ⟨x, hx⟩ < (⟨x, hx⟩ : (↑s : Set α)) :=
          lt_of_le_of_ne hyx fun he => h (congrArg Subtype.val he)
        exact (localSpec s).separates hlt ((localSpec s).fixed _)
  choose f hf using possible
  have lift_pair (x y : α) : ∃ s : Finset α, x ∈ s ∧ y ∈ s ∧
      assign s x = f x ∧ assign s y = f y := by
    have h : ∀ᶠ n in (u : Filter ι), x ∈ stage n ∧ y ∈ stage n ∧
        assign (stage n) x = f x ∧ assign (stage n) y = f y := by
      filter_upwards [eventually_mem x, eventually_mem y, hf x, hf y] with n hx hy hfx hfy
      exact ⟨hx, hy, hfx, hfy⟩
    obtain ⟨n, hn⟩ := h.exists
    exact ⟨stage n, hn⟩
  refine SpineAssignment.hasSpine (f := f) ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨s, hx, hfx, he, hfe⟩ := lift_pair x (f x)
    rw [← hfe, assign_of_mem hfx]
    have hrep : (⟨f x, hfx⟩ : (↑s : Set α)) = localAssignment s ⟨x, hx⟩ :=
      Subtype.ext (he.symm.trans (assign_of_mem hx))
    rw [hrep, (localSpec s).fixed]
    exact (assign_of_mem hx).symm.trans he
  · intro x y
    obtain ⟨s, hx, hy, hfx, hfy⟩ := lift_pair x y
    rw [← hfx, ← hfy, assign_of_mem hx, assign_of_mem hy]
    exact (localSpec s).comparable ⟨x, hx⟩ ⟨y, hy⟩
  · intro x y hxy he
    obtain ⟨s, hx, hy, hfx, hfy⟩ := lift_pair x y
    apply (localSpec s).separates (show (⟨x, hx⟩ : (↑s : Set α)) < ⟨y, hy⟩ from hxy)
    exact Subtype.ext ((assign_of_mem hx).symm.trans (hfx.trans
      (he.trans (hfy.symm.trans (assign_of_mem hy)))))

private theorem IsTube.subtype_univ {T : Set α} (hT : IsTube T) : IsTube (univ : Set T) := by
  intro x _
  apply Set.Finite.of_injOn (f := Subtype.val) ?_ Subtype.val_injective.injOn (hT x.1 x.2)
  intro y hy
  exact ⟨y.2, hy.2⟩

private theorem hasSpineOn_of_subtype {T : Set α} (h : HasSpine T) : HasSpineOn T := by
  obtain ⟨C, ⟨S⟩⟩ := h
  let e : C ≃ (Subtype.val '' C) := Equiv.Set.imageOfInjOn Subtype.val C
    Subtype.val_injective.injOn
  refine ⟨Subtype.val '' C, ⟨⟨S.chain.image (OrderEmbedding.subtype T), ?_,
    fun x => Subtype.val '' S.block (e.symm x), ?_, ?_, ?_, ?_⟩⟩⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.2
  · intro x a ha b hb hne hab
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    exact S.block_antichain _ ha hb (fun h => hne (congrArg Subtype.val h)) hab
  · exact fun x => ⟨(e.symm x).1, S.mem_block (e.symm x), congrArg Subtype.val (e.apply_symm_apply x)⟩
  · intro x y hxy
    refine disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
    have hab : b = a := Subtype.ext he
    exact disjoint_left.mp (S.blocks_disjoint _ _ (e.symm.injective.ne hxy)) ha (hab ▸ hb)
  · apply subset_antisymm
    · rintro _ hx
      obtain ⟨_, a, _, rfl⟩ := mem_iUnion.mp hx
      exact a.2
    · intro x hx
      have hx' : (⟨x, hx⟩ : T) ∈ ⋃ c, S.block c := by rw [S.iUnion_blocks]; trivial
      obtain ⟨c, hc⟩ := mem_iUnion.mp hx'
      exact mem_iUnion_of_mem (e c) ⟨⟨x, hx⟩, by simpa only [e.symm_apply_apply] using hc, rfl⟩

private theorem spine_on_locallyFinite_tube {T : Set α} (hT : IsTube T)
    (hfin : ∀ a b : T, (Icc a b).Finite) : HasSpineOn T := by
  have hsub := hT.subtype_univ
  obtain ⟨stage, hstage, hcover⟩ := hsub.isFAC_univ.exists_finite_exhaustion hfin
  have hmem (x : T) : ∀ᶠ n in atTop, x ∈ stage n := by
    obtain ⟨n, hn⟩ := hcover x
    exact (eventually_ge_atTop n).mono fun m hm => hstage hm hn
  exact hasSpineOn_of_subtype (spine_of_finite_stages atTop stage hmem hsub)

/-- Paper Theorem `thm:zaguia-spine-reformed`. Partition the tube by the initial segments of
its nonprincipal points. Each piece has finite intervals and admits a compactness argument. -/
theorem IsTube.hasSpine_univ (hT : IsTube (univ : Set α)) : HasSpine α := by
  classical
  let cut (x : α) : Set (H.N α) := {g | g.1 < H.principal x}
  let piece (I : Set (H.N α)) : Set α := {x | cut x = I}
  have spine_piece (I : Set (H.N α)) : HasSpineOn (piece I) := by
    apply spine_on_locallyFinite_tube (hT.mono (subset_univ _))
    intro x y
    have hfinite : (Icc x.1 y.1).Finite := by
      by_contra hinfinite
      obtain ⟨g, hg, hx, hy⟩ := hT.isFAC_univ.exists_limit_between_of_infinite_Icc hinfinite
      have hcut : cut x.1 = cut y.1 := x.2.trans y.2.symm
      have hgy : (⟨g, hg.1⟩ : H.N α) ∈ cut y.1 := hy
      have hgx : (⟨g, hg.1⟩ : H.N α) ∈ cut x.1 := hcut.symm ▸ hgy
      exact hx.not_gt hgx
    exact Set.Finite.of_injOn (f := Subtype.val) (fun _ hz => hz)
      Subtype.val_injective.injOn hfinite
  choose C hC using spine_piece
  let data (I : Set (H.N α)) := (hC I).some
  have has_block (x : α) (I : Set (H.N α)) (hx : cut x = I) :
      ∃ c : C I, x ∈ (data I).block c := by
    apply mem_iUnion.mp
    rw [(data I).iUnion_blocks]
    exact hx
  let rep (x : α) (I : Set (H.N α)) (hx : cut x = I) := (has_block x I hx).choose
  have mem_block (x : α) (I : Set (H.N α)) (hx : cut x = I) :
      x ∈ (data I).block (rep x I hx) := (has_block x I hx).choose_spec
  let f (x : α) := (rep x (cut x) rfl).1
  have rep_eq (x : α) (I : Set (H.N α)) (hx : cut x = I) :
      f x = (rep x I hx).1 := by subst I; rfl
  have same_cut (x : α) : cut (f x) = cut x :=
    (data (cut x)).chain_subset (rep x (cut x) rfl).2
  have across {x y : α} (h : cut x ≠ cut y) : x < y ∨ y < x := by
    by_contra hnc
    apply h
    have incl {a b : α} (hn : ¬ b < a) : cut a ⊆ cut b := by
      intro g hg
      rcases hT.nonprincipal_comparable g.2 (H.principal b) with hgb | hbg
      · rcases lt_or_eq_of_le hgb with hlt | heq
        · exact hlt
        · exact (hn ((H.principal_lt_principal _ _).mp (heq ▸ hg))).elim
      · exact (hn ((H.principal_lt_principal _ _).mp (hbg.trans_lt hg))).elim
    exact subset_antisymm (incl fun hlt => hnc (Or.inr hlt))
      (incl fun hlt => hnc (Or.inl hlt))
  refine SpineAssignment.hasSpine (f := f) ⟨?_, ?_, ?_⟩
  · intro x
    rw [rep_eq (f x) (cut x) (same_cut x)]
    by_contra hne
    have hdis := (data (cut x)).blocks_disjoint _ _ (fun he => hne (congrArg Subtype.val he))
    exact disjoint_left.mp hdis (mem_block (f x) (cut x) (same_cut x))
      ((data (cut x)).mem_block (rep x (cut x) rfl))
  · intro x y
    by_cases hcut : cut x = cut y
    · rw [rep_eq x (cut y) hcut]
      exact (data (cut y)).chain.total (rep x _ hcut).2 (rep y _ rfl).2
    · have h : cut (f x) ≠ cut (f y) := by simpa only [same_cut] using hcut
      exact (across h).imp le_of_lt le_of_lt
  · intro x y hxy hfy
    have hcut : cut x = cut y := (same_cut x).symm.trans (hfy ▸ same_cut y)
    have hreps : rep x (cut y) hcut = rep y (cut y) rfl :=
      Subtype.ext ((rep_eq x _ hcut).symm.trans hfy)
    exact (data (cut y)).block_antichain _ (hreps ▸ mem_block x _ hcut)
      (mem_block y _ rfl) hxy.ne hxy.le

/-- The tube theorem in the ambient set formulation. -/
theorem IsTube.hasSpine {T : Set α} (hT : IsTube T) : HasSpineOn T := by
  exact hasSpineOn_of_subtype hT.subtype_univ.hasSpine_univ

end AharoniKorman
