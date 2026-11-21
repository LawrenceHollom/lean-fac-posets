import AharoniKorman.Completion.WitnessChains
import AharoniKorman.Tube.Defs
import Mathlib.Order.Interval.Set.Infinite

namespace AharoniKorman

open Set Completion

variable {α : Type*} [PartialOrder α]

theorem IsTube.orderDual_univ (hT : IsTube (univ : Set α)) :
    IsTube (univ : Set αᵒᵈ) := by
  intro x hx
  exact (hT x hx).subset fun y hy => ⟨hy.1, ⟨hy.2.not_ge, hy.2.not_le⟩⟩

theorem IsTube.isFAC_univ (hT : IsTube (univ : Set α)) : IsFAC α := by
  intro A hA
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact finite_empty
  apply ((hT a (mem_univ a)).insert a).subset
  intro b hb
  by_cases heq : b = a
  · exact Or.inl heq
  · exact Or.inr ⟨mem_univ b, ⟨hA ha hb (Ne.symm heq), hA hb ha heq⟩⟩

private theorem IsTube.finite_chainTrace (hT : IsTube (univ : Set α))
    (C : SaturatedChain α) (x : α) : (incomparabilityTrace C x).Finite :=
  Set.Finite.of_injOn (f := Subtype.val) (t := univ ∩ incomparableSet x)
    (fun y hy => ⟨mem_univ _, (show Incomparable y.1 x from hy).symm⟩)
    Subtype.val_injective.injOn (hT x (mem_univ x))

private theorem tube_principal_increasing (hT : IsTube (univ : Set α))
    (x : α) (C : IncreasingChain α) :
    (∃ c : C.1, x < c.1) ∨ ∀ c : C.1, c.1 < x := by
  classical
  by_cases h : ∃ c : C.1, x < c.1
  · exact Or.inl h
  right
  intro c
  by_contra hcx
  let : NoMaxOrder C.1 := ⟨C.2.exists_gt⟩
  apply (Set.Ioi_infinite c) ((hT.finite_chainTrace C.1 x).subset ?_)
  intro d (hcd : c < d)
  have hcd' : c.1 < d.1 := hcd
  refine ⟨fun hdx => hcx (hcd'.trans_le hdx), fun hxd => h ⟨d, ?_⟩⟩
  exact lt_of_le_of_ne hxd (fun he => hcx (he ▸ hcd'))

private theorem tube_increasing_comparable (hT : IsTube (univ : Set α))
    (C D : IncreasingChain α) :
    Comparable (H.increasing (IncreasingGerm.ofChain C))
      (H.increasing (IncreasingGerm.ofChain D)) := by
  classical
  let X : H α := H.increasing (IncreasingGerm.ofChain C)
  let Y : H α := H.increasing (IncreasingGerm.ofChain D)
  by_cases hXY : X < Y
  · exact Or.inl hXY.le
  by_cases hYX : Y < X
  · exact Or.inr hYX.le
  refine Or.inl (le_of_eq (congrArg H.increasing (IncreasingGerm.ofChain_eq_iff.mpr ?_)))
  apply (IncreasingEquivalent.iff_finite_cofinal C D).mpr
  refine ⟨C.1, D.1, ⟨Subset.rfl, fun _ _ _ hy _ => hy⟩,
    ⟨Subset.rfl, fun _ _ _ hy _ => hy⟩, ?_, ?_, fun t => hT.finite_chainTrace C.1 t.1,
    fun s => hT.finite_chainTrace D.1 s.1⟩
  · intro c
    exact (tube_principal_increasing hT c.1 D).resolve_right fun h =>
      hYX ((H.increasing_ofChain_lt_increasing_ofChain D C).mpr ⟨c, h⟩)
  · intro d
    exact (tube_principal_increasing hT d.1 C).resolve_right fun h =>
      hXY ((H.increasing_ofChain_lt_increasing_ofChain C D).mpr ⟨d, h⟩)

private theorem tube_mixed_comparable (hT : IsTube (univ : Set α))
    (C : IncreasingChain α) (D : DecreasingChain α) :
    Comparable (H.increasing (IncreasingGerm.ofChain C))
      (H.decreasing (DecreasingGerm.ofChain D)) := by
  classical
  by_cases h : ∃ d : D.1, ∃ c : C.1, d.1 < c.1
  · exact Or.inr ((H.decreasing_ofChain_lt_increasing_ofChain D C).mpr h).le
  apply Or.inl ((H.increasing_ofChain_lt_decreasing_ofChain C D).mpr ?_).le
  intro c d
  exact (tube_principal_increasing hT d.1 C).resolve_left (fun hd => h ⟨d, hd⟩) c

private theorem tube_increasing_total (hT : IsTube (univ : Set α))
    (X : IncreasingGerm α) (Y : H α) : Comparable (H.increasing X) Y := by
  induction X using IncreasingGerm.inductionOn with
  | h C =>
    cases Y with
    | principal y =>
      rcases tube_principal_increasing hT y C with h | h
      · exact Or.inr ((H.principal_lt_increasing_ofChain y C).mpr h).le
      · exact Or.inl ((H.increasing_ofChain_lt_principal C y).mpr h).le
    | increasing g =>
      induction g using IncreasingGerm.inductionOn with
      | h D => exact tube_increasing_comparable hT C D
    | decreasing g =>
      induction g using DecreasingGerm.inductionOn with
      | h D => exact tube_mixed_comparable hT C D
    | bottom => exact Or.inr bot_le
    | top => exact Or.inl le_top

/-- Paper `lem:tube-nonprincipal-comparable`. Each nonprincipal point is a cut point
of the extension of a tube. -/
theorem IsTube.nonprincipal_comparable (hT : IsTube (univ : Set α))
    {X : H α} (hX : X.IsNonprincipal) (Y : H α) : Comparable X Y := by
  cases X with
  | principal x => simp [H.IsNonprincipal] at hX
  | increasing g => exact tube_increasing_total hT g Y
  | decreasing g =>
    rcases tube_increasing_total hT.orderDual_univ g.toDual Y.dual with h | h
    · exact Or.inr ((H.dual_le_dual _ _).mp h)
    · exact Or.inl ((H.dual_le_dual _ _).mp h)
  | bottom => exact Or.inl bot_le
  | top => exact Or.inr le_top

private theorem increasing_limit_between {x y : α} {f : ℕ → α} (hf : StrictMono f)
    (hxy : ∀ n, f n ∈ Icc x y) :
    ∃ G : H α, G.IsGenuineNonprincipal ∧ H.principal x < G ∧ G < H.principal y := by
  obtain ⟨D, hD, hsub⟩ := hf.monotone.isChain_range.exists_maxChain
  have hsat : IsSaturatedChain D := ⟨hD.1, fun _ _ _ _ _ _ _ hz => by
    rw [hD.2 (hD.1.insert fun c hc _ => hz c hc) (Set.subset_insert _ D)]
    exact Set.mem_insert _ _⟩
  let B : SaturatedChain α := ⟨D, ⟨f 0, hsub (mem_range_self 0)⟩, hsat⟩
  let S : Set α := {z ∈ D | ∃ n, z ≤ f n}
  have hseg : IsInitialSegment S D :=
    ⟨fun _ hz => hz.1, fun _ _ hz hw hwz => ⟨hw, hz.2.imp fun _ hn => hwz.trans hn⟩⟩
  have hfS (n : ℕ) : f n ∈ S := ⟨hsub (mem_range_self n), n, le_rfl⟩
  let C : SaturatedChain α := B.restrict .decreasing S hseg ⟨f 0, hfS 0⟩
  have hno : C.NoTop := by
    rintro ⟨c, hc⟩
    obtain ⟨n, hn⟩ := c.2.2
    exact (hn.trans_lt (hf (Nat.lt_succ_self n))).not_ge (hc ⟨f (n + 1), hfS _⟩)
  let E : IncreasingChain α := ⟨C, hno⟩
  let g := IncreasingGerm.ofChain E
  refine ⟨H.increasing g, ⟨⟨.increasing, rfl⟩, H.increasing_ne_bot _, H.increasing_ne_top _⟩,
    (H.principal_lt_increasing_ofChain _ E).mpr ⟨⟨f 1, hfS _⟩, (hxy 0).1.trans_lt (hf (by decide))⟩,
    (H.increasing_ofChain_lt_principal E _).mpr ?_⟩
  intro c
  obtain ⟨n, hn⟩ := c.2.2
  exact hn.trans_lt ((hf (Nat.lt_succ_self n)).trans_le (hxy (n + 1)).2)

/-- An infinite closed interval of an FAC poset contains a nonprincipal cut strictly
between its endpoints in the chain extension. -/
theorem IsFAC.exists_limit_between_of_infinite_Icc (hfac : IsFAC α)
    {x y : α} (hxy : (Icc x y).Infinite) :
    ∃ G : H α, G.IsGenuineNonprincipal ∧ H.principal x < G ∧ G < H.principal y := by
  obtain ⟨f, hmono | hanti⟩ := hfac.exists_strictMono_or_strictAnti_sequence_in hxy
  · exact increasing_limit_between (f := fun n => (f n).1) hmono (fun n => (f n).2)
  · have hrev (n : ℕ) : (f n).1 ∈ @Icc αᵒᵈ _ y x := ⟨(f n).2.2, (f n).2.1⟩
    obtain ⟨G, hG, h1, h2⟩ := increasing_limit_between (α := αᵒᵈ) hanti hrev
    have hnon : G.dual.IsNonprincipal := by
      cases G with
      | principal z => exact (by simpa [H.IsNonprincipal] using hG.1)
      | increasing g => exact ⟨.decreasing, rfl⟩
      | decreasing g => exact ⟨.increasing, rfl⟩
      | bottom => exact ⟨.increasing, rfl⟩
      | top => exact ⟨.decreasing, rfl⟩
    have hLow := (H.dual_lt_dual (H.principal (α := αᵒᵈ) x) G).mpr h2
    have hHigh := (H.dual_lt_dual G (H.principal (α := αᵒᵈ) y)).mpr h1
    exact ⟨G.dual, ⟨hnon, ne_bot_of_gt hLow, ne_top_of_lt hHigh⟩, hLow, hHigh⟩

end AharoniKorman
