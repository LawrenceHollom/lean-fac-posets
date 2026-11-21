import AharoniKorman.Tube.OpenSplitting
import AharoniKorman.Preliminaries.FACCore
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Pigeonhole

namespace AharoniKorman

open Set Completion Illfounded

variable {α : Type*} [PartialOrder α]

private theorem exists_block_in_finite_convex_cover {ι : Type*} [Finite ι]
    (V : ι → Set α) (hc : ∀ i, (V i).OrdConnected) (C : ℕ → Set α)
    (hne : ∀ n, (C n).Nonempty)
    (horder : (∀ ⦃i j : ℕ⦄, i < j → SetStrictLT (C i) (C j)) ∨
      (∀ ⦃i j : ℕ⦄, i < j → SetStrictLT (C j) (C i)))
    (hcover : ∀ n x, x ∈ C n → ∃ k, x ∈ V k) : ∃ n k, C n ⊆ V k := by
  classical
  choose x hx using hne
  choose f hf using fun n => hcover n (x n) (hx n)
  obtain ⟨k, hk⟩ := Finite.exists_infinite_fiber f
  have hinf := Set.infinite_coe_iff.1 hk
  obtain ⟨i, hi⟩ := hinf.nonempty
  obtain ⟨j, hj, hij⟩ := hinf.exists_gt (i + 1)
  have hi' : x i ∈ V k := (Set.mem_singleton_iff.1 hi) ▸ hf i
  have hj' : x j ∈ V k := (Set.mem_singleton_iff.1 hj) ▸ hf j
  refine ⟨i + 1, k, fun p hp => ?_⟩
  rcases horder with h | h
  · exact (hc k).out hi' hj'
      ⟨(h (Nat.lt_succ_self i) (hx i) hp).le, (h hij hp (hx j)).le⟩
  · exact (hc k).out hj' hi'
      ⟨(h hij (hx j) hp).le, (h (Nat.lt_succ_self i) hp (hx i)).le⟩

private theorem exact_quasifounded_zeta_interval
    (hsc : IsScattered α) (hvac : IsVacillating α)
    {Q : Set α} (hQ : OrdConnected Q) (e : ℤ ↪o α) (he : range e ⊆ Q)
    (hes : IsSaturatedChain (range e))
    (hno : ∀ p ∈ Q, ¬HasSaturatedZeta (Q ∩ incomparableSet p)) (m n : ℤ) :
    AharoniKorman.IsQuasifounded (Icc (e m) (e n)) := by
  classical
  by_contra hqf
  let B : Set α := Icc (e m) (e n)
  let emb : B ↪o α := OrderEmbedding.subtype B
  let hemb : SaturationPreserving emb := saturationPreserving_subtype_of_ordConnected ordConnected_Icc
  obtain ⟨E, hE, horder⟩ := exists_ordered_open_chains
    (hvac.ordConnected_subtype (show B.OrdConnected from ordConnected_Icc)) hqf
  let C (j : ℕ) := emb '' E j
  have hCne (j : ℕ) : (C j).Nonempty := (hE j).2.1.image emb
  have hCopen (j : ℕ) : IsOpenSubposet (C j) := (hE j).2.2.image emb
  have hCsat (j : ℕ) : IsSaturatedChain (C j) := hemb _ (hE j).1
  have lift_order {i j : ℕ} (hij : SetStrictLT (E i) (E j)) : SetStrictLT (C i) (C j) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact emb.strictMono (hij hx hy)
  let F (k : Bool × ((Finset.Icc m n : Finset ℤ) : Type)) : Set α :=
    if k.1 then Q ∩ incomparableSet (e k.2.1) else {e k.2.1}
  have hFconv (k) : (F k).OrdConnected := by
    rcases k with ⟨b, i⟩
    cases b
    · exact ordConnected_singleton
    · exact hQ.inter (incomparableSet_ordConnected _)
  have hFno (k) : ¬HasSaturatedZeta (F k) := by
    rcases k with ⟨b, i⟩
    cases b
    · exact not_hasSaturatedZeta_singleton _
    · exact hno _ (he ⟨i.1, rfl⟩)
  have hcover (j x) (hx : x ∈ C j) : ∃ k, x ∈ F k := by
    obtain ⟨p, _, rfl⟩ := hx
    rcases zeta_interval_cover e hes m n p.2 with ⟨i, hi, hxi | hxi⟩
    · exact ⟨(false, ⟨i, hi⟩), hxi⟩
    · exact ⟨(true, ⟨i, hi⟩), hQ.out (he ⟨m, rfl⟩) (he ⟨n, rfl⟩) p.2, hxi⟩
  obtain ⟨j, k, hjk⟩ := exists_block_in_finite_convex_cover F hFconv C hCne
    (horder.imp (fun h _ _ hij => lift_order (h hij)) (fun h _ _ hij => lift_order (h hij))) hcover
  exact hFno k ((hasSaturatedZeta_of_open_saturated (hCsat j) (hCne j) (hCopen j)
    hsc hvac).mono hjk)

private theorem quasifounded_of_convex_subset {S T : Set α}
    (hS : S.OrdConnected) (hST : S ⊆ T) (hT : AharoniKorman.IsQuasifounded T) :
    AharoniKorman.IsQuasifounded S := by
  let e : S ↪o T := OrderEmbedding.ofMapLEIff (Set.inclusion hST) (fun _ _ => Iff.rfl)
  apply hT.of_saturationPreserving e
  intro C hC
  refine ⟨hC.1.image e, ?_⟩
  rintro _ _ x ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hax hxb hcomp
  have hxS : x.1 ∈ S := hS.out a.2 b.2 ⟨hax, hxb⟩
  refine ⟨⟨x.1, hxS⟩, hC.2 ha hb hax hxb ?_, Subtype.ext rfl⟩
  exact fun c hc => hcomp (e c) ⟨c, hc, rfl⟩

/-- Paper `lem:find-convex-open-subposet`, in any prescribed convex region.
Localize at a maximal antichain, rule out a non-quasifounded bounded interval,
then take the convex hull of the middle of three open chains if needed. -/
theorem exists_open_quasifounded_in_convex
    (hfac : IsFAC α) (hsc : IsScattered α) (hvac : IsVacillating α)
    {G : Set α} (hG : G.OrdConnected) (hex : HasSaturatedZeta G) :
    ∃ V : Set α, V ⊆ G ∧ V.Nonempty ∧ V.OrdConnected ∧
      IsOpenSubposet V ∧ AharoniKorman.IsQuasifounded V := by
  classical
  have hex' : HasSaturatedZeta (G ∩ univ) := by simpa using hex
  obtain ⟨Q, hQ, ⟨e, heQ, hes⟩, hno⟩ :=
    hfac.exists_convex_core (fun Q => HasSaturatedZeta (G ∩ Q)) hex'
  let R := G ∩ Q
  have hR : R.OrdConnected := hG.inter hQ
  have hno' : ∀ p ∈ R, ¬HasSaturatedZeta (R ∩ incomparableSet p) := by
    intro p hp
    simpa only [R, inter_assoc] using hno p hp.2
  let W := convexHull (range e)
  have hW : W.OrdConnected := convexHull_ordConnected _
  have hWG : W ⊆ G := (convexHull_subset_of_ordConnected hR heQ).trans inter_subset_left
  obtain ⟨hWne, hWlo, hWhi⟩ := zetaHull_no_endpoints e
  by_cases hWq : AharoniKorman.IsQuasifounded W
  · exact ⟨W, hWG, hWne, hW, ⟨hWlo, hWhi⟩, hWq⟩
  obtain ⟨E, hE, hord⟩ := exists_ordered_open_chains (hvac.ordConnected_subtype hW) hWq
  obtain ⟨u, hu⟩ := (hE 0).2.1
  obtain ⟨v, hv⟩ := (hE 2).2.1
  let C : Set α := Subtype.val '' E 1
  have hCne : C.Nonempty := (hE 1).2.1.image Subtype.val
  have hCopen : IsOpenSubposet C := (hE 1).2.2.image (OrderEmbedding.subtype W)
  have hCW : C ⊆ W := by rintro _ ⟨p, _, rfl⟩; exact p.2
  let V := convexHull C
  have hVC : C ⊆ V := fun p hp => ⟨p, hp, p, hp, le_rfl, le_rfl⟩
  have hV : V.OrdConnected := convexHull_ordConnected _
  have hVopen : IsOpenSubposet V := by
    constructor
    · rintro x ⟨a, ha, b, hb, hax, hxb⟩
      obtain ⟨p, hp, hpa⟩ := hCopen.1 a ha
      exact ⟨p, hVC hp, hpa.trans_le hax⟩
    · rintro x ⟨a, ha, b, hb, hax, hxb⟩
      obtain ⟨p, hp, hbp⟩ := hCopen.2 b hb
      exact ⟨p, hVC hp, hxb.trans_lt hbp⟩
  refine ⟨V, (convexHull_subset_of_ordConnected hW hCW).trans hWG,
    hCne.mono hVC, hV, hVopen, ?_⟩
  have hbounded : ∃ a b : W, C ⊆ Icc a.1 b.1 := by
    rcases hord with h | h
    · refine ⟨u, v, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨(h (by decide : 0 < 1) hu hp).le, (h (by decide : 1 < 2) hp hv).le⟩
    · refine ⟨v, u, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨(h (by decide : 1 < 2) hv hp).le, (h (by decide : 0 < 1) hp hu).le⟩
  obtain ⟨a, b, hCB⟩ := hbounded
  obtain ⟨_, ⟨m, rfl⟩, _, _, hma, _⟩ := a.2
  obtain ⟨_, _, _, ⟨n, rfl⟩, _, hbn⟩ := b.2
  have hCI : C ⊆ Icc (e m) (e n) := fun x hx =>
    ⟨hma.trans (hCB hx).1, (hCB hx).2.trans hbn⟩
  exact quasifounded_of_convex_subset hV
    (convexHull_subset_of_ordConnected ordConnected_Icc hCI)
    (exact_quasifounded_zeta_interval hsc hvac hR e heQ hes hno' m n)

end AharoniKorman
