import AharoniKorman.Tube.OpenChains
import AharoniKorman.Tube.IntegerChains
import Mathlib.Order.SuccPred.LinearLocallyFinite

namespace AharoniKorman

open Set Completion Completion.H Illfounded

variable {α : Type*} [LinearOrder α]

/- The splitting argument only needs a dense set of selected points. A maximal
set of points with a splittable interval between every pair gives these points
without assigning coordinates to the dyadic rationals. -/
private theorem not_scattered_of_splitting (Rich : Set α → Prop)
    (hne : ∀ S, Rich S → S.Nonempty)
    (hsplit : ∀ S, Rich S → ∃ L M R : Set α, L ⊆ S ∧ M ⊆ S ∧ R ⊆ S ∧
      Rich L ∧ Rich M ∧ Rich R ∧ SetStrictLT L M ∧ SetStrictLT M R)
    (hstart : Rich (univ : Set α)) : ¬IsScattered α := by
  classical
  let Sep (a b : α) := ∃ S : Set α, Rich S ∧ S ⊆ Ioo a b
  have sep_lt {a b} (h : Sep a b) : a < b := by
    obtain ⟨S, hs, hsub⟩ := h
    obtain ⟨x, hx⟩ := hne S hs
    exact (hsub hx).1.trans (hsub hx).2
  have sep_mono {a b c d} (ha : a ≤ b) (hd : c ≤ d) (h : Sep b c) : Sep a d := by
    obtain ⟨S, hs, hsub⟩ := h
    exact ⟨S, hs, fun x hx => ⟨ha.trans_lt (hsub hx).1, (hsub hx).2.trans_le hd⟩⟩
  let Candidates := {S : Set α | S.Pairwise fun a b => Sep a b ∨ Sep b a}
  obtain ⟨L, M, R, _, _, _, hL, hM, hR, hLM, hMR⟩ := hsplit univ hstart
  obtain ⟨a, ha⟩ := hne L hL
  obtain ⟨b, hb⟩ := hne R hR
  have hab : Sep a b := ⟨M, hM, fun x hx => ⟨hLM ha hx, hMR hx hb⟩⟩
  have hinit : ({a, b} : Set α) ∈ Candidates := by
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · exact Or.inl hab
    · exact Or.inr hab
    · exact (hxy rfl).elim
  have hbound : ∀ c ⊆ Candidates, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ U ∈ Candidates, ∀ S ∈ c, S ⊆ U := by
    intro c hc hcc _
    refine ⟨⋃₀ c, ?_, fun S hS => subset_sUnion_of_mem hS⟩
    rintro x ⟨S, hSc, hxS⟩ y ⟨T, hTc, hyT⟩ hxy
    rcases hcc.total hSc hTc with hST | hTS
    · exact (hc hTc) (hST hxS) hyT hxy
    · exact (hc hSc) hxS (hTS hyT) hxy
  obtain ⟨D, hinitD, hD⟩ := zorn_subset_nonempty Candidates hbound _ hinit
  let : Nontrivial D := ⟨⟨⟨a, hinitD (mem_insert a _)⟩,
    ⟨b, hinitD (mem_insert_of_mem _ (mem_singleton b))⟩,
    fun h => (sep_lt hab).ne (congrArg Subtype.val h)⟩⟩
  let : DenselyOrdered D := ⟨by
    intro x y hxy
    let x' := x.1
    let y' := y.1
    have hor : Sep x' y' ∨ Sep y' x' := hD.prop x.2 y.2 (ne_of_lt hxy)
    obtain ⟨S, hS, hsub⟩ := hor.resolve_right (fun h => (sep_lt h).not_gt hxy)
    obtain ⟨A, B, C, hAS, hBS, hCS, hA, hB, hC, hAB, hBC⟩ := hsplit S hS
    obtain ⟨p, hp⟩ := hne B hB
    have hxp : Sep x' p := ⟨A, hA, fun _ hx => ⟨(hsub (hAS hx)).1, hAB hx hp⟩⟩
    have hpy : Sep p y' := ⟨C, hC, fun _ hx => ⟨hBC hp hx, (hsub (hCS hx)).2⟩⟩
    by_contra hgap
    have hc (z : α) (hz : z ∈ D) : Sep z p ∨ Sep p z := by
      by_cases hzx : z ≤ x'
      · exact Or.inl (sep_mono hzx le_rfl hxp)
      · have hyz : y' ≤ z := by
          apply le_of_not_gt
          intro hzy
          exact hgap ⟨⟨z, hz⟩, lt_of_not_ge hzx, hzy⟩
        exact Or.inr (sep_mono le_rfl hyz hpy)
    have hpd : p ∈ D := hD.2 (show insert p D ∈ Candidates by
      intro u hu v hv huv
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact (huv rfl).elim
      · exact (hc _ hv).symm
      · exact hc _ hu
      · exact hD.prop hu hv huv) (subset_insert _ _) (mem_insert _ _)
    exact hgap ⟨⟨p, hpd⟩, sep_lt hxp, sep_lt hpy⟩⟩
  intro hsc
  obtain ⟨e⟩ := Order.embedding_from_countable_to_dense (α := ℚ) (β := D)
  exact hsc ⟨e.trans (OrderEmbedding.subtype D)⟩

private theorem positive_chain_between {a b : α} (f : ℕ → Icc a b) (hf : StrictMono f) :
    ∃ A : IncreasingChain α, (A.1 : Set α) ⊆ Icc a b := by
  let D : Set α := {x | (f 0).1 ≤ x ∧ ∃ n, x ≤ (f n).1}
  have hD : D.OrdConnected := by
    constructor
    intro x hx y hy z hz
    obtain ⟨n, hn⟩ := hy.2
    exact ⟨hx.1.trans hz.1, n, hz.2.trans hn⟩
  let C : SaturatedChain α := ⟨D, ⟨(f 0).1, le_rfl, 0, le_rfl⟩, (isSaturatedChain_iff _).2 hD⟩
  refine ⟨⟨C, ?_⟩, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := x.2.2
    have hfD : (f (n+1)).1 ∈ D := ⟨hf.monotone (Nat.zero_le _), n+1, le_rfl⟩
    exact (hn.trans_lt (hf (Nat.lt_succ_self n))).not_ge (hx ⟨_, hfD⟩)
  · rintro x ⟨hax, n, hxb⟩
    exact ⟨(f 0).2.1.trans hax, hxb.trans (f n).2.2⟩

private theorem hasSaturatedZeta_of_open_quasifounded (hne : Nonempty α)
    (hopen : IsOpenSubposet (univ : Set α)) (hqf : AharoniKorman.IsQuasifounded α) :
    HasSaturatedZeta (univ : Set α) := by
  classical
  let C : SaturatedChain α := ⟨univ, hne.elim (fun x => ⟨x, mem_univ x⟩),
    (isSaturatedChain_iff _).2 ordConnected_univ⟩
  let A : IncreasingChain α := ⟨C, by
    rintro ⟨u, hu⟩
    obtain ⟨v, hv, huv⟩ := hopen.2 u.1 u.2
    exact huv.not_ge (hu ⟨v, hv⟩)⟩
  let Pos : Set (NPlus α) := {X | X.1 ≠ ⊤}
  obtain ⟨X, hX, hmin⟩ := hqf.1.has_min Pos
    ⟨⟨H.increasing (IncreasingGerm.ofChain A), rfl⟩, H.increasing_ne_top _⟩
  obtain ⟨g, hg⟩ := ((H.direction_eq_increasing_iff _).1 X.2).resolve_right hX
  have hmin_g (a : IncreasingGerm α) : ¬H.increasing a < H.increasing g := by
    intro h
    apply hmin ⟨H.increasing a, rfl⟩ (H.increasing_ne_top _)
    change H.increasing a < X.1
    simpa only [hg] using h
  let D : Set α := {p | H.principal p < H.increasing g}
  have hD : D.OrdConnected := by
    constructor
    intro a ha b hb z hz
    change H.principal b < H.increasing g at hb
    exact ((H.principal_le_principal z b).2 hz.2).trans_lt hb
  let e : D ↪o α := OrderEmbedding.subtype D
  let he : SaturationPreserving e := saturationPreserving_subtype_of_ordConnected hD
  have hDne : D.Nonempty := by
    obtain ⟨p, hp⟩ := g.representative.1.nonempty
    exact ⟨p, (H.strictLT_principal_increasing g.representative_spec _).2
      (g.representative.2.exists_gt ⟨p, hp⟩)⟩
  let Cd : SaturatedChain D := ⟨univ, by
    obtain ⟨p, hp⟩ := hDne
    exact ⟨⟨p, hp⟩, mem_univ _⟩, (isSaturatedChain_iff _).2 ordConnected_univ⟩
  let B : DecreasingChain D := ⟨Cd, by
    rintro ⟨u, hu⟩
    obtain ⟨v, _, hvu⟩ := hopen.1 u.1.1 (mem_univ _)
    have hv : v ∈ D := by
      change H.principal v < H.increasing g
      exact ((H.principal_lt_principal v u.1.1).2 hvu).trans u.1.2
    exact hvu.not_ge (hu ⟨⟨v, hv⟩, mem_univ _⟩)⟩
  let Neg : Set (NMinus D) := {Y | Y.1 ≠ ⊥}
  obtain ⟨Y, hY, hmax⟩ := (hqf.ordConnected_subtype hD).2.has_min Neg
    ⟨⟨H.decreasing (DecreasingGerm.ofChain B), rfl⟩, H.decreasing_ne_bot _⟩
  obtain ⟨j, hj⟩ := ((H.direction_eq_decreasing_iff _).1 Y.2).resolve_right hY
  let J := j.representative.map e he
  let j₀ := DecreasingGerm.ofChain J
  have hmap : H.mapEmbedding e he (H.decreasing j) = H.decreasing j₀ := by
    change H.decreasing (j.map e he) = H.decreasing (DecreasingGerm.ofChain J)
    rw [show J = j.representative.map e he from rfl, ← DecreasingGerm.map_ofChain]
    exact congrArg (fun d => H.decreasing (d.map e he)) j.representative_spec.symm
  have hjmax (t : DecreasingChain D) : ¬ H.decreasing j₀ <
      H.decreasing (DecreasingGerm.ofChain (t.map e he)) := by
    intro h
    have hh : H.decreasing j < H.decreasing (DecreasingGerm.ofChain t) := by
      apply (H.mapEmbedding e he).lt_iff_lt.1
      rw [hmap]
      change H.decreasing j₀ < H.decreasing ((DecreasingGerm.ofChain t).map e he)
      rwa [DecreasingGerm.map_ofChain]
    apply hmax ⟨H.decreasing (DecreasingGerm.ofChain t), rfl⟩ (H.decreasing_ne_bot _)
    change Y.1 < H.decreasing (DecreasingGerm.ofChain t)
    simpa only [hj] using hh
  have hjg : H.decreasing j₀ < H.increasing g := by
    obtain ⟨p, hp⟩ := j.representative.1.nonempty
    let q : J.1 := j.representative.1.mapOrderIso e he ⟨p, hp⟩
    exact ((H.decreasing_ofChain_lt_principal J q.1).2 (J.2.exists_lt q)).trans p.2
  let S := betweenInChain (univ : Set α) (H.decreasing j₀) (H.increasing g)
  have hS : IsSaturatedChain S := betweenInChain_saturated C.saturated _ _
  obtain ⟨hSne, hopenS⟩ := betweenInChain_nonempty_open C
    (show H.Witnesses C (H.decreasing j₀) from ⟨J.1, subset_univ _, J.2, rfl⟩)
    (show H.Witnesses C (H.increasing g) from
      ⟨g.representative.1, subset_univ _, g.representative.2, g.representative_spec⟩) hjg
  have hSfin (a b : S) : (Icc a b : Set S).Finite := by
    by_contra hi
    let F := (Icc a b : Set S)
    let : Infinite F := (show F.Infinite from hi).to_subtype
    obtain ⟨f, hmono | hanti⟩ := Infinite.exists_strictMono_or_strictAnti F
    · let f' (n : ℕ) : Icc a.1 b.1 := ⟨(f n).1.1, (f n).2⟩
      obtain ⟨K, hK⟩ := positive_chain_between f' hmono
      apply hmin_g (IncreasingGerm.ofChain K)
      have hb : H.increasing (IncreasingGerm.ofChain K) < H.principal b.1 := by
        apply (H.increasing_ofChain_lt_principal _ _).2
        intro c
        obtain ⟨d, hcd⟩ := K.2.exists_gt c
        exact (show c.1 < d.1 from hcd).trans_le (hK d.2).2
      exact hb.trans b.2.2.2
    · let f' (n : ℕ) : @Icc αᵒᵈ _ b.1 a.1 := ⟨(f n).1.1, (f n).2.2, (f n).2.1⟩
      obtain ⟨K, hK⟩ := positive_chain_between (α := αᵒᵈ) f' hanti
      let L : DecreasingChain α := K.toDual
      have hLD : (L.1 : Set α) ⊆ D := fun x hx =>
        ((H.principal_le_principal x b.1).2 (hK hx).1).trans_lt b.2.2.2
      apply hjmax (L.within hLD)
      rw [L.map_within hLD he]
      refine a.2.2.1.trans ((H.principal_lt_decreasing_ofChain a.1 L).2 ?_)
      intro c
      obtain ⟨d, hdc⟩ := L.2.exists_lt c
      have had : a.1 ≤ d.1 := (hK d.2).2
      exact had.trans_lt (show d.1 < c.1 from hdc)
  let : LocallyFiniteOrder S := LocallyFiniteOrder.ofFiniteIcc hSfin
  let : Nonempty S := hSne.to_subtype
  let : NoMinOrder S := ⟨fun x => by
    obtain ⟨y, hy, hyx⟩ := hopenS.1 x.1 x.2
    exact ⟨⟨y, hy⟩, hyx⟩⟩
  let : NoMaxOrder S := ⟨fun x => by
    obtain ⟨y, hy, hxy⟩ := hopenS.2 x.1 x.2
    exact ⟨⟨y, hy⟩, hxy⟩⟩
  let : SuccOrder S := LinearLocallyFiniteOrder.succOrder S
  let : PredOrder S := LinearLocallyFiniteOrder.predOrder S
  let z : ℤ ↪o S := (orderIsoIntOfLinearSuccPredArch (ι := S)).symm.toOrderEmbedding
  have hz : range z = univ := Set.range_eq_univ.2 (OrderIso.surjective _)
  exact hasSaturatedZeta_of_convex_int_in_subtype hS z (hz.symm ▸ ordConnected_univ) |>.mono (subset_univ _)

private theorem hasSaturatedZeta_image {β : Type*} [PartialOrder β] {S : Set α}
    (hZ : HasSaturatedZeta S) (e : α ↪o β) (he : SaturationPreserving e) :
    HasSaturatedZeta (e '' S) := by
  obtain ⟨z, hz, hzs⟩ := hZ
  have heq : range (z.trans e) = e '' range z := by
    ext p
    exact ⟨fun ⟨n, hn⟩ => ⟨z n, ⟨n, rfl⟩, hn⟩,
      fun ⟨x, ⟨n, hn⟩, hx⟩ => ⟨n, by
        change e (z n) = p
        simpa only [← hn] using hx⟩⟩
  exact ⟨z.trans e, heq.symm ▸ image_mono hz, heq.symm ▸ he _ hzs⟩

private theorem hasSaturatedZeta_of_open_linear (hne : Nonempty α)
    (hopen : IsOpenSubposet (univ : Set α)) (hsc : IsScattered α) (hvac : IsVacillating α) :
    HasSaturatedZeta (univ : Set α) := by
  classical
  by_contra hno
  let Rich (S : Set α) := S.Nonempty ∧ S.OrdConnected ∧ IsOpenSubposet S
  apply not_scattered_of_splitting Rich (fun _ hs => hs.1) _ _ hsc
  · intro S hS
    let e : S ↪o α := OrderEmbedding.subtype S
    let he : SaturationPreserving e := saturationPreserving_subtype_of_ordConnected hS.2.1
    have hopenS : IsOpenSubposet (univ : Set S) := by
      constructor
      · intro x _
        obtain ⟨y, hy, hyx⟩ := hS.2.2.1 x.1 x.2
        exact ⟨⟨y, hy⟩, mem_univ _, hyx⟩
      · intro x _
        obtain ⟨y, hy, hxy⟩ := hS.2.2.2 x.1 x.2
        exact ⟨⟨y, hy⟩, mem_univ _, hxy⟩
    have hqf : ¬AharoniKorman.IsQuasifounded S := by
      intro h
      exact hno ((hasSaturatedZeta_image (hasSaturatedZeta_of_open_quasifounded
        hS.1.to_subtype hopenS h) e he).mono (subset_univ _))
    obtain ⟨C, hC, ho⟩ := exists_ordered_open_chains (hvac.ordConnected_subtype hS.2.1) hqf
    let V (n : ℕ) := e '' C n
    have hsub (n : ℕ) : V n ⊆ S := by rintro _ ⟨p, _, rfl⟩; exact p.2
    have hRich (n : ℕ) : Rich (V n) := ⟨(hC n).2.1.image e,
      (isSaturatedChain_iff _).1 (he _ (hC n).1), (hC n).2.2.image e⟩
    have hLift {i j : ℕ} (hij : SetStrictLT (C i) (C j)) : SetStrictLT (V i) (V j) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact e.strictMono (hij hx hy)
    rcases ho with ho | ho
    · exact ⟨V 0, V 1, V 2, hsub 0, hsub 1, hsub 2, hRich 0, hRich 1, hRich 2,
        hLift (ho (by decide : 0 < 1)), hLift (ho (by decide : 1 < 2))⟩
    · exact ⟨V 2, V 1, V 0, hsub 2, hsub 1, hsub 0, hRich 2, hRich 1, hRich 0,
        hLift (ho (by decide : 1 < 2)), hLift (ho (by decide : 0 < 1))⟩
  · exact ⟨hne.elim (fun x => ⟨x, mem_univ x⟩), ordConnected_univ, hopen⟩

/-- Paper `lem:find-zeta`: nested open regions force a dense set of points
unless an endpoint-free locally finite interval supplies a saturated `ℤ`. -/
theorem hasSaturatedZeta_of_open_saturated {β : Type*} [PartialOrder β] {C : Set β}
    (hC : IsSaturatedChain C) (hne : C.Nonempty) (hopen : IsOpenSubposet C)
    (hsc : IsScattered β) (hvac : IsVacillating β) : HasSaturatedZeta C := by
  classical
  let : LinearOrder C := hC.1.linearOrder
  have hopenC : IsOpenSubposet (univ : Set C) := by
    constructor
    · intro x _
      obtain ⟨y, hy, hyx⟩ := hopen.1 x.1 x.2
      exact ⟨⟨y, hy⟩, mem_univ _, hyx⟩
    · intro x _
      obtain ⟨y, hy, hxy⟩ := hopen.2 x.1 x.2
      exact ⟨⟨y, hy⟩, mem_univ _, hxy⟩
  have hZ := hasSaturatedZeta_of_open_linear hne.to_subtype hopenC
    (hsc.subtype C) (hvac.saturated_subtype hC)
  exact (hasSaturatedZeta_image hZ (OrderEmbedding.subtype C)
    (saturationPreserving_subtype_of_saturated hC)).mono (by rintro _ ⟨x, _, rfl⟩; exact x.2)

end AharoniKorman
