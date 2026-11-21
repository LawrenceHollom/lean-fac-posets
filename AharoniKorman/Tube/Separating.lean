import AharoniKorman.Tube.Defs
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.Interval.Set.OrdConnected

/-! Separating tubes and maximal tubes in convex regions. -/

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- An ambient-set version of a maximal tube of the induced order on `V`. -/
def IsMaximalTubeIn (V T : Set α) : Prop :=
  T ⊆ V ∧ IsTube T ∧ ∀ x ∈ V, x ∉ T → (T ∩ incomparableSet x).Infinite

/-- A nonempty tube which puts every external point entirely on one side,
unless that point has infinitely many incomparabilities in the tube. -/
def IsSeparatingTube (T : Set α) : Prop :=
  IsTube T ∧ T.Nonempty ∧ ∀ x ∉ T,
    (∀ t ∈ T, x < t) ∨ (∀ t ∈ T, t < x) ∨ (T ∩ incomparableSet x).Infinite

theorem IsMaximalTube.image_subtype {V : Set α} {T : Set V}
    (hT : IsMaximalTube T) : IsMaximalTubeIn V (Subtype.val '' T) := by
  refine ⟨by rintro _ ⟨x, _, rfl⟩; exact x.2, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    apply ((hT.1 x hx).image Subtype.val).subset
    rintro _ ⟨⟨y, hy, rfl⟩, hinc⟩
    exact ⟨y, ⟨hy, hinc⟩, rfl⟩
  · intro x hx hxT
    let xv : V := ⟨x, hx⟩
    have hnot : xv ∉ T := fun h => hxT ⟨xv, h, rfl⟩
    have hinf := (isMaximalTube_iff T).mp hT |>.2 xv hnot
    apply (hinf.image Subtype.val_injective.injOn).mono
    rintro _ ⟨y, ⟨hy, hinc⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, hinc⟩

theorem IsMaximalTubeIn.nonempty {V T : Set α} (hT : IsMaximalTubeIn V T)
    (hV : V.Nonempty) : T.Nonempty := by
  obtain ⟨x, hx⟩ := hV
  by_contra h
  have he : T = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hi := hT.2.2 x hx (by simp [he])
  simp [he] at hi

theorem IsMaximalTubeIn.exists_gt {V T : Set α} (hT : IsMaximalTubeIn V T)
    (hV : ∀ x ∈ V, ∃ y ∈ V, x < y) {t : α} (ht : t ∈ T) :
    ∃ u ∈ T, t < u := by
  classical
  by_contra h
  push Not at h
  obtain ⟨q, hqV, htq⟩ := hV t (hT.1 ht)
  have hqT : q ∉ T := fun hq => h q hq htq
  apply hT.2.2 q hqV hqT
  apply (hT.2.1 t ht).subset
  rintro y ⟨hy, hinc⟩
  refine ⟨hy, ?_⟩
  show ¬ t ≤ y ∧ ¬ y ≤ t
  constructor
  · intro hty
    have hyt : y = t := by
      by_contra hne
      exact h y hy (lt_of_le_of_ne hty (Ne.symm hne))
    exact hinc.not_ge (hyt.le.trans htq.le)
  · intro hyt
    exact hinc.not_ge (hyt.trans htq.le)

theorem IsMaximalTubeIn.exists_lt {V T : Set α} (hT : IsMaximalTubeIn V T)
    (hV : ∀ x ∈ V, ∃ y ∈ V, y < x) {t : α} (ht : t ∈ T) :
    ∃ u ∈ T, u < t := by
  have hTd : @IsMaximalTubeIn αᵒᵈ _ V T := by
    refine ⟨hT.1, ?_, ?_⟩
    · intro x hx
      exact (hT.2.1 x hx).subset (fun y hy => ⟨hy.1, ⟨hy.2.2, hy.2.1⟩⟩)
    · intro x hx hn
      exact (hT.2.2 x hx hn).mono (fun y hy => ⟨hy.1, ⟨hy.2.2, hy.2.1⟩⟩)
  exact hTd.exists_gt hV ht

theorem IsMaximalTubeIn.isSeparatingTube {V T : Set α}
    (hT : IsMaximalTubeIn V T) (hV : V.Nonempty) (hconv : OrdConnected V)
    (hmin : ∀ x ∈ V, ∃ y ∈ V, y < x)
    (hmax : ∀ x ∈ V, ∃ y ∈ V, x < y) : IsSeparatingTube T := by
  classical
  refine ⟨hT.2.1, hT.nonempty hV, ?_⟩
  intro x hxT
  by_cases hinf : (T ∩ incomparableSet x).Infinite
  · exact Or.inr (Or.inr hinf)
  have hfin : (T ∩ incomparableSet x).Finite := Set.not_infinite.mp hinf
  have hxV : x ∉ V := fun hx => hinf (hT.2.2 x hx hxT)
  let : NoMaxOrder T := ⟨fun t => by
    obtain ⟨u, hu, htu⟩ := hT.exists_gt hmax t.2
    exact ⟨⟨u, hu⟩, htu⟩⟩
  let : NoMinOrder T := ⟨fun t => by
    obtain ⟨u, hu, hut⟩ := hT.exists_lt hmin t.2
    exact ⟨⟨u, hu⟩, hut⟩⟩
  have hcomp : ∀ t ∈ T, x ≤ t ∨ t ≤ x := by
    intro t ht
    by_contra h
    push Not at h
    have hbad : (Subtype.val ⁻¹' (T ∩ incomparableSet x) : Set T).Finite :=
      hfin.preimage Subtype.val_injective.injOn
    obtain ⟨lo, hlo, hlogood⟩ :=
      (Set.Iio_infinite (⟨t, ht⟩ : T)).sdiff hbad |>.nonempty
    obtain ⟨hi, hhi, hhigood⟩ :=
      (Set.Ioi_infinite (⟨t, ht⟩ : T)).sdiff hbad |>.nonempty
    have hloComp : x ≤ lo.1 ∨ lo.1 ≤ x := by
      by_contra hn
      exact hlogood ⟨lo.2, ⟨(not_or.mp hn).1, (not_or.mp hn).2⟩⟩
    have hhiComp : x ≤ hi.1 ∨ hi.1 ≤ x := by
      by_contra hn
      exact hhigood ⟨hi.2, ⟨(not_or.mp hn).1, (not_or.mp hn).2⟩⟩
    have hlox : lo.1 ≤ x := hloComp.resolve_left (fun hxl => h.1 (hxl.trans hlo.le))
    have hxhi : x ≤ hi.1 := hhiComp.resolve_right (fun hhx => h.2 (hhi.le.trans hhx))
    exact hxV (hconv.out (hT.1 lo.2) (hT.1 hi.2) ⟨hlox, hxhi⟩)
  obtain ⟨t, ht⟩ := hT.nonempty hV
  rcases hcomp t ht with hxt | htx
  · left
    intro u hu
    have hxu : x ≤ u := (hcomp u hu).resolve_right fun hux =>
      hxV (hconv.out (hT.1 hu) (hT.1 ht) ⟨hux, hxt⟩)
    exact lt_of_le_of_ne hxu (fun h => hxT (h ▸ hu))
  · right; left
    intro u hu
    have hux : u ≤ x := (hcomp u hu).resolve_left fun hxu =>
      hxV (hconv.out (hT.1 ht) (hT.1 hu) ⟨htx, hxu⟩)
    exact lt_of_le_of_ne hux (fun h => hxT (h ▸ hu))

end AharoniKorman
