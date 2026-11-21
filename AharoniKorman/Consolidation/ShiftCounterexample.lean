import AharoniKorman.Consolidation.AtomicOrder
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Set.Card

/-! The first consolidation counterexample in `vacillating.tex`. The lane
coordinate encodes the paper's `(z,i)` as `2*z+i`. -/

namespace AharoniKorman.Consolidation.ShiftCounterexample

open Set Completion

noncomputable section

structure Point where
  lane : ℤ
  height : ℕ
  deriving DecidableEq

private theorem Point.eq_of_coordinates {a b : Point}
    (hl : a.lane = b.lane) (hh : a.height = b.height) : a = b := by
  cases a
  cases b
  simp_all

instance : PartialOrder Point where
  le a b := a.lane + 2 ≤ b.lane ∨ (a.lane ≤ b.lane ∧ a.height ≤ b.height)
  le_refl a := Or.inr ⟨le_rfl, le_rfl⟩
  le_trans a b c hab hbc := by
    rcases hab with hab | ⟨hab, hab'⟩ <;> rcases hbc with hbc | ⟨hbc, hbc'⟩
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨hab.trans hbc, hab'.trans hbc'⟩
  le_antisymm a b hab hba := by
    rcases hab with h | ⟨h, h'⟩ <;> rcases hba with k | ⟨k, k'⟩
    · omega
    · omega
    · omega
    · exact Point.eq_of_coordinates (le_antisymm h k) (le_antisymm h' k')

theorem le_iff {a b : Point} : a ≤ b ↔
    a.lane + 2 ≤ b.lane ∨ (a.lane ≤ b.lane ∧ a.height ≤ b.height) := Iff.rfl

theorem lane_mono {a b : Point} (hab : a ≤ b) : a.lane ≤ b.lane := by
  rcases le_iff.1 hab with h | h <;> omega

/-- The paper's generating vertical, reset, and interleaving relations. -/
def Step (a b : Point) : Prop :=
  (a.lane = b.lane ∧ b.height = a.height + 1) ∨
  (a.lane + 2 = b.lane ∧ b.height = 0) ∨
  (a.lane + 1 = b.lane ∧ a.height = b.height)

theorem le_iff_steps {a b : Point} : a ≤ b ↔ Relation.ReflTransGen Step a b := by
  have vertical (z : ℤ) (n m : ℕ) (hnm : n ≤ m) :
      Relation.ReflTransGen Step ⟨z, n⟩ ⟨z, m⟩ := by
    induction m, hnm using Nat.le_induction with
    | base => exact Relation.ReflTransGen.refl
    | succ m hnm ih => exact ih.tail (Or.inl ⟨rfl, rfl⟩)
  have horizontal (z : ℤ) (k : ℕ) (n : ℕ) :
      Relation.ReflTransGen Step ⟨z, n⟩ ⟨z + k, n⟩ := by
    induction k with
    | zero => simp only [Nat.cast_zero, add_zero]; exact Relation.ReflTransGen.refl
    | succ k ih => exact ih.tail (Or.inr (Or.inr ⟨by simp; omega, rfl⟩))
  have hbetween (a b : ℤ) (hab : a ≤ b) (n : ℕ) :
      Relation.ReflTransGen Step ⟨a, n⟩ ⟨b, n⟩ := by
    have heq : a + ((b-a).toNat : ℤ) = b := by omega
    simpa only [heq] using horizontal a (b-a).toNat n
  constructor
  · rcases a with ⟨z, n⟩
    rcases b with ⟨w, m⟩
    rintro (h | ⟨h, h'⟩)
    · change z + 2 ≤ w at h
      have hreset : Relation.ReflTransGen Step ⟨z, n⟩ ⟨z+2, 0⟩ :=
        Relation.ReflTransGen.single (Or.inr (Or.inl ⟨rfl, rfl⟩))
      exact (hreset.trans (hbetween (z+2) w h 0)).trans (vertical w 0 m (Nat.zero_le _))
    · exact (hbetween z w h n).trans (vertical w n m h')
  · intro h
    induction h with
    | refl => exact le_rfl
    | tail _ hbc ih =>
      apply ih.trans
      rcases hbc with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
      · exact Or.inr ⟨h.le, by omega⟩
      · exact Or.inl h.le
      · exact Or.inr ⟨by omega, h'.le⟩

private def parity (i : Bool) : ℤ := if i then 1 else 0

def branch (i : Bool) : Set Point := {p | p.lane % 2 = parity i}

theorem branch_maximal (i : Bool) : IsMaximalChain (branch i) := by
  have hchain : IsChain (· ≤ ·) (branch i) := by
    intro a ha b hb _
    change a.lane % 2 = parity i at ha
    change b.lane % 2 = parity i at hb
    rcases lt_trichotomy a.lane b.lane with hl | heq | hl
    · exact Or.inl (le_iff.2 (Or.inl (by omega)))
    · exact (le_total a.height b.height).imp
        (fun hh => le_iff.2 (Or.inr ⟨heq.le, hh⟩))
        (fun hh => le_iff.2 (Or.inr ⟨heq.ge, hh⟩))
    · exact Or.inr (le_iff.2 (Or.inl (by omega)))
  refine ⟨hchain, fun C hC hsub => Set.Subset.antisymm hsub ?_⟩
  intro p hp
  by_contra hnot
  let q : Point := ⟨p.lane - 1, p.height + 1⟩
  have hq : q ∈ branch i := by
    change p.lane % 2 ≠ parity i at hnot
    change (p.lane - 1) % 2 = parity i
    cases i <;> simp [parity] at * <;> omega
  rcases hC.total hp (hsub hq) with hpq | hqp
  · have hh := lane_mono hpq
    change p.lane ≤ p.lane - 1 at hh
    omega
  · have hh := le_iff.1 hqp
    change p.lane - 1 + 2 ≤ p.lane ∨ (p.lane - 1 ≤ p.lane ∧ p.height + 1 ≤ p.height) at hh
    omega

private def laneParity (p : Point) : Bool := decide (p.lane % 2 = 1)

private theorem mem_laneParity (p : Point) : p ∈ branch (laneParity p) := by
  change p.lane % 2 = (if decide (p.lane % 2 = 1) then 1 else 0)
  by_cases h : p.lane % 2 = 1
  · simp [h]
  · have hzero : p.lane % 2 = 0 := by omega
    simp [hzero]

/-- The two parity chains bound the width by two, and adjacent lanes furnish a two-point antichain. -/
theorem width_two : (∀ A : Set Point, IsAntichain (· ≤ ·) A → A.encard ≤ 2) ∧
    ∃ A : Set Point, IsAntichain (· ≤ ·) A ∧ A.encard = 2 := by
  constructor
  · intro A hA
    have hinj : Set.InjOn laneParity A := by
      intro a ha b hb heq
      by_contra hne
      rcases (branch_maximal (laneParity a)).1.total (mem_laneParity a)
        (heq.symm ▸ mem_laneParity b) with h | h
      · exact hA ha hb hne h
      · exact hA hb ha (fun heq => hne heq.symm) h
    rw [← hinj.encard_image]
    have huniv : (univ : Set Bool) = {false, true} := by ext p; cases p <;> simp
    have hle : (laneParity '' A).encard ≤ (univ : Set Bool).encard :=
      encard_le_encard (subset_univ _)
    rwa [huniv, encard_pair (by decide : false ≠ true)] at hle
  · let a : Point := ⟨0, 1⟩
    let b : Point := ⟨1, 0⟩
    have hab : Incomparable a b := ⟨by simp [a, b, le_iff], by simp [a, b, le_iff]⟩
    refine ⟨{a, b}, ?_, encard_pair hab.ne⟩
    exact IsAntichain.singleton.insert (fun _ hmem _ => (mem_singleton_iff.1 hmem).symm ▸ hab.not_ge)
      (fun _ hmem _ => (mem_singleton_iff.1 hmem).symm ▸ hab.not_le)

private def atHeight (n : ℕ) : Set Point := {p | p.height = n}

private theorem atHeight_maximal (n : ℕ) : IsMaximalChain (atHeight n) := by
  refine ⟨?_, fun C hC hsub => Set.Subset.antisymm hsub ?_⟩
  · intro a ha b hb _
    have hh : a.height = b.height := ha.trans hb.symm
    exact (le_total a.lane b.lane).imp
      (fun h => le_iff.2 (Or.inr ⟨h, hh.le⟩)) (fun h => le_iff.2 (Or.inr ⟨h, hh.ge⟩))
  · intro p hp
    by_contra hnot
    have hne : p.height ≠ n := hnot
    rcases lt_or_gt_of_ne hne with hpn | hnp
    · let q : Point := ⟨p.lane - 1, n⟩
      have hq : q ∈ atHeight n := rfl
      rcases hC.total hp (hsub hq) with hpq | hqp
      · have h := lane_mono hpq
        change p.lane ≤ p.lane - 1 at h
        omega
      · have h := le_iff.1 hqp
        change p.lane - 1 + 2 ≤ p.lane ∨ (p.lane - 1 ≤ p.lane ∧ n ≤ p.height) at h
        omega
    · let q : Point := ⟨p.lane + 1, n⟩
      have hq : q ∈ atHeight n := rfl
      rcases hC.total hp (hsub hq) with hpq | hqp
      · have h := le_iff.1 hpq
        change p.lane + 2 ≤ p.lane + 1 ∨ (p.lane ≤ p.lane + 1 ∧ p.height ≤ n) at h
        omega
      · have h := lane_mono hqp
        change p.lane + 1 ≤ p.lane at h
        omega

/-- Every finite set misses the maximal chain at a height above all its members. -/
theorem no_finite_cut (S : Set Point) (hS : S.Finite) :
    ∃ C : Set Point, IsMaximalChain C ∧ Disjoint S C := by
  obtain ⟨n, hn⟩ := (hS.image Point.height).bddAbove
  refine ⟨atHeight (n + 1), atHeight_maximal _, Set.disjoint_left.2 ?_⟩
  intro p hp hc
  have hbound : p.height ≤ n := hn (mem_image_of_mem _ hp)
  have heq : p.height = n + 1 := hc
  omega

private def shift : Point ≃o Point where
  toFun p := ⟨p.lane-1,p.height⟩
  invFun p := ⟨p.lane+1,p.height⟩
  left_inv p := Point.eq_of_coordinates (by simp) rfl
  right_inv p := Point.eq_of_coordinates (by simp) rfl
  map_rel_iff' := by
    intro a b
    change (a.lane-1+2 ≤ b.lane-1 ∨ (a.lane-1 ≤ b.lane-1 ∧ a.height ≤ b.height)) ↔
      (a.lane+2 ≤ b.lane ∨ (a.lane ≤ b.lane ∧ a.height ≤ b.height))
    omega

private theorem shift_mem {p : Point} {i : Bool} (hp : p ∈ branch i) : shift p ∈ branch (!i) := by
  change p.lane % 2 = parity i at hp
  change (p.lane - 1) % 2 = parity (!i)
  cases i <;> simp [parity] at * <;> omega

private theorem shift_preserves : SaturationPreserving shift.toOrderEmbedding := by
  intro C hC
  refine ⟨hC.1.image shift.toOrderEmbedding, ?_⟩
  rintro _ _ p ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hap hpb hcomp
  refine ⟨shift.symm p, ?_, shift.apply_symm_apply p⟩
  apply hC.2 ha hb
  · change shift a ≤ p at hap
    exact shift.le_iff_le.1 (by simpa only [shift.apply_symm_apply] using hap)
  · change p ≤ shift b at hpb
    exact shift.le_iff_le.1 (by simpa only [shift.apply_symm_apply] using hpb)
  · intro c hc
    have h := hcomp (shift c) ⟨c, hc, rfl⟩
    change p ≤ shift c ∨ shift c ≤ p at h
    exact h.imp (fun h => by simpa only [shift.symm_apply_apply] using shift.symm.monotone h)
      (fun h => by simpa only [shift.symm_apply_apply] using shift.symm.monotone h)

private theorem shift_lt (p : Point) : shift p < p :=
  lt_of_le_of_ne (le_iff.2 (Or.inr ⟨by change p.lane - 1 ≤ p.lane; omega, le_rfl⟩))
    (fun heq => by have h := congrArg Point.lane heq; change p.lane - 1 = p.lane at h; omega)

private theorem strictAnti_unbounded_lane {f : ℕ → Point} (hf : StrictAnti f) (z : ℤ) :
    ∃ n, (f n).lane < z := by
  classical
  by_contra! hbdd
  let L := range fun n => (f n).lane
  have hB : BddBelow L := ⟨z, by rintro _ ⟨n, rfl⟩; exact hbdd n⟩
  obtain ⟨n, hn⟩ := Int.csInf_mem (range_nonempty _) hB
  let R (height : ℕ) := ∃ n, (f n).lane = sInf L ∧ (f n).height = height
  have hR : ∃ height, R height := ⟨(f n).height, n, hn, rfl⟩
  obtain ⟨m, hb, hmin⟩ := Nat.find_spec hR
  let b := f m
  let c := f (m + 1)
  have hcb : c < b := hf (Nat.lt_succ_self m)
  have hcl := lane_mono hcb.le
  have hleast : sInf L ≤ c.lane := csInf_le hB (mem_range_self (m + 1))
  have hcle : c.lane = sInf L := le_antisymm (hcl.trans_eq hb) hleast
  have hsame : c.lane = b.lane := hcle.trans hb.symm
  have hheight : c.height ≤ b.height := by
    rcases le_iff.1 hcb.le with h | h
    · omega
    · exact h.2
  have hheight' : b.height ≤ c.height := hmin.symm ▸ Nat.find_min' hR ⟨m + 1, hcle, rfl⟩
  exact hcb.ne (Point.eq_of_coordinates (hcle.trans hb.symm) (le_antisymm hheight hheight'))

private theorem negative_rep_unbounded_lane (A : DecreasingChain Point) (z : ℤ) :
    ∃ a : A.1, a.1.lane < z := by
  let : Nonempty A.1 := A.1.nonempty.to_subtype
  let : NoMinOrder A.1 := ⟨A.2.exists_lt⟩
  obtain ⟨f, hf⟩ := Nat.exists_strictAnti (α := A.1)
  obtain ⟨n, hn⟩ := strictAnti_unbounded_lane (f := fun i => (f i).1) hf z
  exact ⟨f n, hn⟩

private theorem negative_upperProfile (A : DecreasingChain Point) :
    (DecreasingGerm.ofChain A).upperProfile = univ := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨a, ha⟩ := negative_rep_unbounded_lane A (p.lane-1)
  apply (DecreasingGerm.mem_upperProfile_ofChain A p).2
  refine ⟨a, lt_of_le_of_ne (le_iff.2 (Or.inl (by omega))) ?_⟩
  exact fun heq => by have h := congrArg Point.lane heq; omega

private def negativeBranch (i : Bool) : DecreasingChain Point := by
  let C : MaximalChains Point := ⟨branch i, branch_maximal i⟩
  have hne : (branch i).Nonempty := ⟨⟨parity i, 0⟩, by
    change parity i % 2 = parity i
    cases i <;> decide⟩
  let A : SaturatedChain Point := ⟨branch i, hne, C.isSaturated⟩
  refine ⟨A, ?_⟩
  rintro ⟨p, hp⟩
  have hp' : p.1.lane % 2 = parity i := p.2
  let q : A := ⟨⟨p.1.lane - 2, 0⟩, by
    change (p.1.lane - 2) % 2 = parity i
    omega⟩
  have h := lane_mono (hp q)
  change p.1.lane ≤ p.1.lane - 2 at h
  omega

private theorem negativeBranch_atomic (i : Bool) :
    H.decreasing (DecreasingGerm.ofChain (negativeBranch i)) ∈ paperAtomicBoundaries (branch i) := by
  refine ⟨Or.inr ⟨negativeBranch i, Subset.rfl, rfl⟩, (negativeBranch i).toDual, rfl, ?_⟩
  rintro ⟨e⟩
  let f (n : ℕ) : Point := (e ↑n).1
  have hanti : StrictAnti f := fun _ _ h => e.strictMono (WithTop.coe_lt_coe.2 h)
  obtain ⟨n, hn⟩ := strictAnti_unbounded_lane hanti (e ⊤).1.lane
  have hbound : e (↑n : WithTop ℕ) ≤ e ⊤ := e.monotone le_top
  exact hn.not_ge (lane_mono (show @LE.le Point _ (e ⊤).1 (f n) from hbound))

private theorem negativeBranches_ne :
    DecreasingGerm.ofChain (negativeBranch false) ≠ DecreasingGerm.ofChain (negativeBranch true) := by
  classical
  intro heq
  obtain ⟨A, B, hA, hB, hAB⟩ := DecreasingGerm.ofChain_eq_iff.1 heq
  obtain ⟨a, ha⟩ := A.nonempty
  let B' : DecreasingChain Point :=
    IncreasingChain.toDual (α := Pointᵒᵈ) ⟨B, (negativeBranch true).toDual.finalSegment_noTop B hB⟩
  obtain ⟨b, hb⟩ := negative_rep_unbounded_lane B' a.lane
  have hbmem : b.1 ∈ B := b.2
  have hbodd : b.1.lane % 2 = 1 := hB.1 hbmem
  let f (n : ℕ) : A := ⟨⟨b.1.lane - 1, b.1.height + n + 1⟩, by
    apply hA.2 ha
    · change (b.1.lane - 1) % 2 = 0
      omega
    · have hgap : b.1.lane - 1 + 2 ≤ a.lane := by omega
      exact le_iff.2 (Or.inl hgap)⟩
  have hinj : Function.Injective f := by
    intro m n h
    have h' := congrArg (fun p : A => p.1.height) h
    change b.1.height + m + 1 = b.1.height + n + 1 at h'
    omega
  apply (infinite_range_of_injective hinj) ((hAB.left_finite ⟨b.1, hbmem⟩).subset ?_)
  rintro _ ⟨n, rfl⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' := lane_mono (show @LE.le Point _ b.1 (f n).1 from h)
    change b.1.lane ≤ b.1.lane - 1 at h'
    omega
  · have h' := le_iff.1 (show @LE.le Point _ (f n).1 b.1 from h)
    change b.1.lane - 1 + 2 ≤ b.1.lane ∨
      (b.1.lane - 1 ≤ b.1.lane ∧ b.1.height + n + 1 ≤ b.1.height) at h'
    omega

/-- The two distinct bottom atoms in the counterexample consolidate in both directions. -/
theorem distinct_negative_atoms_mutually_consolidate :
    ∃ g h : DecreasingGerm Point, g ≠ h ∧
      H.decreasing g ∈ paperAtomicBoundaries (branch false) ∧
      H.decreasing h ∈ paperAtomicBoundaries (branch true) ∧
      DecreasingGerm.CoinitialBelow g h ∧ DecreasingGerm.CoinitialBelow h g := by
  refine ⟨DecreasingGerm.ofChain (negativeBranch false), DecreasingGerm.ofChain (negativeBranch true),
    negativeBranches_ne, negativeBranch_atomic false, negativeBranch_atomic true, ?_, ?_⟩
  · change (DecreasingGerm.ofChain (negativeBranch true)).upperProfile ⊆
      (DecreasingGerm.ofChain (negativeBranch false)).upperProfile
    simp only [negative_upperProfile, Subset.rfl]
  · change (DecreasingGerm.ofChain (negativeBranch false)).upperProfile ⊆
      (DecreasingGerm.ofChain (negativeBranch true)).upperProfile
    simp only [negative_upperProfile, Subset.rfl]

private theorem atomic_map {X : H Point} (hX : IsPaperAtomicGerm X) :
    IsPaperAtomicGerm (H.map shift.toOrderEmbedding shift_preserves X) := by
  cases X with
  | increasing g =>
    obtain ⟨A, hA, hno⟩ := hX
    change IsAtomicIncreasing (IncreasingGerm.map shift.toOrderEmbedding shift_preserves g)
    rw [← hA, IncreasingGerm.map_ofChain]
    refine ⟨A.map _ _, rfl, ?_⟩
    rintro ⟨e⟩
    exact hno ⟨e.trans (A.1.mapOrderIso shift.toOrderEmbedding shift_preserves).symm.toOrderEmbedding⟩
  | decreasing g =>
    obtain ⟨A, hA, hno⟩ := hX
    change IsAtomicDecreasing (DecreasingGerm.map shift.toOrderEmbedding shift_preserves g)
    let D : DecreasingChain Point := A.toDual
    have hd : DecreasingGerm.ofChain D = g := hA
    rw [← hd, DecreasingGerm.map_ofChain]
    refine ⟨A.map shift.toOrderEmbedding.dual shift_preserves.dual, rfl, ?_⟩
    rintro ⟨e⟩
    exact hno ⟨e.trans (A.1.mapOrderIso shift.toOrderEmbedding.dual shift_preserves.dual).symm.toOrderEmbedding⟩
  | principal _ | bottom | top => exact hX.elim

private theorem boundaries_shift {X : H Point} {i : Bool} (hX : X ∈ boundaries (branch i)) :
    H.map shift.toOrderEmbedding shift_preserves X ∈ boundaries (branch (!i)) := by
  rcases hX with ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
  · refine Or.inl ⟨A.map shift.toOrderEmbedding shift_preserves, ?_, rfl⟩
    intro p hp
    change p ∈ (A.map shift.toOrderEmbedding shift_preserves).1 at hp
    rw [IncreasingChain.map_val] at hp
    obtain ⟨q, hq, hqp⟩ := hp
    exact hqp ▸ shift_mem (hA hq)
  · refine Or.inr ⟨A.map shift.toOrderEmbedding shift_preserves, ?_,
      by simp only [H.map, DecreasingGerm.map_ofChain]⟩
    intro p hp
    change p ∈ (A.map shift.toOrderEmbedding shift_preserves).1 at hp
    rw [DecreasingChain.map_val] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact shift_mem (hA hq)

private theorem shift_improves {X : H Point} {i : Bool} (hX : X ∈ boundaries (branch i)) :
    boundaryProfile (H.map shift.toOrderEmbedding shift_preserves X) ⊆ boundaryProfile X := by
  rcases hX with ⟨A, _, rfl⟩ | ⟨A, _, rfl⟩
  · intro p hp
    change p ∈ (IncreasingGerm.ofChain (A.map shift.toOrderEmbedding shift_preserves)).lowerProfile at hp
    obtain ⟨q, hpq⟩ := (IncreasingGerm.mem_lowerProfile_ofChain _ _).1 hp
    obtain ⟨a, ha, heq⟩ := q.2
    exact (IncreasingGerm.mem_lowerProfile_ofChain _ _).2 ⟨⟨a, ha⟩,
      hpq.trans (heq ▸ shift_lt a)⟩
  · rw [H.map, DecreasingGerm.map_ofChain]
    change (DecreasingGerm.ofChain _).upperProfile ⊆ (DecreasingGerm.ofChain _).upperProfile
    simp only [negative_upperProfile, Subset.rfl]

def branch_consolidation (i : Bool) : PaperAtomicWitness (branch i) (branch (!i)) where
  embedding := OrderEmbedding.ofMapLEIff
    (fun X => ⟨H.map shift.toOrderEmbedding shift_preserves X.1, boundaries_shift X.2.1, atomic_map X.2.2⟩)
    (fun _ _ => H.map_le_map _ _ _ _)
  direction X := H.direction_map _ _ X.1
  profile X := shift_improves X.2.1

private def zeroBlock : IncreasingChain Point := by
  let C : Set Point := {p | p.lane = 0}
  have hC : IsSaturatedChain C := by
    apply IsSaturatedChain.of_ordConnected
    · intro a ha b hb _
      have heq : a.lane = b.lane := ha.trans hb.symm
      exact (le_total a.height b.height).imp (fun h => Or.inr ⟨heq.le, h⟩) (fun h => Or.inr ⟨heq.ge, h⟩)
    · refine ⟨fun a ha b hb p hp => ?_⟩
      exact le_antisymm ((lane_mono hp.2).trans_eq hb) (ha.symm.trans_le (lane_mono hp.1))
  let A : SaturatedChain Point := ⟨C, ⟨⟨0,0⟩, rfl⟩, hC⟩
  refine ⟨A, ?_⟩
  rintro ⟨p, hp⟩
  let q : A := ⟨⟨0, p.1.height + 1⟩, rfl⟩
  rcases le_iff.1 (hp q) with h | h
  · have hl : p.1.lane = 0 := p.2
    change 0 + 2 ≤ p.1.lane at h
    omega
  · exact (Nat.not_succ_le_self p.1.height) h.2

private theorem zeroBlock_omega : IsOmegaRepresentative zeroBlock := by
  intro a
  have hinj : Function.Injective (fun p : zeroBlock.1 => p.1.height) := by
    intro p q h
    have hp : p.1.lane = 0 := p.2
    have hq : q.1.lane = 0 := q.2
    exact Subtype.ext (Point.eq_of_coordinates (hp.trans hq.symm) h)
  apply ((finite_Iic a.1.height).preimage hinj.injOn).subset
  intro p hpa
  rcases le_iff.1 hpa with h | h
  · have hp : p.1.lane = 0 := p.2
    have ha : a.1.lane = 0 := a.2
    omega
  · exact h.2

theorem distinct_profiles : paperAtomicBoundaries (branch false) ≠ paperAtomicBoundaries (branch true) := by
  intro heq
  have h0 : H.increasing (IncreasingGerm.ofChain zeroBlock) ∈ paperAtomicBoundaries (branch false) := by
    refine ⟨Or.inl ⟨zeroBlock, fun p hp => ?_, rfl⟩, zeroBlock, rfl, zeroBlock_omega.no_omegaSucc⟩
    change p.lane = 0 at hp
    change p.lane % 2 = 0
    simp [hp]
  have h1 : H.increasing (IncreasingGerm.ofChain zeroBlock) ∈ boundaries (branch true) :=
    (show H.increasing (IncreasingGerm.ofChain zeroBlock) ∈ paperAtomicBoundaries (branch true) from heq ▸ h0).1
  rcases h1 with ⟨A, hA, ha⟩ | ⟨A, hA, ha⟩
  · have hcuts := congrArg IncreasingGerm.lowerProfile (H.increasing.inj ha)
    obtain ⟨p, hp⟩ := A.1.nonempty
    have hpr := IncreasingGerm.representative_mem_lowerProfile A ⟨p, hp⟩
    obtain ⟨q, hpq⟩ := (IncreasingGerm.mem_lowerProfile_ofChain zeroBlock p).1 (hcuts ▸ hpr)
    have qp : q.1.lane = 0 := q.2
    have hodd : p.lane % 2 = 1 := hA hp
    have hple : p.lane ≤ 0 := (lane_mono hpq.le).trans_eq qp
    obtain ⟨r, hqr⟩ := (IncreasingGerm.mem_lowerProfile_ofChain A q.1).1
      (hcuts ▸ IncreasingGerm.representative_mem_lowerProfile zeroBlock q)
    have hrpos : 0 ≤ r.1.lane := qp.symm.trans_le (lane_mono hqr.le)
    have hrr := IncreasingGerm.representative_mem_lowerProfile A r
    obtain ⟨s, hrs⟩ := (IncreasingGerm.mem_lowerProfile_ofChain zeroBlock r.1).1 (hcuts ▸ hrr)
    have hrl : r.1.lane ≤ 0 := (lane_mono hrs.le).trans_eq s.2
    have hro : r.1.lane % 2 = 1 := hA r.2
    omega
  · cases ha

/-- Paper `ex:no-finite-cut`: the two maximal branches consolidate to each
other and have different atomic profiles. -/
theorem mutual_consolidation_of_distinct_profiles :
    IsMaximalChain (branch false) ∧ IsMaximalChain (branch true) ∧
      Nonempty (PaperAtomicWitness (branch false) (branch true)) ∧
      Nonempty (PaperAtomicWitness (branch true) (branch false)) ∧
      paperAtomicBoundaries (branch false) ≠ paperAtomicBoundaries (branch true) :=
  ⟨branch_maximal _, branch_maximal _, ⟨branch_consolidation false⟩,
    ⟨branch_consolidation true⟩, distinct_profiles⟩

end

end AharoniKorman.Consolidation.ShiftCounterexample
