import AharoniKorman.Structural.EtaReplacement

/-! The example following `def:esmc`: an eta-replacement need not cover its target. -/

namespace AharoniKorman.EtaReplacementExample

open Set

/-- The rational source, a second rational chain in its zero fibre, and a point above both
branches of that fibre. -/
inductive Point
  | original (q : ℚ)
  | replacement (q : ℚ)
  | extra
  deriving DecidableEq

namespace Point

private def index : Point → ℚ
  | .original q => q
  | .replacement _ | .extra => 0

private def withinFibre : Point → Point → Prop
  | .original q, .original r => q = r
  | .original q, .extra => q = 0
  | .replacement q, .replacement r => q ≤ r
  | .replacement _, .extra | .extra, .extra => True
  | _, _ => False

private theorem index_eq_of_within {x y : Point} (h : withinFibre x y) : x.index = y.index := by
  cases x <;> cases y <;> simp_all [index, withinFibre]

private theorem within_trans {x y z : Point} (hxy : withinFibre x y) (hyz : withinFibre y z) :
    withinFibre x z := by
  cases x <;> cases y <;> cases z <;> simp_all [withinFibre]
  exact le_trans hxy hyz

private theorem within_antisymm {x y : Point} (hxy : withinFibre x y) (hyx : withinFibre y x) :
    x = y := by
  cases x <;> cases y <;> simp_all [withinFibre]
  exact le_antisymm hxy hyx

instance : PartialOrder Point where
  le x y := x.index < y.index ∨ withinFibre x y
  le_refl x := Or.inr (by cases x <;> simp [withinFibre])
  le_trans x y z hxy hyz := by
    rcases hxy with hx | hx <;> rcases hyz with hy | hy
    · exact Or.inl (hx.trans hy)
    · exact Or.inl (index_eq_of_within hy ▸ hx)
    · exact Or.inl ((index_eq_of_within hx).symm ▸ hy)
    · exact Or.inr (within_trans hx hy)
  le_antisymm x y hxy hyx := by
    rcases hxy with hx | hx <;> rcases hyx with hy | hy
    · exact (hx.asymm hy).elim
    · exact (hx.ne (index_eq_of_within hy).symm).elim
    · exact (hy.ne (index_eq_of_within hx).symm).elim
    · exact within_antisymm hx hy

private theorem index_mono : Monotone index := fun _ _ h => h.elim le_of_lt
  (fun he => le_of_eq (index_eq_of_within he))

private theorem lt_of_index_lt {x y : Point} (h : x.index < y.index) : x < y :=
  lt_of_le_not_ge (Or.inl h) (fun h' => h.not_ge (index_mono h'))

private theorem original_le (q r : ℚ) : original q ≤ original r ↔ q ≤ r := by
  change q < r ∨ q = r ↔ q ≤ r
  exact ⟨fun h => h.elim le_of_lt le_of_eq, lt_or_eq_of_le⟩

private theorem replacement_le (q r : ℚ) : replacement q ≤ replacement r ↔ q ≤ r := by
  change (0 < (0 : ℚ) ∨ q ≤ r) ↔ q ≤ r
  simp

private theorem replacement_lt (q r : ℚ) : replacement q < replacement r ↔ q < r := by
  rw [lt_iff_le_not_ge, replacement_le, replacement_le, lt_iff_le_not_ge]

private theorem replacement_lt_extra (q : ℚ) : replacement q < extra := by
  change (0 < (0 : ℚ) ∨ True) ∧ ¬ (0 < (0 : ℚ) ∨ False)
  simp

private theorem original_zero_lt_extra : original 0 < extra := by
  change (0 < (0 : ℚ) ∨ (0 : ℚ) = 0) ∧ ¬ (0 < (0 : ℚ) ∨ False)
  simp

private theorem original_zero_incomparable (q : ℚ) :
    Incomparable (original 0) (replacement q) := by
  change (¬ (0 < (0 : ℚ) ∨ False)) ∧ (¬ (0 < (0 : ℚ) ∨ False))
  simp

instance : Countable Point := by
  let encode : Point → ℚ ⊕ (ℚ ⊕ Unit)
    | .original q => .inl q
    | .replacement q => .inr (.inl q)
    | .extra => .inr (.inr ())
  apply Function.Injective.countable (f := encode)
  intro x y h
  cases x <;> cases y <;> simp_all [encode]

end Point

open Point

def source : Set Point := range original

def replacementFibre : Set Point := range replacement

def target : Set Point := {x | x ≠ original 0}

private theorem eta_range {f : ℚ → Point} (hf : ∀ q r, f q ≤ f r ↔ q ≤ r) :
    IsEtaChain (range f) := by
  have hi : Function.Injective f := fun x y h => le_antisymm
    ((hf x y).mp h.le) ((hf y x).mp h.ge)
  refine ⟨{ toEquiv := Equiv.ofInjective f hi, map_rel_iff' := ?_ }⟩
  intro q r
  exact hf q r

private theorem source_eta : IsEtaChain source := eta_range original_le

private theorem replacement_eta : IsEtaChain replacementFibre := eta_range replacement_le

private theorem no_replacement_in_chain_with_zero {S : Set Point} (hS : IsChain (· ≤ ·) S)
    (hzero : original 0 ∈ S) (q : ℚ) : replacement q ∉ S := by
  intro hq
  rcases hS.total hzero hq with h | h
  · exact (original_zero_incomparable q).not_le h
  · exact (original_zero_incomparable q).not_ge h

theorem source_eta_maximal : IsEtaMaximalChain source := by
  refine ⟨source_eta, fun D hD hCD => Set.Subset.antisymm ?_ hCD⟩
  have hz : original 0 ∈ D := hCD (mem_range_self 0)
  intro x hx
  cases x with
  | original q => exact mem_range_self q
  | replacement q => exact (no_replacement_in_chain_with_zero hD.isChain hz q hx).elim
  | extra =>
    obtain ⟨p, hp, hlo, hhi⟩ := hD.exists_between hz hx original_zero_lt_extra
    cases p with
    | original q =>
      have h0q : (0 : ℚ) < q := by
        exact lt_of_le_of_ne ((original_le _ _).mp hlo.le) (fun he => hlo.ne (congrArg original he))
      exact (h0q.not_ge (index_mono hhi.le)).elim
    | replacement q => exact (no_replacement_in_chain_with_zero hD.isChain hz q hp).elim
    | extra => exact (lt_irrefl _ hhi).elim

private theorem target_chain : IsChain (· ≤ ·) target := by
  intro x hx y hy _
  rcases lt_trichotomy x.index y.index with h | h | h
  · exact Or.inl (lt_of_index_lt h).le
  · cases x <;> cases y <;> simp_all [target, index]
    · exact (le_total _ _).imp ((replacement_le _ _).mpr) ((replacement_le _ _).mpr)
    · exact Or.inl (replacement_lt_extra _).le
    · exact Or.inr (replacement_lt_extra _).le
  · exact Or.inr (lt_of_index_lt h).le

private theorem target_dense {x y : Point} (hx : x ∈ target) (hy : y ∈ target) (hxy : x < y) :
    ∃ z ∈ target, x < z ∧ z < y := by
  rcases lt_or_eq_of_le (index_mono hxy.le) with h | h
  · obtain ⟨q, hq, hqy⟩ := exists_between h
    by_cases hz : q = 0
    · obtain ⟨r, hr, hrq⟩ := exists_between hq
      exact ⟨original r, fun he => (hrq.trans_eq hz).ne (original.inj he),
        lt_of_index_lt hr, lt_of_index_lt (hrq.trans hqy)⟩
    · exact ⟨original q, fun he => hz (original.inj he), lt_of_index_lt hq, lt_of_index_lt hqy⟩
  · cases x <;> cases y <;> simp_all [target, index]
    · obtain ⟨q, hq, hqr⟩ := exists_between ((replacement_lt _ _).mp hxy)
      exact ⟨replacement q, by simp, (replacement_lt _ _).mpr hq,
        (replacement_lt _ _).mpr hqr⟩
    · rename_i r
      obtain ⟨q, hq⟩ := exists_gt r
      exact ⟨replacement q, by simp, (replacement_lt _ _).mpr hq, replacement_lt_extra _⟩
    · exact (hxy.not_ge (replacement_lt_extra _).le).elim

private theorem target_eta : IsEtaChain target := by
  apply isEtaChain_of_countable_dense target_chain ⟨extra, by simp [target]⟩
    (fun ⦃_ _⦄ => target_dense)
  · intro x _
    obtain ⟨q, hq⟩ := exists_lt (min x.index 0)
    exact ⟨original q, fun he => (hq.trans_le (min_le_right _ _)).ne (original.inj he),
      lt_of_index_lt (hq.trans_le (min_le_left _ _))⟩
  · intro x _
    obtain ⟨q, hq⟩ := exists_gt (max x.index 0)
    exact ⟨original q, fun he => ((le_max_right _ _).trans_lt hq).ne (original.inj he).symm,
      lt_of_index_lt ((le_max_left _ _).trans_lt hq)⟩

theorem target_eta_maximal : IsEtaMaximalChain target := by
  refine ⟨target_eta, fun D hD hCD => Set.Subset.antisymm ?_ hCD⟩
  intro p hp hp0
  have hz : original 0 ∈ D := hp0 ▸ hp
  exact no_replacement_in_chain_with_zero hD.isChain hz 0 (hCD (by simp [target]))

private theorem replacement_interval : IsIntervalIn replacementFibre target := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨q, rfl⟩
    simp [target]
  · rintro _ ⟨q, rfl⟩ _ ⟨r, rfl⟩ _ p hp hqp hpr
    have hzero : p.index = 0 := le_antisymm (index_mono hpr) (index_mono hqp)
    cases p with
    | original s => exact (hp (congrArg original hzero)).elim
    | replacement s => exact mem_range_self s
    | extra => exact ((replacement_lt_extra _).not_ge hpr).elim

/-- The witness fixes each nonzero rational and replaces zero by the second rational chain. -/
noncomputable def witness : EtaReplacement source target where
  source := source_eta_maximal
  target := target_eta_maximal
  image x := if x.1 = original 0 then replacementFibre else {x.1}
  image_nonempty := by
    intro x
    split_ifs
    · exact replacement_eta.nonempty
    · exact singleton_nonempty _
  image_interval := by
    intro x
    split_ifs with h
    · exact replacement_interval
    · refine ⟨Set.singleton_subset_iff.mpr h, ?_⟩
      rintro _ rfl _ rfl _ z _ hxz hzx
      exact mem_singleton_iff.mpr (le_antisymm hzx hxz)
  image_shape := by
    intro x
    split_ifs
    · exact Or.inr replacement_eta
    · exact Or.inl rfl
  source_lt_image := by
    rintro ⟨_, ⟨q, rfl⟩⟩ ⟨_, ⟨r, rfl⟩⟩ h z hz
    split_ifs at hz with hr
    · obtain ⟨s, rfl⟩ := hz
      have hqr : q < r := lt_of_le_of_ne ((original_le _ _).mp h.le)
        (fun he => h.ne (congrArg original he))
      exact lt_of_index_lt (hqr.trans_eq (original.inj hr))
    · exact (mem_singleton_iff.mp hz).symm ▸ h
  image_lt_source := by
    rintro ⟨_, ⟨q, rfl⟩⟩ ⟨_, ⟨r, rfl⟩⟩ h z hz
    split_ifs at hz with hq
    · obtain ⟨s, rfl⟩ := hz
      have hqr : q < r := lt_of_le_of_ne ((original_le _ _).mp h.le)
        (fun he => h.ne (congrArg original he))
      exact lt_of_index_lt ((original.inj hq).symm.trans_lt hqr)
    · exact (mem_singleton_iff.mp hz).symm ▸ h

/-- The target contains the extra point, although it belongs to none of the witness fibres. -/
theorem target_not_covered : extra ∈ target \ ⋃ x, witness.image x := by
  refine ⟨by simp [target], ?_⟩
  intro h
  obtain ⟨⟨_, ⟨q, rfl⟩⟩, hq⟩ := mem_iUnion.mp h
  change extra ∈ (if original q = original 0 then replacementFibre else {original q}) at hq
  split_ifs at hq
  · obtain ⟨r, hr⟩ := hq
    cases hr
  · cases mem_singleton_iff.mp hq

/-- Before adding the extra point, the union of the replacement fibres is precisely
the retained rationals together with the new rational chain. -/
theorem union_image : (⋃ x, witness.image x) = (source \ {original 0}) ∪ replacementFibre := by
  ext p
  constructor
  · intro hp
    obtain ⟨x, hx⟩ := mem_iUnion.mp hp
    by_cases h : x.1 = original 0
    · exact Or.inr (by simpa only [witness, if_pos h] using hx)
    · have hp' : p = x.1 := mem_singleton_iff.mp (by simpa only [witness, if_neg h] using hx)
      exact Or.inl (hp'.symm ▸ ⟨x.2, fun he => h (mem_singleton_iff.mp he)⟩)
  · rintro (⟨hp, h0⟩ | hp)
    · refine mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
      have hp0 : p ≠ original 0 := fun he => h0 (mem_singleton_iff.mpr he)
      simp only [witness, if_neg hp0, mem_singleton_iff]
    · exact mem_iUnion.mpr ⟨⟨original 0, mem_range_self 0⟩, by simpa only [witness, if_pos rfl]⟩

theorem union_image_not_eta_maximal : ¬ IsEtaMaximalChain (⋃ x, witness.image x) := by
  intro hmax
  have hsub : (⋃ x, witness.image x) ⊆ target :=
    iUnion_subset fun x => (witness.image_interval x).1
  have heq := hmax.2 target target_eta hsub
  exact target_not_covered.2 (heq ▸ target_not_covered.1)

end AharoniKorman.EtaReplacementExample
