import AharoniKorman.Completion.WitnessChains

/-! The poset in `ex:cannot-witness`. -/

namespace AharoniKorman.Completion.WitnessObstruction

open Set

inductive Point
  | row (index position : ℕ)
  | ray (position : ℕ)

namespace Point

private def compareLE : Point → Point → Prop
  | row i j, row k l => i < k ∨ i = k ∧ j ≤ l
  | row i _, ray k => i < k
  | ray _, row _ _ => False
  | ray j, ray k => j ≤ k

instance : PartialOrder Point where
  le := compareLE
  le_refl p := by cases p <;> simp [compareLE]
  le_trans p q r := by cases p <;> cases q <;> cases r <;> simp [compareLE] <;> omega
  le_antisymm p q := by cases p <;> cases q <;> simp [compareLE] <;> omega

private theorem row_le_row (i j k l : ℕ) :
    row i j ≤ row k l ↔ i < k ∨ i = k ∧ j ≤ l := Iff.rfl

private theorem row_le_ray (i j k : ℕ) : row i j ≤ ray k ↔ i < k := Iff.rfl

private theorem not_ray_le_row (i j k : ℕ) : ¬ray i ≤ row j k := id

private theorem ray_le_ray (i j : ℕ) : ray i ≤ ray j ↔ i ≤ j := Iff.rfl

private theorem row_strictMono (a : ℕ) : StrictMono (row a) := fun i j hij =>
  lt_of_le_not_ge ((row_le_row ..).mpr (Or.inr ⟨rfl, hij.le⟩)) (by
    rw [row_le_row]
    omega)

private theorem ray_strictMono : StrictMono ray := fun _ _ hij =>
  lt_of_le_not_ge ((ray_le_ray ..).mpr hij.le) (fun hj => hij.not_ge ((ray_le_ray ..).mp hj))

private def rowChain (a : ℕ) : IncreasingChain Point := by
  have hsat : IsSaturatedChain (range (row a)) := by
    refine ⟨(row_strictMono a).monotone.isChain_range, ?_⟩
    rintro _ _ p ⟨i, rfl⟩ ⟨j, rfl⟩ hi hj _
    cases p with
    | row k l =>
        rw [row_le_row] at hi hj
        have heq : k = a := by omega
        subst k
        exact ⟨l, rfl⟩
    | ray k => exact (not_ray_le_row k a j hj).elim
  let C : SaturatedChain Point := ⟨range (row a), range_nonempty _, hsat⟩
  refine ⟨C, ?_⟩
  rintro ⟨m, hmax⟩
  obtain ⟨n, hn⟩ := m.2
  have hnext := hmax ⟨row a (n+1), ⟨n+1, rfl⟩⟩
  change row a (n+1) ≤ m.1 at hnext
  rw [← hn, row_le_row] at hnext
  omega

private def rayChain : IncreasingChain Point := by
  have hsat : IsSaturatedChain (range ray) := by
    refine ⟨ray_strictMono.monotone.isChain_range, ?_⟩
    rintro _ _ p ⟨i, rfl⟩ ⟨_, rfl⟩ hi _ _
    cases p with
    | row k l => exact (not_ray_le_row i k l hi).elim
    | ray k => exact ⟨k, rfl⟩
  let C : SaturatedChain Point := ⟨range ray, range_nonempty _, hsat⟩
  refine ⟨C, ?_⟩
  rintro ⟨m, hmax⟩
  obtain ⟨n, hn⟩ := m.2
  have hnext := hmax ⟨ray (n+1), ⟨n+1, rfl⟩⟩
  change ray (n+1) ≤ m.1 at hnext
  rw [← hn, ray_le_ray] at hnext
  omega

/-- The point denoted `Xₙ` in the paper. -/
def rowLimit (a : ℕ) : H Point := H.increasing (IncreasingGerm.ofChain (rowChain a))

/-- The point denoted `⊤_ℕ` in the paper. -/
def rayLimit : H Point := H.increasing (IncreasingGerm.ofChain rayChain)

private theorem exists_ray_of_witness {C : SaturatedChain Point} (hC : H.Witnesses C rayLimit) :
    ∃ n, ray n ∈ C := by
  obtain ⟨A, hAC, hn, he⟩ := hC
  have hEq : IncreasingEquivalent ⟨A, hn⟩ rayChain := IncreasingGerm.ofChain_eq_iff.mp he
  obtain ⟨p, hp⟩ := hEq.exists_left_gt ⟨ray 0, ⟨0, rfl⟩⟩
  cases h : p.1 with
  | row i j =>
      have hh : ray 0 < p.1 := hp
      rw [h] at hh
      exact (not_ray_le_row 0 i j hh.le).elim
  | ray n => exact ⟨n, h ▸ hAC p.2⟩

private theorem exists_row_of_witness (a : ℕ) {C : SaturatedChain Point}
    (hC : H.Witnesses C (rowLimit a)) : ∃ j, row a j ∈ C := by
  obtain ⟨A, hAC, hn, he⟩ := hC
  have hEq : IncreasingEquivalent ⟨A, hn⟩ (rowChain a) := IncreasingGerm.ofChain_eq_iff.mp he
  obtain ⟨A', D, hA', hD, hAD⟩ := hEq
  obtain ⟨p, hp⟩ := A'.nonempty
  have hrow (d : D) : ∃ i, row a i = d.1 := hD.1 d.2
  obtain ⟨d, hd⟩ := hAD.exists_crossRelated_right ⟨p, hp⟩
  obtain ⟨i, hi⟩ := hrow d
  have hd' : p = row a i ∨ Incomparable p (row a i) := by
    simpa only [CrossRelated, hi] using hd
  cases p with
  | row k j =>
      have hak : a = k := by
        rcases hd' with heq | hinc
        · cases heq
          rfl
        · rcases lt_trichotomy a k with hlt | heq | hgt
          · exact (hinc.not_ge ((row_le_row ..).mpr (Or.inl hlt))).elim
          · exact heq
          · exact (hinc.not_le ((row_le_row ..).mpr (Or.inl hgt))).elim
      exact ⟨j, hak ▸ hAC (hA'.1 hp)⟩
  | ray k =>
      have hka : k ≤ a := by
        apply le_of_not_gt
        intro hak
        exact hd'.elim (fun heq => by cases heq)
          (fun hinc => hinc.not_ge ((row_le_ray ..).mpr hak))
      have hfin : (univ : Set D).Finite := (hAD.right_finite ⟨ray k, hp⟩).subset (by
        intro q _
        change Incomparable q.1 (ray k)
        obtain ⟨j, hj⟩ := hrow q
        rw [← hj]
        exact ⟨fun h => (not_lt_of_ge hka) ((row_le_ray ..).mp h), not_ray_le_row k a j⟩)
      obtain ⟨m, _, hmax⟩ := hfin.exists_maximal ⟨d, Set.mem_univ d⟩
      obtain ⟨b, hmb⟩ := ((rowChain a).finalSegment_noTop D hD).exists_gt m
      exact (hmb.not_ge (hmax (Set.mem_univ b) hmb.le)).elim

/-- Paper `ex:cannot-witness`: the ray germ and all row germs have no common witness. -/
theorem no_common_witness :
    ¬ ∃ C : SaturatedChain Point, H.Witnesses C rayLimit ∧ ∀ n, H.Witnesses C (rowLimit n) := by
  rintro ⟨C, hRay, hRow⟩
  obtain ⟨n, hn⟩ := exists_ray_of_witness hRay
  obtain ⟨j, hj⟩ := exists_row_of_witness (n+1) (hRow (n+1))
  exact (C.isChain.total hn hj).elim (not_ray_le_row n (n+1) j)
    (fun h => (Nat.not_lt_of_ge (Nat.le_succ n)) ((row_le_ray ..).mp h))

end Point

end AharoniKorman.Completion.WitnessObstruction
