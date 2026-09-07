import AharoniKorman.Structural.Decomposition
import AharoniKorman.Preliminaries.Vacillating
import AharoniKorman.Tube.Defs

namespace AharoniKorman

open Set

universe u

variable {α : Type u} [PartialOrder α]

/-- Paper Corollary `cor:scattered-reduction` (the second Stage 2 target). -/
theorem maximalTube_reduction_to_scattered [Countable α]
    (hfac : IsFAC α) (hvac : IsVacillating α)
    (scattered_case : ∀ (β : Type u) [PartialOrder β] [Countable β],
      IsFAC β → IsVacillating β → IsScattered β → ∃ T : Set β, IsMaximalTube T) :
    ∃ T : Set α, IsMaximalTube T := by
  classical
  rcases structural_decomposition hfac with hscattered | hd
  · exact scattered_case α hfac hvac hscattered
  · obtain ⟨d⟩ := hd
    have hPieceTube : ∀ r : EReal, ∃ T : Set (d.piece r), IsMaximalTube T := by
      intro r
      exact scattered_case (d.piece r) (hfac.subtype (d.piece r))
        (hvac.ordConnected_subtype (d.piece_ordConnected r)) (d.piece_scattered r)
    choose Tr hTr using hPieceTube
    let liftT : EReal → Set α := fun r => Subtype.val '' Tr r
    let T : Set α := ⋃ r, liftT r
    have hTube : IsTube T := by
      intro x hxT
      simp only [T, liftT, Set.mem_iUnion, Set.mem_image] at hxT
      obtain ⟨r, xr, hxr, rfl⟩ := hxT
      have hlocal := (hTr r).1 xr hxr
      have hfiniteImage : (Subtype.val '' (Tr r ∩ incomparableSet xr) : Set α).Finite :=
        hlocal.image Subtype.val
      apply hfiniteImage.subset
      rintro y ⟨hyT, hyinc⟩
      simp only [T, liftT, Set.mem_iUnion, Set.mem_image] at hyT
      obtain ⟨s, ys, hys, rfl⟩ := hyT
      have hrs : r = s := by
        by_contra hrs
        rcases lt_or_gt_of_ne hrs with hrs | hsr
        · have hlt := d.ordered hrs xr.2 ys.2
          exact hyinc.not_le hlt.le
        · have hlt := d.ordered hsr ys.2 xr.2
          exact hyinc.not_ge hlt.le
      subst s
      refine ⟨ys, ⟨hys, ?_⟩, rfl⟩
      exact hyinc
    refine ⟨T, (isMaximalTube_iff T).mpr ⟨hTube, ?_⟩⟩
    intro x hxT
    by_cases hxPieces : x ∈ ⋃ r, d.piece r
    · simp only [Set.mem_iUnion] at hxPieces
      obtain ⟨r, hxr⟩ := hxPieces
      let xr : d.piece r := ⟨x, hxr⟩
      have hxrNot : xr ∉ Tr r := by
        intro hxmem
        apply hxT
        exact Set.mem_iUnion_of_mem r ⟨xr, hxmem, rfl⟩
      have hlocal := (isMaximalTube_iff (Tr r)).mp (hTr r) |>.2 xr hxrNot
      have himage : (Subtype.val '' (Tr r ∩ incomparableSet xr) : Set α).Infinite :=
        hlocal.image Subtype.val_injective.injOn
      apply himage.mono
      rintro y ⟨yr, ⟨hyr, hyinc⟩, rfl⟩
      exact ⟨Set.mem_iUnion_of_mem r ⟨yr, hyr, rfl⟩, hyinc⟩
    · obtain ⟨I, hIconvex, hIinfinite, hIinc⟩ := d.outside_incomparable x hxPieces
      letI : Infinite I := Set.infinite_coe_iff.mpr hIinfinite
      obtain ⟨r, s, hrs⟩ := exists_pair_ne I
      have hrs' : r.1 < s.1 ∨ s.1 < r.1 := lt_or_gt_of_ne (fun h => hrs (Subtype.ext h))
      rcases hrs' with hrs' | hrs'
      · let r' := r
        let s' := s
        have hr's' : r'.1 < s'.1 := hrs'
        have hr'I : r'.1 ∈ I := r'.2
        have hs'I : s'.1 ∈ I := s'.2
        clear_value r' s'
        obtain ⟨m, hrm, hms⟩ := EReal.exists_rat_btwn_of_lt hr's'
        obtain ⟨a, hra, ham⟩ := EReal.exists_rat_btwn_of_lt hrm
        obtain ⟨b, hmb, hbs⟩ := EReal.exists_rat_btwn_of_lt hms
        let Q : Set ℚ := Set.Ioo a b
        have hab : a < b := by
          exact_mod_cast EReal.coe_lt_coe_iff.mp (ham.trans hmb)
        have hQinf : Q.Infinite := Set.Ioo_infinite hab
        have hTrne (q : Q) : (Tr (((q.1 : ℝ) : EReal))).Nonempty := by
          letI : Nonempty (d.piece (((q.1 : ℝ) : EReal))) :=
            (d.rational_nonempty q.1).to_subtype
          exact (hTr (((q.1 : ℝ) : EReal))).nonempty
        choose t ht using hTrne
        let g : Q → α := fun q => (t q).1
        have hgInjective : Function.Injective g := by
          intro p q hpq
          by_contra hpq'
          rcases lt_or_gt_of_ne hpq' with hpq' | hqp'
          · have hpqE : (((p.1 : ℝ) : EReal)) < (((q.1 : ℝ) : EReal)) := by
              exact_mod_cast hpq'
            have hlt := d.ordered hpqE (t p).2 (t q).2
            exact hlt.ne (by simpa [g] using hpq)
          · have hqpE : (((q.1 : ℝ) : EReal)) < (((p.1 : ℝ) : EReal)) := by
              exact_mod_cast hqp'
            have hlt := d.ordered hqpE (t q).2 (t p).2
            exact hlt.ne (by simpa [g] using hpq.symm)
        have hrange : (Set.range g).Infinite := by
          letI : Infinite Q := Set.infinite_coe_iff.mpr hQinf
          exact Set.infinite_range_of_injective hgInjective
        apply hrange.mono
        rintro y ⟨q, rfl⟩
        have hqE_mem : (((q.1 : ℝ) : EReal)) ∈ I := by
          apply hIconvex.out hr'I hs'I
          constructor
          · have haq : ((a : ℝ) : EReal) < ((q.1 : ℝ) : EReal) := by
              exact_mod_cast q.2.1
            exact (hra.trans haq).le
          · have hqb : ((q.1 : ℝ) : EReal) < ((b : ℝ) : EReal) := by
              exact_mod_cast q.2.2
            exact (hqb.trans hbs).le
        refine ⟨Set.mem_iUnion_of_mem (((q.1 : ℝ) : EReal)) ⟨t q, ht q, rfl⟩, ?_⟩
        exact hIinc _ hqE_mem _ (t q).2
      · let r' := s
        let s' := r
        have hr's' : r'.1 < s'.1 := hrs'
        have hr'I : r'.1 ∈ I := r'.2
        have hs'I : s'.1 ∈ I := s'.2
        clear_value r' s'
        obtain ⟨m, hrm, hms⟩ := EReal.exists_rat_btwn_of_lt hr's'
        obtain ⟨a, hra, ham⟩ := EReal.exists_rat_btwn_of_lt hrm
        obtain ⟨b, hmb, hbs⟩ := EReal.exists_rat_btwn_of_lt hms
        let Q : Set ℚ := Set.Ioo a b
        have hab : a < b := by exact_mod_cast EReal.coe_lt_coe_iff.mp (ham.trans hmb)
        have hQinf : Q.Infinite := Set.Ioo_infinite hab
        have hTrne (q : Q) : (Tr (((q.1 : ℝ) : EReal))).Nonempty := by
          letI : Nonempty (d.piece (((q.1 : ℝ) : EReal))) :=
            (d.rational_nonempty q.1).to_subtype
          exact (hTr (((q.1 : ℝ) : EReal))).nonempty
        choose t ht using hTrne
        let g : Q → α := fun q => (t q).1
        have hgInjective : Function.Injective g := by
          intro p q hpq
          by_contra hpq'
          rcases lt_or_gt_of_ne hpq' with hpq' | hqp'
          · have hpqE : (((p.1 : ℝ) : EReal)) < (((q.1 : ℝ) : EReal)) := by exact_mod_cast hpq'
            exact (d.ordered hpqE (t p).2 (t q).2).ne (by simpa [g] using hpq)
          · have hqpE : (((q.1 : ℝ) : EReal)) < (((p.1 : ℝ) : EReal)) := by exact_mod_cast hqp'
            exact (d.ordered hqpE (t q).2 (t p).2).ne (by simpa [g] using hpq.symm)
        have hrange : (Set.range g).Infinite := by
          letI : Infinite Q := Set.infinite_coe_iff.mpr hQinf
          exact Set.infinite_range_of_injective hgInjective
        apply hrange.mono
        rintro y ⟨q, rfl⟩
        have hqE_mem : (((q.1 : ℝ) : EReal)) ∈ I := by
          apply hIconvex.out hr'I hs'I
          constructor
          · have haq : ((a : ℝ) : EReal) < ((q.1 : ℝ) : EReal) := by
              exact_mod_cast q.2.1
            exact (hra.trans haq).le
          · have hqb : ((q.1 : ℝ) : EReal) < ((b : ℝ) : EReal) := by
              exact_mod_cast q.2.2
            exact (hqb.trans hbs).le
        refine ⟨Set.mem_iUnion_of_mem (((q.1 : ℝ) : EReal)) ⟨t q, ht q, rfl⟩, ?_⟩
        exact hIinc _ hqE_mem _ (t q).2

end AharoniKorman
