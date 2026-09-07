import AharoniKorman.Preliminaries.Chains
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Encodable
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Order.Zorn

namespace AharoniKorman

open Set

variable {α : Type*} [PartialOrder α]

/-- A poset is scattered when it contains no order-embedded copy of the rationals. -/
def IsScattered (α : Type*) [PartialOrder α] : Prop := ¬ Nonempty (ℚ ↪o α)

/-- Scatteredness is inherited by induced subposets. -/
theorem IsScattered.subtype (h : IsScattered α) (S : Set α) : IsScattered S := by
  rintro ⟨e⟩
  exact h ⟨e.trans (OrderEmbedding.subtype S)⟩

/-- Scatteredness is invariant under reversing the order. -/
theorem IsScattered.orderDual (h : IsScattered α) : IsScattered αᵒᵈ := by
  rintro ⟨e⟩
  let negEmbedding : ℚ ↪o ℚᵒᵈ :=
    OrderEmbedding.ofStrictMono (fun q : ℚ => OrderDual.toDual (-q)) fun _ _ hab =>
      neg_lt_neg_iff.mpr hab
  exact h ⟨negEmbedding.trans e.dual⟩

/-- Paper fact `fact:covers`. -/
theorem IsScattered.exists_covBy_between (h : IsScattered α) {x y : α} (hxy : x < y) :
    ∃ u v, x ≤ u ∧ u < v ∧ v ≤ y ∧ u ⋖ v := by
  classical
  by_contra hno
  have hpair : IsChain (· ≤ ·) ({x, y} : Set α) := IsChain.pair hxy.le
  obtain ⟨M, hM, hxyM⟩ := hpair.exists_maxChain
  have hxM : x ∈ M := hxyM (by simp)
  have hyM : y ∈ M := hxyM (by simp)
  have hbetween : ∀ {u v : α}, u ∈ M → v ∈ M → x ≤ u → u < v → v ≤ y →
      ∃ z ∈ M, u < z ∧ z < v := by
    intro u v huM hvM hxu huv hvy
    by_cases hex : ∃ z ∈ M, u < z ∧ z < v
    · exact hex
    have hnotcov : ¬u ⋖ v := by
      intro huvCov
      exact hno ⟨u, v, hxu, huv, hvy, huvCov⟩
    obtain ⟨z, huz, hzv⟩ := exists_lt_lt_of_not_covBy huv hnotcov
    have hzM : z ∈ M := by
      have hzcomp : ∀ a ∈ M, z ≠ a → z ≤ a ∨ a ≤ z := by
        intro a haM hza
        rcases hM.1.total haM huM with hau | hua
        · exact Or.inr (hau.trans huz.le)
        rcases hM.1.total haM hvM with hav | hva
        · by_cases hau_eq : a = u
          · subst a
            exact Or.inr huz.le
          by_cases hav_eq : a = v
          · subst a
            exact Or.inl hzv.le
          have hua_strict : u < a := lt_of_le_of_ne hua (Ne.symm hau_eq)
          have hav_strict : a < v := lt_of_le_of_ne hav hav_eq
          exact False.elim (hex ⟨a, haM, hua_strict, hav_strict⟩)
        · exact Or.inl (hzv.le.trans hva)
      have hins : IsChain (· ≤ ·) (insert z M) := hM.1.insert hzcomp
      have heq : insert z M = M := (hM.2 hins (Set.subset_insert z M)).symm
      exact heq ▸ Set.mem_insert z M
    exact ⟨z, hzM, huz, hzv⟩
  let I : Set α := M ∩ Ioo x y
  have hIchain : IsChain (· ≤ ·) I := hM.1.mono inter_subset_left
  letI : LinearOrder I := hIchain.linearOrder
  letI : DenselyOrdered I :=
    ⟨by
      rintro ⟨a, haM, hxa, hay⟩ ⟨b, hbM, hxb, hby⟩ hab
      obtain ⟨z, hzM, haz, hzb⟩ :=
        hbetween haM hbM hxa.le hab hby.le
      exact ⟨⟨z, hzM, hxa.trans haz, hzb.trans hby⟩, haz, hzb⟩⟩
  obtain ⟨a, haM, hxa, hay⟩ := hbetween hxM hyM le_rfl hxy le_rfl
  obtain ⟨b, hbM, hab, hby⟩ := hbetween haM hyM hxa.le hay le_rfl
  let aI : I := ⟨a, haM, hxa, hay⟩
  let bI : I := ⟨b, hbM, hxa.trans hab, hby⟩
  letI : Nontrivial I := ⟨⟨aI, bI, ne_of_lt hab⟩⟩
  obtain ⟨e⟩ := Order.embedding_from_countable_to_dense (α := ℚ) (β := I)
  exact h ⟨e.trans (OrderEmbedding.subtype I)⟩

/-- Induced-subposet form of `IsScattered.exists_covBy_between`. -/
theorem IsScattered.exists_covBy_between_subtype (h : IsScattered α) (S : Set α)
    {x y : S} (hxy : x < y) :
    ∃ u v : S, x ≤ u ∧ u < v ∧ v ≤ y ∧ u ⋖ v :=
  (h.subtype S).exists_covBy_between hxy

/-- Order-dual form of `IsScattered.exists_covBy_between`. -/
theorem IsScattered.exists_dual_covBy_between (h : IsScattered α) {x y : α} (hyx : y < x) :
    ∃ u v, u ≤ x ∧ v < u ∧ y ≤ v ∧ v ⋖ u := by
  obtain ⟨u, v, hxu, huv, hvy, hcov⟩ :=
    h.orderDual.exists_covBy_between (x := (x : αᵒᵈ)) (y := (y : αᵒᵈ)) hyx
  exact ⟨u, v, hxu, huv, hvy, hcov.ofDual⟩

/-- A scattered subset of a nontrivial dense linear order misses a nonempty open interval. -/
theorem IsScattered.exists_disjoint_Ioo {β : Type*} [LinearOrder β] [DenselyOrdered β]
    [Nontrivial β] {S : Set β} (h : IsScattered S) :
    ∃ a b : β, a < b ∧ Disjoint (Ioo a b) S := by
  classical
  by_contra hgap
  have hdense : ∀ {a b : β}, a < b → ∃ z ∈ S, a < z ∧ z < b := by
    intro a b hab
    by_contra hn
    apply hgap
    refine ⟨a, b, hab, Set.disjoint_left.mpr ?_⟩
    intro z hzI hzS
    exact hn ⟨z, hzS, hzI.1, hzI.2⟩
  letI : DenselyOrdered S :=
    ⟨by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      obtain ⟨z, hzS, haz, hzb⟩ := hdense hab
      exact ⟨⟨z, hzS⟩, haz, hzb⟩⟩
  obtain ⟨a, b, hab⟩ := exists_pair_lt β
  obtain ⟨z, hzS, haz, hzb⟩ := hdense hab
  obtain ⟨w, hwS, hzw, hwb⟩ := hdense hzb
  letI : Nontrivial S := ⟨⟨⟨z, hzS⟩, ⟨w, hwS⟩, ne_of_lt hzw⟩⟩
  obtain ⟨e⟩ := Order.embedding_from_countable_to_dense (α := ℚ) (β := S)
  exact h ⟨e⟩

/-- Indivisibility of the rational order under a finite colouring: one colour contains an
order-embedded copy of `ℚ`. -/
theorem finite_coloring_rat_exists_monochromatic_embedding {κ : Type*} [Finite κ]
    (colour : ℚ → κ) : ∃ i : κ, Nonempty (ℚ ↪o {q : ℚ // colour q = i}) := by
  classical
  letI := Fintype.ofFinite κ
  by_contra hmono
  push_neg at hmono
  have hscattered : ∀ i : κ, IsScattered {q : ℚ | colour q = i} := by
    intro i hnonempty
    exact (hmono i).false hnonempty.some
  have hAvoid : ∀ t : Finset κ,
      ∃ a b : ℚ, a < b ∧ ∀ q : ℚ, a < q → q < b → colour q ∉ t := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        exact ⟨0, 1, zero_lt_one, by simp⟩
    | insert i t hi ih =>
        obtain ⟨a, b, hab, ht⟩ := ih
        let I : Set ℚ := Ioo a b
        obtain ⟨m, ham, hmb⟩ := exists_between hab
        obtain ⟨n, hmn, hnb⟩ := exists_between hmb
        let mI : I := ⟨m, ham, hmb⟩
        let nI : I := ⟨n, ham.trans hmn, hnb⟩
        letI : Nontrivial I := ⟨⟨mI, nI, ne_of_lt hmn⟩⟩
        have hFiberI : IsScattered {q : I | colour q = i} := by
          rintro ⟨e⟩
          apply hscattered i
          let inc : {q : I | colour q = i} ↪o {q : ℚ | colour q = i} :=
            OrderEmbedding.ofMapLEIff
              (fun q => ⟨q.1.1, q.2⟩) (by intro p q; rfl)
          exact ⟨e.trans inc⟩
        obtain ⟨u, v, huv, huvDisj⟩ := hFiberI.exists_disjoint_Ioo
        refine ⟨u.1, v.1, huv, ?_⟩
        intro q huq hqv hqColour
        rcases Finset.mem_insert.mp hqColour with hqi | hqt
        · let qI : I := ⟨q, u.2.1.trans huq, hqv.trans v.2.2⟩
          exact (Set.disjoint_left.mp huvDisj) (show qI ∈ Ioo u v from ⟨huq, hqv⟩)
            (show colour qI = i from hqi)
        · exact ht q (u.2.1.trans huq) (hqv.trans v.2.2) hqt
  obtain ⟨a, b, hab, hAvoidAll⟩ := hAvoid Finset.univ
  obtain ⟨q, haq, hqb⟩ := exists_between hab
  exact hAvoidAll q haq hqb (Finset.mem_univ _)

end AharoniKorman
