import AharoniKorman.Tube.QuasifoundedBlocks
import AharoniKorman.Tube.SeparatingAssembly

namespace AharoniKorman

open Set Completion Illfounded

universe u

variable {α : Type u} [PartialOrder α]

/-- Paper `cor:find-separating`: a convex non-quasifounded region contains a
maximal tube of an open quasifounded subregion, which separates the ambient order. -/
theorem exists_separatingTube_of_not_quasifounded [Countable α]
    (hfac : IsFAC α) (hsc : IsScattered α) (hvac : IsVacillating α)
    (hTube : ∀ (β : Type u) [PartialOrder β] [Countable β],
      IsFAC β → IsScattered β → AharoniKorman.IsQuasifounded β →
      ∃ T : Set β, IsMaximalTube T)
    {Q : Set α} (hQ : Q.OrdConnected) (hqf : ¬AharoniKorman.IsQuasifounded Q) :
    ∃ T ⊆ Q, IsSeparatingTube T := by
  obtain ⟨C, hC, _⟩ := exists_ordered_open_chains (hvac.ordConnected_subtype hQ) hqf
  obtain ⟨e, _, hes⟩ := hasSaturatedZeta_of_open_saturated (hC 0).1 (hC 0).2.1 (hC 0).2.2
    (hsc.subtype Q) (hvac.ordConnected_subtype hQ)
  let i : Q ↪o α := OrderEmbedding.subtype Q
  have hZ : HasSaturatedZeta Q := by
    have heq : range (e.trans i) = i '' range e := by
      ext p
      exact ⟨fun ⟨n, hn⟩ => ⟨e n, ⟨n, rfl⟩, hn⟩,
        fun ⟨x, ⟨n, hnx⟩, hxp⟩ => ⟨n, (congrArg i hnx).trans hxp⟩⟩
    refine ⟨e.trans i, ?_, heq.symm ▸ saturationPreserving_subtype_of_ordConnected hQ _ hes⟩
    rintro _ ⟨n, rfl⟩
    exact (e n).2
  obtain ⟨V, hVQ, hVne, hV, hVopen, hVq⟩ :=
    exists_open_quasifounded_in_convex hfac hsc hvac hQ hZ
  obtain ⟨T, hT⟩ := hTube V (hfac.subtype V) (hsc.subtype V) hVq
  have hTV := hT.image_subtype
  exact ⟨Subtype.val '' T, hTV.1.trans hVQ, hTV.isSeparatingTube hVne hV hVopen.1 hVopen.2⟩

/-- Paper `prop:quasifdd-reduction`: the gaps of a maximal separating family
are quasifounded and their maximal tubes complete the family. -/
theorem maximalTube_reduction_to_quasifounded [Countable α]
    (hfac : IsFAC α) (hsc : IsScattered α) (hvac : IsVacillating α)
    (hTube : ∀ (β : Type u) [PartialOrder β] [Countable β],
      IsFAC β → IsScattered β → AharoniKorman.IsQuasifounded β →
      ∃ T : Set β, IsMaximalTube T) : ∃ T : Set α, IsMaximalTube T := by
  classical
  apply exists_isMaximalTube_of_convex_regions
  intro Q hQ _
  by_cases hq : AharoniKorman.IsQuasifounded Q
  · obtain ⟨T, hT⟩ := hTube Q (hfac.subtype Q) (hsc.subtype Q) hq
    exact Or.inl ⟨Subtype.val '' T, hT.image_subtype⟩
  · exact Or.inr (exists_separatingTube_of_not_quasifounded hfac hsc hvac hTube hQ hq)

end AharoniKorman
