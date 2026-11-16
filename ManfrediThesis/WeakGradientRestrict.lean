import ManfrediThesis.Preamble
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
open MeasureTheory

/-- Restriction to an open subset: `W^{1,q}` and `W^{1,q}_loc` membership on an
open set pass to every open subset, and `W^{1,q}` is contained in
`W^{1,q}_loc`. -/
theorem WeakGradientRestrict :
    ∀ (n : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ q →
      ∀ (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
        (f : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        IsOpen Ω → IsOpen Ω' → Ω' ⊆ Ω →
        (MemW1pOn n q Ω f g → MemW1pOn n q Ω' f g)
          ∧ (MemW1pLocOn n q Ω f g → MemW1pLocOn n q Ω' f g)
          ∧ (MemW1pOn n q Ω f g → MemW1pLocOn n q Ω f g)
          ∧ (MemW1pLocOn n q Ω f g → IsCompact (closure Ω') → closure Ω' ⊆ Ω →
              MemW1pOn n q Ω' f g) := by
  intro n q _ _ Ω Ω' f g hΩ hΩ' hsub
  -- The weak-gradient clause: restricting the domain of integration to Ω'
  -- changes neither integral, because φ and its derivative vanish off tsupport φ.
  have hwg : HasWeakGradientOn n Ω f g → HasWeakGradientOn n Ω' f g := by
    intro hw φ hφ hcs hts i
    have hts' : tsupport φ ⊆ Ω := hts.trans hsub
    have hmeas : MeasurableSet Ω := hΩ.measurableSet
    have hzero : ∀ x ∈ Ω \ Ω', fderiv ℝ φ x = 0 ∧ φ x = 0 := by
      intro x hx
      have hxo : x ∉ tsupport φ := fun hh => hx.2 (hts hh)
      have hev : φ =ᶠ[nhds x] (fun _ => (0:ℝ)) := by
        filter_upwards [(isOpen_compl_iff.2 (isClosed_tsupport φ)).mem_nhds hxo] with y hy
        exact image_eq_zero_of_notMem_tsupport hy
      refine ⟨?_, image_eq_zero_of_notMem_tsupport hxo⟩
      rw [hev.fderiv_eq]
      simp
    have h1 : (∫ x in Ω, f x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        = ∫ x in Ω', f x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) := by
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hsub ?_
      intro x hx
      simp [(hzero x hx).1]
    have h2 : (∫ x in Ω, g x i * φ x) = ∫ x in Ω', g x i * φ x := by
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hsub ?_
      intro x hx
      simp [(hzero x hx).2]
    rw [← h1, ← h2]
    exact hw φ hφ hcs hts' i
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨hw, hf, hg⟩
    exact ⟨hwg hw, hf.mono_measure (Measure.restrict_mono hsub le_rfl),
      hg.mono_measure (Measure.restrict_mono hsub le_rfl)⟩
  · rintro ⟨hw, hloc⟩
    exact ⟨hwg hw, fun K hK hKsub => hloc K hK (hKsub.trans hsub)⟩
  · rintro ⟨hw, hf, hg⟩
    refine ⟨hw, fun K _ hKsub => ⟨hf.mono_measure (Measure.restrict_mono hKsub le_rfl),
      hg.mono_measure (Measure.restrict_mono hKsub le_rfl)⟩⟩
  · rintro ⟨hw, hloc⟩ hc hcsub
    obtain ⟨hf, hg⟩ := hloc (closure Ω') hc hcsub
    exact ⟨hwg hw, hf.mono_measure (Measure.restrict_mono subset_closure le_rfl),
      hg.mono_measure (Measure.restrict_mono subset_closure le_rfl)⟩
