import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pOn
import Mathlib.Geometry.Manifold.PartitionOfUnity
set_option maxHeartbeats 800000
open MeasureTheory

/-- A small translate of a compactly supported `W^{1,2}` test pair is again
admissible for the same open set.

Let `Ω ⊆ ℝⁿ` be open, let `φ ∈ W^{1,2}(Ω)` with weak gradient `gφ`, compact
support and `supp φ ⊆ Ω`, and suppose `gφ` vanishes almost everywhere on
`Ω \ supp φ`.  Let `δ > 0` be small enough that the `3δ`-thickening of
`supp φ` still lies in `Ω`.  Then for every real `h` with `0 < |h| ≤ δ` the
translate `x ↦ φ(x - h e_k)` lies in `W^{1,2}(Ω)` with weak gradient
`x ↦ 1_{supp φ}(x - h e_k) gφ(x - h e_k)`, has compact support, and has its
support inside `Ω`.

This is exactly the test class of the differentiated equation: by pm-0018 that
equation is an `L²` statement, so its test functions are `W^{1,2}` with compact
support in `Ω`, and the three conjuncts above are the three clauses of that
membership.  The exponent is `2` throughout and is never promoted to `p`.

The weak-gradient clause is the only one with content.  The translation
operator preserves Lebesgue measure, so it preserves `L²` membership and turns
the integral identity for `φ` into the identity for the translate against the
translated test function; the obstruction is that the translated test function
need not be supported in `Ω`, since the translation moves `supp ψ` by `|h| ≤ δ`.
That is repaired by a smooth cut-off `χ` which is `1` on the `δ`-thickening of
`supp φ` and supported in the `2δ`-thickening -- taken off the shelf from the
existence of a smooth function separating two disjoint closed sets rather than
built by mollification -- so that `χψ` is admissible for `φ` and `χ = 1`
wherever the integrands of either side are nonzero.  The indicator
`1_{supp φ}` in the gradient is what makes the translated gradient vanish off
the translated support, and the hypothesis that `gφ` vanishes almost everywhere
off `supp φ` is what makes the indicator harmless. -/
theorem TranslatedTestPairAdmissible :
    ∀ (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))), IsOpen Ω →
      ∀ (k : Fin n) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
        (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        MemW1pOn n 2 Ω φ gφ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          x ∈ Ω → x ∉ tsupport φ → gφ x = 0) →
      ∀ δ : ℝ, 0 < δ → Metric.cthickening (3 * δ) (tsupport φ) ⊆ Ω →
      ∀ h : ℝ, 0 < |h| → |h| ≤ δ →
        MemW1pOn n 2 Ω (fun x => φ (x - h • EuclideanSpace.single k (1 : ℝ)))
            (fun x => (tsupport φ).indicator gφ
              (x - h • EuclideanSpace.single k (1 : ℝ))) ∧
          HasCompactSupport (fun x => φ (x - h • EuclideanSpace.single k (1 : ℝ))) ∧
          tsupport (fun x => φ (x - h • EuclideanSpace.single k (1 : ℝ))) ⊆ Ω := by
  intro n Ω hΩ k φ gφ hφW hφcs hφΩ hgφ0 δ hδ0 hδsub h hh0 hhδ
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hK0m : MeasurableSet (tsupport φ) := hφcs.isClosed.measurableSet
  have hnormsmul : ∀ s : ℝ,
      ‖s • EuclideanSpace.single k (1 : ℝ)‖ = |s| := by
    intro s
    rw [norm_smul, Real.norm_eq_abs]
    simp
  have hKδΩ : Metric.cthickening δ (tsupport φ) ⊆ Ω :=
    (Metric.cthickening_mono (by linarith) _).trans hδsub
  have hshiftK : ∀ (y : EuclideanSpace ℝ (Fin n)) (s : ℝ), y ∈ tsupport φ → |s| ≤ δ →
      y + s • EuclideanSpace.single k (1 : ℝ) ∈ Metric.cthickening δ (tsupport φ) := by
    intro y s hy hs
    refine Metric.mem_cthickening_of_dist_le _ y δ _ hy ?_
    rw [dist_eq_norm]
    simpa [hnormsmul] using hs
  -- the smooth cut-off, taken off the shelf rather than built by mollification
  obtain ⟨χ, hχsm, hχcs, hχts, hχ1⟩ :
      ∃ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧
        HasCompactSupport χ ∧
        tsupport χ ⊆ Metric.cthickening (2 * δ) (tsupport φ) ∧
        (∀ x ∈ Metric.cthickening δ (tsupport φ), χ x = 1) := by
    have hd : Disjoint ((Metric.thickening (2 * δ) (tsupport φ))ᶜ)
        (Metric.cthickening δ (tsupport φ)) := by
      rw [Set.disjoint_left]
      intro x hx hcc
      exact hx (Metric.cthickening_subset_thickening' (by linarith) (by linarith) _ hcc)
    obtain ⟨f, hf0, hf1, _⟩ := exists_contMDiffMap_zero_one_of_isClosed
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (n := (⊤ : ℕ∞))
      (Metric.isOpen_thickening).isClosed_compl Metric.isClosed_cthickening hd
    refine ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, ?_, ?_, fun x hx => hf1 hx⟩
    · refine HasCompactSupport.of_support_subset_isCompact
        (hφcs.cthickening (r := 2 * δ)) ?_
      intro x hx
      by_contra hcc
      exact hx (hf0 fun hmem => hcc (Metric.thickening_subset_cthickening _ _ hmem))
    · refine closure_minimal ?_ Metric.isClosed_cthickening
      intro x hx
      by_contra hcc
      exact hx (hf0 fun hmem => hcc (Metric.thickening_subset_cthickening _ _ hmem))
  have hχΩ : tsupport χ ⊆ Ω :=
    hχts.trans ((Metric.cthickening_mono (by linarith) _).trans hδsub)
  -- the translated supports
  have htssub : ∀ u : EuclideanSpace ℝ (Fin n) → ℝ,
      tsupport (fun x => u (x - h • EuclideanSpace.single k (1 : ℝ)))
        ⊆ (fun x => x - h • EuclideanSpace.single k (1 : ℝ)) ⁻¹' (tsupport u) := by
    intro u
    refine closure_minimal (fun y hy => subset_closure hy) ?_
    exact (isClosed_tsupport u).preimage (continuous_id.sub continuous_const)
  have hvanΩ : ∀ x : EuclideanSpace ℝ (Fin n), x ∉ Ω →
      x - h • EuclideanSpace.single k (1 : ℝ) ∉ tsupport φ := by
    intro x hx hcc
    have hb := hshiftK _ h hcc hhδ
    rw [sub_add_cancel] at hb
    exact hx (hKδΩ hb)
  have hcs6 : HasCompactSupport
      (fun x => φ (x - h • EuclideanSpace.single k (1 : ℝ))) := by
    refine IsCompact.of_isClosed_subset ?_ (isClosed_tsupport _) (htssub φ)
    exact (Homeomorph.subRight
      (h • EuclideanSpace.single k (1 : ℝ))).isCompact_preimage.2 hφcs
  have hsupp6 : tsupport (fun x => φ (x - h • EuclideanSpace.single k (1 : ℝ))) ⊆ Ω := by
    refine (htssub φ).trans fun x hx => ?_
    have hb := hshiftK _ h hx hhδ
    rw [sub_add_cancel] at hb
    exact hKδΩ hb
  -- the two `L²` memberships
  have hmpadd : MeasurePreserving
      (fun x : EuclideanSpace ℝ (Fin n) => x + h • EuclideanSpace.single k (1 : ℝ))
      volume volume := measurePreserving_add_right volume _
  have hmpsub : MeasurePreserving
      (fun x : EuclideanSpace ℝ (Fin n) => x - h • EuclideanSpace.single k (1 : ℝ))
      volume volume := by
    have h1 := measurePreserving_add_right volume
      (-(h • EuclideanSpace.single k (1 : ℝ)))
    have h2 : (fun x : EuclideanSpace ℝ (Fin n) =>
        x + -(h • EuclideanSpace.single k (1 : ℝ)))
        = fun x => x - h • EuclideanSpace.single k (1 : ℝ) := by
      funext x; rw [← sub_eq_add_neg]
    rwa [h2] at h1
  have hφind : φ = (tsupport φ).indicator φ := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
  have hφglob : MemLp φ (ENNReal.ofReal 2) volume := by
    rw [hφind]
    exact (memLp_indicator_iff_restrict hK0m).2
      (hφW.2.1.mono_measure (Measure.restrict_mono hφΩ le_rfl))
  have hĝglob : MemLp ((tsupport φ).indicator gφ) (ENNReal.ofReal 2) volume :=
    (memLp_indicator_iff_restrict hK0m).2
      (hφW.2.2.mono_measure (Measure.restrict_mono hφΩ le_rfl))
  have hφ6 : MemLp (fun x => φ (x - h • EuclideanSpace.single k (1 : ℝ)))
      (ENNReal.ofReal 2) (volume.restrict Ω) :=
    (hφglob.comp_measurePreserving hmpsub).mono_measure Measure.restrict_le_self
  have hĝ6 : MemLp (fun x => (tsupport φ).indicator gφ
        (x - h • EuclideanSpace.single k (1 : ℝ)))
      (ENNReal.ofReal 2) (volume.restrict Ω) :=
    (hĝglob.comp_measurePreserving hmpsub).mono_measure Measure.restrict_le_self
  -- the weak-gradient identity for the translated pair
  refine ⟨⟨?_, hφ6, hĝ6⟩, hcs6, hsupp6⟩
  intro ψ hψsm hψcs hψΩ i
  -- the translated test function and its derivative
  have hψhatd : ∀ y : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fun z => ψ (z + h • EuclideanSpace.single k (1 : ℝ))) y
        = fderiv ℝ ψ (y + h • EuclideanSpace.single k (1 : ℝ)) := by
    intro y
    have h1 : HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin n) => z + h • EuclideanSpace.single k (1 : ℝ))
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y :=
      (hasFDerivAt_id y).add_const _
    have h2 : HasFDerivAt ψ
        (fderiv ℝ ψ (y + h • EuclideanSpace.single k (1 : ℝ)))
        (y + h • EuclideanSpace.single k (1 : ℝ)) :=
      (hψsm.differentiable (by simp) _).hasFDerivAt
    have h30 := h2.comp y h1
    have h3 : HasFDerivAt (fun z => ψ (z + h • EuclideanSpace.single k (1 : ℝ)))
        ((fderiv ℝ ψ (y + h • EuclideanSpace.single k (1 : ℝ))).comp
          (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) y := h30
    rw [h3.fderiv]
    ext v
    simp
  have hψhatsm : ContDiff ℝ (⊤ : ℕ∞)
      (fun z => ψ (z + h • EuclideanSpace.single k (1 : ℝ))) :=
    hψsm.comp (contDiff_id.add contDiff_const)
  -- `χ · ψ̂` is a test function for `Ω`
  have hprodsm : ContDiff ℝ (⊤ : ℕ∞)
      (fun z => χ z * ψ (z + h • EuclideanSpace.single k (1 : ℝ))) :=
    hχsm.mul hψhatsm
  have hprodts : tsupport
      (fun z => χ z * ψ (z + h • EuclideanSpace.single k (1 : ℝ))) ⊆ tsupport χ := by
    refine closure_minimal (fun z hz => ?_) (isClosed_tsupport χ)
    by_contra hcc
    refine hz ?_
    show χ z * ψ (z + h • EuclideanSpace.single k (1 : ℝ)) = 0
    rw [image_eq_zero_of_notMem_tsupport hcc, zero_mul]
  have hprodcs : HasCompactSupport
      (fun z => χ z * ψ (z + h • EuclideanSpace.single k (1 : ℝ))) :=
    IsCompact.of_isClosed_subset hχcs (isClosed_tsupport _) hprodts
  -- on a neighbourhood of `tsupport φ` the cut-off is `1`
  have hagree : ∀ y : EuclideanSpace ℝ (Fin n), y ∈ tsupport φ →
      fderiv ℝ (fun z => χ z * ψ (z + h • EuclideanSpace.single k (1 : ℝ))) y
        = fderiv ℝ (fun z => ψ (z + h • EuclideanSpace.single k (1 : ℝ))) y := by
    intro y hy
    refine Filter.EventuallyEq.fderiv_eq ?_
    refine Filter.eventuallyEq_of_mem
      (Metric.isOpen_thickening.mem_nhds
        (Metric.self_subset_thickening hδ0 _ hy)) fun z hz => ?_
    rw [hχ1 z (Metric.thickening_subset_cthickening _ _ hz), one_mul]
  -- chaining the four displays
  have d1 : (∫ x in Ω, φ (x - h • EuclideanSpace.single k (1 : ℝ)) *
        fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))
      = ∫ x, φ (x - h • EuclideanSpace.single k (1 : ℝ)) *
        fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport (hvanΩ x hx), zero_mul]
  have d2 : (∫ x, φ (x - h • EuclideanSpace.single k (1 : ℝ)) *
        fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))
      = ∫ y, φ y * fderiv ℝ
        (fun z => ψ (z + h • EuclideanSpace.single k (1 : ℝ))) y
          (EuclideanSpace.single i (1 : ℝ)) := by
    have hmp := hmpadd.integral_comp
      (MeasurableEquiv.addRight
        (h • EuclideanSpace.single k (1 : ℝ))).measurableEmbedding
      (fun x => φ (x - h • EuclideanSpace.single k (1 : ℝ)) *
        fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))
    rw [← hmp]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [add_sub_cancel_right, hψhatd y]
  have d3 : (∫ y, φ y * fderiv ℝ
        (fun z => ψ (z + h • EuclideanSpace.single k (1 : ℝ))) y
          (EuclideanSpace.single i (1 : ℝ)))
      = ∫ y in Ω, φ y * fderiv ℝ
        (fun z => χ z * ψ (z + h • EuclideanSpace.single k (1 : ℝ))) y
          (EuclideanSpace.single i (1 : ℝ)) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)
      (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hcc => hx (hφΩ hcc)), zero_mul])]
    refine setIntegral_congr_fun hΩm fun y _ => ?_
    by_cases hy : y ∈ tsupport φ
    · rw [hagree y hy]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_mul]
  have d4 := hφW.1 (fun z => χ z * ψ (z + h • EuclideanSpace.single k (1 : ℝ)))
    hprodsm hprodcs (hprodts.trans hχΩ) i
  have d5 : (∫ y in Ω, gφ y i *
        (χ y * ψ (y + h • EuclideanSpace.single k (1 : ℝ))))
      = ∫ y in Ω, (tsupport φ).indicator gφ y i *
        ψ (y + h • EuclideanSpace.single k (1 : ℝ)) := by
    refine setIntegral_congr_ae hΩm ?_
    filter_upwards [hgφ0] with y hy hyΩ
    by_cases hys : y ∈ tsupport φ
    · rw [Set.indicator_of_mem hys,
        hχ1 y (Metric.self_subset_cthickening _ hys)]
      ring
    · rw [Set.indicator_of_notMem hys, hy hyΩ hys]
      simp
  have d6 : (∫ y in Ω, (tsupport φ).indicator gφ y i *
        ψ (y + h • EuclideanSpace.single k (1 : ℝ)))
      = ∫ x in Ω, (tsupport φ).indicator gφ
        (x - h • EuclideanSpace.single k (1 : ℝ)) i * ψ x := by
    have e1 : (∫ y in Ω, (tsupport φ).indicator gφ y i *
          ψ (y + h • EuclideanSpace.single k (1 : ℝ)))
        = ∫ y, (tsupport φ).indicator gφ y i *
          ψ (y + h • EuclideanSpace.single k (1 : ℝ)) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
        rw [Set.indicator_of_notMem fun hcc => hy (hφΩ hcc)]
        simp
    have e2 : (∫ x in Ω, (tsupport φ).indicator gφ
          (x - h • EuclideanSpace.single k (1 : ℝ)) i * ψ x)
        = ∫ x, (tsupport φ).indicator gφ
          (x - h • EuclideanSpace.single k (1 : ℝ)) i * ψ x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [Set.indicator_of_notMem (hvanΩ x hx)]
        simp
    have hmp := hmpadd.integral_comp
      (MeasurableEquiv.addRight
        (h • EuclideanSpace.single k (1 : ℝ))).measurableEmbedding
      (fun x => (tsupport φ).indicator gφ
        (x - h • EuclideanSpace.single k (1 : ℝ)) i * ψ x)
    rw [e1, e2, ← hmp]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [add_sub_cancel_right]
  rw [d1, d2, d3, d4, d5, d6]
