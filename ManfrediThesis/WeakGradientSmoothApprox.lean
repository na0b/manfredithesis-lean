import ManfrediThesis.Preamble
import ManfrediThesis.ConvolutionLqContraction
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.MollifiedWeakGradientIdentity
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MollifierLqConvergence
open MeasureTheory

/-- Smooth approximation of a compactly supported `W^{1,q}` function: the
mollifications are smooth, supported in one compact subset of `Ω`, and converge
to `φ` together with their gradients in `L^q` of that compact set. -/
theorem WeakGradientSmoothApprox :
    ∀ (n : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ q →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (φ : EuclideanSpace ℝ (Fin n) → ℝ)
        (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        IsOpen Ω → MemW1pOn n q Ω φ gφ →
        HasCompactSupport φ → tsupport φ ⊆ Ω →
        ∃ (K : Set (EuclideanSpace ℝ (Fin n)))
          (Φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ),
          IsCompact K ∧ K ⊆ Ω ∧ tsupport φ ⊆ K ∧
          (∀ m, ContDiff ℝ (⊤ : ℕ∞) (Φ m)) ∧
          (∀ m, HasCompactSupport (Φ m)) ∧
          (∀ m, tsupport (Φ m) ⊆ K) ∧
          Filter.Tendsto (fun m => ∫ x in K, |Φ m x - φ x| ^ q)
            Filter.atTop (nhds 0) ∧
          (∀ i : Fin n, Filter.Tendsto
            (fun m => ∫ x in K,
              |fderiv ℝ (Φ m) x (EuclideanSpace.single i (1 : ℝ)) - gφ x i| ^ q)
            Filter.atTop (nhds 0)) := by
  intro n q _hn hq Ω φ gφ hΩ hW hφcs hφsupp
  obtain ⟨hwg, hφLp, hgLp⟩ := hW
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hp0 : (ENNReal.ofReal q) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero]; linarith
  have hptop : (ENNReal.ofReal q) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq0.le
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 hq
  -- Step 1: geometry
  obtain ⟨d, hd0, hdsub⟩ := hφcs.exists_cthickening_subset_open hΩ hφsupp
  obtain ⟨δ₀, hδ₀0, h3δ₀⟩ :
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ Metric.cthickening (3 * δ₀) (tsupport φ) ⊆ Ω := by
    refine ⟨d / 3, by positivity, ?_⟩
    have : 3 * (d / 3) = d := by ring
    rw [this]; exact hdsub
  refine ⟨Metric.cthickening (2 * δ₀) (tsupport φ), ?_⟩
  have hKcpt : IsCompact (Metric.cthickening (2 * δ₀) (tsupport φ)) := hφcs.cthickening
  have hKΩ : Metric.cthickening (2 * δ₀) (tsupport φ) ⊆ Ω :=
    (Metric.cthickening_mono (by linarith) _).trans h3δ₀
  have hK0K : tsupport φ ⊆ Metric.cthickening (2 * δ₀) (tsupport φ) :=
    Metric.self_subset_cthickening _
  -- Step 2: the data as functions on all of ℝⁿ
  have hproj : ∀ i : Fin n, Continuous (fun y : EuclideanSpace ℝ (Fin n) => y i) :=
    fun i => (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
  have hcoord : ∀ (u : EuclideanSpace ℝ (Fin n)) (i : Fin n), ‖u i‖ ≤ ‖u‖ := by
    intro u i
    rw [EuclideanSpace.norm_eq, Real.norm_eq_abs,
      show |u i| = Real.sqrt (|u i| ^ 2) by rw [Real.sqrt_sq (abs_nonneg _)]]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (f := fun j => |u j| ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i))
  have hφmem : MemLp φ (ENNReal.ofReal q) volume := by
    have h1 : MemLp φ (ENNReal.ofReal q) (volume.restrict (tsupport φ)) :=
      hφLp.mono_measure (Measure.restrict_mono hφsupp le_rfl)
    have h2 : MemLp ((tsupport φ).indicator φ) (ENNReal.ofReal q) volume :=
      (memLp_indicator_iff_restrict (isClosed_tsupport φ).measurableSet).2 h1
    have h3 : (tsupport φ).indicator φ = φ := by
      funext x
      by_cases hx : x ∈ tsupport φ
      · simp [hx]
      · simp [hx, image_eq_zero_of_notMem_tsupport hx]
    rwa [h3] at h2
  have hgmem : MemLp (Ω.indicator gφ) (ENNReal.ofReal q) volume :=
    (memLp_indicator_iff_restrict hΩ.measurableSet).2 hgLp
  have hgimem : ∀ i : Fin n,
      MemLp (fun x => (Ω.indicator gφ) x i) (ENNReal.ofReal q) volume :=
    fun i => hgmem.mono ((hproj i).comp_aestronglyMeasurable hgmem.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => hcoord _ i)
  have hφloc : LocallyIntegrable φ volume := hφmem.locallyIntegrable hp1
  have hgiloc : ∀ i : Fin n,
      LocallyIntegrable (fun x => (Ω.indicator gφ) x i) volume :=
    fun i => (hgimem i).locallyIntegrable hp1
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have dict : ∀ h : EuclideanSpace ℝ (Fin n) → ℝ,
      MemLp h (ENNReal.ofReal q) volume →
      ∫ x, |h x| ^ q = ((eLpNorm h (ENNReal.ofReal q) volume).toReal) ^ q := by
    intro h hh
    have hnn : 0 ≤ ∫ x, |h x| ^ q :=
      integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
    rw [hh.eLpNorm_eq_integral_rpow_norm hp0 hptop, hpt]
    simp only [Real.norm_eq_abs]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _), ← Real.rpow_mul hnn,
      inv_mul_cancel₀ hq0.ne', Real.rpow_one]
  have squeeze : ∀ (S : Set (EuclideanSpace ℝ (Fin n)))
      (H : ℕ → EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ m, MemLp (H m) (ENNReal.ofReal q) volume) →
      Filter.Tendsto (fun m => eLpNorm (H m) (ENNReal.ofReal q) volume)
        Filter.atTop (nhds 0) →
      Filter.Tendsto (fun m => ∫ x in S, |H m x| ^ q) Filter.atTop (nhds 0) := by
    intro S H hHmem hH
    refine squeeze_zero
      (g := fun m => ((eLpNorm (H m) (ENNReal.ofReal q) volume).toReal) ^ q)
      (fun m => integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _)
      (fun m => ?_) ?_
    · have hint : Integrable (fun x => |H m x| ^ q) volume := by
        have := (hHmem m).integrable_norm_rpow hp0 hptop
        simpa [hpt, Real.norm_eq_abs] using this
      calc ∫ x in S, |H m x| ^ q
          ≤ ∫ x, |H m x| ^ q :=
            setIntegral_le_integral hint
              (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _)
        _ = ((eLpNorm (H m) (ENNReal.ofReal q) volume).toReal) ^ q := dict _ (hHmem m)
    · have h1 : Filter.Tendsto
          (fun m => (eLpNorm (H m) (ENNReal.ofReal q) volume).toReal)
          Filter.atTop (nhds 0) := by
        have := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp hH
        simpa [Function.comp_def] using this
      have h2 : ContinuousAt (fun t : ℝ => t ^ q) 0 :=
        Real.continuousAt_rpow_const 0 q (Or.inr hq0.le)
      have := h2.tendsto.comp h1
      simpa [Function.comp_def, Real.zero_rpow hq0.ne'] using this
  -- Step 6: convolution against a probability density contracts the `L^q` seminorm
  -- Step 5: on `K` the derivative of the mollification is the mollified weak gradient
  have step5 : ∀ (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (d : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ρ → HasCompactSupport ρ →
      tsupport ρ = Metric.closedBall 0 d →
      ∀ x : EuclideanSpace ℝ (Fin n), Metric.closedBall x d ⊆ Ω → ∀ i : Fin n,
      fderiv ℝ (convolution φ ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
          (EuclideanSpace.single i (1 : ℝ))
        = convolution (fun y => (Ω.indicator gφ) y i) ρ
            (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    intro ρ d hρsm hρcs hρts x hball i
    have h := MollifiedWeakGradientIdentity n Ω hΩ φ gφ hwg hφloc ρ d hρsm hρcs
      hρts x hball i
    rw [h]
    refine congrArg
      (fun f => convolution f ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume x) ?_
    funext y
    by_cases hy : y ∈ Ω
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      simp
  -- Step 3: the mollifier family
  have hδpos : ∀ m : ℕ, (0 : ℝ) < δ₀ / (m + 1) := fun m => by positivity
  have hδle : ∀ m : ℕ, δ₀ / (m + 1) ≤ δ₀ := by
    intro m
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) m, hδ₀0]
  set B : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun m =>
    ⟨δ₀ / (m + 1) / 2, δ₀ / (m + 1), by positivity, by linarith [hδpos m]⟩ with hBdef
  set ρ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m => (B m).normed volume with hρdef
  have hρsmooth : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (ρ m) := fun m => (B m).contDiff_normed
  have hρnonneg : ∀ m x, 0 ≤ ρ m x := fun m x => (B m).nonneg_normed x
  have hρint : ∀ m, ∫ z, ρ m z = 1 := fun m => (B m).integral_normed
  have hρts : ∀ m, tsupport (ρ m) = Metric.closedBall 0 (δ₀ / (m + 1)) := by
    intro m
    simpa [hBdef] using (B m).tsupport_normed_eq (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
  have hρcs : ∀ m, HasCompactSupport (ρ m) := fun m => (B m).hasCompactSupport_normed
  have hρc : ∀ m, Continuous (ρ m) := fun m => (hρsmooth m).continuous
  have hδlim : Filter.Tendsto (fun m : ℕ => δ₀ / ((m : ℝ) + 1)) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ₀
  have contractρ : ∀ u : EuclideanSpace ℝ (Fin n) → ℝ,
      MemLp u (ENNReal.ofReal q) volume → ∀ m,
      eLpNorm (convolution u (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (ENNReal.ofReal q) volume
        ≤ eLpNorm u (ENNReal.ofReal q) volume :=
    fun u hu m => ConvolutionLqContraction n q hq (ρ m) (hρc m) (hρnonneg m)
      (hρcs m) (hρint m) u hu
  have convmem : ∀ u : EuclideanSpace ℝ (Fin n) → ℝ,
      MemLp u (ENNReal.ofReal q) volume → LocallyIntegrable u volume → ∀ m,
      MemLp (convolution u (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        (ENNReal.ofReal q) volume := by
    intro u hu hul m
    refine ⟨((hρcs m).contDiff_convolution_right _ hul
      (hρsmooth m)).continuous.aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (contractρ u hu m) hu.2
  have convergeρ : ∀ w : EuclideanSpace ℝ (Fin n) → ℝ,
      MemLp w (ENNReal.ofReal q) volume →
      Filter.Tendsto (fun m => eLpNorm
        (fun x => convolution w (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - w x)
        (ENNReal.ofReal q) volume) Filter.atTop (nhds 0) :=
    MollifierLqConvergence n q _hn hq ρ (fun m => δ₀ / ((m : ℝ) + 1)) hδlim hρsmooth hρnonneg hρcs
      (fun m => (hρts m).subset) hρint contractρ
  have hballsub : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin n)),
      x ∈ Metric.cthickening (2 * δ₀) (tsupport φ) →
      Metric.closedBall x (δ₀ / ((m : ℝ) + 1)) ⊆ Ω := by
    intro m x hx y hy
    have h1 : y ∈ Metric.cthickening (δ₀ / ((m : ℝ) + 1))
        (Metric.cthickening (2 * δ₀) (tsupport φ)) :=
      Metric.mem_cthickening_of_dist_le y x _ _ hx (by simpa using hy)
    have h2 : y ∈ Metric.cthickening (δ₀ / ((m : ℝ) + 1) + 2 * δ₀) (tsupport φ) :=
      Metric.cthickening_cthickening_subset (hδpos m).le (by linarith) _ h1
    exact h3δ₀ (Metric.cthickening_mono (by linarith [hδle m]) _ h2)
  -- Step 4: the sequence and its support
  have hΦsupp : ∀ m, tsupport (convolution φ (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      ⊆ Metric.cthickening (2 * δ₀) (tsupport φ) := by
    intro m
    refine closure_minimal (fun z hz => ?_) Metric.isClosed_cthickening
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 (support_convolution_subset _ hz)
    have hbn : ‖b‖ ≤ δ₀ / (m + 1) := by
      have : b ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (δ₀ / (m + 1)) := by
        rw [← hρts m]; exact subset_tsupport _ hb
      simpa using this
    refine Metric.mem_cthickening_of_dist_le _ a (2 * δ₀) _ (subset_tsupport _ ha) ?_
    have hd : dist (a + b) a = ‖b‖ := by
      simp [dist_eq_norm]
    rw [hd]
    linarith [hδle m, hδ₀0]
  refine ⟨fun m => convolution φ (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume,
    hKcpt, hKΩ, hK0K, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun m => (hρcs m).contDiff_convolution_right _ hφloc (hρsmooth m)
  · exact fun m => IsCompact.of_isClosed_subset hKcpt (isClosed_tsupport _) (hΦsupp m)
  · exact hΦsupp
  · exact squeeze _
      (fun m x => convolution φ (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - φ x)
      (fun m => (convmem φ hφmem hφloc m).sub hφmem) (convergeρ φ hφmem)
  · intro i
    have hrw : ∀ m : ℕ, (∫ x in Metric.cthickening (2 * δ₀) (tsupport φ),
          |fderiv ℝ (convolution φ (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
              (EuclideanSpace.single i (1 : ℝ)) - gφ x i| ^ q)
        = ∫ x in Metric.cthickening (2 * δ₀) (tsupport φ),
          |convolution (fun y => (Ω.indicator gφ) y i) (ρ m)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume x - (Ω.indicator gφ) x i| ^ q := by
      intro m
      refine setIntegral_congr_fun hKcpt.measurableSet fun x hx => ?_
      rw [step5 (ρ m) (δ₀ / ((m : ℝ) + 1)) (hρsmooth m) (hρcs m) (hρts m) x
        (hballsub m x hx) i, Set.indicator_of_mem (hKΩ hx)]
    simp only [hrw]
    exact squeeze _
      (fun m x => convolution (fun y => (Ω.indicator gφ) y i) (ρ m)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x - (Ω.indicator gφ) x i)
      (fun m => (convmem _ (hgimem i) (hgiloc i) m).sub (hgimem i))
      (convergeρ _ (hgimem i))
