import ManfrediThesis.Preamble
set_option maxHeartbeats 1600000
open MeasureTheory

/-- The limit `η_j ↓ 0` in the regularised Caccioppoli estimate, stated once
for both signs.

Conventions, restated here because a helper inherits none of its parent's.  The
exponent range is `1 < p < 2`, so `p/2 - 1 < 0` and `p - 2 < 0`; all powers of
nonnegative reals are real powers, so `0^{p/2-1} = 0`.  The weight is
`w = ε + ‖g‖²` and `w^{p/2-1}` is written exactly as the structure conditions
(Q1)/(Q2) print it.  `π_η` is the thesis' regularisation of the signed power,
`ψ_η = π_η(g^k)` and `ψ = |g^k|^{p-2}g^k`, and
`V_η = (p/2)(|g^k|+η)^{p/2-1}Dg^k`, `V = (p/2)|g^k|^{p/2-1}Dg^k`.
`η_j` is the regularisation sequence, positive and tending to `0`.

The open set `S ⊆ ℝ` is what cuts out the level set: taking `S = (ℓ,∞)` gives
`A^{+}_ℓ` and `S = (-∞,ℓ)` gives `A^{-}_ℓ`, and `b` is the matching truncation
`(\cdot-ℓ)^{+}` or `(ℓ-\cdot)^{+}` on the right.  Given the estimate at every
`η_j`, together with the integrability of each left-hand integrand, the
conclusion is the same estimate at the limit, with `ψ` in place of `ψ_η` and
`V` in place of `V_η`.

The route is Fatou on the left and dominated convergence on the right.  Fatou
consumes only the POINTWISE convergence `π_{η_j}(t) → |t|^{p-2}t` for every
real `t` --- at a point where `g^k ≠ 0` the map `η ↦ (|g^k|+η)^{p-2}g^k` is
continuous at `η = 0`, and where `g^k = 0` both `ψ_η` and `ψ` vanish --- and
*not* any monotonicity of the sets `A^{±}_ℓ(η)` in `η`, *which is
false and is the one thing a reader will ask about*.  At a point with
`g^k = 0` the limit integrand vanishes outright, because `0^{p/2-1} = 0` for
the negative exponent, so Fatou needs no information there.  On the right, `b`
is continuous and bounded by `M` on the range of `ψ_η`, which (H) bounds by
`μ^{p-1}` almost everywhere, and the gradient-square factor
`Σ_i(D_iζ)²` is continuous, hence bounded on the compact closed ball; so
dominated convergence identifies the limit of the right-hand sides. -/
theorem RegularisedCaccioppoliEtaLimit :
    ∀ (n : ℕ) (p : ℝ), 1 < p → p < 2 →
      ∀ (C₂ ε μ : ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ) (k : Fin n),
        0 ≤ C₂ → 0 < ε →
        AEStronglyMeasurable (fun x => g x k)
          (volume.restrict (Metric.ball x₀ R)) →
        AEStronglyMeasurable (fun x => |g x k|)
          (volume.restrict (Metric.ball x₀ R)) →
      ∀ pie : ℝ → ℝ → ℝ,
        (∀ (η : ℝ), 0 < η → ContDiff ℝ 1 (pie η)) →
      ∀ ηs : ℕ → ℝ, (∀ j : ℕ, 0 < ηs j) →
        Filter.Tendsto ηs Filter.atTop (nhds 0) →
        (∀ t : ℝ, Filter.Tendsto (fun j : ℕ => pie (ηs j) t) Filter.atTop
          (nhds (|t| ^ (p - 2) * t))) →
        (∀ (η : ℝ), 0 < η →
          ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
            |pie η (g x k)| ≤ μ ^ (p - 1)) →
        (∀ (η : ℝ) (ζ : EuclideanSpace ℝ (Fin n) → ℝ), Continuous ζ →
          AEStronglyMeasurable (fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
              * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
            (volume.restrict (Metric.ball x₀ R))) →
        (∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous ζ →
          AEStronglyMeasurable (fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
              * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
            (volume.restrict (Metric.ball x₀ R))) →
      ∀ (S : Set ℝ), IsOpen S →
      ∀ (b : ℝ → ℝ), Continuous b → (∀ s : ℝ, 0 ≤ b s) →
      ∀ M : ℝ, (∀ s : ℝ, |s| ≤ μ ^ (p - 1) → b s ≤ M) →
      ∀ (ζ : EuclideanSpace ℝ (Fin n) → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) ζ →
        (∀ j : ℕ, (∫ x in Metric.ball x₀ R ∩ {y | pie (ηs j) (g y k) ∈ S},
              (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
                * ‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
            ≤ C₂ * (∫ x in Metric.ball x₀ R,
                b (pie (ηs j) (g x k)) ^ 2
                  * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2))) →
        (∀ j : ℕ, IntegrableOn (fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
              * ‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
            (Metric.ball x₀ R) volume) →
        (∫ x in Metric.ball x₀ R ∩ {y | |g y k| ^ (p - 2) * g y k ∈ S},
            (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
              * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
          ≤ C₂ * (∫ x in Metric.ball x₀ R,
              b (|g x k| ^ (p - 2) * g x k) ^ 2
                * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)) := by
  intro n p hp hp2 C₂ ε μ g Dg x₀ R k hC₂0 hε hgmR habsR pie hpieC1 ηs hηs0 hηt
    hpielim hpiebd hFmeasη hFmeas0 S hS b hbc hbnn M hbM ζ hζsm' hyp hint
  have hp0 : (0:ℝ) < p := by linarith
  have hexpn : p / 2 - 1 < 0 := by linarith
  have hwlow : ∀ x : EuclideanSpace ℝ (Fin n), ε ≤ ε + ‖g x‖ ^ 2 := by
    intro x
    have := sq_nonneg ‖g x‖
    linarith
  -- the gradient-square weight on the right is continuous, hence bounded on
  -- the compact `closedBall x₀ R`
  have hGcont : Continuous
      (fun x => ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2) := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((hζsm'.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2
  obtain ⟨Lg, hLg⟩ := (isCompact_closedBall x₀ R).exists_bound_of_continuousOn
    hGcont.continuousOn
  have hGnn : ∀ x : EuclideanSpace ℝ (Fin n),
      0 ≤ ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 :=
    fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hGle : ∀ x ∈ Metric.ball x₀ R,
      (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2) ≤ Lg := by
    intro x hx
    have h1 := hLg x (Metric.ball_subset_closedBall hx)
    rw [Real.norm_eq_abs] at h1
    exact le_trans (le_abs_self _) h1
  have hfin : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  -- (D6.1) dominated convergence on the right
  have hbjm : ∀ j : ℕ, AEStronglyMeasurable
      (fun x => b (pie (ηs j) (g x k)) ^ 2
        * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2))
      (volume.restrict (Metric.ball x₀ R)) := by
    intro j
    have h1 : AEStronglyMeasurable (fun x => pie (ηs j) (g x k))
        (volume.restrict (Metric.ball x₀ R)) :=
      ((hpieC1 (ηs j) (hηs0 j)).continuous).comp_aestronglyMeasurable hgmR
    exact ((hbc.comp_aestronglyMeasurable h1).pow 2).mul
      hGcont.aestronglyMeasurable
  have hBlim : Filter.Tendsto
      (fun j : ℕ => ∫ x in Metric.ball x₀ R,
          b (pie (ηs j) (g x k)) ^ 2
            * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2))
      Filter.atTop
      (nhds (∫ x in Metric.ball x₀ R,
          b (|g x k| ^ (p - 2) * g x k) ^ 2
            * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ => M ^ 2 * Lg) hbjm (integrable_const _) ?_ ?_
    · intro j
      filter_upwards [hpiebd (ηs j) (hηs0 j),
        ae_restrict_mem measurableSet_ball] with x hx hxb
      have hb1 : b (pie (ηs j) (g x k)) ≤ M := hbM _ hx
      have hb0 : 0 ≤ b (pie (ηs j) (g x k)) := hbnn _
      have h2 : b (pie (ηs j) (g x k)) ^ 2 ≤ M ^ 2 := by nlinarith only [hb0, hb1]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (hGnn x))]
      exact mul_le_mul h2 (hGle x hxb) (hGnn x) (sq_nonneg M)
    · filter_upwards with x
      have h1 := (hbc.continuousAt
        (x := |g x k| ^ (p - 2) * g x k)).tendsto.comp (hpielim (g x k))
      exact (h1.pow 2).mul_const _
  -- (D6.2) the level sets are null-measurable for the restricted measure
  have hψaem : AEMeasurable (fun y => |g y k| ^ (p - 2) * g y k)
      (volume.restrict (Metric.ball x₀ R)) :=
    (habsR.aemeasurable.pow_const (p - 2)).mul hgmR.aemeasurable
  have hAnm : NullMeasurableSet {y | |g y k| ^ (p - 2) * g y k ∈ S}
      (volume.restrict (Metric.ball x₀ R)) :=
    hψaem.nullMeasurable hS.measurableSet
  have hAjnm : ∀ j : ℕ, NullMeasurableSet {y | pie (ηs j) (g y k) ∈ S}
      (volume.restrict (Metric.ball x₀ R)) := by
    intro j
    exact ((((hpieC1 (ηs j) (hηs0 j)).continuous).comp_aestronglyMeasurable
      hgmR).aemeasurable).nullMeasurable hS.measurableSet
  have hrw : ∀ (A : Set (EuclideanSpace ℝ (Fin n))),
      NullMeasurableSet A (volume.restrict (Metric.ball x₀ R)) →
      ∀ f : EuclideanSpace ℝ (Fin n) → ENNReal,
      ∫⁻ x in Metric.ball x₀ R ∩ A, f x
        = ∫⁻ x, A.indicator f x ∂(volume.restrict (Metric.ball x₀ R)) := by
    intro A hA f
    rw [lintegral_indicator₀ hA, Measure.restrict_restrict₀ hA,
      Set.inter_comm A (Metric.ball x₀ R)]
  have hF0nn : ∀ x : EuclideanSpace ℝ (Fin n),
      0 ≤ (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
        * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2 := fun x =>
    mul_nonneg (mul_nonneg
      (Real.rpow_nonneg (le_trans hε.le (hwlow x)) _) (sq_nonneg _)) (sq_nonneg _)
  have hFjnn : ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)),
      0 ≤ (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
        * ‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2 :=
    fun j x => mul_nonneg (mul_nonneg
      (Real.rpow_nonneg (le_trans hε.le (hwlow x)) _) (sq_nonneg _)) (sq_nonneg _)
  -- (D6.3) each level-`η_j` left-hand side as a lintegral of an indicator
  have hLj : ∀ j : ℕ,
      (∫⁻ x, ({y | pie (ηs j) (g y k) ∈ S}).indicator
          (fun y => ENNReal.ofReal ((ε + ‖g y‖ ^ 2) ^ (p / 2 - 1)
            * ‖(p / 2 * (|g y k| + ηs j) ^ (p / 2 - 1)) • Dg k y‖ ^ 2 * ζ y ^ 2)) x
        ∂(volume.restrict (Metric.ball x₀ R)))
      ≤ ENNReal.ofReal (C₂ * (∫ x in Metric.ball x₀ R,
          b (pie (ηs j) (g x k)) ^ 2
            * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2))) := by
    intro j
    rw [← hrw _ (hAjnm j),
      ← ofReal_integral_eq_lintegral_ofReal
        ((hint j).mono_set Set.inter_subset_left)
        (Filter.Eventually.of_forall (hFjnn j))]
    exact ENNReal.ofReal_le_ofReal (hyp j)
  have hWm : ∀ j : ℕ, AEMeasurable
      (({y | pie (ηs j) (g y k) ∈ S}).indicator
          (fun y => ENNReal.ofReal ((ε + ‖g y‖ ^ 2) ^ (p / 2 - 1)
            * ‖(p / 2 * (|g y k| + ηs j) ^ (p / 2 - 1)) • Dg k y‖ ^ 2 * ζ y ^ 2)))
      (volume.restrict (Metric.ball x₀ R)) := fun j =>
    ((hFmeasη (ηs j) ζ hζsm'.continuous).aemeasurable.ennreal_ofReal).indicator₀
      (hAjnm j)
  -- (D6.4) the pointwise statement (D.6) that Fatou consumes
  have hptw : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      ({y | |g y k| ^ (p - 2) * g y k ∈ S}).indicator
          (fun y => ENNReal.ofReal ((ε + ‖g y‖ ^ 2) ^ (p / 2 - 1)
            * ‖(p / 2 * |g y k| ^ (p / 2 - 1)) • Dg k y‖ ^ 2 * ζ y ^ 2)) x
        ≤ Filter.liminf (fun j : ℕ =>
            ({y | pie (ηs j) (g y k) ∈ S}).indicator
              (fun y => ENNReal.ofReal ((ε + ‖g y‖ ^ 2) ^ (p / 2 - 1)
                * ‖(p / 2 * (|g y k| + ηs j) ^ (p / 2 - 1)) • Dg k y‖ ^ 2
                  * ζ y ^ 2)) x) Filter.atTop := by
    filter_upwards with x
    by_cases hxA : x ∈ {y | |g y k| ^ (p - 2) * g y k ∈ S}
    · rw [Set.indicator_of_mem hxA]
      have hev : ∀ᶠ j in (Filter.atTop : Filter ℕ),
          x ∈ {y | pie (ηs j) (g y k) ∈ S} :=
        (hpielim (g x k)).eventually (hS.mem_nhds hxA)
      have hcg : Filter.liminf (fun j : ℕ =>
            ({y | pie (ηs j) (g y k) ∈ S}).indicator
              (fun y => ENNReal.ofReal ((ε + ‖g y‖ ^ 2) ^ (p / 2 - 1)
                * ‖(p / 2 * (|g y k| + ηs j) ^ (p / 2 - 1)) • Dg k y‖ ^ 2
                  * ζ y ^ 2)) x) Filter.atTop
          = Filter.liminf (fun j : ℕ =>
            ENNReal.ofReal ((ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
              * ‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2
                * ζ x ^ 2)) Filter.atTop := by
        refine Filter.liminf_congr ?_
        filter_upwards [hev] with j hj
        rw [Set.indicator_of_mem (s := {y | pie (ηs j) (g y k) ∈ S}) hj]
      rw [hcg]
      rcases eq_or_ne (g x k) 0 with hg0 | hg0
      · have hz : (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2 = 0 := by
          rw [hg0, abs_zero, Real.zero_rpow (ne_of_lt hexpn), mul_zero, zero_smul,
            norm_zero]
          ring
        rw [hz, ENNReal.ofReal_zero]
        exact zero_le
      · have hc : ContinuousAt (fun s : ℝ => s ^ (p / 2 - 1)) |g x k| :=
          Real.continuousAt_rpow_const _ _ (Or.inl (abs_ne_zero.2 hg0))
        have h1 : Filter.Tendsto (fun j : ℕ => |g x k| + ηs j) Filter.atTop
            (nhds |g x k|) := by
          have h2 := (tendsto_const_nhds (x := |g x k|)
            (f := (Filter.atTop : Filter ℕ))).add hηt
          simpa using h2
        have h4 : Filter.Tendsto
            (fun j : ℕ => ‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
            Filter.atTop
            (nhds (‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)) :=
          ((((hc.tendsto.comp h1).const_mul (p / 2)).smul_const
            (Dg k x)).norm).pow 2
        have h5 := (h4.const_mul ((ε + ‖g x‖ ^ 2) ^ (p / 2 - 1))).mul_const
          (ζ x ^ 2)
        exact le_of_eq ((ENNReal.tendsto_ofReal h5).liminf_eq).symm
    · rw [Set.indicator_of_notMem hxA]
      exact zero_le
  -- (D6.5) Fatou
  have hfat : (∫⁻ x, ({y | |g y k| ^ (p - 2) * g y k ∈ S}).indicator
          (fun y => ENNReal.ofReal ((ε + ‖g y‖ ^ 2) ^ (p / 2 - 1)
            * ‖(p / 2 * |g y k| ^ (p / 2 - 1)) • Dg k y‖ ^ 2 * ζ y ^ 2)) x
        ∂(volume.restrict (Metric.ball x₀ R)))
      ≤ ENNReal.ofReal (C₂ * (∫ x in Metric.ball x₀ R,
          b (|g x k| ^ (p - 2) * g x k) ^ 2
            * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2))) := by
    calc _ ≤ ∫⁻ x, Filter.liminf (fun j : ℕ =>
              ({y | pie (ηs j) (g y k) ∈ S}).indicator
                (fun y => ENNReal.ofReal ((ε + ‖g y‖ ^ 2) ^ (p / 2 - 1)
                  * ‖(p / 2 * (|g y k| + ηs j) ^ (p / 2 - 1)) • Dg k y‖ ^ 2
                    * ζ y ^ 2)) x) Filter.atTop
            ∂(volume.restrict (Metric.ball x₀ R)) := lintegral_mono_ae hptw
      _ ≤ Filter.liminf (fun j : ℕ => ∫⁻ x,
            ({y | pie (ηs j) (g y k) ∈ S}).indicator
              (fun y => ENNReal.ofReal ((ε + ‖g y‖ ^ 2) ^ (p / 2 - 1)
                * ‖(p / 2 * (|g y k| + ηs j) ^ (p / 2 - 1)) • Dg k y‖ ^ 2
                  * ζ y ^ 2)) x
            ∂(volume.restrict (Metric.ball x₀ R))) Filter.atTop :=
          lintegral_liminf_le' hWm
      _ ≤ Filter.liminf (fun j : ℕ => ENNReal.ofReal (C₂ *
            (∫ x in Metric.ball x₀ R, b (pie (ηs j) (g x k)) ^ 2
              * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2))))
            Filter.atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall hLj)
      _ = _ := (ENNReal.tendsto_ofReal (hBlim.const_mul C₂)).liminf_eq
  -- (D6.6) back to the Bochner integral
  have hBnn : 0 ≤ ∫ x in Metric.ball x₀ R,
      b (|g x k| ^ (p - 2) * g x k) ^ 2
        * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2) :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hGnn x)
  have hCB : 0 ≤ C₂ * (∫ x in Metric.ball x₀ R,
      b (|g x k| ^ (p - 2) * g x k) ^ 2
        * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)) :=
    mul_nonneg hC₂0 hBnn
  rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall hF0nn)
      ((hFmeas0 ζ hζsm'.continuous).mono_measure
        (Measure.restrict_mono Set.inter_subset_left le_rfl)),
    hrw _ hAnm]
  calc _ ≤ (ENNReal.ofReal (C₂ * (∫ x in Metric.ball x₀ R,
            b (|g x k| ^ (p - 2) * g x k) ^ 2
              * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hfat
    _ = _ := ENNReal.toReal_ofReal hCB
