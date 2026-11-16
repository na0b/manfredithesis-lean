import ManfrediThesis.Preamble
set_option maxHeartbeats 800000
open MeasureTheory

/-- The common core of the two sides of the subquadratic level transport: a
Caccioppoli bound on `B_R(x₀) ∩ S` for the weighted energy of the signed power
is transported into the un-weighted bound on the inner ball
`B_{ρ₀}(x₀) ∩ S`,
\[
∫_{B_{ρ₀}∩S}\bigl\|(\tfrac p2|g^k|^{\frac p2-1})Dg^k\bigr\|^2
  \ \le\ \max\{1,C_b\}\frac{(\lambda^{p/2})^2}{(\sigma\rho)^2}\,
    \bigl|B_\rho∩S\bigr| .
\]

Conventions, restated here because a helper inherits none of its parent's.
`g` plays the role of `∇u` and `Dg k` of `∇D_ku`; `ζ` is the cut-off, equal to
`1` on `B_{ρ₀}(x₀)` and with `supp ζ` --- the CLOSED support --- inside
`B_ρ(x₀)`, and `ρ - ρ₀ = σρ` is the width of the annulus; `λ = μ/2` is the
level parameter of the subquadratic branch; `W_{2L}` is the uniform lower
bound for the weight on `B_R(x₀)`.  Every power of a nonnegative real is the
real power, written exactly as the structure conditions print the weight
`(ε + ‖g‖²)^{p/2-1}`; no σ₂ identity from the paper is assumed or used here.

The statement is deliberately abstract in the pair `(S, d)`: `S` is a level set
and `d` the corresponding truncation of the signed power, and the two
consumers --- the `−` side and the `+` side of the subquadratic case --- differ
only in which level set and which truncation they supply.  The four hypotheses
on `(S, d)` are the Caccioppoli bound with constant `C₂`, the nonnegativity of
`d`, its uniform bound `d ≤ (1 + 2^{p-1})λ^{p-1}` almost everywhere on
`B_R(x₀)`, and its vanishing off `S`.

The route.  Since `ζ = 1` on `B_{ρ₀}(x₀)` and the integrand is nonnegative, the
left-hand side is at most the same integral over `B_R(x₀) ∩ S` with the factor
`ζ²` inserted; and since the weight is at least `W_{2L}` almost everywhere
there, dividing by `W_{2L} > 0` bounds it by `W_{2L}^{-1}` times the weighted
integral.  The Caccioppoli hypothesis bounds that weighted integral by
`C₂∫_{B_R}d²|∇ζ|²`, and `d` vanishes off `S` while `∇ζ` vanishes off `supp ζ ⊆ B_ρ`,
so the domain of that integral may be cut down to `B_ρ ∩ S`; there the uniform
bound on `d` and the cut-off gradient bound `|∇ζ|² ≤ L_c/(σρ)²` give
`C₂·K_c·|B_ρ ∩ S|` with
`K_c = ((1+2^{p-1})λ^{p-1})²L_c/(σρ)²`.  Collecting the constants, using
`W_{2L}^{-1} = (1+4n)^{1-p/2}λ^{2-p}` and the two power identities
`(λ^{p-1})² = λ^{2p-2}`, `λ^{2-p}λ^{2p-2} = λ^{p}= (λ^{p/2})²`, turns the
product into `C_b(λ^{p/2})²/(σρ)²·|B_ρ∩S|`, and `C_b ≤ \max\{1,C_b\}` finishes.
The degenerate case in which the left-hand integrand is not integrable is
handled separately: there the integral is `0` by convention and the right-hand
side is nonnegative. -/
theorem SignedPowerLevelTransportCore :
    ∀ (n : ℕ) (p r C₁ Lc C₂ Cb ε lam ρ σ ρ₀ W2L R : ℝ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (k : Fin n) (ζ : EuclideanSpace ℝ (Fin n) → ℝ)
      (x₀ : EuclideanSpace ℝ (Fin n)),
      C₂ = (2 * (n:ℝ) * r * C₁ * p ^ 2 / (4 * (p - 1))) ^ 2 →
      Cb = C₂ * (1 + (2:ℝ) ^ (p - 1)) ^ 2 * (1 + 4 * (n:ℝ)) ^ (1 - p / 2) * Lc →
      0 < ε → 0 < lam → 0 < ρ → 0 < σ → 0 < Lc →
      (∀ x : EuclideanSpace ℝ (Fin n), ε ≤ ε + ‖g x‖ ^ 2) →
      ρ ≤ R → ρ₀ < ρ → ρ - ρ₀ = σ * ρ →
      tsupport ζ ⊆ Metric.ball x₀ ρ →
      (∀ x ∈ Metric.closedBall x₀ ρ₀, ζ x = 1) →
      (∀ x : EuclideanSpace ℝ (Fin n),
        ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2
          ≤ Lc / (ρ - ρ₀) ^ 2) →
      (∀ x, x ∉ tsupport ζ →
        ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 = 0) →
      (∀ S : Set (EuclideanSpace ℝ (Fin n)),
        IntegrableOn (fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
          * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2) S volume) →
      0 < W2L →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
        W2L ≤ (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)) →
      (0:ℝ) < (σ * ρ) ^ 2 →
      Cb ≤ max 1 Cb →
      (lam ^ (p / 2)) ^ 2 = lam ^ p →
      (lam ^ (p - 1)) ^ 2 = lam ^ (2 * p - 2) →
      W2L⁻¹ = (1 + 4 * (n:ℝ)) ^ (1 - p / 2) * lam ^ (2 - p) →
      lam ^ (2 - p) * lam ^ (2 * p - 2) = lam ^ p →
      (∀ S : Set (EuclideanSpace ℝ (Fin n)),
        (0:ℝ) ≤ max 1 Cb * (lam ^ (p / 2)) ^ 2 / (σ * ρ) ^ 2
          * (volume (Metric.ball x₀ ρ ∩ S)).toReal) →
      ∀ (S : Set (EuclideanSpace ℝ (Fin n)))
      (d : EuclideanSpace ℝ (Fin n) → ℝ),
      (∫ x in Metric.ball x₀ R ∩ S, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
      * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
      ≤ C₂ * (∫ x in Metric.ball x₀ R, d x ^ 2
      * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)) →
      (∀ x, 0 ≤ d x) →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      d x ≤ (1 + (2:ℝ) ^ (p - 1)) * lam ^ (p - 1)) →
      (∀ x, x ∉ S → d x = 0) →
      (∫ x in Metric.ball x₀ ρ₀ ∩ S,
      ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
      ≤ max 1 Cb * (lam ^ (p / 2)) ^ 2 / (σ * ρ) ^ 2
      * (volume (Metric.ball x₀ ρ ∩ S)).toReal := by
  intro n p r C₁ Lc C₂ Cb ε lam ρ σ ρ₀ W2L R g Dg k ζ x₀ hC₂def hCbdef hε
    hlam0 hρ hσ hLc0 hwlow hρR hρ₀ρ hdρ hζts hζone hζgrad hDz0 hintW hW2L0 hwlowK hsq0
    hCble hlamp hlam2 hW2Linv hlamsum hcommon
  intro S d hcac hd0 hdbd hdoff
  obtain ⟨Kc, hKcdef⟩ : ∃ t : ℝ,
    t = ((1 + (2:ℝ) ^ (p - 1)) * lam ^ (p - 1)) ^ 2 * (Lc / (σ * ρ) ^ 2) :=
    ⟨_, rfl⟩
  have hKc0 : (0:ℝ) ≤ Kc := by
    rw [hKcdef]; exact mul_nonneg (sq_nonneg _) (by positivity)
  -- the right-hand integral
  have hB : (∫ x in Metric.ball x₀ R, d x ^ 2
        * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2))
      ≤ Kc * (volume (Metric.ball x₀ ρ ∩ S)).toReal := by
    by_cases hint : IntegrableOn (fun x => d x ^ 2
        * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2))
        (Metric.ball x₀ R) volume
    · obtain ⟨Tm, hTmm, hTmsub, hTmvol⟩ : ∃ Tm : Set (EuclideanSpace ℝ (Fin n)),
          MeasurableSet Tm ∧ Metric.ball x₀ ρ ∩ S ⊆ Tm ∧
          volume Tm = volume (Metric.ball x₀ ρ ∩ S) :=
        ⟨toMeasurable volume _, measurableSet_toMeasurable _ _,
          subset_toMeasurable _ _, measure_toMeasurable _⟩
      have hindT : IntegrableOn (fun x => Kc * Tm.indicator (fun _ => (1:ℝ)) x)
          (Metric.ball x₀ R) volume := by
        refine Integrable.const_mul ?_ Kc
        have hfin : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
        refine Integrable.mono' (g := fun _ => (1:ℝ)) (integrable_const _)
          ((measurable_const.indicator hTmm).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun x => ?_)
        by_cases hb : x ∈ Tm
        · rw [Set.indicator_of_mem hb]; simp
        · rw [Set.indicator_of_notMem hb]; simp
      have hptw : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
          d x ^ 2 * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
            ≤ Kc * Tm.indicator (fun _ => (1:ℝ)) x := by
        filter_upwards [hdbd] with x hdx
        have hDnn : (0:ℝ) ≤ ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 :=
          Finset.sum_nonneg fun i _ => sq_nonneg _
        have hIT0 : (0:ℝ) ≤ Kc * Tm.indicator (fun _ => (1:ℝ)) x :=
          mul_nonneg hKc0 (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
        by_cases hb : x ∈ Metric.ball x₀ ρ
        · by_cases hs : x ∈ S
          · rw [Set.indicator_of_mem (hTmsub ⟨hb, hs⟩), mul_one, hKcdef]
            have hD : ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2
                ≤ Lc / (σ * ρ) ^ 2 := by
              have hgr := hζgrad x
              rwa [hdρ] at hgr
            have hd2 : d x ^ 2 ≤ ((1 + (2:ℝ) ^ (p - 1)) * lam ^ (p - 1)) ^ 2 :=
              pow_le_pow_left₀ (hd0 x) hdx 2
            exact mul_le_mul hd2 hD hDnn (sq_nonneg _)
          · rw [hdoff x hs, show (0:ℝ) ^ 2 = 0 from by ring, zero_mul]
            exact hIT0
        · have hxt : x ∉ tsupport ζ := fun hc => hb (hζts hc)
          rw [hDz0 x hxt, mul_zero]
          exact hIT0
      refine le_trans (setIntegral_mono_ae_restrict hint hindT hptw) ?_
      rw [integral_const_mul, setIntegral_indicator hTmm, setIntegral_const,
        MeasureTheory.measureReal_def, smul_eq_mul, mul_one]
      refine mul_le_mul_of_nonneg_left ?_ hKc0
      refine ENNReal.toReal_mono ?_ ?_
      · exact (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
          measure_ball_lt_top).ne
      · rw [← hTmvol]
        exact measure_mono Set.inter_subset_right
    · rw [integral_undef hint]
      exact mul_nonneg hKc0 ENNReal.toReal_nonneg
  -- the left-hand side
  by_cases hVint : IntegrableOn
      (fun x => ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
      (Metric.ball x₀ ρ₀ ∩ S) volume
  · have hsub0 : Metric.ball x₀ ρ₀ ∩ S ⊆ Metric.ball x₀ R ∩ S := fun y hy =>
      ⟨Metric.ball_subset_ball (le_trans hρ₀ρ.le hρR) hy.1, hy.2⟩
    have hmem0 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ₀ ∩ S)),
        x ∈ Metric.ball x₀ ρ₀ :=
      (ae_restrict_mem Metric.isOpen_ball.measurableSet).filter_mono
        (ae_mono (Measure.restrict_mono Set.inter_subset_left le_rfl))
    have hwlow0 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ₀ ∩ S)),
        W2L ≤ (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) :=
      hwlowK.filter_mono (ae_mono (Measure.restrict_mono
        (fun y hy => Metric.ball_subset_ball (le_trans hρ₀ρ.le hρR) hy.1) le_rfl))
    have hstep1 : (∫ x in Metric.ball x₀ ρ₀ ∩ S, W2L *
          ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
        ≤ ∫ x in Metric.ball x₀ ρ₀ ∩ S, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2 := by
      refine integral_mono_ae (hVint.const_mul _) (hintW _) ?_
      filter_upwards [hmem0, hwlow0] with x hx hw
      rw [hζone x (Metric.ball_subset_closedBall hx)]
      have : (1:ℝ) ^ 2 = 1 := by ring
      rw [this, mul_one]
      exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    have hstep2 : (∫ x in Metric.ball x₀ ρ₀ ∩ S, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
          * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
        ≤ ∫ x in Metric.ball x₀ R ∩ S, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2 := by
      refine setIntegral_mono_set (hintW _)
        (Filter.Eventually.of_forall fun x => ?_)
        (Filter.Eventually.of_forall fun x hx => hsub0 hx)
      have h1 : (0:ℝ) ≤ (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) :=
        Real.rpow_nonneg (le_trans hε.le (hwlow x)) _
      exact mul_nonneg (mul_nonneg h1 (sq_nonneg _)) (sq_nonneg _)
    have hconst : W2L⁻¹ * (C₂ * Kc) = Cb * lam ^ p / (σ * ρ) ^ 2 := by
      rw [hKcdef, hW2Linv, hCbdef, mul_pow, hlam2]
      have hne : ((σ * ρ) ^ 2) ≠ 0 := ne_of_gt hsq0
      field_simp
      rw [← hlamsum]
      ring_nf
    have hfinal : W2L⁻¹ * (C₂ * (Kc * (volume (Metric.ball x₀ ρ ∩ S)).toReal))
        ≤ max 1 Cb * (lam ^ (p / 2)) ^ 2 / (σ * ρ) ^ 2
          * (volume (Metric.ball x₀ ρ ∩ S)).toReal := by
      have e1 : W2L⁻¹ * (C₂ * (Kc * (volume (Metric.ball x₀ ρ ∩ S)).toReal))
          = (W2L⁻¹ * (C₂ * Kc)) * (volume (Metric.ball x₀ ρ ∩ S)).toReal := by
        ring
      rw [e1, hconst, hlamp]
      refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCble (Real.rpow_nonneg hlam0.le p))
        (le_of_lt (inv_pos.2 hsq0))
    have hchain : W2L * (∫ x in Metric.ball x₀ ρ₀ ∩ S,
          ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
        ≤ C₂ * (Kc * (volume (Metric.ball x₀ ρ ∩ S)).toReal) := by
      rw [← integral_const_mul]
      refine le_trans (le_trans hstep1 hstep2) (le_trans hcac ?_)
      exact mul_le_mul_of_nonneg_left hB (by rw [hC₂def]; positivity)
    calc (∫ x in Metric.ball x₀ ρ₀ ∩ S,
          ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
        = W2L⁻¹ * (W2L * ∫ x in Metric.ball x₀ ρ₀ ∩ S,
            ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2) := by
          field_simp
      _ ≤ W2L⁻¹ * (C₂ * (Kc * (volume (Metric.ball x₀ ρ ∩ S)).toReal)) :=
          mul_le_mul_of_nonneg_left hchain (le_of_lt (inv_pos.2 hW2L0))
      _ ≤ _ := hfinal
  · rw [integral_undef hVint]
    exact hcommon S
