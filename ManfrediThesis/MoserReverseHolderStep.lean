import ManfrediThesis.Preamble
import ManfrediThesis.SmoothProfileRadialCutoff
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.WeakGradientSmoothMul
set_option maxHeartbeats 1600000
open MeasureTheory

/-- The reverse-Hölder step of Moser's iteration.

Throughout, `v ≥ 0` is the function being iterated on the ball `B_R(x₀)`,
`gv θ` is the weak gradient of `v^θ` on `B_R(x₀)`, and
`Y s ρ = (|B_R|^{-1} ∫_{B_ρ} v^{2s})^{1/(2s)}`
is the normalised `L^{2s}` mean on the inner ball `B_ρ`, *normalised by the
measure of the outer ball `B_R`* in every instance -- that is the convention
that makes the radii cancel in the iteration, and it is restated here because a
helper inherits none of its parent's notation.  `χ > 1` and `CS > 0` are the
Sobolev exponent and constant on balls at the exponent `2`, supplied as the
hypothesis displayed below; `ψ` is the one-dimensional cut-off profile with
`ψ = 1` on `(-∞, 3/8]`, `ψ = 0` on `[5/8, ∞)` and `|ψ'| ≤ Λ`; and
`D ≥ CS (2Q+2)^{1/2} (2Λ)` with `D > 0` is the step constant.  `supp` denotes
the closed support.

The conclusion is: for every `θ > 1` and all radii `R/2 ≤ r' < r ≤ 3R/4`,
`Y (θχ) r' ≤ (D R / (r - r'))^{1/θ} · Y θ r`.

The route is Steps 1b, 2 and 3 of the parent's argument.  A radial cut-off `ζ`
is built from `ψ` between `B_{r'}` and `B_r`, smooth, equal to `1` on
`B_{r'}`, supported in `B_r` and with `Σ_i (∂_i ζ)² ≤ (2Λ/(r-r'))²`.  The
Sobolev inequality applied to `φ = v^θ ζ`, whose weak gradient is
`ζ · gv θ + v^θ ∇ζ` by the product rule for a smooth compactly supported
factor, bounds the normalised `L^{2θχ}` mean of `v^θ ζ` by
`CS · r · (normalised L² mean of ζ gv θ + v^θ ∇ζ)`.  The Caccioppoli
hypothesis at the exponent `θ` and this `ζ` absorbs the first summand into
`Q ∫ (v^θ)² Σ_i (∂_i ζ)²`, so the right-hand side is at most
`CS (2Q+2)^{1/2} (2Λ) · r/(r-r') · (normalised L^{2θ} mean of v on B_r)`, and
`r ≤ R` together with `D ≥ CS (2Q+2)^{1/2}(2Λ)` turns the factor into
`D R/(r-r')`.  Raising to the power `1/θ` and using `ζ = 1` on `B_{r'}` on the
left gives the assertion. -/
theorem MoserReverseHolderStep :
    ∀ (n : ℕ) (Q : ℝ), 2 ≤ n → 0 < Q →
      ∀ χ CS : ℝ, 1 < χ → 0 < CS →
        (∀ (x₀ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
          (φ : EuclideanSpace ℝ (Fin n) → ℝ)
          (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 < ρ → MemW1pOn n 2 (Metric.ball x₀ ρ) φ gφ →
          HasCompactSupport φ → tsupport φ ⊆ Metric.ball x₀ ρ →
          ((volume (Metric.ball x₀ ρ)).toReal⁻¹
              * ∫ x in Metric.ball x₀ ρ, |φ x| ^ (2 * χ)) ^ (1 / (2 * χ))
            ≤ CS * ρ * ((volume (Metric.ball x₀ ρ)).toReal⁻¹
                * ∫ x in Metric.ball x₀ ρ, ‖gφ x‖ ^ 2) ^ (1 / 2 : ℝ)) →
      ∀ (ψ : ℝ → ℝ) (Λ : ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → 1 ≤ Λ →
        (∀ t, 0 ≤ ψ t) → (∀ t, ψ t ≤ 1) →
        (∀ t, t ≤ 3 / 8 → ψ t = 1) → (∀ t, 5 / 8 ≤ t → ψ t = 0) →
        (∀ t, |deriv ψ t| ≤ Λ) →
      ∀ D : ℝ, 0 < D → CS * (2 * Q + 2) ^ (1 / 2 : ℝ) * (2 * Λ) ≤ D →
      ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
        (v : EuclideanSpace ℝ (Fin n) → ℝ)
        (gv : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < R → Measurable v → (∀ x, 0 ≤ v x) →
        (∀ θ : ℝ, 1 < θ →
          MemW1pLocOn n 2 (Metric.ball x₀ R) (fun x => v x ^ θ) (gv θ)) →
        (∀ θ : ℝ, 1 < θ → ∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
          tsupport ζ ⊆ Metric.ball x₀ R →
          (∫ x in Metric.ball x₀ R, ‖gv θ x‖ ^ 2 * ζ x ^ 2)
            ≤ Q * ∫ x in Metric.ball x₀ R, (v x ^ θ) ^ 2
                * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) →
        0 < (volume (Metric.ball x₀ R)).toReal →
      ∀ Y : ℝ → ℝ → ℝ,
        (∀ s ρ : ℝ, Y s ρ = ((volume (Metric.ball x₀ R)).toReal⁻¹
            * ∫ x in Metric.ball x₀ ρ, v x ^ (2 * s)) ^ (1 / (2 * s))) →
        (∀ ρ : ℝ, 0 < ρ → ρ < R →
          IsCompact (Metric.closedBall x₀ ρ)
            ∧ Metric.closedBall x₀ ρ ⊆ Metric.ball x₀ R) →
        (∀ s ρ : ℝ, 1 < s → 0 < ρ → ρ < R →
          IntegrableOn (fun x => v x ^ (2 * s)) (Metric.ball x₀ ρ) volume) →
        (∀ w : EuclideanSpace ℝ (Fin n), ∑ i : Fin n, (w i) ^ 2 = ‖w‖ ^ 2) →
        (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ^ (2 : ℝ) = ‖w‖ ^ 2) →
        (∀ (S T : Set (EuclideanSpace ℝ (Fin n)))
          (F : EuclideanSpace ℝ (Fin n) → ℝ),
          (∀ x, x ∉ S → F x = 0) → S ⊆ T → (∫ x in T, F x) = ∫ x in S, F x) →
      ∀ θ r' r : ℝ, 1 < θ → R / 2 ≤ r' → r' < r → r ≤ 3 * R / 4 →
        Y (θ * χ) r' ≤ (D * R / (r - r')) ^ (1 / θ) * Y θ r := by
  intro n Q hn hQ χ CS hχ1 hCS0 hSob ψ Λ hψsm hΛ1 hψ0 hψle1 hψlo hψhi hψd D hD0 hDge
    x₀ R v gv hR hvmeas hvnn hloc hcacc hmR0 Y hYeq hcb hintpow hnormsq hnpow2
    hsetint θ r' r hθ hr'lo hr'r hrhi
  have hθ0 : (0 : ℝ) < θ := lt_trans one_pos hθ
  have hr'0 : 0 < r' := by linarith
  have hdr : 0 < r - r' := by linarith
  have hrR : r < R := by linarith
  have hθχ : 1 < θ * χ :=
    lt_of_lt_of_le hθ (le_mul_of_one_le_right (by linarith) hχ1.le)
  have hθχ0 : (0 : ℝ) < θ * χ := lt_trans one_pos hθχ
  -- Step 1b: the radial cut-off between `B_{r'}` and `B_r`
  obtain ⟨ζ, hζsm, hζnn, hζle, hζone, hζcs, hζsupp, hζgrad⟩ :
      ∃ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) ζ ∧ (∀ x, 0 ≤ ζ x) ∧ (∀ x, ζ x ≤ 1) ∧
        (∀ x ∈ Metric.ball x₀ r', ζ x = 1) ∧
        HasCompactSupport ζ ∧ tsupport ζ ⊆ Metric.ball x₀ r ∧
        (∀ x, ∑ i : Fin n, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2
          ≤ (2 * Λ / (r - r')) ^ 2) :=
    SmoothProfileRadialCutoff n ψ Λ r' r x₀ hψsm hψ0 hψle1 hψlo hψhi hψd hnormsq
      hr'0 hr'r hdr
  have hζsuppR : tsupport ζ ⊆ Metric.ball x₀ R :=
    hζsupp.trans (Metric.ball_subset_ball (by linarith))
  -- Step 2: `v^θ ζ` is an admissible test function for the Sobolev inequality
  have hprod := (WeakGradientSmoothMul n 2 (by omega) (by norm_num)
    (Metric.ball x₀ R) (fun x => v x ^ θ) (gv θ) ζ Metric.isOpen_ball
    hζsm hζcs hζsuppR).2 (hloc θ hθ)
  have hφcs : HasCompactSupport (fun x => v x ^ θ * ζ x) :=
    HasCompactSupport.mul_left hζcs
  have hφsupp : tsupport (fun x => v x ^ θ * ζ x) ⊆ Metric.ball x₀ R :=
    tsupport_mul_subset_right.trans hζsuppR
  -- Step 3: the reverse-Hölder step
  have hr0 : 0 < r := by linarith
  have hsubRr : Metric.ball x₀ r ⊆ Metric.ball x₀ R :=
    Metric.ball_subset_ball (by linarith)
  have hcrpow : ∀ c : ℝ, 0 ≤ c → Continuous (fun t : ℝ => t ^ c) := by
    intro c hc
    rw [continuous_iff_continuousAt]
    intro t
    exact Real.continuousAt_rpow_const t c (Or.inr hc)
  have hvθmeas : Measurable (fun x => v x ^ θ) :=
    (hcrpow θ hθ0.le).measurable.comp hvmeas
  have hζzero : ∀ x, x ∉ Metric.ball x₀ r → ζ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hc => hx (hζsupp hc))
  have hDzero : ∀ x, x ∉ Metric.ball x₀ r → ∀ i : Fin n,
      fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)) = 0 := by
    intro x hx i
    rw [fderiv_of_notMem_tsupport ℝ (fun hc => hx (hζsupp hc))]
    simp
  -- the left-hand side of the Sobolev inequality
  have hLint : IntegrableOn (fun x => |v x ^ θ * ζ x| ^ (2 * χ))
      (Metric.ball x₀ r) volume := by
    refine Integrable.mono' (hintpow (θ * χ) r hθχ hr0 hrR)
      ((hcrpow (2 * χ) (by positivity)).measurable.comp
        (continuous_abs.measurable.comp
          (hvθmeas.mul hζsm.continuous.measurable))).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hb : |v x ^ θ * ζ x| ≤ v x ^ θ := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hvnn x) _)]
      have h1 : |ζ x| ≤ 1 := abs_le.2 ⟨by linarith [hζnn x], hζle x⟩
      exact mul_le_of_le_one_right (Real.rpow_nonneg (hvnn x) θ) h1
    calc |v x ^ θ * ζ x| ^ (2 * χ) ≤ (v x ^ θ) ^ (2 * χ) :=
          Real.rpow_le_rpow (abs_nonneg _) hb (by positivity)
      _ = v x ^ (2 * (θ * χ)) := by
          rw [← Real.rpow_mul (hvnn x)]
          congr 1
          ring
  have hleft : (∫ x in Metric.ball x₀ r', v x ^ (2 * (θ * χ)))
      ≤ ∫ x in Metric.ball x₀ R, |v x ^ θ * ζ x| ^ (2 * χ) := by
    have e1 : (∫ x in Metric.ball x₀ R, |v x ^ θ * ζ x| ^ (2 * χ))
        = ∫ x in Metric.ball x₀ r, |v x ^ θ * ζ x| ^ (2 * χ) := by
      refine hsetint _ _ _ (fun x hx => ?_) hsubRr
      rw [hζzero x hx, mul_zero, abs_zero, Real.zero_rpow (by positivity)]
    have e2 : (∫ x in Metric.ball x₀ r', |v x ^ θ * ζ x| ^ (2 * χ))
        = ∫ x in Metric.ball x₀ r', v x ^ (2 * (θ * χ)) := by
      refine setIntegral_congr_fun measurableSet_ball (fun x hx => ?_)
      rw [hζone x hx, mul_one, abs_of_nonneg (Real.rpow_nonneg (hvnn x) _),
        ← Real.rpow_mul (hvnn x)]
      congr 1
      ring
    rw [e1, ← e2]
    exact setIntegral_mono_set hLint
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _)
      (LE.le.eventuallyLE (Metric.ball_subset_ball hr'r.le))
  -- the right-hand side: the three integrals, all on `B_r`
  have hgvL2 : MemLp (gv θ) (ENNReal.ofReal 2)
      (volume.restrict (Metric.closedBall x₀ r)) :=
    ((hloc θ hθ).2 (Metric.closedBall x₀ r) (hcb r hr0 hrR).1 (hcb r hr0 hrR).2).2
  have hgvsq : IntegrableOn (fun x => ‖gv θ x‖ ^ 2) (Metric.ball x₀ r) volume := by
    have h1 : Integrable (fun x => ‖gv θ x‖ ^ (ENNReal.ofReal 2).toReal)
        (volume.restrict (Metric.closedBall x₀ r)) :=
      hgvL2.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp] at h1
    have h2 : IntegrableOn (fun x => ‖gv θ x‖ ^ 2) (Metric.closedBall x₀ r) volume := by
      refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
      show ‖gv θ x‖ ^ (2 : ℝ) = ‖gv θ x‖ ^ 2
      rw [← Real.rpow_natCast ‖gv θ x‖ 2]
      norm_num
    exact h2.mono_set Metric.ball_subset_closedBall
  have hPint : IntegrableOn (fun x => ‖gv θ x‖ ^ 2 * ζ x ^ 2)
      (Metric.ball x₀ r) volume := by
    refine Integrable.mono' hgvsq
      (((hgvL2.1.mono_measure (Measure.restrict_mono
          Metric.ball_subset_closedBall le_rfl)).norm.pow 2).mul
        (hζsm.continuous.pow 2).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ζ x ^ 2 ≤ 1 := by
      have h2 := pow_le_pow_left₀ (hζnn x) (hζle x) 2
      simpa using h2
    have h3 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖gv θ x‖)
    rw [mul_one] at h3
    exact h3
  have hSint : IntegrableOn (fun x => (v x ^ θ) ^ 2
      * ∑ i : Fin n, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2)
      (Metric.ball x₀ r) volume := by
    refine Integrable.mono' ((hintpow θ r hθ hr0 hrR).const_mul ((2 * Λ / (r - r')) ^ 2))
      (((hvθmeas.pow_const 2)).mul
        (Finset.measurable_sum _ (fun i _ =>
          (((hζsm.continuous_fderiv (by simp)).clm_apply
            continuous_const).measurable).pow_const 2))).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := hζgrad x
    have h2 : (v x ^ θ) ^ 2 = v x ^ (2 * θ) := by
      rw [← Real.rpow_natCast (v x ^ θ) 2, ← Real.rpow_mul (hvnn x)]
      congr 1
      push_cast
      ring
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (hvnn x) (2 * θ))
  have hDzsq : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖((EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) :
          EuclideanSpace ℝ (Fin n))‖ ^ 2
        = ∑ i : Fin n, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 := by
    intro x
    rw [← hnormsq]
    simp
  have hptw : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖ζ x • gv θ x + (v x ^ θ) • ((EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))))‖ ^ 2
      ≤ 2 * (‖gv θ x‖ ^ 2 * ζ x ^ 2)
        + 2 * ((v x ^ θ) ^ 2
          * ∑ i : Fin n, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) := by
    intro x
    have h1 : ‖ζ x • gv θ x + (v x ^ θ) • ((EuclideanSpace.equiv (Fin n) ℝ).symm
          (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))))‖
        ≤ |ζ x| * ‖gv θ x‖
          + |v x ^ θ| * ‖((EuclideanSpace.equiv (Fin n) ℝ).symm
            (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) :
              EuclideanSpace ℝ (Fin n))‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans ?_
    have h2 : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
      intro a b; nlinarith [sq_nonneg (a - b)]
    refine (h2 _ _).trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, sq_abs, sq_abs, hDzsq x]
    ring
  have hFint : IntegrableOn (fun x => ‖ζ x • gv θ x + (v x ^ θ) •
      ((EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))))‖ ^ 2)
      (Metric.ball x₀ r) volume := by
    have hm := hprod.2.2.mono_measure (Measure.restrict_mono hsubRr le_rfl)
    have h1 : Integrable (fun x => ‖ζ x • gv θ x + (v x ^ θ) •
        ((EuclideanSpace.equiv (Fin n) ℝ).symm
          (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))))‖
          ^ (ENNReal.ofReal 2).toReal)
        (volume.restrict (Metric.ball x₀ r)) :=
      hm.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp] at h1
    exact h1.congr (Filter.Eventually.of_forall fun x => hnpow2 _)
  have hadd : IntegrableOn (fun x => 2 * (‖gv θ x‖ ^ 2 * ζ x ^ 2)
      + 2 * ((v x ^ θ) ^ 2 * ∑ i : Fin n,
        (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2))
      (Metric.ball x₀ r) volume := (hPint.const_mul 2).add (hSint.const_mul 2)
  have hW3 : (∫ x in Metric.ball x₀ r, ‖ζ x • gv θ x + (v x ^ θ) •
        ((EuclideanSpace.equiv (Fin n) ℝ).symm
          (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))))‖ ^ 2)
      ≤ 2 * (∫ x in Metric.ball x₀ r, ‖gv θ x‖ ^ 2 * ζ x ^ 2)
        + 2 * (∫ x in Metric.ball x₀ r, (v x ^ θ) ^ 2
          * ∑ i : Fin n, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) :=
    calc (∫ x in Metric.ball x₀ r, ‖ζ x • gv θ x + (v x ^ θ) •
            ((EuclideanSpace.equiv (Fin n) ℝ).symm
              (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))))‖ ^ 2)
        ≤ ∫ x in Metric.ball x₀ r, (2 * (‖gv θ x‖ ^ 2 * ζ x ^ 2)
            + 2 * ((v x ^ θ) ^ 2 * ∑ i : Fin n,
              (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2)) :=
          integral_mono_ae hFint hadd (Filter.Eventually.of_forall hptw)
      _ = 2 * (∫ x in Metric.ball x₀ r, ‖gv θ x‖ ^ 2 * ζ x ^ 2)
            + 2 * (∫ x in Metric.ball x₀ r, (v x ^ θ) ^ 2
              * ∑ i : Fin n, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) := by
          rw [integral_add (hPint.const_mul 2) (hSint.const_mul 2),
            integral_const_mul, integral_const_mul]
  have hW2 : (∫ x in Metric.ball x₀ r, (v x ^ θ) ^ 2
        * ∑ i : Fin n, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2)
      ≤ (2 * Λ / (r - r')) ^ 2 * ∫ x in Metric.ball x₀ r, v x ^ (2 * θ) := by
    rw [← integral_const_mul]
    refine integral_mono_ae hSint ((hintpow θ r hθ hr0 hrR).const_mul _) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    show (v x ^ θ) ^ 2 * ∑ i : Fin n,
        (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2
      ≤ (2 * Λ / (r - r')) ^ 2 * v x ^ (2 * θ)
    have h1 := hζgrad x
    have h2 : (v x ^ θ) ^ 2 = v x ^ (2 * θ) := by
      rw [← Real.rpow_natCast (v x ^ θ) 2, ← Real.rpow_mul (hvnn x)]
      congr 1
      push_cast
      ring
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (hvnn x) (2 * θ))
  -- hypothesis (2) of the lemma, transported to `B_r`
  have hPzero : ∀ x, x ∉ Metric.ball x₀ r → ‖gv θ x‖ ^ 2 * ζ x ^ 2 = 0 := by
    intro x hx
    rw [hζzero x hx]
    ring
  have hSzero : ∀ x, x ∉ Metric.ball x₀ r →
      (v x ^ θ) ^ 2 * ∑ i : Fin n,
        (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 = 0 := by
    intro x hx
    have hz : ∑ i : Fin n, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hDzero x hx i]; ring
    rw [hz, mul_zero]
  have hGzero : ∀ x, x ∉ Metric.ball x₀ r →
      ‖ζ x • gv θ x + (v x ^ θ) • ((EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) :
          EuclideanSpace ℝ (Fin n))‖ ^ 2 = 0 := by
    intro x hx
    have hz : ((EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) :
          EuclideanSpace ℝ (Fin n)) = 0 := by
      ext i
      exact hDzero x hx i
    rw [hζzero x hx, hz]
    simp
  have hcac := hcacc θ hθ ζ hζsm hζcs hζsuppR
  rw [hsetint (Metric.ball x₀ r) (Metric.ball x₀ R) _ hPzero hsubRr,
    hsetint (Metric.ball x₀ r) (Metric.ball x₀ R) _ hSzero hsubRr] at hcac
  have hSnn : (0 : ℝ) ≤ ∫ x in Metric.ball x₀ r, (v x ^ θ) ^ 2
      * ∑ i : Fin n, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 :=
    integral_nonneg fun x => by positivity
  have hGR : (∫ x in Metric.ball x₀ R, ‖ζ x • gv θ x + (v x ^ θ) •
        ((EuclideanSpace.equiv (Fin n) ℝ).symm
          (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))))‖ ^ 2)
      ≤ (2 * Q + 2) * ((2 * Λ / (r - r')) ^ 2
        * ∫ x in Metric.ball x₀ r, v x ^ (2 * θ)) := by
    rw [hsetint (Metric.ball x₀ r) (Metric.ball x₀ R) _ hGzero hsubRr]
    have hstep1 : (∫ x in Metric.ball x₀ r, ‖ζ x • gv θ x + (v x ^ θ) •
          ((EuclideanSpace.equiv (Fin n) ℝ).symm
            (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))))‖ ^ 2)
        ≤ (2 * Q + 2) * (∫ x in Metric.ball x₀ r, (v x ^ θ) ^ 2
          * ∑ i : Fin n, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) := by
      linarith [hW3, hcac]
    exact hstep1.trans (mul_le_mul_of_nonneg_left hW2 (by linarith))
  -- Step 3 (tail): the Sobolev inequality at radius `R`, and the `1/θ` power
  have hSA := hSob x₀ R (fun x => v x ^ θ * ζ x) _ hR hprod hφcs hφsupp
  have hmRinv : (0 : ℝ) ≤ (volume (Metric.ball x₀ R)).toReal⁻¹ := inv_nonneg.2 hmR0.le
  have hIr'0 : (0 : ℝ) ≤ ∫ x in Metric.ball x₀ r', v x ^ (2 * (θ * χ)) :=
    integral_nonneg fun x => Real.rpow_nonneg (hvnn x) _
  have hIr0 : (0 : ℝ) ≤ ∫ x in Metric.ball x₀ r, v x ^ (2 * θ) :=
    integral_nonneg fun x => Real.rpow_nonneg (hvnn x) _
  have hGnn : (0 : ℝ) ≤ ∫ x in Metric.ball x₀ R, ‖ζ x • gv θ x + (v x ^ θ) •
      ((EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))))‖ ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hQ2 : (0 : ℝ) ≤ (2 * Q + 2) * (2 * Λ / (r - r')) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hstar : ((volume (Metric.ball x₀ R)).toReal⁻¹
        * ∫ x in Metric.ball x₀ r', v x ^ (2 * (θ * χ))) ^ (1 / (2 * χ))
      ≤ (D * R / (r - r')) * ((volume (Metric.ball x₀ R)).toReal⁻¹
        * ∫ x in Metric.ball x₀ r, v x ^ (2 * θ)) ^ (1 / 2 : ℝ) := by
    refine le_trans ?_ (le_trans hSA ?_)
    · refine Real.rpow_le_rpow (mul_nonneg hmRinv hIr'0) ?_
        (le_of_lt (div_pos one_pos (by linarith : (0:ℝ) < 2 * χ)))
      exact mul_le_mul_of_nonneg_left hleft hmRinv
    · have hb : (volume (Metric.ball x₀ R)).toReal⁻¹
            * ∫ x in Metric.ball x₀ R, ‖ζ x • gv θ x + (v x ^ θ) •
              ((EuclideanSpace.equiv (Fin n) ℝ).symm
                (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))))‖ ^ 2
          ≤ ((2 * Q + 2) * (2 * Λ / (r - r')) ^ 2)
            * ((volume (Metric.ball x₀ R)).toReal⁻¹
              * ∫ x in Metric.ball x₀ r, v x ^ (2 * θ)) := by
        calc (volume (Metric.ball x₀ R)).toReal⁻¹
              * ∫ x in Metric.ball x₀ R, ‖ζ x • gv θ x + (v x ^ θ) •
                ((EuclideanSpace.equiv (Fin n) ℝ).symm
                  (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))))‖ ^ 2
            ≤ (volume (Metric.ball x₀ R)).toReal⁻¹ * ((2 * Q + 2)
                * ((2 * Λ / (r - r')) ^ 2
                  * ∫ x in Metric.ball x₀ r, v x ^ (2 * θ))) :=
              mul_le_mul_of_nonneg_left hGR hmRinv
          _ = ((2 * Q + 2) * (2 * Λ / (r - r')) ^ 2)
                * ((volume (Metric.ball x₀ R)).toReal⁻¹
                  * ∫ x in Metric.ball x₀ r, v x ^ (2 * θ)) := by ring
      have hΛd : (0 : ℝ) ≤ 2 * Λ / (r - r') := by positivity
      have hsq : (((2 * Q + 2) * (2 * Λ / (r - r')) ^ 2)
            * ((volume (Metric.ball x₀ R)).toReal⁻¹
              * ∫ x in Metric.ball x₀ r, v x ^ (2 * θ))) ^ (1 / 2 : ℝ)
          = ((2 * Q + 2) ^ (1 / 2 : ℝ) * (2 * Λ / (r - r')))
            * ((volume (Metric.ball x₀ R)).toReal⁻¹
              * ∫ x in Metric.ball x₀ r, v x ^ (2 * θ)) ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow hQ2 (mul_nonneg hmRinv hIr0)]
        congr 1
        rw [Real.mul_rpow (by linarith) (sq_nonneg _)]
        congr 1
        rw [← Real.rpow_natCast (2 * Λ / (r - r')) 2, ← Real.rpow_mul hΛd]
        norm_num
      have hRd : (0 : ℝ) ≤ R / (r - r') := le_of_lt (div_pos hR hdr)
      calc CS * R * ((volume (Metric.ball x₀ R)).toReal⁻¹
              * ∫ x in Metric.ball x₀ R, ‖ζ x • gv θ x + (v x ^ θ) •
                ((EuclideanSpace.equiv (Fin n) ℝ).symm
                  (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))))‖ ^ 2)
              ^ (1 / 2 : ℝ)
          ≤ CS * R * ((((2 * Q + 2) * (2 * Λ / (r - r')) ^ 2)
              * ((volume (Metric.ball x₀ R)).toReal⁻¹
                * ∫ x in Metric.ball x₀ r, v x ^ (2 * θ))) ^ (1 / 2 : ℝ)) := by
            refine mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (mul_nonneg hmRinv hGnn) hb (by norm_num)) ?_
            exact mul_nonneg hCS0.le hR.le
        _ = CS * R * ((2 * Q + 2) ^ (1 / 2 : ℝ) * (2 * Λ / (r - r')))
              * ((volume (Metric.ball x₀ R)).toReal⁻¹
                * ∫ x in Metric.ball x₀ r, v x ^ (2 * θ)) ^ (1 / 2 : ℝ) := by
            rw [hsq]; ring
        _ ≤ (D * R / (r - r')) * ((volume (Metric.ball x₀ R)).toReal⁻¹
              * ∫ x in Metric.ball x₀ r, v x ^ (2 * θ)) ^ (1 / 2 : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_
              (Real.rpow_nonneg (mul_nonneg hmRinv hIr0) _)
            calc CS * R * ((2 * Q + 2) ^ (1 / 2 : ℝ) * (2 * Λ / (r - r')))
                = (CS * (2 * Q + 2) ^ (1 / 2 : ℝ) * (2 * Λ)) * (R / (r - r')) := by
                  field_simp
              _ ≤ D * (R / (r - r')) := mul_le_mul_of_nonneg_right hDge hRd
              _ = D * R / (r - r') := by ring
  -- raise (★) to the power `1/θ`
  rw [hYeq (θ * χ) r', hYeq θ r]
  have hL0 : (0 : ℝ) ≤ ((volume (Metric.ball x₀ R)).toReal⁻¹
      * ∫ x in Metric.ball x₀ r', v x ^ (2 * (θ * χ))) ^ (1 / (2 * χ)) :=
    Real.rpow_nonneg (mul_nonneg hmRinv hIr'0) _
  have hDR : (0 : ℝ) ≤ D * R / (r - r') := by
    refine le_of_lt (div_pos (mul_pos hD0 hR) hdr)
  have hfin := Real.rpow_le_rpow hL0 hstar (le_of_lt (div_pos one_pos hθ0))
  rw [← Real.rpow_mul (mul_nonneg hmRinv hIr'0),
    Real.mul_rpow hDR (Real.rpow_nonneg (mul_nonneg hmRinv hIr0) _),
    ← Real.rpow_mul (mul_nonneg hmRinv hIr0),
    show 1 / (2 * χ) * (1 / θ) = 1 / (2 * (θ * χ)) from by field_simp,
    show (1 / 2 : ℝ) * (1 / θ) = 1 / (2 * θ) from by field_simp] at hfin
  exact hfin
