import ManfrediThesis.Preamble
import ManfrediThesis.SmoothGradientFieldL2Facts
import ManfrediThesis.LadyzhenskayaBallInequalityTwo
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import ManfrediThesis.MemW1pOn
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.WeakGradientC1Comp
import ManfrediThesis.WeakGradientSmoothApprox
import ManfrediThesis.SmoothCompactSupportMemW1p
import ManfrediThesis.SobolevInequalityFromSmoothCase
open MeasureTheory

/-- The scale-invariant Sobolev inequality at exponent `2` for functions with
compact support in a ball: the `L^{2χ}` average of `φ` is controlled by `ρ`
times the `L²` average of its weak gradient, with `χ = n/(n-2)` for `n ≥ 3` and
`χ = 2` for `n = 2`. -/
theorem SobolevExponentTwoBall :
    ∀ n : ℕ, 2 ≤ n → CitedSobolevPoincareBall n →
      ∃ χ C : ℝ, 1 < χ ∧ 0 < C ∧
        ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
          (φ : EuclideanSpace ℝ (Fin n) → ℝ)
          (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 < ρ → MemW1pOn n 2 (Metric.ball x₀ ρ) φ gφ →
          HasCompactSupport φ → tsupport φ ⊆ Metric.ball x₀ ρ →
          ((volume (Metric.ball x₀ ρ)).toReal⁻¹
              * ∫ x in Metric.ball x₀ ρ, |φ x| ^ (2 * χ)) ^ (1 / (2 * χ))
            ≤ C * ρ * ((volume (Metric.ball x₀ ρ)).toReal⁻¹
                * ∫ x in Metric.ball x₀ ρ, ‖gφ x‖ ^ 2) ^ (1 / 2 : ℝ) := by
  intro n hn _hSPB
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hntriv : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, hnpos⟩ (1 : ℝ), ?_⟩⟩
    intro hc
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hnpos⟩) hc
    simp at h
  -- the volume of the unit ball
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℝ,
      ω = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := ⟨_, rfl⟩
  have hω : 0 < ω := by
    rw [hωdef]
    refine ENNReal.toReal_pos ?_ measure_ball_lt_top.ne
    exact (Metric.isOpen_ball.measure_pos volume
      ⟨0, Metric.mem_ball_self one_pos⟩).ne'
  have hballvol : ∀ (y : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 ≤ r →
      (volume (Metric.ball y r)).toReal = ω * r ^ n := by
    intro y r hr
    rw [Measure.addHaar_ball volume y hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity),
      show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n by simp, ← hωdef]
    ring
  -- the dictionary between `eLpNorm` and the real `rpow` integral
  have hdictR : ∀ (r : ℝ), 0 < r → ∀ (S : Set (EuclideanSpace ℝ (Fin n)))
      (v : EuclideanSpace ℝ (Fin n) → ℝ),
      MemLp v (ENNReal.ofReal r) (volume.restrict S) →
      (eLpNorm v (ENNReal.ofReal r) (volume.restrict S)).toReal
        = (∫ x in S, |v x| ^ r) ^ (1 / r) := by
    intro r hr S v hv
    rw [hv.eLpNorm_eq_integral_rpow_norm (by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hr) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hr.le]
    simp only [Real.norm_eq_abs, one_div]
  have hdictV : ∀ (r : ℝ), 0 < r → ∀ (S : Set (EuclideanSpace ℝ (Fin n)))
      (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      MemLp v (ENNReal.ofReal r) (volume.restrict S) →
      (eLpNorm v (ENNReal.ofReal r) (volume.restrict S)).toReal
        = (∫ x in S, ‖v x‖ ^ r) ^ (1 / r) := by
    intro r hr S v hv
    rw [hv.eLpNorm_eq_integral_rpow_norm (by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hr) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hr.le]
    simp only [one_div]
  -- the coordinate expansion of a vector and the `ℓ¹` bound on its norm
  have hexpand : ∀ y : EuclideanSpace ℝ (Fin n),
      ∑ i : Fin n, y i • (EuclideanSpace.single i (1 : ℝ) :
        EuclideanSpace ℝ (Fin n)) = y := by
    intro y
    have h := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr y
    simpa [EuclideanSpace.basisFun_apply] using h
  -- the Riesz bridge: the operator norm of `dΦ` is at most the norm of the gradient vector
  have hfdnorm : ∀ (Φ : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)),
      ‖fderiv ℝ Φ x‖
        ≤ ‖(WithLp.toLp 2 fun i => fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
            EuclideanSpace ℝ (Fin n))‖ := by
    intro Φ x
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
    have hexp := hexpand y
    have hval : fderiv ℝ Φ x y
        = inner ℝ (WithLp.toLp 2 fun i => fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
            EuclideanSpace ℝ (Fin n)) y := by
      rw [PiLp.inner_apply]
      conv_lhs => rw [← hexp]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
      simp
    rw [Real.norm_eq_abs, hval]
    exact abs_real_inner_le_norm _ _
  -- a function vanishing off the ball has the same `eLpNorm` for `volume` and for
  -- the restriction, and the `rpow`/`npow` bridge for the square
  have hresR : ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (pp : ENNReal)
      (v : EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ x, x ∉ Metric.ball x₀ ρ → v x = 0) →
      eLpNorm v pp volume = eLpNorm v pp (volume.restrict (Metric.ball x₀ ρ)) := by
    intro x₀ ρ pp v hv
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball]
    congr 1
    funext x
    by_cases hx : x ∈ Metric.ball x₀ ρ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hv x hx]
  have hresV : ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (pp : ENNReal)
      (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      (∀ x, x ∉ Metric.ball x₀ ρ → v x = 0) →
      eLpNorm v pp volume = eLpNorm v pp (volume.restrict (Metric.ball x₀ ρ)) := by
    intro x₀ ρ pp v hv
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball]
    congr 1
    funext x
    by_cases hx : x ∈ Metric.ball x₀ ρ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hv x hx]
  have hnpow : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ^ (2 : ℝ) = ‖v‖ ^ 2 := by
    intro v
    rw [← Real.rpow_natCast ‖v‖ 2]
    norm_num
  have hofr2 : ENNReal.ofReal 2 = ((2 : NNReal) : ENNReal) := by
    simp [ENNReal.ofReal]
  -- the gradient field of a smooth function: continuity and compact support
  obtain ⟨hgradcs, hcoord, hsqint, hone2⟩ := SmoothGradientFieldL2Facts n
  -- Step 5: the approximation passage, generic in the exponent data.  This is
  -- `SobolevInequalityFromSmoothCase`, whose docstring records the route
  -- (`WeakGradientSmoothApprox`, the smooth case at each `Φ m`, the `L²` limit
  -- on the right and Fatou on the left).
  have hstep5 := SobolevInequalityFromSmoothCase n hn
  -- Step 6: the passage from the plain form to the averaged form, in both cases
  have hstep6 : ∀ (q aa C₁ : ℝ), 1 < q → 0 < C₁ →
      (n : ℝ) * (1 / q - 1 / 2) = aa - 1 →
      (∀ (x₀ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
        (φ : EuclideanSpace ℝ (Fin n) → ℝ)
        (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < ρ → MemW1pOn n 2 (Metric.ball x₀ ρ) φ gφ →
        HasCompactSupport φ → tsupport φ ⊆ Metric.ball x₀ ρ →
        (∫ x in Metric.ball x₀ ρ, |φ x| ^ q) ^ (1 / q)
          ≤ C₁ * ρ ^ aa
            * (∫ x in Metric.ball x₀ ρ, ‖gφ x‖ ^ 2) ^ (1 / 2 : ℝ)) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
        (φ : EuclideanSpace ℝ (Fin n) → ℝ)
        (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < ρ → MemW1pOn n 2 (Metric.ball x₀ ρ) φ gφ →
        HasCompactSupport φ → tsupport φ ⊆ Metric.ball x₀ ρ →
        ((volume (Metric.ball x₀ ρ)).toReal⁻¹
            * ∫ x in Metric.ball x₀ ρ, |φ x| ^ q) ^ (1 / q)
          ≤ C₁ * ω ^ (1 / 2 - 1 / q) * ρ
            * ((volume (Metric.ball x₀ ρ)).toReal⁻¹
                * ∫ x in Metric.ball x₀ ρ, ‖gφ x‖ ^ 2) ^ (1 / 2 : ℝ) := by
    intro q aa C₁ hq1 hC₁0 hexp h8 x₀ ρ φ gφ hρ hW hcs hsupp
    have hq0 : (0 : ℝ) < q := lt_trans one_pos hq1
    have hI0 : (0 : ℝ) ≤ ∫ x in Metric.ball x₀ ρ, |φ x| ^ q :=
      integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
    have hJ0 : (0 : ℝ) ≤ ∫ x in Metric.ball x₀ ρ, ‖gφ x‖ ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    have hBv : (volume (Metric.ball x₀ ρ)).toReal⁻¹ = (ω * ρ ^ n)⁻¹ := by
      rw [hballvol x₀ ρ hρ.le]
    have hBpos : (0 : ℝ) < ω * ρ ^ n := by
      exact mul_pos hω (pow_pos hρ n)
    rw [hBv, Real.mul_rpow (by positivity) hI0,
      Real.mul_rpow (by positivity) hJ0]
    -- the single rpow identity of Step 6
    have hinv : ∀ c : ℝ, ((ω * ρ ^ n)⁻¹) ^ c = ω ^ (-c) * ρ ^ (-((n : ℝ) * c)) := by
      intro c
      rw [Real.inv_rpow hBpos.le, ← Real.rpow_neg hBpos.le,
        Real.mul_rpow hω.le (by positivity), ← Real.rpow_natCast ρ n,
        ← Real.rpow_mul hρ.le]
      congr 2
      ring
    have hkey : ((ω * ρ ^ n)⁻¹) ^ (1 / q) * (C₁ * ρ ^ aa)
        = C₁ * ω ^ (1 / 2 - 1 / q) * ρ * ((ω * ρ ^ n)⁻¹) ^ (1 / 2 : ℝ) := by
      rw [hinv (1 / q), hinv (1 / 2 : ℝ)]
      have hω1 : ω ^ (1 / 2 - 1 / q) * ω ^ (-(1 / 2 : ℝ)) = ω ^ (-(1 / q)) := by
        rw [← Real.rpow_add hω]
        congr 1
        ring
      have hρ1 : ρ ^ (-((n : ℝ) * (1 / q))) * ρ ^ aa
          = ρ * ρ ^ (-((n : ℝ) * (1 / 2 : ℝ))) := by
        have h1 : ρ * ρ ^ (-((n : ℝ) * (1 / 2 : ℝ)))
            = ρ ^ (1 + -((n : ℝ) * (1 / 2 : ℝ))) := by
          rw [Real.rpow_add hρ, Real.rpow_one]
        rw [← Real.rpow_add hρ, h1]
        congr 1
        linarith [hexp]
      calc ω ^ (-(1 / q)) * ρ ^ (-((n : ℝ) * (1 / q))) * (C₁ * ρ ^ aa)
          = C₁ * ω ^ (-(1 / q)) * (ρ ^ (-((n : ℝ) * (1 / q))) * ρ ^ aa) := by ring
        _ = C₁ * (ω ^ (1 / 2 - 1 / q) * ω ^ (-(1 / 2 : ℝ)))
              * (ρ * ρ ^ (-((n : ℝ) * (1 / 2 : ℝ)))) := by rw [hω1, hρ1]
        _ = C₁ * ω ^ (1 / 2 - 1 / q) * ρ
              * (ω ^ (-(1 / 2 : ℝ)) * ρ ^ (-((n : ℝ) * (1 / 2 : ℝ)))) := by ring
    calc ((ω * ρ ^ n)⁻¹) ^ (1 / q)
            * (∫ x in Metric.ball x₀ ρ, |φ x| ^ q) ^ (1 / q)
        ≤ ((ω * ρ ^ n)⁻¹) ^ (1 / q)
            * (C₁ * ρ ^ aa
              * (∫ x in Metric.ball x₀ ρ, ‖gφ x‖ ^ 2) ^ (1 / 2 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (h8 x₀ ρ φ gφ hρ hW hcs hsupp) ?_
          positivity
      _ = (((ω * ρ ^ n)⁻¹) ^ (1 / q) * (C₁ * ρ ^ aa))
            * (∫ x in Metric.ball x₀ ρ, ‖gφ x‖ ^ 2) ^ (1 / 2 : ℝ) := by ring
      _ = C₁ * ω ^ (1 / 2 - 1 / q) * ρ
            * (((ω * ρ ^ n)⁻¹) ^ (1 / 2 : ℝ)
              * (∫ x in Metric.ball x₀ ρ, ‖gφ x‖ ^ 2) ^ (1 / 2 : ℝ)) := by
          rw [hkey]; ring
  -- the two dimensional cases
  rcases eq_or_lt_of_le hn with hn2 | hn3
  · -- `n = 2`: `χ = 2`, `q = 4`, `a = 1/2` (the Ladyzhenskaya case)
    obtain ⟨C₁, hC₁0, hsm⟩ : ∃ C₁ : ℝ, 0 < C₁ ∧
        ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
          (Φ : EuclideanSpace ℝ (Fin n) → ℝ),
          0 < ρ → ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
          tsupport Φ ⊆ Metric.ball x₀ ρ →
          (∫ x in Metric.ball x₀ ρ, |Φ x| ^ (2 * (2 : ℝ))) ^ (1 / (2 * (2 : ℝ)))
            ≤ C₁ * ρ ^ (1 / 2 : ℝ)
              * (∫ x in Metric.ball x₀ ρ,
                  ‖(WithLp.toLp 2 fun i =>
                      fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
                    EuclideanSpace ℝ (Fin n))‖ ^ 2) ^ (1 / 2 : ℝ) :=
      LadyzhenskayaBallInequalityTwo n hn2 ω hω hballvol hdictR hdictV hfdnorm
        hresR hresV hnpow hofr2 hgradcs
    refine ⟨2, C₁ * ω ^ (1 / 2 - 1 / (2 * (2 : ℝ))), by norm_num,
      mul_pos hC₁0 (Real.rpow_pos_of_pos hω _), ?_⟩
    exact hstep6 (2 * (2 : ℝ)) (1 / 2 : ℝ) C₁ (by norm_num) hC₁0
      (by rw [← hn2]; norm_num)
      (hstep5 (2 * (2 : ℝ)) (1 / 2 : ℝ) C₁ (by norm_num) (by norm_num) hC₁0 hsm)
  · -- `n ≥ 3`: `χ = n/(n-2)`, `q = 2n/(n-2)`, `a = 0` (Gagliardo-Nirenberg-Sobolev)
    have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hnm2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    have hq1 : (1 : ℝ) < 2 * ((n : ℝ) / ((n : ℝ) - 2)) := by
      rw [show (2 : ℝ) * ((n : ℝ) / ((n : ℝ) - 2)) = 2 * (n : ℝ) / ((n : ℝ) - 2) from by
        ring, lt_div_iff₀ hnm2]
      linarith
    obtain ⟨C₁, hC₁0, hsm⟩ : ∃ C₁ : ℝ, 0 < C₁ ∧
        ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
          (Φ : EuclideanSpace ℝ (Fin n) → ℝ),
          0 < ρ → ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
          tsupport Φ ⊆ Metric.ball x₀ ρ →
          (∫ x in Metric.ball x₀ ρ, |Φ x| ^ (2 * ((n : ℝ) / ((n : ℝ) - 2))))
              ^ (1 / (2 * ((n : ℝ) / ((n : ℝ) - 2))))
            ≤ C₁ * ρ ^ (0 : ℝ)
              * (∫ x in Metric.ball x₀ ρ,
                  ‖(WithLp.toLp 2 fun i =>
                      fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
                    EuclideanSpace ℝ (Fin n))‖ ^ 2) ^ (1 / 2 : ℝ) := by
      have hq0 : (0 : ℝ) < 2 * ((n : ℝ) / ((n : ℝ) - 2)) := by positivity
      have hCnn0 : (0 : ℝ) ≤ (SNormLESNormFDerivOfEqConst ℝ
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ((2 : NNReal) : ℝ) : ℝ) :=
        NNReal.coe_nonneg _
      refine ⟨(SNormLESNormFDerivOfEqConst ℝ
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ((2 : NNReal) : ℝ) : ℝ) + 1,
        by linarith, ?_⟩
      intro x₀ ρ Φ hρ hΦ hcs hsupp
      obtain ⟨hGc, hGcs, hGsupp⟩ := hgradcs Φ hΦ hcs
      have hΦ0 : ∀ x, x ∉ Metric.ball x₀ ρ → Φ x = 0 := fun x hx =>
        image_eq_zero_of_notMem_tsupport (fun hc => hx (hsupp hc))
      have hG0 : ∀ x, x ∉ Metric.ball x₀ ρ →
          (WithLp.toLp 2 fun i => fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
            EuclideanSpace ℝ (Fin n)) = 0 := fun x hx =>
        hGsupp x (fun hc => hx (hsupp hc))
      have hΦmem : MemLp Φ (ENNReal.ofReal (2 * ((n : ℝ) / ((n : ℝ) - 2))))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
        hΦ.continuous.memLp_of_hasCompactSupport hcs
      have hGmem : MemLp (fun x => (WithLp.toLp 2 fun i =>
            fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
          EuclideanSpace ℝ (Fin n)))
          (ENNReal.ofReal 2) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
        hGc.memLp_of_hasCompactSupport hGcs
      have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
      have hGNS : eLpNorm Φ (ENNReal.ofReal (2 * ((n : ℝ) / ((n : ℝ) - 2)))) volume
          ≤ ((SNormLESNormFDerivOfEqConst ℝ
                (volume : Measure (EuclideanSpace ℝ (Fin n))) ((2 : NNReal) : ℝ) :
              NNReal) : ENNReal)
            * eLpNorm (fderiv ℝ Φ) (ENNReal.ofReal 2) volume := by
        rw [hofr2, show ENNReal.ofReal (2 * ((n : ℝ) / ((n : ℝ) - 2)))
            = ((Real.toNNReal (2 * ((n : ℝ) / ((n : ℝ) - 2))) : NNReal) : ENNReal) from rfl]
        refine eLpNorm_le_eLpNorm_fderiv_of_eq volume (hΦ.of_le (by simp)) hcs
          (by norm_num) ?_ ?_
        · rw [hfr]; omega
        · rw [hfr, Real.coe_toNNReal _ hq0.le]
          have hn0 : (n : ℝ) ≠ 0 := by linarith
          push_cast
          field_simp
      have hmono2 : eLpNorm (fderiv ℝ Φ) (ENNReal.ofReal 2) volume
          ≤ eLpNorm (fun x => (WithLp.toLp 2 fun i =>
              fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
            EuclideanSpace ℝ (Fin n))) (ENNReal.ofReal 2) volume :=
        eLpNorm_mono fun x => hfdnorm Φ x
      have hchain : eLpNorm Φ (ENNReal.ofReal (2 * ((n : ℝ) / ((n : ℝ) - 2)))) volume
          ≤ ((SNormLESNormFDerivOfEqConst ℝ
                (volume : Measure (EuclideanSpace ℝ (Fin n))) ((2 : NNReal) : ℝ) :
              NNReal) : ENNReal)
            * eLpNorm (fun x => (WithLp.toLp 2 fun i =>
                fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
              EuclideanSpace ℝ (Fin n))) (ENNReal.ofReal 2) volume := by
        refine hGNS.trans ?_
        gcongr
      have hrtop : ((SNormLESNormFDerivOfEqConst ℝ
            (volume : Measure (EuclideanSpace ℝ (Fin n))) ((2 : NNReal) : ℝ) :
          NNReal) : ENNReal)
          * eLpNorm (fun x => (WithLp.toLp 2 fun i =>
              fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
            EuclideanSpace ℝ (Fin n))) (ENNReal.ofReal 2) volume ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.coe_ne_top hGmem.eLpNorm_lt_top.ne
      have htr := ENNReal.toReal_mono hrtop hchain
      rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
        hresR x₀ ρ _ Φ hΦ0, hresV x₀ ρ _ _ hG0,
        hdictR _ hq0 _ Φ (hΦmem.restrict _),
        hdictV 2 (by norm_num) _ _ (hGmem.restrict _)] at htr
      refine htr.trans ?_
      rw [Real.rpow_zero, mul_one]
      have hJ : (∫ x in Metric.ball x₀ ρ,
            ‖(WithLp.toLp 2 fun i => fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
              EuclideanSpace ℝ (Fin n))‖ ^ (2 : ℝ))
          = ∫ x in Metric.ball x₀ ρ,
            ‖(WithLp.toLp 2 fun i => fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
              EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact hnpow _
      rw [hJ]
      refine mul_le_mul_of_nonneg_right (by linarith) ?_
      refine Real.rpow_nonneg ?_ _
      exact integral_nonneg fun x => sq_nonneg _
    refine ⟨(n : ℝ) / ((n : ℝ) - 2),
      C₁ * ω ^ (1 / 2 - 1 / (2 * ((n : ℝ) / ((n : ℝ) - 2)))), ?_,
      mul_pos hC₁0 (Real.rpow_pos_of_pos hω _), ?_⟩
    · rw [lt_div_iff₀ hnm2]
      linarith
    · refine hstep6 (2 * ((n : ℝ) / ((n : ℝ) - 2))) (0 : ℝ) C₁ hq1 hC₁0 ?_
        (hstep5 (2 * ((n : ℝ) / ((n : ℝ) - 2))) (0 : ℝ) C₁ hq1 le_rfl hC₁0 hsm)
      field_simp
      ring
