import ManfrediThesis.Preamble
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
set_option maxHeartbeats 1600000
open MeasureTheory

/-- The Ladyzhenskaya inequality on a ball in dimension `n = 2`: there is a
constant `C₁ > 0` such that every smooth `Φ` with compact support inside
`B_ρ(x₀)` satisfies
`‖Φ‖_{L⁴(B_ρ)} ≤ C₁ρ^{1/2}‖∇Φ‖_{L²(B_ρ)}`.

Conventions, restated here because a helper inherits none of its parent's.
`supp Φ` denotes the CLOSED support, so the support hypothesis is
`tsupport Φ ⊆ B_ρ(x₀)`; the gradient of `Φ` is the `EuclideanSpace`-valued
field `x ↦ (D_iΦ(x))_i` assembled by `WithLp.toLp 2`, which is how the parent
and its consumers write it, and `‖·‖` on it is the Euclidean norm; the
exponents are real, so `|Φ|^{2·2}` and the outer power `1/(2·2)` are
`Real.rpow`, and `ω` is the volume of the unit ball of `ℝⁿ`.  In dimension `2`
there is no Sobolev exponent --- `n/(n-2)` is undefined --- which is why the
inequality is stated at the fixed exponent `4 = 2·2` with the scaling factor
`ρ^{1/2}` rather than at a dimensional exponent with no scaling, and why this
case has to be built by hand instead of read off a single Sobolev embedding.

The hypotheses are all dimension-free plumbing the parent has already set up:
the volume identity for balls, the two dictionary lemmas converting `eLpNorm`
to an explicit integral for a scalar and for a vector field, the comparison
between the operator norm of `fderiv` and the norm of the assembled gradient,
the two restriction lemmas for a function vanishing off the ball, the
coincidence of the real and natural second powers of a norm, the identification
of `ENNReal.ofReal 2` with the coerced `(2 : NNReal)`, and the continuity,
compact support and vanishing of the assembled gradient of a smooth compactly
supported function.

The route is Step 4 of the parent's argument, specialised to `n = 2`.  (4a) The
Ladyzhenskaya step: Mathlib's Gagliardo--Nirenberg--Sobolev inequality in the
borderline form, applied to `Φ` and then to `Φ²`, gives
`‖Φ‖_{L⁴}² = ‖Φ²‖_{L²} ≤ c‖∇(Φ²)‖_{L¹} = 2c‖Φ∇Φ‖_{L¹}`, and Cauchy--Schwarz
on the right bounds that by `2c‖Φ‖_{L²}‖∇Φ‖_{L²}`.  (4b) The Poincaré step:
because `Φ` vanishes off `B_ρ(x₀)`, `‖Φ‖_{L²(B_ρ)} ≤ Cρ‖∇Φ‖_{L²(B_ρ)}`, which
on a ball follows from the same borderline inequality together with the volume
identity `|B_ρ| = ωρ²`.  (4c) Combining, `‖Φ‖_{L⁴}² ≤ C'ρ‖∇Φ‖_{L²}²`, and
taking square roots gives the asserted `ρ^{1/2}`.  Every passage between
`eLpNorm` and an explicit integral is one of the two dictionary hypotheses, and
every passage between the whole space and the ball is one of the two
restriction hypotheses. -/
theorem LadyzhenskayaBallInequalityTwo :
    ∀ (n : ℕ), 2 = n → ∀ ω : ℝ, 0 < ω →
      (∀ (y : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 ≤ r →
        (volume (Metric.ball y r)).toReal = ω * r ^ n) →
      (∀ (r : ℝ), 0 < r → ∀ (S : Set (EuclideanSpace ℝ (Fin n)))
        (v : EuclideanSpace ℝ (Fin n) → ℝ),
        MemLp v (ENNReal.ofReal r) (volume.restrict S) →
        (eLpNorm v (ENNReal.ofReal r) (volume.restrict S)).toReal
          = (∫ x in S, |v x| ^ r) ^ (1 / r)) →
      (∀ (r : ℝ), 0 < r → ∀ (S : Set (EuclideanSpace ℝ (Fin n)))
        (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        MemLp v (ENNReal.ofReal r) (volume.restrict S) →
        (eLpNorm v (ENNReal.ofReal r) (volume.restrict S)).toReal
          = (∫ x in S, ‖v x‖ ^ r) ^ (1 / r)) →
      (∀ (Φ : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)),
        ‖fderiv ℝ Φ x‖
          ≤ ‖(WithLp.toLp 2 fun i =>
              fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
            EuclideanSpace ℝ (Fin n))‖) →
      (∀ (x₀ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (pp : ENNReal)
        (v : EuclideanSpace ℝ (Fin n) → ℝ),
        (∀ x, x ∉ Metric.ball x₀ ρ → v x = 0) →
        eLpNorm v pp volume = eLpNorm v pp (volume.restrict (Metric.ball x₀ ρ))) →
      (∀ (x₀ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (pp : ENNReal)
        (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        (∀ x, x ∉ Metric.ball x₀ ρ → v x = 0) →
        eLpNorm v pp volume = eLpNorm v pp (volume.restrict (Metric.ball x₀ ρ))) →
      (∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ^ (2 : ℝ) = ‖v‖ ^ 2) →
      ENNReal.ofReal 2 = ((2 : NNReal) : ENNReal) →
      (∀ Φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) Φ →
        HasCompactSupport Φ →
        Continuous (fun x => (WithLp.toLp 2 fun i =>
            fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
          EuclideanSpace ℝ (Fin n)))
        ∧ HasCompactSupport (fun x => (WithLp.toLp 2 fun i =>
            fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
          EuclideanSpace ℝ (Fin n)))
        ∧ ∀ x, x ∉ tsupport Φ →
            (WithLp.toLp 2 fun i => fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
              EuclideanSpace ℝ (Fin n)) = 0) →
      ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
      (Φ : EuclideanSpace ℝ (Fin n) → ℝ),
      0 < ρ → ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      tsupport Φ ⊆ Metric.ball x₀ ρ →
      (∫ x in Metric.ball x₀ ρ, |Φ x| ^ (2 * (2 : ℝ))) ^ (1 / (2 * (2 : ℝ)))
      ≤ C₁ * ρ ^ (1 / 2 : ℝ)
      * (∫ x in Metric.ball x₀ ρ,
      ‖(WithLp.toLp 2 fun i =>
      fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2) ^ (1 / 2 : ℝ) := by
  intro n hn2 ω hω hballvol hdictR hdictV hfdnorm hresR hresV hnpow hofr2 hgradcs
  have hconj : Real.HolderConjugate (2 : ℝ) (2 : ℝ) :=
    Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have hc0 : (0 : ℝ) ≤ (SNormLESNormFDerivOfEqConst ℝ
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ((1 : NNReal) : ℝ) : ℝ) :=
    NNReal.coe_nonneg _
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  have hone1 : (1 : ENNReal) ≤ ENNReal.ofReal 1 := by
    rw [ENNReal.one_le_ofReal]
  have h1ne : (ENNReal.ofReal 1) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; norm_num
  have hofr1 : ENNReal.ofReal 1 = ((1 : NNReal) : ENNReal) := by
    simp [ENNReal.ofReal]
  refine ⟨Real.sqrt 2 * (SNormLESNormFDerivOfEqConst ℝ
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ((1 : NNReal) : ℝ) : ℝ)
      * ω ^ (1 / 4 : ℝ) + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ Real.sqrt 2 * (SNormLESNormFDerivOfEqConst ℝ
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ((1 : NNReal) : ℝ) : ℝ)
        * ω ^ (1 / 4 : ℝ) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hc0) (Real.rpow_nonneg hω.le _)
    linarith
  intro x₀ ρ Φ hρ hΦ hcs hsupp
  simp only [show (2 : ℝ) * 2 = 4 from by norm_num]
  obtain ⟨hGc, hGcs, hGsupp⟩ := hgradcs Φ hΦ hcs
  have hΦ0 : ∀ x, x ∉ Metric.ball x₀ ρ → Φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hc => hx (hsupp hc))
  have hG0 : ∀ x, x ∉ Metric.ball x₀ ρ →
      (WithLp.toLp 2 fun i => fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
        EuclideanSpace ℝ (Fin n)) = 0 := fun x hx =>
    hGsupp x (fun hc => hx (hsupp hc))
  have hBfin : IsFiniteMeasure (volume.restrict (Metric.ball x₀ ρ)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  -- the four `MemLp` facts on the ball
  have hΦmemB : ∀ r : ℝ, 0 < r →
      MemLp Φ (ENNReal.ofReal r) (volume.restrict (Metric.ball x₀ ρ)) := fun r _ =>
    (hΦ.continuous.memLp_of_hasCompactSupport
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hcs).restrict _
  have hGmemB : ∀ r : ℝ, 0 < r →
      MemLp (fun x => (WithLp.toLp 2 fun i =>
          fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
        EuclideanSpace ℝ (Fin n))) (ENNReal.ofReal r)
        (volume.restrict (Metric.ball x₀ ρ)) := fun r _ =>
    (hGc.memLp_of_hasCompactSupport
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hGcs).restrict _
  have h1memB : MemLp (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))
      (ENNReal.ofReal 2) (volume.restrict (Metric.ball x₀ ρ)) := memLp_const 1
  -- the three nonnegative quantities
  have hP20 : (0 : ℝ) ≤ ∫ x in Metric.ball x₀ ρ, |Φ x| ^ (2 : ℝ) :=
    integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
  have hJ0 : (0 : ℝ) ≤ ∫ x in Metric.ball x₀ ρ,
      ‖(WithLp.toLp 2 fun i => fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
        EuclideanSpace ℝ (Fin n))‖ ^ (2 : ℝ) :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hP40 : (0 : ℝ) ≤ ∫ x in Metric.ball x₀ ρ, |Φ x| ^ (4 : ℝ) :=
    integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
  -- (4b) the Poincaré step: `‖Φ‖_{L²} ≤ c |B|^{1/2} ‖G‖_{L²}`
  have hD : (∫ x in Metric.ball x₀ ρ, |Φ x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (SNormLESNormFDerivOfEqConst ℝ
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ((1 : NNReal) : ℝ) : ℝ)
        * ((volume (Metric.ball x₀ ρ)).toReal ^ (1 / 2 : ℝ)
          * (∫ x in Metric.ball x₀ ρ,
              ‖(WithLp.toLp 2 fun i =>
                  fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
                EuclideanSpace ℝ (Fin n))‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
    have hGmemVol : MemLp (fun x => (WithLp.toLp 2 fun i =>
          fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
        EuclideanSpace ℝ (Fin n))) (ENNReal.ofReal 1)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      hGc.memLp_of_hasCompactSupport hGcs
    have hGNS : eLpNorm Φ (ENNReal.ofReal 2) volume
        ≤ ((SNormLESNormFDerivOfEqConst ℝ
              (volume : Measure (EuclideanSpace ℝ (Fin n))) ((1 : NNReal) : ℝ) :
            NNReal) : ENNReal)
          * eLpNorm (fderiv ℝ Φ) (ENNReal.ofReal 1) volume := by
      rw [hofr1, hofr2]
      exact eLpNorm_le_eLpNorm_fderiv_of_eq volume (hΦ.of_le (by simp)) hcs
        le_rfl (by rw [hfr]; omega)
        (by rw [hfr, ← hn2]; push_cast; norm_num)
    have hcomb : eLpNorm Φ (ENNReal.ofReal 2) volume
        ≤ ((SNormLESNormFDerivOfEqConst ℝ
              (volume : Measure (EuclideanSpace ℝ (Fin n))) ((1 : NNReal) : ℝ) :
            NNReal) : ENNReal)
          * eLpNorm (fun x => (WithLp.toLp 2 fun i =>
              fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
            EuclideanSpace ℝ (Fin n))) (ENNReal.ofReal 1) volume :=
      hGNS.trans (mul_le_mul' le_rfl (eLpNorm_mono fun x => hfdnorm Φ x))
    rw [hresR x₀ ρ _ Φ hΦ0, hresV x₀ ρ _ _ hG0] at hcomb
    have htr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (hGmemVol.restrict _).eLpNorm_lt_top.ne) hcomb
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
      hdictR 2 (by norm_num) _ Φ (hΦmemB 2 (by norm_num)),
      hdictV 1 one_pos _ _ (hGmemVol.restrict _)] at htr
    refine htr.trans ?_
    have he1 : (∫ x in Metric.ball x₀ ρ,
          ‖(WithLp.toLp 2 fun i => fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
            EuclideanSpace ℝ (Fin n))‖ ^ (1 : ℝ)) ^ (1 / 1 : ℝ)
        = ∫ x in Metric.ball x₀ ρ,
          ‖(WithLp.toLp 2 fun i => fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
            EuclideanSpace ℝ (Fin n))‖ := by
      norm_num
    rw [he1]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    -- Hölder at the conjugate pair `(2,2)` with the constant function `1`
    have hhol := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume.restrict (Metric.ball x₀ ρ)) hconj
      (f := fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))
      (g := fun x => ‖(WithLp.toLp 2 fun i =>
          fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
        EuclideanSpace ℝ (Fin n))‖)
      (Filter.Eventually.of_forall fun x => zero_le_one)
      (Filter.Eventually.of_forall fun x => norm_nonneg _)
      h1memB ((hGmemB 2 (by norm_num)).norm)
    simp only [one_mul, Real.one_rpow, setIntegral_const] at hhol
    rw [show ((volume.real (Metric.ball x₀ ρ)) • (1 : ℝ))
        = (volume (Metric.ball x₀ ρ)).toReal from by
      simp [MeasureTheory.measureReal_def]] at hhol
    exact hhol
  -- (4a) the Ladyzhenskaya step: `‖Φ²‖_{L²} ≤ 2c ‖Φ‖_{L²} ‖G‖_{L²}`
  have hA : (∫ x in Metric.ball x₀ ρ, |Φ x| ^ (4 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ 2 * (SNormLESNormFDerivOfEqConst ℝ
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ((1 : NNReal) : ℝ) : ℝ)
        * ((∫ x in Metric.ball x₀ ρ, |Φ x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
          * (∫ x in Metric.ball x₀ ρ,
              ‖(WithLp.toLp 2 fun i =>
                  fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
                EuclideanSpace ℝ (Fin n))‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
    have hΦ2sm : ContDiff ℝ (⊤ : ℕ∞) (fun x => Φ x * Φ x) := hΦ.mul hΦ
    have hΦ2cs : HasCompactSupport (fun x => Φ x * Φ x) := hcs.mul_right
    have hΦ20 : ∀ x, x ∉ Metric.ball x₀ ρ → Φ x * Φ x = 0 := by
      intro x hx
      rw [hΦ0 x hx, mul_zero]
    have hfd2 : ∀ x, fderiv ℝ (fun y => Φ y * Φ y) x = (2 * Φ x) • fderiv ℝ Φ x := by
      intro x
      have hd : HasFDerivAt Φ (fderiv ℝ Φ x) x :=
        ((hΦ.differentiable (by simp)) x).hasFDerivAt
      have h : HasFDerivAt (fun y => Φ y * Φ y)
          (Φ x • fderiv ℝ Φ x + Φ x • fderiv ℝ Φ x) x := hd.mul hd
      rw [h.fderiv, ← add_smul]
      congr 1
      ring
    have hptw : ∀ x, ‖fderiv ℝ (fun y => Φ y * Φ y) x‖
        ≤ 2 * (|Φ x| * ‖(WithLp.toLp 2 fun i =>
            fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
          EuclideanSpace ℝ (Fin n))‖) := by
      intro x
      rw [hfd2 x, norm_smul, Real.norm_eq_abs, abs_mul,
        show |(2 : ℝ)| = 2 from by norm_num, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hfdnorm Φ x) (abs_nonneg _)) (by norm_num)
    have hBmemVol : MemLp (fun x => 2 * (|Φ x| * ‖(WithLp.toLp 2 fun i =>
            fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
          EuclideanSpace ℝ (Fin n))‖)) (ENNReal.ofReal 1)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      refine Continuous.memLp_of_hasCompactSupport ?_ ?_
      · exact (continuous_const.mul (hΦ.continuous.abs.mul hGc.norm))
      · refine HasCompactSupport.mul_left ?_
        refine HasCompactSupport.mul_right ?_
        exact hcs.comp_left (g := fun t : ℝ => |t|) (by simp)
    have hΦ2memVol : MemLp (fun x => Φ x * Φ x) (ENNReal.ofReal 2)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      hΦ2sm.continuous.memLp_of_hasCompactSupport hΦ2cs
    have hGNS : eLpNorm (fun x => Φ x * Φ x) (ENNReal.ofReal 2) volume
        ≤ ((SNormLESNormFDerivOfEqConst ℝ
              (volume : Measure (EuclideanSpace ℝ (Fin n))) ((1 : NNReal) : ℝ) :
            NNReal) : ENNReal)
          * eLpNorm (fderiv ℝ (fun x => Φ x * Φ x)) (ENNReal.ofReal 1) volume := by
      rw [hofr1, hofr2]
      exact eLpNorm_le_eLpNorm_fderiv_of_eq volume (hΦ2sm.of_le (by simp)) hΦ2cs
        le_rfl (by rw [hfr]; omega)
        (by rw [hfr, ← hn2]; push_cast; norm_num)
    have hcomb : eLpNorm (fun x => Φ x * Φ x) (ENNReal.ofReal 2) volume
        ≤ ((SNormLESNormFDerivOfEqConst ℝ
              (volume : Measure (EuclideanSpace ℝ (Fin n))) ((1 : NNReal) : ℝ) :
            NNReal) : ENNReal)
          * eLpNorm (fun x => 2 * (|Φ x| * ‖(WithLp.toLp 2 fun i =>
              fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
            EuclideanSpace ℝ (Fin n))‖)) (ENNReal.ofReal 1) volume :=
      hGNS.trans (mul_le_mul' le_rfl (eLpNorm_mono_real hptw))
    rw [hresR x₀ ρ _ _ hΦ20, hresR x₀ ρ _ _ (by
      intro x hx
      rw [hΦ0 x hx, hG0 x hx]
      simp)] at hcomb
    have htr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (hBmemVol.restrict _).eLpNorm_lt_top.ne) hcomb
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
      hdictR 2 (by norm_num) _ _ (hΦ2memVol.restrict _),
      hdictR 1 one_pos _ _ (hBmemVol.restrict _)] at htr
    have hL : (∫ x in Metric.ball x₀ ρ, |Φ x * Φ x| ^ (2 : ℝ))
        = ∫ x in Metric.ball x₀ ρ, |Φ x| ^ (4 : ℝ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show |Φ x * Φ x| ^ (2 : ℝ) = |Φ x| ^ (4 : ℝ)
      rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _),
        ← Real.rpow_add' (abs_nonneg _) (by norm_num : (2 : ℝ) + 2 ≠ 0)]
      norm_num
    have hR : (∫ x in Metric.ball x₀ ρ, |2 * (|Φ x| * ‖(WithLp.toLp 2 fun i =>
            fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
          EuclideanSpace ℝ (Fin n))‖)| ^ (1 : ℝ)) ^ (1 / 1 : ℝ)
        = 2 * ∫ x in Metric.ball x₀ ρ, |Φ x| * ‖(WithLp.toLp 2 fun i =>
            fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
          EuclideanSpace ℝ (Fin n))‖ := by
      rw [show (1 / 1 : ℝ) = 1 from by norm_num, Real.rpow_one]
      rw [show (fun x => |2 * (|Φ x| * ‖(WithLp.toLp 2 fun i =>
              fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
            EuclideanSpace ℝ (Fin n))‖)| ^ (1 : ℝ))
          = fun x => 2 * (|Φ x| * ‖(WithLp.toLp 2 fun i =>
              fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
            EuclideanSpace ℝ (Fin n))‖) from by
        funext x
        rw [Real.rpow_one, abs_of_nonneg (by positivity)]]
      exact integral_const_mul _ _
    rw [hL, hR] at htr
    refine htr.trans ?_
    have hhol := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume.restrict (Metric.ball x₀ ρ)) hconj
      (f := fun x => |Φ x|)
      (g := fun x => ‖(WithLp.toLp 2 fun i =>
          fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
        EuclideanSpace ℝ (Fin n))‖)
      (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (Filter.Eventually.of_forall fun x => norm_nonneg _)
      (by
        have h := (hΦmemB 2 (by norm_num)).norm
        simpa only [Real.norm_eq_abs] using h)
      ((hGmemB 2 (by norm_num)).norm)
    rw [show (SNormLESNormFDerivOfEqConst ℝ
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ((1 : NNReal) : ℝ) : ℝ)
        * (2 * ∫ x in Metric.ball x₀ ρ, |Φ x| * ‖(WithLp.toLp 2 fun i =>
            fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
          EuclideanSpace ℝ (Fin n))‖)
        = 2 * (SNormLESNormFDerivOfEqConst ℝ
            (volume : Measure (EuclideanSpace ℝ (Fin n))) ((1 : NNReal) : ℝ) : ℝ)
          * (∫ x in Metric.ball x₀ ρ, |Φ x| * ‖(WithLp.toLp 2 fun i =>
              fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
            EuclideanSpace ℝ (Fin n))‖) from by ring]
    refine mul_le_mul_of_nonneg_left hhol ?_
    have : (0:ℝ) ≤ (SNormLESNormFDerivOfEqConst ℝ
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ((1 : NNReal) : ℝ) : ℝ) := hc0
    linarith
  -- (4c) combining
  have hnpow2 : (∫ x in Metric.ball x₀ ρ,
        ‖(WithLp.toLp 2 fun i => fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
          EuclideanSpace ℝ (Fin n))‖ ^ 2)
      = ∫ x in Metric.ball x₀ ρ,
        ‖(WithLp.toLp 2 fun i => fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
          EuclideanSpace ℝ (Fin n))‖ ^ (2 : ℝ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => (hnpow _).symm)
  rw [hnpow2]
  set cc : ℝ := (SNormLESNormFDerivOfEqConst ℝ
    (volume : Measure (EuclideanSpace ℝ (Fin n))) ((1 : NNReal) : ℝ) : ℝ) with hccdef
  set Jh : ℝ := (∫ x in Metric.ball x₀ ρ,
    ‖(WithLp.toLp 2 fun i => fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
      EuclideanSpace ℝ (Fin n))‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) with hJhdef
  set P2 : ℝ := (∫ x in Metric.ball x₀ ρ, |Φ x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) with hP2def
  set I4 : ℝ := ∫ x in Metric.ball x₀ ρ, |Φ x| ^ (4 : ℝ) with hI4def
  have hJh0 : (0 : ℝ) ≤ Jh := by rw [hJhdef]; exact Real.rpow_nonneg hJ0 _
  have hmBr : (volume (Metric.ball x₀ ρ)).toReal ^ (1 / 2 : ℝ)
      = ω ^ (1 / 2 : ℝ) * ρ := by
    rw [hballvol x₀ ρ hρ.le, ← hn2,
      show (ρ : ℝ) ^ (2 : ℕ) = ρ ^ (2 : ℝ) from by
        rw [← Real.rpow_natCast ρ 2]; norm_num,
      Real.mul_rpow hω.le (Real.rpow_nonneg hρ.le _), ← Real.rpow_mul hρ.le]
    norm_num
  have hD0 : (0 : ℝ) ≤ Real.sqrt 2 * cc * ω ^ (1 / 4 : ℝ) * (ρ ^ (1 / 2 : ℝ) * Jh) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) ?_)
      (Real.rpow_nonneg hω.le _)) (mul_nonneg (Real.rpow_nonneg hρ.le _) hJh0)
    rw [hccdef]; exact hc0
  have hstep : I4 ^ (1 / 2 : ℝ)
      ≤ (Real.sqrt 2 * cc * ω ^ (1 / 4 : ℝ) * (ρ ^ (1 / 2 : ℝ) * Jh)) ^ 2 := by
    have h1 : I4 ^ (1 / 2 : ℝ)
        ≤ 2 * cc * ((cc * ((volume (Metric.ball x₀ ρ)).toReal ^ (1 / 2 : ℝ) * Jh))
          * Jh) := by
      refine hA.trans ?_
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hD hJh0) ?_
      have : (0 : ℝ) ≤ cc := by rw [hccdef]; exact hc0
      linarith
    refine h1.trans_eq ?_
    have e1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have e2 : (ω ^ (1 / 4 : ℝ)) ^ 2 = ω ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast (ω ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hω.le]
      norm_num
    have e3 : (ρ ^ (1 / 2 : ℝ)) ^ 2 = ρ := by
      rw [← Real.rpow_natCast (ρ ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hρ.le]
      norm_num
    rw [hmBr, show (Real.sqrt 2 * cc * ω ^ (1 / 4 : ℝ) * (ρ ^ (1 / 2 : ℝ) * Jh)) ^ 2
        = Real.sqrt 2 ^ 2 * cc ^ 2 * (ω ^ (1 / 4 : ℝ)) ^ 2
          * ((ρ ^ (1 / 2 : ℝ)) ^ 2 * Jh ^ 2) from by ring, e1, e2, e3]
    ring
  have hfin : I4 ^ (1 / 4 : ℝ)
      ≤ Real.sqrt 2 * cc * ω ^ (1 / 4 : ℝ) * (ρ ^ (1 / 2 : ℝ) * Jh) := by
    have h2 : I4 ^ (1 / 4 : ℝ) = (I4 ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_mul hP40]
      norm_num
    rw [h2]
    refine (Real.rpow_le_rpow (Real.rpow_nonneg hP40 _) hstep (by norm_num)).trans_eq ?_
    rw [← Real.rpow_natCast
        (Real.sqrt 2 * cc * ω ^ (1 / 4 : ℝ) * (ρ ^ (1 / 2 : ℝ) * Jh)) 2,
      ← Real.rpow_mul hD0]
    norm_num
  refine hfin.trans ?_
  rw [show (Real.sqrt 2 * cc * ω ^ (1 / 4 : ℝ) + 1) * ρ ^ (1 / 2 : ℝ) * Jh
      = (Real.sqrt 2 * cc * ω ^ (1 / 4 : ℝ) + 1) * (ρ ^ (1 / 2 : ℝ) * Jh) from by ring]
  exact mul_le_mul_of_nonneg_right (by linarith)
    (mul_nonneg (Real.rpow_nonneg hρ.le _) hJh0)
