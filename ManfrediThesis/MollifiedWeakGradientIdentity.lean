import ManfrediThesis.Preamble
import ManfrediThesis.HasWeakGradientOn
set_option maxHeartbeats 400000
open MeasureTheory

/-- On the inner region, differentiating a mollification gives the mollification
of the zero-extended weak gradient:
`D_i(φ ∗ ρ)(x) = (1_Ω D_iφ) ∗ ρ (x)`
whenever the closed ball of the mollifier's radius around `x` lies in `Ω`.

Conventions, restated here because a helper inherits none of its parent's.
`φ ∗ ρ` is Mathlib's `convolution φ ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume`,
i.e. `(φ ∗ ρ)(x) = ∫ φ(y)ρ(x - y)dy`; `supp ρ` is the CLOSED support, and the
hypothesis `supp ρ = closedBall 0 d` is what fixes the mollifier's radius `d`.
`D_i` is the derivative in the direction of the `i`-th standard basis vector,
written `fderiv ℝ · x (EuclideanSpace.single i 1)`.  `gφ` is a weak gradient of
`φ` on `Ω` in the sense of `HasWeakGradientOn`, which is an identity against
smooth test functions compactly supported in `Ω` and says nothing about `φ`
off `Ω`; the zero extension `1_Ω D_iφ`, written `Ω.indicator (fun z => gφ z i)`,
is therefore the right integrand globally, and it is what makes the right-hand
convolution well defined even though `gφ` is only controlled on `Ω`.  The
hypothesis `LocallyIntegrable φ volume` is about `φ` on all of `ℝⁿ` and is what
makes the left-hand convolution differentiable.

The route has three steps.  (A) Because `ρ` is smooth with compact support and
`φ` is locally integrable, the convolution `φ ∗ ρ` is differentiable and its
derivative is the convolution against `dρ`, so
`D_i(φ ∗ ρ)(x) = ∫ φ(y)(dρ(x - y)e_i)dy`.  (B) The integrand vanishes off `Ω`:
for `y ∉ Ω` the containment `closedBall x d ⊆ Ω` forces `d < ‖x - y‖`, hence
`ρ(x - y) = 0` and `dρ(x - y) = 0`, since both vanish off `supp ρ = closedBall 0 d`.
So the integral may be restricted to `Ω`.  (C) On `Ω` the test function
`y ↦ ρ(x - y)` is smooth with compact support inside `Ω` --- its support is
contained in `closedBall x d` --- so it is an admissible test function for
`HasWeakGradientOn`, whose identity in the direction `i` converts
`∫_Ω φ(y)(dρ(x - y)e_i)dy` into `-∫_Ω gφ(y)_i ρ(x - y)dy` up to the sign
carried by differentiating `y ↦ ρ(x - y)`.  Re-extending that integral from `Ω`
to `ℝⁿ` through the indicator, which changes nothing because the indicator
vanishes off `Ω`, is the asserted right-hand convolution. -/
theorem MollifiedWeakGradientIdentity :
    ∀ (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))), IsOpen Ω →
      ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ)
        (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        HasWeakGradientOn n Ω φ gφ → LocallyIntegrable φ volume →
      ∀ (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (d : ℝ),
        ContDiff ℝ (⊤ : ℕ∞) ρ → HasCompactSupport ρ →
        tsupport ρ = Metric.closedBall 0 d →
      ∀ x : EuclideanSpace ℝ (Fin n), Metric.closedBall x d ⊆ Ω → ∀ i : Fin n,
        fderiv ℝ (convolution φ ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
            (EuclideanSpace.single i (1 : ℝ))
          = convolution (Ω.indicator (fun z => gφ z i)) ρ
              (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  intro n Ω hΩ φ gφ hwg hφloc ρ d hρsm hρcs hρts x hball i
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hdρc : Continuous (fderiv ℝ ρ) := hρsm.continuous_fderiv (by simp)
  have hdρcs : HasCompactSupport (fderiv ℝ ρ) := hρcs.fderiv ℝ
  -- Step A/B: the derivative of the convolution, applied to eᵢ
  have hce : ConvolutionExists φ (fderiv ℝ ρ)
      (ContinuousLinearMap.precompR (EuclideanSpace ℝ (Fin n))
        (ContinuousLinearMap.lsmul ℝ ℝ)) volume :=
    hdρcs.convolutionExists_right _ hφloc hdρc
  have hFD := hρcs.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    hφloc (hρsm.of_le (by simp)) x
  have hB : fderiv ℝ (convolution φ ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
      (EuclideanSpace.single i (1 : ℝ))
      = ∫ y, φ y * (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)) := by
    have hc := ContinuousLinearMap.integral_comp_comm
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))) (hce x)
    simp only [ContinuousLinearMap.apply_apply] at hc
    rw [hFD.fderiv, convolution_def, ← hc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [ContinuousLinearMap.precompR_apply]
  -- Step C: the translated kernel is a test function for Ω
  have hψsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => ρ (x - y)) :=
    hρsm.comp (contDiff_const.sub contDiff_id)
  have hρvan : ∀ z : EuclideanSpace ℝ (Fin n), d < ‖z‖ → ρ z = 0 ∧ fderiv ℝ ρ z = 0 := by
    intro z hz
    have hzn : z ∉ tsupport ρ := by
      rw [hρts]; simpa using not_le.2 hz
    exact ⟨image_eq_zero_of_notMem_tsupport hzn, fderiv_of_notMem_tsupport ℝ hzn⟩
  have hnormsub : ∀ y : EuclideanSpace ℝ (Fin n), ‖x - y‖ = dist y x := by
    intro y; rw [dist_eq_norm, ← norm_neg]; simp
  have hψts : tsupport (fun y => ρ (x - y)) ⊆ Metric.closedBall x d := by
    refine closure_minimal (fun y hy => ?_) Metric.isClosed_closedBall
    by_contra hy'
    have hgt : d < ‖x - y‖ := by
      rw [hnormsub y]
      simpa using hy'
    exact hy (hρvan _ hgt).1
  have hψcs : HasCompactSupport (fun y => ρ (x - y)) :=
    IsCompact.of_isClosed_subset (isCompact_closedBall x d) (isClosed_tsupport _) hψts
  have hψΩ : tsupport (fun y => ρ (x - y)) ⊆ Ω := hψts.trans hball
  have hψd : ∀ y, fderiv ℝ (fun y' => ρ (x - y')) y (EuclideanSpace.single i (1 : ℝ))
      = -((fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ))) := by
    intro y
    have h1 : HasFDerivAt (fun y' : EuclideanSpace ℝ (Fin n) => x - y')
        (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y :=
      (hasFDerivAt_id y).const_sub x
    have h2 : HasFDerivAt ρ (fderiv ℝ ρ (x - y)) (x - y) :=
      (hρsm.differentiable (by simp) (x - y)).hasFDerivAt
    have h3 : HasFDerivAt (fun y' => ρ (x - y'))
        ((fderiv ℝ ρ (x - y)).comp
          (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) y :=
      h2.comp y h1
    rw [h3.fderiv]
    simp
  have hWG := hwg (fun y => ρ (x - y)) hψsm hψcs hψΩ i
  have hL : (∫ y in Ω, φ y *
        fderiv ℝ (fun y' => ρ (x - y')) y (EuclideanSpace.single i (1 : ℝ)))
      = -∫ y in Ω, φ y * (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun hΩm fun y _ => ?_
    rw [hψd y]; ring
  rw [hL] at hWG
  have hC : (∫ y in Ω, φ y * (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)))
      = ∫ y in Ω, gφ y i * ρ (x - y) := neg_inj.1 hWG
  -- Step D: both integrals over Ω agree with the integrals over ℝⁿ
  have hvanΩ : ∀ y : EuclideanSpace ℝ (Fin n), y ∉ Ω → d < ‖x - y‖ := by
    intro y hy
    by_contra h
    refine hy (hball ?_)
    rw [Metric.mem_closedBall]
    rw [← hnormsub y]
    exact not_lt.1 h
  have hLfull : (∫ y in Ω, φ y * (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)))
      = ∫ y, φ y * (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    rw [(hρvan _ (hvanΩ y hy)).2]; simp
  have hRfull : (∫ y in Ω, gφ y i * ρ (x - y))
      = ∫ y, Ω.indicator (fun z => gφ z i) y * ρ (x - y) := by
    rw [show (∫ y in Ω, gφ y i * ρ (x - y))
        = ∫ y in Ω, Ω.indicator (fun z => gφ z i) y * ρ (x - y) from
      setIntegral_congr_fun hΩm fun y hy => by rw [Set.indicator_of_mem hy]]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    rw [Set.indicator_of_notMem hy]; simp
  rw [hB, ← hLfull, hC, hRfull, convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [ContinuousLinearMap.lsmul_apply]
