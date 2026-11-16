import ManfrediThesis.Preamble
set_option maxHeartbeats 400000
open MeasureTheory

/-- Young's inequality at the `L¹` end: convolution against a probability
density contracts the `L^q` seminorm.  If `ρ` is continuous, nonnegative,
compactly supported and of unit mass, and `w ∈ L^q`, then
`‖w ∗ ρ‖_{L^q} ≤ ‖w‖_{L^q}` for every real `q ≥ 1`.

Conventions, restated here because a helper inherits none of its parent's.
`w ∗ ρ` is Mathlib's `convolution w ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume`,
i.e. `(w ∗ ρ)(x) = ∫ w(y)ρ(x - y)dy`, and the exponent is `ENNReal.ofReal q`
throughout, so `eLpNorm` is the `L^q` seminorm of the real `q ≥ 1`.  `supp ρ`
means the CLOSED support, and compact support enters only through the
integrability of `ρ`.  No smoothness of `ρ` is needed: continuity,
nonnegativity, compact support and `∫ρ = 1` are the whole hypothesis, and the
`L^q` membership of `w` is used only to name a strongly measurable
representative.

The route.  First replace `w` by a strongly measurable `w'` with `w = w'`
almost everywhere; neither side changes, both being integrals.  Two unit-mass
facts follow from `∫ρ = 1` and the translation invariance of Lebesgue measure:
`∫⁻_y ρ(x - y)dy = 1` for every `x`, and `∫⁻_x ρ(x - y)dx = 1` for every `y`.
Then, pointwise in `x`, the norm inequality for the integral gives
`‖(w' ∗ ρ)(x)‖ ≤ ∫⁻_y ‖w'(y)‖ρ(x - y)dy`.  For `q = 1` that is already the
claim.  For `q > 1`, split `ρ(x - y) = ρ(x - y)^{1/q}ρ(x - y)^{1/q'}` with `q'`
the Hölder conjugate and apply Hölder's inequality in the pair `(q,q')`: the
second factor integrates to `(∫⁻_y ρ(x - y)dy)^{1/q'} = 1`, leaving
`‖(w' ∗ ρ)(x)‖ ≤ (∫⁻_y ‖w'(y)‖^qρ(x - y)dy)^{1/q}`, which raised to the `q`-th
power is the pointwise bound.  Integrating it in `x`, exchanging the two
integrations by Tonelli --- legitimate with no integrability hypothesis because
the whole computation is carried out for extended-nonnegative integrands, the
integrand being jointly measurable in `(x,y)` --- and using the second
unit-mass fact for each fixed `y` gives
`∫⁻‖w' ∗ ρ‖^q ≤ ∫⁻‖w'‖^q`.  Taking `q`-th roots is the assertion. -/
theorem ConvolutionLqContraction :
    ∀ (n : ℕ) (q : ℝ), 1 ≤ q →
      ∀ ρ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous ρ → (∀ z, 0 ≤ ρ z) →
      HasCompactSupport ρ → (∫ z, ρ z) = 1 →
      ∀ w : EuclideanSpace ℝ (Fin n) → ℝ, MemLp w (ENNReal.ofReal q) volume →
      eLpNorm (convolution w ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (ENNReal.ofReal q) volume
        ≤ eLpNorm w (ENNReal.ofReal q) volume := by
  intro n q hq ρ hρc hρ0 hρcs hρint w hw
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hp0 : (ENNReal.ofReal q) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hptop : (ENNReal.ofReal q) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq0.le
  obtain ⟨w', hw'sm, hww'⟩ : ∃ w', StronglyMeasurable w' ∧ w =ᵐ[volume] w' :=
    ⟨hw.1.mk w, hw.1.stronglyMeasurable_mk, hw.1.ae_eq_mk⟩
  have hconv : ∀ x, convolution w ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume x
      = convolution w' ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    intro x
    rw [convolution_def, convolution_def]
    exact integral_congr_ae (hww'.mono fun y hy => by simp [hy])
  rw [eLpNorm_congr_ae hww',
    eLpNorm_congr_ae (Filter.Eventually.of_forall hconv : _ =ᵐ[volume] _)]
  have hRm : Measurable (fun z : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (ρ z)) :=
    hρc.measurable.ennreal_ofReal
  have hρI : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hρcs
  have hmassY : ∀ x : EuclideanSpace ℝ (Fin n), ∫⁻ y, ENNReal.ofReal (ρ (x - y)) = 1 := by
    intro x
    rw [← ofReal_integral_eq_lintegral_ofReal (hρI.comp_sub_left x)
      (Filter.Eventually.of_forall fun y => hρ0 _), integral_sub_left_eq_self ρ volume x, hρint]
    simp
  have hmassX : ∀ y : EuclideanSpace ℝ (Fin n), ∫⁻ x, ENNReal.ofReal (ρ (x - y)) = 1 := by
    intro y
    have hI : Integrable (fun x => ρ (x - y)) volume := hρI.comp_sub_right y
    rw [← ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall fun x => hρ0 _), integral_sub_right_eq_self ρ y, hρint]
    simp
  have hptwise : ∀ x, ‖convolution w' ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ q
      ≤ ∫⁻ y, ‖w' y‖ₑ ^ q * ENNReal.ofReal (ρ (x - y)) := by
    intro x
    have h1 : ‖convolution w' ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ
        ≤ ∫⁻ y, ‖w' y‖ₑ * ENNReal.ofReal (ρ (x - y)) := by
      rw [convolution_def]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun y => ?_))
      rw [ContinuousLinearMap.lsmul_apply, smul_eq_mul, enorm_mul,
        Real.enorm_eq_ofReal (hρ0 _)]
    rcases eq_or_lt_of_le hq with h1q | h1q
    · rw [← h1q]
      simpa using h1
    · have hconj : q.HolderConjugate q.conjExponent := Real.HolderConjugate.conjExponent h1q
      have hq'0 : (0 : ℝ) < q.conjExponent := hconj.symm.pos
      have hsum : 1 / q + 1 / q.conjExponent = 1 := by
        simpa [one_div] using hconj.inv_add_inv_eq_one
      have hRsub : Measurable
          (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (ρ (x - y))) :=
        hRm.comp (measurable_const.sub measurable_id)
      have hfm : AEMeasurable (fun y : EuclideanSpace ℝ (Fin n) =>
          ‖w' y‖ₑ * (ENNReal.ofReal (ρ (x - y))) ^ (1 / q)) volume :=
        (hw'sm.measurable.enorm.mul (hRsub.pow_const _)).aemeasurable
      have hgm : AEMeasurable (fun y : EuclideanSpace ℝ (Fin n) =>
          (ENNReal.ofReal (ρ (x - y))) ^ (1 / q.conjExponent)) volume :=
        (hRsub.pow_const _).aemeasurable
      have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj hfm hgm
      have e1 : ∀ y : EuclideanSpace ℝ (Fin n),
          ‖w' y‖ₑ * (ENNReal.ofReal (ρ (x - y))) ^ (1 / q) *
            (ENNReal.ofReal (ρ (x - y))) ^ (1 / q.conjExponent)
            = ‖w' y‖ₑ * ENNReal.ofReal (ρ (x - y)) := by
        intro y
        rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hsum,
          ENNReal.rpow_one]
      have e2 : ∀ y : EuclideanSpace ℝ (Fin n),
          (‖w' y‖ₑ * (ENNReal.ofReal (ρ (x - y))) ^ (1 / q)) ^ q
            = ‖w' y‖ₑ ^ q * ENNReal.ofReal (ρ (x - y)) := by
        intro y
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul,
          one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
      have e3 : ∀ y : EuclideanSpace ℝ (Fin n),
          ((ENNReal.ofReal (ρ (x - y))) ^ (1 / q.conjExponent)) ^ q.conjExponent
            = ENNReal.ofReal (ρ (x - y)) := by
        intro y
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hq'0.ne', ENNReal.rpow_one]
      have hH2 : (∫⁻ y, ‖w' y‖ₑ * ENNReal.ofReal (ρ (x - y)))
          ≤ (∫⁻ y, ‖w' y‖ₑ ^ q * ENNReal.ofReal (ρ (x - y))) ^ (1 / q) := by
        simp only [Pi.mul_apply] at hH
        rw [lintegral_congr e1, lintegral_congr e2, lintegral_congr e3, hmassY x] at hH
        simpa using hH
      calc ‖convolution w' ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ q
          ≤ ((∫⁻ y, ‖w' y‖ₑ ^ q * ENNReal.ofReal (ρ (x - y))) ^ (1 / q)) ^ q :=
            ENNReal.rpow_le_rpow (h1.trans hH2) hq0.le
        _ = ∫⁻ y, ‖w' y‖ₑ ^ q * ENNReal.ofReal (ρ (x - y)) := by
            rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
  have huncurry : Measurable (Function.uncurry
      (fun (x y : EuclideanSpace ℝ (Fin n)) =>
        ‖w' y‖ₑ ^ q * ENNReal.ofReal (ρ (x - y)))) :=
    ((hw'sm.measurable.comp measurable_snd).enorm.pow_const q).mul
      (hRm.comp (measurable_fst.sub measurable_snd))
  have hmain : (∫⁻ x, ‖convolution w' ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ q)
      ≤ ∫⁻ y, ‖w' y‖ₑ ^ q := by
    calc (∫⁻ x, ‖convolution w' ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ q)
        ≤ ∫⁻ x, ∫⁻ y, ‖w' y‖ₑ ^ q * ENNReal.ofReal (ρ (x - y)) := lintegral_mono hptwise
      _ = ∫⁻ y, ∫⁻ x, ‖w' y‖ₑ ^ q * ENNReal.ofReal (ρ (x - y)) :=
          lintegral_lintegral_swap huncurry.aemeasurable
      _ = ∫⁻ y, ‖w' y‖ₑ ^ q := by
          refine lintegral_congr fun y => ?_
          have hfin : ‖w' y‖ₑ ^ q ≠ ⊤ :=
            ENNReal.rpow_ne_top_of_nonneg hq0.le (by simp [enorm_eq_nnnorm])
          rw [lintegral_const_mul' _ _ hfin, hmassX y, mul_one]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop, hpt]
  exact ENNReal.rpow_le_rpow hmain (by positivity)
