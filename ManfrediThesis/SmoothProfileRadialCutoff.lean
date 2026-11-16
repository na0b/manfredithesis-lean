import ManfrediThesis.Preamble
set_option maxHeartbeats 800000
open MeasureTheory

/-- A radial cut-off built from an abstract smooth profile: given
`ψ : ℝ → ℝ` smooth with `0 ≤ ψ ≤ 1`, `ψ = 1` on `(-∞, 3/8]`, `ψ = 0` on
`[5/8, ∞)` and `|ψ'| ≤ Λ`, and given `0 < r' < r`, there is a smooth
`ζ : ℝⁿ → ℝ` with `0 ≤ ζ ≤ 1`, `ζ = 1` on `B_{r'}(x₀)`, compact support
contained in `B_r(x₀)`, and
`|∇ζ|² ≤ \bigl(2Λ/(r - r')\bigr)^2` everywhere.

Conventions, restated here because a helper inherits none of its parent's.
`supp ζ` means `tsupport ζ`, the CLOSED support, and `|∇ζ|²` abbreviates
`∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i 1))²`.  The profile is an
arbitrary function with the listed properties, NOT `Real.smoothTransition`, so
this is a different construction from the one \noderef{StandardRadialCutoff}
states and not an instance of it; what the two share is only the shape of the
conclusion.  The hypothesis relating a vector's coordinate sum of squares to
its norm is taken as given, as the consumer holds it.

The route.  Put `a = r^2 - r'^2 > 0` and
`h(x) = a^{-1}\bigl(\|x - x₀\|^2 - r'^2\bigr)`, an affine function of
`\|x-x₀\|^2` with `h = 0` on the sphere of radius `r'` and `h = 1` on the
sphere of radius `r`; set `ζ = ψ ∘ h`.  Smoothness is the composition of the
smooth `ψ` with the polynomial `h`.  Since `h ≤ 0 < 3/8` on `B_{r'}(x₀)`, the
lower plateau of `ψ` gives `ζ = 1` there, and since `h ≥ 1 > 5/8` off
`B_r(x₀)`, the upper plateau gives `ζ = 0` there; hence `supp ζ` is a closed
subset of the bounded set `B_r(x₀)`, so it is compact, and
`supp ζ ⊆ B_r(x₀)`.  The bounds `0 ≤ ζ ≤ 1` are inherited from `ψ`
pointwise.  For the gradient, the chain rule gives
`∇ζ(x) = ψ'(h(x))·a^{-1}·2(x - x₀)`, so
\[
|∇ζ(x)|^2=\bigl(ψ'(h(x))\bigr)^2\,\frac{4\|x-x₀\|^2}{a^2}
\ \le\ Λ^2\,\frac{4r^2}{(r^2-r'^2)^2}
\ \le\ \Bigl(\frac{2Λ}{r-r'}\Bigr)^{2},
\]
where the first inequality uses `|ψ'| ≤ Λ` and the fact that `ψ'` vanishes off
the transition band, so only `\|x - x₀\| ≤ r` contributes, and the second uses
`r^2 - r'^2 = (r-r')(r+r') ≥ (r-r')r`, valid because `r' > 0`.  Off `supp ζ` the
derivative vanishes and the bound is trivial. -/
theorem SmoothProfileRadialCutoff :
    ∀ (n : ℕ) (ψ : ℝ → ℝ) (Λ r' r : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∀ t, 0 ≤ ψ t) → (∀ t, ψ t ≤ 1) →
      (∀ t, t ≤ 3 / 8 → ψ t = 1) → (∀ t, 5 / 8 ≤ t → ψ t = 0) →
      (∀ t, |deriv ψ t| ≤ Λ) →
      (∀ w : EuclideanSpace ℝ (Fin n), ∑ i : Fin n, (w i) ^ 2 = ‖w‖ ^ 2) →
      0 < r' → r' < r → 0 < r - r' →
      ∃ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) ζ ∧ (∀ x, 0 ≤ ζ x) ∧ (∀ x, ζ x ≤ 1) ∧
        (∀ x ∈ Metric.ball x₀ r', ζ x = 1) ∧
        HasCompactSupport ζ ∧ tsupport ζ ⊆ Metric.ball x₀ r ∧
        (∀ x, ∑ i : Fin n, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2
          ≤ (2 * Λ / (r - r')) ^ 2) := by
  intro n ψ Λ r' r x₀ hψsm hψ0 hψle1 hψlo hψhi hψd hnormsq hr'0 hr'r hdr
  obtain ⟨aa, haadef⟩ : ∃ aa : ℝ, aa = r ^ 2 - r' ^ 2 := ⟨_, rfl⟩
  have haa0 : 0 < aa := by
    rw [haadef]
    exact sub_pos.2 (pow_lt_pow_left₀ hr'r hr'0.le two_ne_zero)
  obtain ⟨hv, hvdef⟩ : ∃ hv : EuclideanSpace ℝ (Fin n) → ℝ,
      hv = fun x => aa⁻¹ * (‖x - x₀‖ ^ 2 - r' ^ 2) := ⟨_, rfl⟩
  have hveq : ∀ x, hv x = aa⁻¹ * (‖x - x₀‖ ^ 2 - r' ^ 2) := fun x => by rw [hvdef]
  have hnsq : ∀ x : EuclideanSpace ℝ (Fin n),
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => ‖y - x₀‖ ^ 2)
        (2 • innerSL ℝ (x - x₀)) x := by
    intro x
    have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => y - x₀)
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) x :=
      (hasFDerivAt_id x).sub_const x₀
    have h2 := ((hasStrictFDerivAt_norm_sq (x - x₀)).hasFDerivAt).comp x h1
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2
  have hhvfd : ∀ x : EuclideanSpace ℝ (Fin n),
      HasFDerivAt hv (aa⁻¹ • (2 • innerSL ℝ (x - x₀))) x := by
    intro x
    rw [hvdef]
    exact ((hnsq x).sub_const (r' ^ 2)).const_mul aa⁻¹
  have hvsm : ContDiff ℝ (⊤ : ℕ∞) hv := by
    rw [hvdef]
    exact contDiff_const.mul
      (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const)
  -- the outer radius at which the cut-off has already vanished
  obtain ⟨sr, hsrdef⟩ : ∃ sr : ℝ, sr = Real.sqrt (r' ^ 2 + (5 / 8) * aa) := ⟨_, rfl⟩
  have hsr0 : 0 ≤ sr := by rw [hsrdef]; exact Real.sqrt_nonneg _
  have hsrsq : sr ^ 2 = r' ^ 2 + (5 / 8) * aa := by
    rw [hsrdef, Real.sq_sqrt]
    exact add_nonneg (sq_nonneg r') (by linarith)
  have hsrr : sr < r := by
    refine lt_of_pow_lt_pow_left₀ 2 (by linarith) ?_
    rw [hsrsq, haadef]
    linarith
  have hzero : ∀ x : EuclideanSpace ℝ (Fin n), x ∉ Metric.closedBall x₀ sr →
      ψ (hv x) = 0 := by
    intro x hx
    refine hψhi _ ?_
    have hgt : sr < ‖x - x₀‖ := by
      rw [← dist_eq_norm]
      exact lt_of_not_ge (fun hc => hx (Metric.mem_closedBall.2 hc))
    have hsq : r' ^ 2 + (5 / 8) * aa < ‖x - x₀‖ ^ 2 := by
      nlinarith [hsrsq, hsr0]
    rw [hveq x]
    have h3 : (0 : ℝ) ≤ aa⁻¹ := le_of_lt (inv_pos.2 haa0)
    have h5 : (5 / 8 : ℝ) * aa ≤ ‖x - x₀‖ ^ 2 - r' ^ 2 := by linarith
    calc (5 : ℝ) / 8 = aa⁻¹ * ((5 / 8) * aa) := by
          field_simp
      _ ≤ aa⁻¹ * (‖x - x₀‖ ^ 2 - r' ^ 2) := mul_le_mul_of_nonneg_left h5 h3
  have hsupp : tsupport (fun x => ψ (hv x)) ⊆ Metric.closedBall x₀ sr := by
    refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
    by_contra hc
    exact hx (hzero x hc)
  have hζfd : ∀ x : EuclideanSpace ℝ (Fin n), HasFDerivAt (fun y => ψ (hv y))
      (deriv ψ (hv x) • (aa⁻¹ • (2 • innerSL ℝ (x - x₀)))) x := by
    intro x
    have hd : HasDerivAt ψ (deriv ψ (hv x)) (hv x) :=
      ((hψsm.differentiable (by simp)) (hv x)).hasDerivAt
    exact hd.comp_hasFDerivAt x (hhvfd x)
  have hζapply : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      fderiv ℝ (fun y => ψ (hv y)) x (EuclideanSpace.single i (1 : ℝ))
        = deriv ψ (hv x) * (aa⁻¹ * (2 * (x - x₀) i)) := by
    intro x i
    rw [(hζfd x).fderiv]
    simp [innerSL_apply_apply, PiLp.inner_apply]
  refine ⟨fun x => ψ (hv x), hψsm.comp hvsm, fun x => hψ0 _, fun x => hψle1 _, ?_,
    ?_, ?_, ?_⟩
  · intro x hx
    refine hψlo _ (le_trans ?_ (by norm_num : (0 : ℝ) ≤ 3 / 8))
    rw [hveq x]
    have hlt : ‖x - x₀‖ < r' := by
      rw [← dist_eq_norm]; exact Metric.mem_ball.1 hx
    have h2 : ‖x - x₀‖ ^ 2 - r' ^ 2 ≤ 0 := by
      have := pow_le_pow_left₀ (norm_nonneg (x - x₀)) hlt.le 2
      linarith
    have h3 : (0 : ℝ) ≤ aa⁻¹ := le_of_lt (inv_pos.2 haa0)
    have h6 := mul_le_mul_of_nonneg_left h2 h3
    rw [mul_zero] at h6
    exact h6
  · exact HasCompactSupport.intro (isCompact_closedBall x₀ sr) hzero
  · refine hsupp.trans (fun y hy => ?_)
    exact Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hy) hsrr)
  · intro x
    by_cases hxs : x ∈ tsupport (fun y => ψ (hv y))
    · have hxle : ‖x - x₀‖ ^ 2 ≤ r ^ 2 := by
        have h1 : ‖x - x₀‖ ≤ sr := by
          rw [← dist_eq_norm]
          exact Metric.mem_closedBall.1 (hsupp hxs)
        have h2 := pow_le_pow_left₀ (norm_nonneg (x - x₀)) h1 2
        have h3 : sr ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hsr0 hsrr.le 2
        linarith
      have hdψ : (deriv ψ (hv x)) ^ 2 ≤ Λ ^ 2 := by
        calc (deriv ψ (hv x)) ^ 2 = |deriv ψ (hv x)| ^ 2 := (sq_abs _).symm
          _ ≤ Λ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hψd (hv x)) 2
      have hpos : (0 : ℝ) < aa⁻¹ ^ 2 * 4 := by positivity
      have hstep : ∑ i : Fin n,
          (fderiv ℝ (fun y => ψ (hv y)) x (EuclideanSpace.single i (1 : ℝ))) ^ 2
          = (deriv ψ (hv x)) ^ 2 * (aa⁻¹ ^ 2 * 4) * ‖x - x₀‖ ^ 2 := by
        rw [← hnormsq (x - x₀), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hζapply x i]
        ring
      rw [hstep]
      have hb1 : (deriv ψ (hv x)) ^ 2 * (aa⁻¹ ^ 2 * 4) * ‖x - x₀‖ ^ 2
          ≤ Λ ^ 2 * (aa⁻¹ ^ 2 * 4) * r ^ 2 := by
        have hc : (0 : ℝ) ≤ aa⁻¹ ^ 2 * 4 := by positivity
        refine mul_le_mul (mul_le_mul_of_nonneg_right hdψ hc) hxle (sq_nonneg _) ?_
        positivity
      refine hb1.trans ?_
      have hrr0 : (0 : ℝ) < r + r' := by linarith
      have haaeq : aa = (r - r') * (r + r') := by rw [haadef]; ring
      have hane1 : (r - r') ≠ 0 := ne_of_gt hdr
      have hane2 : (r + r') ≠ 0 := ne_of_gt hrr0
      rw [div_pow, le_div_iff₀ (by positivity : (0 : ℝ) < (r - r') ^ 2), haaeq]
      have hexp : Λ ^ 2 * (((r - r') * (r + r'))⁻¹ ^ 2 * 4) * r ^ 2 * (r - r') ^ 2
          = 4 * Λ ^ 2 * r ^ 2 / (r + r') ^ 2 := by
        field_simp
      rw [hexp, div_le_iff₀ (by positivity : (0 : ℝ) < (r + r') ^ 2)]
      have h1 : r ^ 2 ≤ (r + r') ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have h2 : (0 : ℝ) ≤ 4 * Λ ^ 2 := by
        have := sq_nonneg Λ
        linarith
      nlinarith [h1, h2]
    · rw [fderiv_of_notMem_tsupport ℝ hxs]
      simp
      positivity
