import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ345
open MeasureTheory

/-- The thesis' (5.8): condition (Q5) bounds the right-hand side term `I₃` by
the essential supremum of `|w|` on the ball times the `p`-energy of `∇u`, and
the comparison data bound that supremum by a multiple of `R^α`.  This is thesis
l. 1503-1518.

The constant carried here is `4 C₁ γ₄` rather than the printed `2 C₁ γ₄`.  The
source carries an adjudicated `CHECK` annotation at l. 1514 recording exactly
this: the hypothesis `sup |u(x₀) - u(x)| ≤ C₁R^α` gives
`osc u ≤ 2C₁R^α`, so the printed chain for `|w|` yields `4C₁R^α`, and the
manuscript keeps the printed `2` and calls the discrepancy harmless.  It is
harmless -- it is a constant, and the modulus `σ₀` absorbs it -- but it is not
silent here.

`u` and `v` are assumed almost-everywhere strongly measurable on the ball, and
the hypothesis is not removable.  Nothing else in the list constrains them:
`IntegrableOn (fun x => B x (u x) (g x))` constrains only the superposition,
`MemLp g` only `g`, and the essential bound on `|u - v|` carries no regularity
at all.  Without it the integrand `B(·,u,g)(u-v)` need not be measurable -- take
`B ≡ γ₄`, which satisfies (Q5) since `γ₄ ≤ γ₄(1+‖h‖²)^{p/2}`, together with
`v ≡ 0` and a non-measurable `u` with `|u| ≤ 1` -- and the conclusion would then
hold only through the Bochner convention that a non-integrable function
integrates to `0`, which is a vacuous branch no consumer can use. -/
theorem SolutionRightHandSideBound :
    ∀ (n : ℕ) (p ε μ γ₂ γ₃ γ₄ : ℝ), 1 ≤ n → 1 < p → 0 < γ₄ →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n))
        (B : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
        (u v : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (x₀ : EuclideanSpace ℝ (Fin n)) (R α C₁ : ℝ),
        0 < R → Metric.ball x₀ R ⊆ Ω → 0 < α → 0 ≤ C₁ →
        EllipticStructureQ345 n p ε μ γ₂ γ₃ γ₄ Ω A B →
        MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) →
        AEStronglyMeasurable u (volume.restrict (Metric.ball x₀ R)) →
        AEStronglyMeasurable v (volume.restrict (Metric.ball x₀ R)) →
        IntegrableOn (fun x => B x (u x) (g x)) (Metric.ball x₀ R) volume →
        (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
            |u x - v x| ≤ 4 * C₁ * R ^ α) →
        |∫ x in Metric.ball x₀ R, B x (u x) (g x) * (u x - v x)|
          ≤ 4 * C₁ * γ₄ * R ^ α
              * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2) := by
  intro n p ε μ γ₂ γ₃ γ₄ hn hp hγ₄ Ω A B u v g x₀ R α C₁ hR hBsub hα0 hC₁ hQ345
    hgLp hum hvm hBint huv
  have hp0 : (0:ℝ) < p := by linarith
  have hfin : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have htoR : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hne0 : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hgp : Integrable (fun x => ‖g x‖ ^ p) (volume.restrict (Metric.ball x₀ R)) := by
    simpa [htoR] using hgLp.integrable_norm_rpow hne0 (by simp)
  -- the majorant `(1 + |g|²)^{p/2}` is integrable on the ball
  have hMm : AEStronglyMeasurable (fun x => (1 + ‖g x‖ ^ 2) ^ (p/2))
      (volume.restrict (Metric.ball x₀ R)) := by
    have h1 : AEStronglyMeasurable (fun x => 1 + ‖g x‖ ^ 2)
        (volume.restrict (Metric.ball x₀ R)) :=
      aestronglyMeasurable_const.add (hgLp.aestronglyMeasurable.norm.pow 2)
    have hcont : Continuous fun s : ℝ => s ^ (p/2) :=
      continuous_id.rpow_const fun _ => Or.inr (by positivity)
    simpa [Function.comp_def] using hcont.comp_aestronglyMeasurable h1
  have helem : ∀ s : ℝ, 0 ≤ s → (1 + s ^ 2) ^ (p/2) ≤ (2:ℝ) ^ (p/2) * (1 + s ^ p) := by
    intro s hs
    have h20 : (0:ℝ) < (2:ℝ) ^ (p/2) := Real.rpow_pos_of_pos (by norm_num) _
    have hsp : (0:ℝ) ≤ s ^ p := Real.rpow_nonneg hs _
    rcases le_total s 1 with h | h
    · have h1 : (1:ℝ) + s ^ 2 ≤ 2 := by nlinarith
      have h2 : (1 + s ^ 2) ^ (p/2) ≤ (2:ℝ) ^ (p/2) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
      nlinarith [h2, h20.le, hsp]
    · have hs0 : (0:ℝ) < s := lt_of_lt_of_le one_pos h
      have h1 : (1:ℝ) + s ^ 2 ≤ 2 * s ^ 2 := by nlinarith
      have h2 : (1 + s ^ 2) ^ (p/2) ≤ (2 * s ^ 2) ^ (p/2) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
      have h3 : (2 * s ^ 2) ^ (p/2) = (2:ℝ) ^ (p/2) * s ^ p := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        congr 1
        rw [show s ^ 2 = s ^ (2:ℝ) by
              rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast],
          ← Real.rpow_mul hs]
        congr 1
        ring
      rw [h3] at h2
      nlinarith [h2, h20.le]
  have hMint : Integrable (fun x => (1 + ‖g x‖ ^ 2) ^ (p/2))
      (volume.restrict (Metric.ball x₀ R)) := by
    have hmaj : Integrable (fun x => (2:ℝ) ^ (p/2) * (1 + ‖g x‖ ^ p))
        (volume.restrict (Metric.ball x₀ R)) :=
      (integrable_const _ |>.add hgp).const_mul _
    refine hmaj.mono' hMm (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact helem _ (norm_nonneg _)
  -- the pointwise bound
  have hCR0 : (0:ℝ) ≤ 4 * C₁ * R ^ α := by positivity
  have hQ5 := hQ345.Q5
  have hbd : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      ‖B x (u x) (g x) * (u x - v x)‖
        ≤ 4 * C₁ * γ₄ * R ^ α * (1 + ‖g x‖ ^ 2) ^ (p/2) := by
    filter_upwards [huv, ae_restrict_of_ae hQ5, ae_restrict_mem measurableSet_ball]
      with x h1 h2 h3
    have hxΩ : x ∈ Ω := hBsub h3
    have hB := h2 hxΩ (u x) (g x)
    have hM0 : (0:ℝ) ≤ (1 + ‖g x‖ ^ 2) ^ (p/2) :=
      Real.rpow_nonneg (by positivity) _
    rw [Real.norm_eq_abs, abs_mul]
    calc |B x (u x) (g x)| * |u x - v x|
        ≤ (γ₄ * (1 + ‖g x‖ ^ 2) ^ (p/2)) * (4 * C₁ * R ^ α) := by
          refine mul_le_mul hB h1 (abs_nonneg _) (by positivity)
      _ = 4 * C₁ * γ₄ * R ^ α * (1 + ‖g x‖ ^ 2) ^ (p/2) := by ring
  -- the integrand is integrable
  have hmeas : AEStronglyMeasurable (fun x => B x (u x) (g x) * (u x - v x))
      (volume.restrict (Metric.ball x₀ R)) :=
    hBint.aestronglyMeasurable.mul (hum.sub hvm)
  have hmajint : Integrable
      (fun x => 4 * C₁ * γ₄ * R ^ α * (1 + ‖g x‖ ^ 2) ^ (p/2))
      (volume.restrict (Metric.ball x₀ R)) := hMint.const_mul _
  have hint : Integrable (fun x => B x (u x) (g x) * (u x - v x))
      (volume.restrict (Metric.ball x₀ R)) := hmajint.mono' hmeas hbd
  -- integrating
  calc |∫ x in Metric.ball x₀ R, B x (u x) (g x) * (u x - v x)|
      ≤ ∫ x in Metric.ball x₀ R, |B x (u x) (g x) * (u x - v x)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x in Metric.ball x₀ R,
          4 * C₁ * γ₄ * R ^ α * (1 + ‖g x‖ ^ 2) ^ (p/2) := by
        refine integral_mono_ae hint.abs hmajint ?_
        filter_upwards [hbd] with x h
        simpa [Real.norm_eq_abs] using h
    _ = 4 * C₁ * γ₄ * R ^ α * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p/2) :=
        integral_const_mul _ _
