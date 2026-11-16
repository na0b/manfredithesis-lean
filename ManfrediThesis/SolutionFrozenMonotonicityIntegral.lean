import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.StructureMonotonicityBound
open MeasureTheory

/-- The thesis' (5.5): integrating the frozen field's monotonicity over the ball
turns the pairing `I₁` into the weighted energy of `∇w` that (5.9) and the
absorption step consume.  This is thesis l. 1480-1491, where the paper obtains it
from the segment expansion of `A⁰` and condition (Q1) and then converts the
`t`-average of the weight into its value at the endpoints. -/
theorem SolutionFrozenMonotonicityIntegral :
    ∀ (n : ℕ) (p r : ℝ), 2 ≤ n → 1 < p → 0 < r →
      ∃ C : ℝ, 0 < C ∧
        ∀ (ε γ₀ γ₁ : ℝ)
          (A0 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
          (g gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 ≤ ε → 0 < γ₀ → γ₁ ≤ r * γ₀ → 0 < R →
          EllipticStructureQ12 n p ε γ₀ γ₁ Set.univ (fun _ _ h => A0 h) →
          MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) →
          MemLp gv (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) →
          MemLp (fun x => g x - gv x) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R)) →
          IntegrableOn
            (fun x => ∑ i, (A0 (g x) - A0 (gv x)) i * (g x - gv x) i)
            (Metric.ball x₀ R) volume →
          C * γ₀ * (∫ x in Metric.ball x₀ R,
              (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2)
            ≤ ∫ x in Metric.ball x₀ R,
                ∑ i, (A0 (g x) - A0 (gv x)) i * (g x - gv x) i := by
  intro n p r hn hp hr
  obtain ⟨C, hC0, hMono⟩ := StructureMonotonicityBound n p r hn hp hr
  refine ⟨C, hC0, ?_⟩
  intro ε γ₀ γ₁ A0 x₀ R g gv hε hγ₀ hγ₁ hR hQ12 hgLp hgvLp hdLp hIint
  have hCγ : (0:ℝ) < C * γ₀ := mul_pos hC0 hγ₀
  have hpt := hMono ε γ₀ γ₁ Set.univ (fun _ _ h => A0 h) hε hγ₀ hγ₁ hQ12
  -- the pointwise monotonicity, a.e. on the ball, at `a = g x`, `b = gv x`
  have hbd : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      C * γ₀ * ((ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2)
        ≤ ∑ i, (A0 (g x) - A0 (gv x)) i * (g x - gv x) i := by
    filter_upwards [ae_restrict_of_ae hpt] with x hx
    have h := hx (Set.mem_univ x) 0 (g x) (gv x)
    calc C * γ₀ * ((ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2)
        = C * γ₀ * (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1)
            * ‖g x - gv x‖ ^ 2 := by ring
      _ ≤ ∑ i, (A0 (g x) i - A0 (gv x) i) * (g x i - gv x i) := by simpa using h
      _ = ∑ i, (A0 (g x) - A0 (gv x)) i * (g x - gv x) i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp
  -- the weighted integrand is measurable, nonnegative and integrable
  have hQae : AEMeasurable (fun x => ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2)
      (volume.restrict (Metric.ball x₀ R)) :=
    ((hgLp.aestronglyMeasurable.aemeasurable.norm.pow_const 2).const_add ε).add
      (hgvLp.aestronglyMeasurable.aemeasurable.norm.pow_const 2)
  have hWmeas : AEStronglyMeasurable
      (fun x => (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2)
      (volume.restrict (Metric.ball x₀ R)) :=
    ((hQae.pow_const (p / 2 - 1)).aestronglyMeasurable).mul
      (hdLp.aestronglyMeasurable.norm.pow 2)
  have hW0 : ∀ x, (0:ℝ)
      ≤ (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2 := by
    intro x
    have h1 : (0:ℝ) ≤ ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2 := by positivity
    exact mul_nonneg (Real.rpow_nonneg h1 _) (by positivity)
  have hdiv : ∀ a b : ℝ, C * γ₀ * a ≤ b → a ≤ (C * γ₀)⁻¹ * b := by
    intro a b hab
    have h2 := mul_le_mul_of_nonneg_left hab (inv_nonneg.2 hCγ.le)
    rwa [show (C * γ₀)⁻¹ * (C * γ₀ * a) = a from by field_simp] at h2
  have hWint : Integrable
      (fun x => (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2)
      (volume.restrict (Metric.ball x₀ R)) := by
    refine (hIint.const_mul (C * γ₀)⁻¹).mono' hWmeas ?_
    filter_upwards [hbd] with x h
    rw [Real.norm_eq_abs, abs_of_nonneg (hW0 x)]
    exact hdiv _ _ h
  -- integrating
  have hstep : (∫ x in Metric.ball x₀ R,
        C * γ₀ * ((ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2))
      ≤ ∫ x in Metric.ball x₀ R,
          ∑ i, (A0 (g x) - A0 (gv x)) i * (g x - gv x) i :=
    integral_mono_ae (hWint.const_mul _) hIint hbd
  rwa [integral_const_mul] at hstep
