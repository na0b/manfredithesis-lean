import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ6
open MeasureTheory

/-- The freezing error (5.6)-(5.7): the cost of replacing the field
`A(x, u(x), ·)` by the field frozen at `(x₀, z₀)`, paired against `∇w`, is
controlled by the modulus of (Q6) evaluated at `R + C₁R^α` times a Young split
of `(1+|∇u|²)^{p/2}` and `|∇w|^p`.  This is thesis l. 1492-1501.

The exponent on `(1 + ‖g x‖ ^ 2` is `(p-1)/2` and **cannot** be made a
parameter at no cost.  It is the exponent (Q6) itself carries
(`EllipticStructureQ6.Q6`), and it is the only exponent for which the Young
step lands on `(1+|∇u|²)^{p/2}`: Young at the conjugate exponents `p/(p-1)` and
`p` sends `s = (1+|∇u|²)^κ` to `s^{p/(p-1)} = (1+|∇u|²)^{κp/(p-1)}`, and
`κ p/(p-1) = p/2` forces `κ = (p-1)/2`.  The source carries an adjudicated
`MISPRINT` annotation at l. 1493 recording exactly this: the print has
`p/2 - 1`, corrected to `(p-1)/2`.

This is **not** `FrozenFreezingErrorBound`.  That node is the §4 branch: its
data is a variational integrand `fdens x z h` together with a frozen integrand
`f0 h`, its modulus hypothesis carries the exponent `p/2`, its comparison input
is `∫ fdens(u,g) ≤ ∫ fdens(v,gv)`, and it *produces* two moduli `σ₀, σ₁` in
closed form.  The present node is the §5 branch: its data is a field `A` with
the (Q6) bundle at the exponent `(p-1)/2`, and it states a single integral
estimate and produces nothing.  Neither statement implies the other, and
neither set of hypotheses is available on the other side. -/
theorem SolutionFreezingErrorBound :
    ∀ (n : ℕ) (p : ℝ), 1 ≤ n → 1 < p →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n))
        (σ : ℝ → ℝ)
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (x₀ : EuclideanSpace ℝ (Fin n)) (z₀ R α C₁ : ℝ),
        EllipticStructureQ6 n p Ω A σ →
        x₀ ∈ Ω → 0 < R → Metric.ball x₀ R ⊆ Ω →
        0 < α → 0 ≤ C₁ →
        (∀ x ∈ Metric.ball x₀ R, |u x - z₀| ≤ C₁ * R ^ α) →
        MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) →
        MemLp (fun x => g x - gv x) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R)) →
        MemLp (fun x => A x (u x) (g x)) (ENNReal.ofReal (p / (p - 1)))
          (volume.restrict (Metric.ball x₀ R)) →
        MemLp (fun x => A x₀ z₀ (g x)) (ENNReal.ofReal (p / (p - 1)))
          (volume.restrict (Metric.ball x₀ R)) →
        |∫ x in Metric.ball x₀ R,
            ∑ i, (A x (u x) (g x) - A x₀ z₀ (g x)) i * (g x - gv x) i|
          ≤ σ (R + C₁ * R ^ α)
              * ((p - 1) / p * (∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2))
                + 1 / p * ∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p) := by
  intro n p hn hp Ω A σ u g gv x₀ z₀ R α C₁ hQ6 hx₀ hR hBsub hα0 hC₁ hu0 hgLp hdLp
    hALp hA0Lp
  have hp0 : (0:ℝ) < p := by linarith
  have hp1 : (0:ℝ) < p - 1 := by linarith
  have hfin : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have htoR : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hne0 : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hconj : Real.HolderConjugate p (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have hconj' : Real.HolderConjugate (p / (p - 1)) p := hconj.symm
  have hHT : ENNReal.HolderTriple (ENNReal.ofReal (p / (p - 1)))
      (ENNReal.ofReal p) 1 :=
    ⟨by rw [inv_one]; exact hconj'.inv_add_inv_ennreal⟩
  -- the modulus value, and its nonnegativity
  have hRα0 : (0:ℝ) ≤ C₁ * R ^ α := by positivity
  have hΘ0 : (0:ℝ) ≤ σ (R + C₁ * R ^ α) := by
    have h := hQ6.σ_mono (show (0:ℝ) ≤ R + C₁ * R ^ α by positivity)
    rwa [hQ6.σ_zero] at h
  -- Cauchy-Schwarz in coordinates
  have hIP : ∀ a b : EuclideanSpace ℝ (Fin n),
      (∑ i, a i * b i) = (innerSL ℝ b) a := by
    intro a b
    show (∑ i, a i * b i) = inner ℝ b a
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hCS : ∀ a b : EuclideanSpace ℝ (Fin n), |∑ i, a i * b i| ≤ ‖a‖ * ‖b‖ := by
    intro a b
    rw [hIP a b, mul_comm ‖a‖ ‖b‖]
    exact abs_real_inner_le_norm b a
  -- the two integrable majorants
  have hgp : Integrable (fun x => ‖g x‖ ^ p)
      (volume.restrict (Metric.ball x₀ R)) := by
    simpa [htoR] using hgLp.integrable_norm_rpow hne0 (by simp)
  have hdp : Integrable (fun x => ‖g x - gv x‖ ^ p)
      (volume.restrict (Metric.ball x₀ R)) := by
    simpa [htoR] using hdLp.integrable_norm_rpow hne0 (by simp)
  have helem : ∀ s q : ℝ, 0 ≤ s → 0 ≤ q →
      (1 + s ^ 2) ^ q ≤ (2:ℝ) ^ q * (1 + s ^ (2 * q)) := by
    intro s q hs hq
    have h20 : (0:ℝ) < (2:ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) _
    have hsq : (0:ℝ) ≤ s ^ (2 * q) := Real.rpow_nonneg hs _
    rcases le_total s 1 with h | h
    · have h1 : (1:ℝ) + s ^ 2 ≤ 2 := by nlinarith
      have h2 : (1 + s ^ 2) ^ q ≤ (2:ℝ) ^ q :=
        Real.rpow_le_rpow (by positivity) h1 hq
      nlinarith [h2, h20.le, hsq]
    · have hs0 : (0:ℝ) < s := lt_of_lt_of_le one_pos h
      have h1 : (1:ℝ) + s ^ 2 ≤ 2 * s ^ 2 := by nlinarith
      have h2 : (1 + s ^ 2) ^ q ≤ (2 * s ^ 2) ^ q :=
        Real.rpow_le_rpow (by positivity) h1 hq
      have h3 : (2 * s ^ 2) ^ q = (2:ℝ) ^ q * s ^ (2 * q) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        congr 1
        rw [show s ^ 2 = s ^ (2:ℝ) by
              rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast],
          ← Real.rpow_mul hs]
      rw [h3] at h2
      nlinarith [h2, h20.le]
  have hQae : AEMeasurable (fun x => 1 + ‖g x‖ ^ 2)
      (volume.restrict (Metric.ball x₀ R)) :=
    (hgLp.aestronglyMeasurable.aemeasurable.norm.pow_const 2).const_add 1
  have hhalfint : Integrable (fun x => (1 + ‖g x‖ ^ 2) ^ (p / 2))
      (volume.restrict (Metric.ball x₀ R)) := by
    refine ((integrable_const ((2:ℝ) ^ (p/2))).mul_const 1 |>.add
      (hgp.const_mul ((2:ℝ) ^ (p/2)))).mono'
      ((hQae.pow_const (p/2)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    have h := helem ‖g x‖ (p/2) (norm_nonneg _) (by positivity)
    rw [show 2 * (p/2) = p by ring] at h
    calc (1 + ‖g x‖ ^ 2) ^ (p/2) ≤ (2:ℝ) ^ (p/2) * (1 + ‖g x‖ ^ p) := h
      _ = (2:ℝ) ^ (p/2) * 1 + (2:ℝ) ^ (p/2) * ‖g x‖ ^ p := by ring
  -- the pointwise bound: (Q6), Cauchy-Schwarz, then Young
  have hpt : ∀ x ∈ Metric.ball x₀ R,
      |∑ i, (A x (u x) (g x) - A x₀ z₀ (g x)) i * (g x - gv x) i|
        ≤ σ (R + C₁ * R ^ α)
            * ((p - 1) / p * (1 + ‖g x‖ ^ 2) ^ (p / 2)
              + 1 / p * ‖g x - gv x‖ ^ p) := by
    intro x hx
    have hxΩ : x ∈ Ω := hBsub hx
    have hq6 := hQ6.Q6 x hxΩ x₀ hx₀ (u x) z₀ (g x)
    have hb0 : (0:ℝ) ≤ (1 + ‖g x‖ ^ 2) ^ ((p - 1) / 2) :=
      Real.rpow_nonneg (by positivity) _
    have hmono : σ (dist x x₀ + |u x - z₀|) ≤ σ (R + C₁ * R ^ α) := by
      refine hQ6.σ_mono ?_
      have h1 : dist x x₀ < R := Metric.mem_ball.1 hx
      have h2 := hu0 x hx
      linarith
    have hA : ‖A x (u x) (g x) - A x₀ z₀ (g x)‖
        ≤ σ (R + C₁ * R ^ α) * (1 + ‖g x‖ ^ 2) ^ ((p - 1) / 2) :=
      le_trans hq6 (mul_le_mul_of_nonneg_right hmono hb0)
    have hy := Real.young_inequality_of_nonneg hb0
      (norm_nonneg (g x - gv x)) hconj'
    have hsp : ((1 + ‖g x‖ ^ 2) ^ ((p - 1) / 2)) ^ (p / (p - 1))
        = (1 + ‖g x‖ ^ 2) ^ (p / 2) := by
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      field_simp
    rw [hsp] at hy
    have hyoung : (1 + ‖g x‖ ^ 2) ^ ((p - 1) / 2) * ‖g x - gv x‖
        ≤ (p - 1) / p * (1 + ‖g x‖ ^ 2) ^ (p / 2)
          + 1 / p * ‖g x - gv x‖ ^ p := by
      refine le_trans hy (le_of_eq ?_)
      field_simp
    calc |∑ i, (A x (u x) (g x) - A x₀ z₀ (g x)) i * (g x - gv x) i|
        ≤ ‖A x (u x) (g x) - A x₀ z₀ (g x)‖ * ‖g x - gv x‖ := hCS _ _
      _ ≤ σ (R + C₁ * R ^ α) * (1 + ‖g x‖ ^ 2) ^ ((p - 1) / 2)
            * ‖g x - gv x‖ :=
          mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      _ = σ (R + C₁ * R ^ α)
            * ((1 + ‖g x‖ ^ 2) ^ ((p - 1) / 2) * ‖g x - gv x‖) := by ring
      _ ≤ σ (R + C₁ * R ^ α)
            * ((p - 1) / p * (1 + ‖g x‖ ^ 2) ^ (p / 2)
              + 1 / p * ‖g x - gv x‖ ^ p) :=
          mul_le_mul_of_nonneg_left hyoung hΘ0
  -- the integrand is integrable (Hölder) and so is the majorant
  have hpairmeas : ∀ F H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      AEStronglyMeasurable F (volume.restrict (Metric.ball x₀ R)) →
      AEStronglyMeasurable H (volume.restrict (Metric.ball x₀ R)) →
      AEStronglyMeasurable (fun x => ∑ i, F x i * H x i)
        (volume.restrict (Metric.ball x₀ R)) := by
    intro F H hF hH
    have hinner : AEStronglyMeasurable (fun x => (inner ℝ (H x) (F x) : ℝ))
        (volume.restrict (Metric.ball x₀ R)) :=
      (continuous_inner (𝕜 := ℝ)
        (E := EuclideanSpace ℝ (Fin n))).comp_aestronglyMeasurable (hH.prodMk hF)
    exact hinner.congr (Filter.Eventually.of_forall fun x => (hIP (F x) (H x)).symm)
  have hFmeas := hpairmeas (fun x => A x (u x) (g x) - A x₀ z₀ (g x))
    (fun x => g x - gv x) (hALp.sub hA0Lp).aestronglyMeasurable
    hdLp.aestronglyMeasurable
  have hmajint : Integrable
      (fun x => σ (R + C₁ * R ^ α)
        * ((p - 1) / p * (1 + ‖g x‖ ^ 2) ^ (p / 2)
          + 1 / p * ‖g x - gv x‖ ^ p))
      (volume.restrict (Metric.ball x₀ R)) :=
    ((hhalfint.const_mul _).add (hdp.const_mul _)).const_mul _
  have hFae : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      ‖∑ i, (A x (u x) (g x) - A x₀ z₀ (g x)) i * (g x - gv x) i‖
        ≤ σ (R + C₁ * R ^ α)
            * ((p - 1) / p * (1 + ‖g x‖ ^ 2) ^ (p / 2)
              + 1 / p * ‖g x - gv x‖ ^ p) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [Real.norm_eq_abs]
    exact hpt x hx
  have hFint : Integrable
      (fun x => ∑ i, (A x (u x) (g x) - A x₀ z₀ (g x)) i * (g x - gv x) i)
      (volume.restrict (Metric.ball x₀ R)) := hmajint.mono' hFmeas hFae
  -- integrate
  calc |∫ x in Metric.ball x₀ R,
          ∑ i, (A x (u x) (g x) - A x₀ z₀ (g x)) i * (g x - gv x) i|
      ≤ ∫ x in Metric.ball x₀ R,
          |∑ i, (A x (u x) (g x) - A x₀ z₀ (g x)) i * (g x - gv x) i| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x in Metric.ball x₀ R, σ (R + C₁ * R ^ α)
          * ((p - 1) / p * (1 + ‖g x‖ ^ 2) ^ (p / 2)
            + 1 / p * ‖g x - gv x‖ ^ p) := by
        refine integral_mono_ae hFint.abs hmajint ?_
        filter_upwards [hFae] with x h
        simpa [Real.norm_eq_abs] using h
    _ = σ (R + C₁ * R ^ α)
          * ((p - 1) / p * (∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2))
            + 1 / p * ∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p) := by
        rw [integral_const_mul, integral_add (hhalfint.const_mul _)
          (hdp.const_mul _), integral_const_mul, integral_const_mul]
