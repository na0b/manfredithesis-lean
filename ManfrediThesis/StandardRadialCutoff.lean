import ManfrediThesis.Preamble
open MeasureTheory

/-- The standard radial cut-off between two concentric balls, with a gradient
bound whose constant is absolute: for every `n ≥ 1` there is an `L > 0` such
that for all `x₀` and all `0 < ρ₀ < ρ₁` there is a smooth, compactly supported
`ζ` with `0 ≤ ζ ≤ 1`, `ζ = 1` on the closed inner ball, support inside the open
outer ball, and `∑ᵢ (∂ᵢζ)² ≤ L/(ρ₁-ρ₀)²` everywhere.  The constant is bound
before the centre and the two radii, which is what makes it absolute. -/
theorem StandardRadialCutoff :
    ∀ n : ℕ, 1 ≤ n →
      ∃ L : ℝ, 0 < L ∧
        ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (ρ₀ ρ₁ : ℝ), 0 < ρ₀ → ρ₀ < ρ₁ →
          ∃ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
            ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧
            tsupport ζ ⊆ Metric.ball x₀ ρ₁ ∧
            (∀ x, 0 ≤ ζ x) ∧ (∀ x, ζ x ≤ 1) ∧
            (∀ x ∈ Metric.closedBall x₀ ρ₀, ζ x = 1) ∧
            (∀ x, ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2
                ≤ L / (ρ₁ - ρ₀) ^ 2) := by
  intro n _hn
  have hcd : ContDiff ℝ (⊤:ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  have hdc : Continuous (deriv Real.smoothTransition) :=
    hcd.continuous_deriv (by exact_mod_cast le_top)
  have hd0 : ∀ t : ℝ, t < 0 → deriv Real.smoothTransition t = 0 := by
    intro t h
    have he : Real.smoothTransition =ᶠ[nhds t] fun _ => (0:ℝ) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Iio h] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [he.deriv_eq]; simp
  have hd1 : ∀ t : ℝ, 1 < t → deriv Real.smoothTransition t = 0 := by
    intro t h
    have he : Real.smoothTransition =ᶠ[nhds t] fun _ => (1:ℝ) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi h] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [he.deriv_eq]; simp
  obtain ⟨Λ, hΛ0, hΛ⟩ : ∃ L : ℝ, 0 ≤ L ∧
      ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ L := by
    obtain ⟨L, hL⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
      hdc.continuousOn
    refine ⟨max L 0, le_max_right _ _, ?_⟩
    intro t
    rcases lt_or_ge t 0 with h | h
    · rw [hd0 t h]; simp
    rcases le_or_gt t 1 with h1 | h1
    · exact le_trans (by simpa using hL t ⟨h, h1⟩) (le_max_left _ _)
    · rw [hd1 t h1]; simp
  refine ⟨16 * Λ ^ 2 + 1, by positivity, ?_⟩
  intro x₀ ρ₀ ρ₁ hρ₀ hρ
  have hmain : ∃ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤:ℕ∞) ζ ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ Metric.ball x₀ ρ₁ ∧
      (∀ x, 0 ≤ ζ x) ∧ (∀ x, ζ x ≤ 1) ∧
      (∀ x ∈ Metric.closedBall x₀ ρ₀, ζ x = 1) ∧
      (∀ x, ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2
          ≤ 16 * Λ ^ 2 / (ρ₁ - ρ₀) ^ 2) := by
      have hcd : ContDiff ℝ (⊤:ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
      have hd : (0:ℝ) < ρ₁ - ρ₀ := by linarith
      obtain ⟨ρa, hρadef⟩ : ∃ t : ℝ, t = ρ₀ + (ρ₁ - ρ₀) / 4 := ⟨_, rfl⟩
      obtain ⟨ρb, hρbdef⟩ : ∃ t : ℝ, t = ρ₀ + 3 * (ρ₁ - ρ₀) / 4 := ⟨_, rfl⟩
      have hab : ρ₀ < ρa := by rw [hρadef]; linarith
      have hbb : ρa < ρb := by rw [hρadef, hρbdef]; linarith
      have hb1 : ρb < ρ₁ := by rw [hρbdef]; linarith
      have hρapos : 0 < ρa := lt_trans hρ₀ hab
      have hρbpos : 0 < ρb := lt_trans hρapos hbb
      obtain ⟨D, hDdef⟩ : ∃ t : ℝ, t = ρb ^ 2 - ρa ^ 2 := ⟨_, rfl⟩
      have hD0 : 0 < D := by rw [hDdef]; nlinarith
      obtain ⟨Q, hQdef⟩ : ∃ F : EuclideanSpace ℝ (Fin n) → ℝ,
        F = fun x => (ρb ^ 2 - ‖x - x₀‖ ^ 2) * D⁻¹ := ⟨_, rfl⟩
      have hnsq : ContDiff ℝ (⊤:ℕ∞) (fun x : EuclideanSpace ℝ (Fin n) => ‖x - x₀‖ ^ 2) :=
        (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
      have hQc : ContDiff ℝ (⊤:ℕ∞) Q := by
        rw [hQdef]; exact (contDiff_const.sub hnsq).mul contDiff_const
      -- the fderiv of `Q`, applied to a basis vector
      have hQfd : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
          (fderiv ℝ Q x) (EuclideanSpace.single i (1:ℝ)) = -2 * ((x - x₀) i) * D⁻¹ := by
        intro x i
        have hN : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => ‖y - x₀‖ ^ 2)
            ((2:ℕ) • (innerSL ℝ (x - x₀)).comp (ContinuousLinearMap.id ℝ _)) x := by
          simpa using ((hasFDerivAt_id x).sub_const x₀).norm_sq
        have hC : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => ρb ^ 2 - ‖y - x₀‖ ^ 2)
            (-((2:ℕ) • (innerSL ℝ (x - x₀)).comp (ContinuousLinearMap.id ℝ _))) x :=
          hN.const_sub _
        rw [hQdef, (hC.mul_const D⁻¹).fderiv]
        simp [EuclideanSpace.inner_single_right]
        ring
      -- values of `Q`
      have hQ1 : ∀ x : EuclideanSpace ℝ (Fin n), ‖x - x₀‖ ≤ ρ₀ → 1 ≤ Q x := by
        intro x hx
        rw [hQdef]
        have h1 : ‖x - x₀‖ ^ 2 ≤ ρ₀ ^ 2 := by
          have := norm_nonneg (x - x₀)
          nlinarith
        rw [le_mul_inv_iff₀ hD0, hDdef]
        nlinarith
      have hQ0 : ∀ x : EuclideanSpace ℝ (Fin n), ρb ≤ ‖x - x₀‖ → Q x ≤ 0 := by
        intro x hx
        rw [hQdef]
        have h1 : ρb ^ 2 ≤ ‖x - x₀‖ ^ 2 := by nlinarith [hρbpos]
        have : ρb ^ 2 - ‖x - x₀‖ ^ 2 ≤ 0 := by linarith
        exact mul_nonpos_of_nonpos_of_nonneg this (le_of_lt (inv_pos.2 hD0))
      have hQ0' : ∀ x : EuclideanSpace ℝ (Fin n), ρb < ‖x - x₀‖ → Q x < 0 := by
        intro x hx
        rw [hQdef]
        have h1 : ρb ^ 2 < ‖x - x₀‖ ^ 2 := by nlinarith [hρbpos]
        have h2 : ρb ^ 2 - ‖x - x₀‖ ^ 2 < 0 := by linarith
        exact mul_neg_of_neg_of_pos h2 (inv_pos.2 hD0)
      have hDexp : D = (ρ₁ - ρ₀) / 2 * (2 * ρ₀ + (ρ₁ - ρ₀)) := by
        rw [hDdef, hρadef, hρbdef]; ring
      have hkey : 4 * ρb ^ 2 * (D⁻¹) ^ 2 ≤ 16 / (ρ₁ - ρ₀) ^ 2 := by
        have hLHS : 4 * ρb ^ 2 * (D⁻¹) ^ 2 = 4 * ρb ^ 2 / D ^ 2 := by
          rw [inv_pow, ← div_eq_mul_inv]
        have hble : ρb ≤ 2 * ρ₀ + (ρ₁ - ρ₀) := by rw [hρbdef]; linarith
        have hsq : ρb ^ 2 ≤ (2 * ρ₀ + (ρ₁ - ρ₀)) ^ 2 := by nlinarith [hρbpos]
        rw [hLHS, div_le_div_iff₀ (by positivity) (by positivity), hDexp]
        nlinarith [mul_le_mul_of_nonneg_right hsq
          (by positivity : (0:ℝ) ≤ 4 * (ρ₁ - ρ₀) ^ 2)]
      refine ⟨fun x => Real.smoothTransition (Q x), hcd.comp hQc, ?_, ?_,
        fun x => Real.smoothTransition.nonneg _, fun x => Real.smoothTransition.le_one _, ?_, ?_⟩
      · -- compact support
        refine HasCompactSupport.intro (isCompact_closedBall x₀ ρb) ?_
        intro x hx
        simp only [Metric.mem_closedBall, not_le] at hx
        refine Real.smoothTransition.zero_of_nonpos (hQ0 x ?_)
        rw [← dist_eq_norm]
        exact le_of_lt hx
      · -- tsupport
        have hsupp : (Function.support fun x => Real.smoothTransition (Q x))
            ⊆ Metric.closedBall x₀ ρb := by
          intro x hx
          by_contra hc
          simp only [Metric.mem_closedBall, not_le] at hc
          exact hx (Real.smoothTransition.zero_of_nonpos
            (hQ0 x (by rw [← dist_eq_norm]; linarith)))
        refine subset_trans (closure_minimal hsupp Metric.isClosed_closedBall) ?_
        intro y hy
        simp only [Metric.mem_closedBall] at hy
        exact Metric.mem_ball.2 (lt_of_le_of_lt hy hb1)
      · intro x hx
        simp only [Metric.mem_closedBall] at hx
        exact Real.smoothTransition.one_of_one_le (hQ1 x (by rwa [dist_eq_norm] at hx))
      · intro x
        have htop : ((⊤:ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
        have hσd : HasDerivAt Real.smoothTransition
            (deriv Real.smoothTransition (Q x)) (Q x) :=
          (hcd.differentiable htop).differentiableAt.hasDerivAt
        have hQd : HasFDerivAt Q (fderiv ℝ Q x) x :=
          (hQc.differentiable htop).differentiableAt.hasFDerivAt
        have hcomp : HasFDerivAt (Real.smoothTransition ∘ Q)
            (deriv Real.smoothTransition (Q x) • fderiv ℝ Q x) x :=
          HasDerivAt.comp_hasFDerivAt x hσd hQd
        have hfd : ∀ i : Fin n,
            (fderiv ℝ (fun y => Real.smoothTransition (Q y)) x)
                (EuclideanSpace.single i (1:ℝ))
              = deriv Real.smoothTransition (Q x) * (-2 * ((x - x₀) i) * D⁻¹) := by
          intro i
          have hE : fderiv ℝ (fun y => Real.smoothTransition (Q y)) x
              = deriv Real.smoothTransition (Q x) • fderiv ℝ Q x := hcomp.fderiv
          rw [hE]
          simp [hQfd x i]
        have hsum : ∑ i, ((fderiv ℝ (fun y => Real.smoothTransition (Q y)) x)
              (EuclideanSpace.single i (1:ℝ))) ^ 2
            = (deriv Real.smoothTransition (Q x)) ^ 2 * (4 * (D⁻¹) ^ 2) * ‖x - x₀‖ ^ 2 := by
          have e : ∀ i : Fin n, ((fderiv ℝ (fun y => Real.smoothTransition (Q y)) x)
                (EuclideanSpace.single i (1:ℝ))) ^ 2
              = (deriv Real.smoothTransition (Q x)) ^ 2 * (4 * (D⁻¹) ^ 2)
                * ((x - x₀) i) ^ 2 := by
            intro i
            rw [hfd i]
            ring
          rw [Finset.sum_congr rfl (fun i _ => e i), ← Finset.mul_sum,
            ← EuclideanSpace.real_norm_sq_eq]
        rw [hsum]
        rcases le_or_gt ‖x - x₀‖ ρb with hc | hc
        · have h1 : (deriv Real.smoothTransition (Q x)) ^ 2 ≤ Λ ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hΛ _) 2
          have h2 : ‖x - x₀‖ ^ 2 ≤ ρb ^ 2 := by nlinarith [norm_nonneg (x - x₀)]
          calc (deriv Real.smoothTransition (Q x)) ^ 2 * (4 * (D⁻¹) ^ 2) * ‖x - x₀‖ ^ 2
              ≤ Λ ^ 2 * (4 * (D⁻¹) ^ 2) * ρb ^ 2 :=
                mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) h2
                  (by positivity) (by positivity)
            _ = Λ ^ 2 * (4 * ρb ^ 2 * (D⁻¹) ^ 2) := by ring
            _ ≤ Λ ^ 2 * (16 / (ρ₁ - ρ₀) ^ 2) := mul_le_mul_of_nonneg_left hkey (by positivity)
            _ = 16 * Λ ^ 2 / (ρ₁ - ρ₀) ^ 2 := by ring
        · rw [hd0 _ (hQ0' x hc)]
          have hz : (0:ℝ) ^ 2 * (4 * (D⁻¹) ^ 2) * ‖x - x₀‖ ^ 2 = 0 := by ring
          rw [hz]
          positivity
  obtain ⟨ζ, h1, h2, h3, h4, h5, h6, h7⟩ := hmain
  refine ⟨ζ, h1, h2, h3, h4, h5, h6, fun x => ?_⟩
  refine le_trans (h7 x) ?_
  have hd : (0:ℝ) < (ρ₁ - ρ₀) ^ 2 := by positivity
  rw [div_le_div_iff_of_pos_right hd]
  linarith only [sq_nonneg Λ]
