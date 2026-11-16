import ManfrediThesis.Preamble
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
open MeasureTheory

/-- The weight sandwich.  The scalar kernel
`K(h,e) = ∫ (|h + √e z|²)^{p/2−1} ρ(z) dz`, through which both structure
conditions of the mollified field pass, is comparable to `(e + |h|²)^{p/2−1}`
with two constants depending only on `n`, `p` and the kernel `ρ`. -/
theorem WeightSandwich :
    ∀ (n : ℕ) (p : ℝ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ),
      2 ≤ n → 1 < p →
      ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) →
      tsupport ρ ⊆ Metric.closedBall 0 1 →
      (∫ z, ρ z) = 1 →
      (∃ κ : ℝ, 0 < κ ∧
        ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (7 / 8), κ ≤ ρ z) →
      ∃ c₁ C₂ : ℝ, 0 < c₁ ∧ c₁ ≤ C₂ ∧
        ∀ (h : EuclideanSpace ℝ (Fin n)) (e : ℝ), 0 < e →
          c₁ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)
              ≤ ∫ z, (‖h + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ρ z
            ∧ (∫ z, (‖h + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ρ z)
              ≤ C₂ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) := by
  intro n p ρ hn hp hρsm hρ0 hρsupp hρint hκex
  obtain ⟨κ, hκ0, hκ⟩ := hκex
  have hnpos : 0 < n := by omega
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnt : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, hnpos⟩ (1 : ℝ), ?_⟩⟩
    intro hc
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hnpos⟩) hc
    simp at h
  -- the kernel, written with a single real power
  have hker : ∀ v : EuclideanSpace ℝ (Fin n),
      (‖v‖ ^ 2 : ℝ) ^ (p / 2 - 1) = ‖v‖ ^ (p - 2) := by
    intro v
    rw [← Real.rpow_natCast ‖v‖ 2, ← Real.rpow_mul (norm_nonneg v)]
    congr 1
    push_cast
    ring
  have hnm0 : ∀ y : EuclideanSpace ℝ (Fin n), 0 ≤ ‖y‖ ^ (p - 2) :=
    fun y => Real.rpow_nonneg (norm_nonneg y) _
  -- the mollifier: continuity, compact support, a sup bound, and vanishing
  have hρcont : Continuous ρ := hρsm.continuous
  have hρcs : HasCompactSupport ρ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 1) isClosed_closure hρsupp
  have hρzero : ∀ z : EuclideanSpace ℝ (Fin n), 1 < ‖z‖ → ρ z = 0 := by
    intro z hz
    refine image_eq_zero_of_notMem_tsupport (fun hc => ?_)
    have := hρsupp hc
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ρ z ≤ M := by
    obtain ⟨L, hL⟩ := hρcs.exists_bound_of_continuousOn hρcont.continuousOn
    refine ⟨max L 0, le_max_right _ _, fun z => ?_⟩
    by_cases hz : z ∈ tsupport ρ
    · exact le_trans (le_trans (le_abs_self _) (by simpa using hL z hz)) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz]
      exact le_max_right _ _
  have hρintble : Integrable ρ := hρcont.integrable_of_hasCompactSupport hρcs
  -- measurability and ball-integrability of `y ↦ |y|^{p-2}`
  have hnm : Measurable (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ (p - 2)) := by
    have heq : (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ (p - 2))
        = fun y => if ‖y‖ = 0 then (0 : ℝ) ^ (p - 2)
          else Real.exp (Real.log ‖y‖ * (p - 2)) := by
      funext y
      by_cases h : ‖y‖ = 0
      · rw [if_pos h, h]
      · rw [if_neg h, Real.rpow_def_of_pos (lt_of_le_of_ne (norm_nonneg y) (Ne.symm h))]
    rw [heq]
    refine Measurable.ite ?_ measurable_const ((measurable_norm.log.mul_const _).exp)
    exact measurable_norm (measurableSet_singleton (0 : ℝ))
  have hballint : ∀ R : ℝ,
      IntegrableOn (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ (p - 2))
        (Metric.ball 0 R) volume := by
    intro R
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
    have hd : 1 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by rw [hfr]; omega
    have hα : (2 : ℝ) - p < (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) := by
      rw [hfr]
      linarith
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := 2 - p) hd hα ?_
      hnm.aestronglyMeasurable
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (hnm0 y), one_mul,
      show -(2 - p) = p - 2 from by ring]
  -- the translated indicator majorant
  have hGint : ∀ (a : EuclideanSpace ℝ (Fin n)) (R : ℝ),
      Integrable (fun z => Set.indicator (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
        (fun y => ‖y‖ ^ (p - 2)) (a + z)) volume := by
    intro a R
    have h1 : Integrable (Set.indicator (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
        (fun y => ‖y‖ ^ (p - 2))) volume :=
      (integrable_indicator_iff measurableSet_ball).2 (hballint R)
    exact h1.comp_add_left a
  have hGnn : ∀ (a z : EuclideanSpace ℝ (Fin n)) (R : ℝ),
      0 ≤ Set.indicator (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
        (fun y => ‖y‖ ^ (p - 2)) (a + z) := by
    intro a z R
    by_cases hz : a + z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R
    · rw [Set.indicator_of_mem hz]
      exact hnm0 _
    · rw [Set.indicator_of_notMem hz]
  have hKm : ∀ a : EuclideanSpace ℝ (Fin n),
      AEStronglyMeasurable (fun z => ‖a + z‖ ^ (p - 2) * ρ z) volume :=
    fun a => ((hnm.comp (measurable_const_add a)).mul hρcont.measurable).aestronglyMeasurable
  have hIint : ∀ a : EuclideanSpace ℝ (Fin n),
      Integrable (fun z => ‖a + z‖ ^ (p - 2) * ρ z) volume := by
    intro a
    refine Integrable.mono' ((hGint a (‖a‖ + 2)).const_mul M) (hKm a) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnm0 _) (hρ0 z))]
    by_cases hz : 1 < ‖z‖
    · rw [hρzero z hz, mul_zero]
      exact mul_nonneg hM0 (hGnn a z _)
    · have hmem : a + z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (‖a‖ + 2) := by
        rw [Metric.mem_ball, dist_zero_right]
        calc ‖a + z‖ ≤ ‖a‖ + ‖z‖ := norm_add_le _ _
          _ < ‖a‖ + 2 := by have h' := not_lt.1 hz; linarith
      rw [Set.indicator_of_mem hmem]
      calc ‖a + z‖ ^ (p - 2) * ρ z ≤ ‖a + z‖ ^ (p - 2) * M :=
            mul_le_mul_of_nonneg_left (hM z) (hnm0 _)
        _ = M * ‖a + z‖ ^ (p - 2) := by ring
  have hSint0 : (0:ℝ)
      ≤ ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 4, ‖y‖ ^ (p - 2) :=
    integral_nonneg fun y => hnm0 y
  have hIbd : ∀ a : EuclideanSpace ℝ (Fin n), ‖a‖ ≤ 2 →
      (∫ z, ‖a + z‖ ^ (p - 2) * ρ z)
        ≤ M * ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 4, ‖y‖ ^ (p - 2) := by
    intro a ha
    have hstep : (∫ z, ‖a + z‖ ^ (p - 2) * ρ z)
        ≤ ∫ z, M * Set.indicator (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 4)
            (fun y => ‖y‖ ^ (p - 2)) (a + z) := by
      refine integral_mono (hIint a) ((hGint a 4).const_mul M) (fun z => ?_)
      by_cases hz : 1 < ‖z‖
      · rw [hρzero z hz, mul_zero]
        exact mul_nonneg hM0 (hGnn a z _)
      · have hmem : a + z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 4 := by
          rw [Metric.mem_ball, dist_zero_right]
          calc ‖a + z‖ ≤ ‖a‖ + ‖z‖ := norm_add_le _ _
            _ < 4 := by have h' := not_lt.1 hz; linarith
        rw [Set.indicator_of_mem hmem]
        calc ‖a + z‖ ^ (p - 2) * ρ z ≤ ‖a + z‖ ^ (p - 2) * M :=
              mul_le_mul_of_nonneg_left (hM z) (hnm0 _)
          _ = M * ‖a + z‖ ^ (p - 2) := by ring
    rw [integral_const_mul,
      integral_add_left_eq_self (Set.indicator (Metric.ball
        (0 : EuclideanSpace ℝ (Fin n)) 4) (fun y => ‖y‖ ^ (p - 2))) a,
      integral_indicator measurableSet_ball] at hstep
    exact hstep
  -- the two-sided comparison of real powers
  have hsand : ∀ x y lo hi : ℝ, 0 < lo → 0 < x → 0 < y →
      lo * y ≤ x → x ≤ hi * y →
      min (lo ^ (p / 2 - 1)) (hi ^ (p / 2 - 1)) * y ^ (p / 2 - 1) ≤ x ^ (p / 2 - 1)
        ∧ x ^ (p / 2 - 1)
          ≤ max (lo ^ (p / 2 - 1)) (hi ^ (p / 2 - 1)) * y ^ (p / 2 - 1) := by
    intro x y lo hi hlo hx hy h1 h2
    have hy0 : (0 : ℝ) < y ^ (p / 2 - 1) := Real.rpow_pos_of_pos hy _
    have hdiv : (0 : ℝ) < x / y := div_pos hx hy
    have hxy : x ^ (p / 2 - 1) = (x / y) ^ (p / 2 - 1) * y ^ (p / 2 - 1) := by
      rw [← Real.mul_rpow hdiv.le hy.le]
      congr 1
      field_simp
    have hlo' : lo ≤ x / y := by rw [le_div_iff₀ hy]; linarith
    have hhi' : x / y ≤ hi := by rw [div_le_iff₀ hy]; linarith
    rcases le_or_gt 0 (p / 2 - 1) with hq | hq
    · refine ⟨?_, ?_⟩
      · rw [hxy]
        exact mul_le_mul_of_nonneg_right
          (le_trans (min_le_left _ _) (Real.rpow_le_rpow hlo.le hlo' hq)) hy0.le
      · rw [hxy]
        exact mul_le_mul_of_nonneg_right
          (le_trans (Real.rpow_le_rpow hdiv.le hhi' hq) (le_max_right _ _)) hy0.le
    · refine ⟨?_, ?_⟩
      · rw [hxy]
        exact mul_le_mul_of_nonneg_right
          (le_trans (min_le_right _ _)
            (Real.rpow_le_rpow_of_nonpos hdiv hhi' hq.le)) hy0.le
      · rw [hxy]
        exact mul_le_mul_of_nonneg_right
          (le_trans (Real.rpow_le_rpow_of_nonpos hlo hlo' hq.le) (le_max_left _ _)) hy0.le
  -- the scaling identity
  have hscale : ∀ (h : EuclideanSpace ℝ (Fin n)) (e : ℝ), 0 < e →
      (∫ z, ‖h + Real.sqrt e • z‖ ^ (p - 2) * ρ z)
        = (Real.sqrt e) ^ (p - 2)
          * ∫ z, ‖(Real.sqrt e)⁻¹ • h + z‖ ^ (p - 2) * ρ z := by
    intro h e he
    have ht : 0 < Real.sqrt e := Real.sqrt_pos.2 he
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show ‖h + Real.sqrt e • z‖ ^ (p - 2) * ρ z
      = Real.sqrt e ^ (p - 2) * (‖(Real.sqrt e)⁻¹ • h + z‖ ^ (p - 2) * ρ z)
    have hid : h + Real.sqrt e • z
        = Real.sqrt e • ((Real.sqrt e)⁻¹ • h + z) := by
      rw [smul_add, smul_inv_smul₀ (ne_of_gt ht)]
    rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
      Real.mul_rpow ht.le (norm_nonneg _)]
    ring
  have hKeq : ∀ (h : EuclideanSpace ℝ (Fin n)) (e : ℝ),
      (∫ z, (‖h + Real.sqrt e • z‖ ^ 2 : ℝ) ^ (p / 2 - 1) * ρ z)
        = ∫ z, ‖h + Real.sqrt e • z‖ ^ (p - 2) * ρ z := by
    intro h e
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (‖h + Real.sqrt e • z‖ ^ 2 : ℝ) ^ (p / 2 - 1) * ρ z
      = ‖h + Real.sqrt e • z‖ ^ (p - 2) * ρ z
    rw [hker]
  -- the mass of the good ball, uniformly in its centre
  obtain ⟨m, hm0, hmZ⟩ : ∃ m : ℝ, 0 < m ∧
      ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 →
        m ≤ ∫ z in Metric.ball ((3 / 4 : ℝ) • u) (1 / 8), ρ z := by
    have hvol : (0 : ℝ)
        < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 8))).toReal := by
      have h1 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 8)) ≠ 0 :=
        (Metric.isOpen_ball.measure_pos volume ⟨0, by simp⟩).ne'
      have h2 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 8)) ≠ ⊤ :=
        (Metric.isBounded_ball.measure_lt_top).ne
      exact ENNReal.toReal_pos h1 h2
    refine ⟨κ * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 8))).toReal,
      by positivity, fun u hu => ?_⟩
    have hsub : Metric.ball ((3 / 4 : ℝ) • u) (1 / 8)
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (7 / 8) := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖((3 : ℝ) / 4) • u‖ = 3 / 4 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/4), hu]
        norm_num
      calc ‖z‖ ≤ ‖z - (3 / 4 : ℝ) • u‖ + ‖((3 : ℝ) / 4) • u‖ := by
            simpa using norm_add_le (z - (3 / 4 : ℝ) • u) ((3 / 4 : ℝ) • u)
        _ ≤ 1 / 8 + 3 / 4 := by rw [h1]; linarith
        _ = 7 / 8 := by norm_num
    have hle : (∫ z in Metric.ball ((3 / 4 : ℝ) • u) (1 / 8), κ)
        ≤ ∫ z in Metric.ball ((3 / 4 : ℝ) • u) (1 / 8), ρ z := by
      refine setIntegral_mono_on (integrableOn_const (μ := volume)
        (Metric.isBounded_ball.measure_lt_top).ne)
        (hρintble.integrableOn) measurableSet_ball (fun z hz => hκ z (hsub hz))
    refine le_trans (le_of_eq ?_) hle
    rw [setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
      Measure.addHaar_ball_center volume ((3 / 4 : ℝ) • u) (1 / 8)]
    ring
  -- the four comparison constants
  have hA1 : (0 : ℝ) < min ((1 / 5 : ℝ) ^ (p / 2 - 1)) ((9 / 4 : ℝ) ^ (p / 2 - 1)) :=
    lt_min (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)
  have hB1 : (0 : ℝ) < min ((5 / 64 : ℝ) ^ (p / 2 - 1)) ((2 : ℝ) ^ (p / 2 - 1)) :=
    lt_min (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨min (min ((1 / 5 : ℝ) ^ (p / 2 - 1)) ((9 / 4 : ℝ) ^ (p / 2 - 1)))
      (m * min ((5 / 64 : ℝ) ^ (p / 2 - 1)) ((2 : ℝ) ^ (p / 2 - 1))),
    max (max ((1 / 5 : ℝ) ^ (p / 2 - 1)) ((9 / 4 : ℝ) ^ (p / 2 - 1)))
      (M * (∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 4, ‖y‖ ^ (p - 2))
        * max ((1 / 5 : ℝ) ^ (p / 2 - 1)) ((1 : ℝ) ^ (p / 2 - 1))),
    lt_min hA1 (by positivity), ?_, ?_⟩
  · exact le_trans (min_le_left _ _)
      (le_trans (min_le_max) (le_max_left _ _))
  -- the geometry of the good ball
  have hgeom : ∀ a u z : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 → 0 ≤ inner ℝ u a →
      ‖z - (3 / 4 : ℝ) • u‖ ≤ 1 / 8 → (5 / 8 : ℝ) ≤ ‖a + z‖ := by
    intro a u z hu hua hz
    have hkey : (3 / 4 : ℝ) ≤ ‖a + (3 / 4 : ℝ) • u‖ := by
      have hsq : ‖a + (3 / 4 : ℝ) • u‖ ^ 2
          = ‖a‖ ^ 2 + 2 * ((3 / 4 : ℝ) * inner ℝ u a) + (3 / 4 : ℝ) ^ 2 * ‖u‖ ^ 2 := by
        rw [norm_add_sq_real, norm_smul, real_inner_smul_right]
        ring_nf
        rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3 / 4)]
        rw [real_inner_comm]
        ring
      nlinarith [hsq, sq_nonneg ‖a‖, norm_nonneg (a + (3 / 4 : ℝ) • u), hu, hua]
    have h2 : ‖a + (3 / 4 : ℝ) • u‖ ≤ ‖a + z‖ + ‖z - (3 / 4 : ℝ) • u‖ := by
      have hid : a + (3 / 4 : ℝ) • u = (a + z) - (z - (3 / 4 : ℝ) • u) := by abel
      rw [hid]
      exact norm_sub_le _ _
    linarith
  have hKint : ∀ (h : EuclideanSpace ℝ (Fin n)) (e : ℝ), 0 < e →
      Integrable (fun z => ‖h + Real.sqrt e • z‖ ^ (p - 2) * ρ z) volume := by
    intro h e he
    have ht : 0 < Real.sqrt e := Real.sqrt_pos.2 he
    refine ((hIint ((Real.sqrt e)⁻¹ • h)).const_mul ((Real.sqrt e) ^ (p - 2))).congr ?_
    filter_upwards with z
    show Real.sqrt e ^ (p - 2) * (‖(Real.sqrt e)⁻¹ • h + z‖ ^ (p - 2) * ρ z)
      = ‖h + Real.sqrt e • z‖ ^ (p - 2) * ρ z
    have hid : h + Real.sqrt e • z = Real.sqrt e • ((Real.sqrt e)⁻¹ • h + z) := by
      rw [smul_add, smul_inv_smul₀ (ne_of_gt ht)]
    rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
      Real.mul_rpow ht.le (norm_nonneg _)]
    ring
  intro h e he
  rw [hKeq h e]
  have ht : 0 < Real.sqrt e := Real.sqrt_pos.2 he
  have ht2 : Real.sqrt e ^ 2 = e := Real.sq_sqrt he.le
  have hhn0 : (0 : ℝ) ≤ ‖h‖ := norm_nonneg h
  have hW0 : (0 : ℝ) < e + ‖h‖ ^ 2 := by nlinarith [sq_nonneg ‖h‖]
  have hWq : (0 : ℝ) < (e + ‖h‖ ^ 2) ^ (p / 2 - 1) := Real.rpow_pos_of_pos hW0 _
  have hzn1 : ∀ z : EuclideanSpace ℝ (Fin n), ‖z‖ ≤ 1 →
      ‖Real.sqrt e • z‖ ≤ Real.sqrt e := by
    intro z hz
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    calc Real.sqrt e * ‖z‖ ≤ Real.sqrt e * 1 := mul_le_mul_of_nonneg_left hz ht.le
      _ = Real.sqrt e := by ring
  rcases le_or_gt ‖h‖ (2 * Real.sqrt e) with hcase | hcase
  · -- `|h| ≤ 2√e`
    have hW5 : e + ‖h‖ ^ 2 ≤ 5 * e := by nlinarith [ht2, hhn0, ht.le]
    constructor
    · -- the lower bound, on the good ball
      obtain ⟨u, hu1, huh⟩ : ∃ u : EuclideanSpace ℝ (Fin n),
          ‖u‖ = 1 ∧ 0 ≤ inner ℝ u ((Real.sqrt e)⁻¹ • h) := by
        by_cases hh : h = 0
        · exact ⟨EuclideanSpace.single ⟨0, hnpos⟩ (1 : ℝ), by simp, by rw [hh]; simp⟩
        · have hhn : 0 < ‖h‖ := norm_pos_iff.2 hh
          refine ⟨‖h‖⁻¹ • h, ?_, ?_⟩
          · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hhn),
              inv_mul_cancel₀ (ne_of_gt hhn)]
          · rw [real_inner_smul_left, real_inner_smul_right,
              real_inner_self_eq_norm_sq]
            positivity
      have hZsub : Metric.ball ((3 / 4 : ℝ) • u) (1 / 8)
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (7 / 8) := by
        intro z hz
        rw [Metric.mem_ball, dist_eq_norm] at hz
        rw [Metric.mem_closedBall, dist_zero_right]
        have h1 : ‖((3 : ℝ) / 4) • u‖ = 3 / 4 := by
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3 / 4), hu1]
          norm_num
        calc ‖z‖ ≤ ‖z - (3 / 4 : ℝ) • u‖ + ‖((3 : ℝ) / 4) • u‖ := by
              simpa using norm_add_le (z - (3 / 4 : ℝ) • u) ((3 / 4 : ℝ) • u)
          _ ≤ 1 / 8 + 3 / 4 := by rw [h1]; linarith
          _ = 7 / 8 := by norm_num
      have hptw : ∀ z ∈ Metric.ball ((3 / 4 : ℝ) • u) (1 / 8),
          min ((5 / 64 : ℝ) ^ (p / 2 - 1)) ((2 : ℝ) ^ (p / 2 - 1))
              * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) * ρ z
            ≤ ‖h + Real.sqrt e • z‖ ^ (p - 2) * ρ z := by
        intro z hz
        have hzn : ‖z‖ ≤ 7 / 8 := by
          have := hZsub hz
          rwa [Metric.mem_closedBall, dist_zero_right] at this
        have hzd : ‖z - (3 / 4 : ℝ) • u‖ ≤ 1 / 8 := by
          rw [Metric.mem_ball, dist_eq_norm] at hz
          linarith
        have hgeo := hgeom ((Real.sqrt e)⁻¹ • h) u z hu1 huh hzd
        have hid : h + Real.sqrt e • z
            = Real.sqrt e • ((Real.sqrt e)⁻¹ • h + z) := by
          rw [smul_add, smul_inv_smul₀ (ne_of_gt ht)]
        have hlow : (5 / 8 : ℝ) * Real.sqrt e ≤ ‖h + Real.sqrt e • z‖ := by
          rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
          calc (5 / 8 : ℝ) * Real.sqrt e = Real.sqrt e * (5 / 8) := by ring
            _ ≤ Real.sqrt e * ‖(Real.sqrt e)⁻¹ • h + z‖ :=
                mul_le_mul_of_nonneg_left hgeo ht.le
        have hup : ‖h + Real.sqrt e • z‖ ≤ ‖h‖ + Real.sqrt e := by
          calc ‖h + Real.sqrt e • z‖ ≤ ‖h‖ + ‖Real.sqrt e • z‖ := norm_add_le _ _
            _ ≤ ‖h‖ + Real.sqrt e := by linarith [hzn1 z (by linarith)]
        have hxpos : (0 : ℝ) < ‖h + Real.sqrt e • z‖ :=
          lt_of_lt_of_le (by positivity) hlow
        have hx0 : (0 : ℝ) < ‖h + Real.sqrt e • z‖ ^ 2 := by positivity
        have hsq1 : ((5 : ℝ) / 8 * Real.sqrt e) ^ 2 ≤ ‖h + Real.sqrt e • z‖ ^ 2 :=
          pow_le_pow_left₀ (by positivity) hlow 2
        have he1 : ((5 : ℝ) / 8 * Real.sqrt e) ^ 2 = 25 / 64 * e := by
          rw [mul_pow, ht2]; ring
        have hlo : (5 / 64 : ℝ) * (e + ‖h‖ ^ 2) ≤ ‖h + Real.sqrt e • z‖ ^ 2 := by
          rw [he1] at hsq1
          linarith
        have hsq2 : ‖h + Real.sqrt e • z‖ ^ 2 ≤ (‖h‖ + Real.sqrt e) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hup 2
        have hexp : (‖h‖ + Real.sqrt e) ^ 2
            = ‖h‖ ^ 2 + 2 * (‖h‖ * Real.sqrt e) + e := by
          rw [add_sq, ht2]; ring
        have hamgm : 2 * (‖h‖ * Real.sqrt e) ≤ ‖h‖ ^ 2 + e := by
          nlinarith [sq_nonneg (‖h‖ - Real.sqrt e), ht2]
        have hhi : ‖h + Real.sqrt e • z‖ ^ 2 ≤ 2 * (e + ‖h‖ ^ 2) := by linarith
        obtain ⟨hs1, -⟩ := hsand (‖h + Real.sqrt e • z‖ ^ 2) (e + ‖h‖ ^ 2)
          (5 / 64) 2 (by norm_num) hx0 hW0 hlo hhi
        rw [← hker]
        exact mul_le_mul_of_nonneg_right hs1 (hρ0 z)
      have hint1 : IntegrableOn
          (fun z => min ((5 / 64 : ℝ) ^ (p / 2 - 1)) ((2 : ℝ) ^ (p / 2 - 1))
            * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) * ρ z)
          (Metric.ball ((3 / 4 : ℝ) • u) (1 / 8)) volume :=
        (hρintble.const_mul _).integrableOn
      have hstep : min ((5 / 64 : ℝ) ^ (p / 2 - 1)) ((2 : ℝ) ^ (p / 2 - 1))
            * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)
            * ∫ z in Metric.ball ((3 / 4 : ℝ) • u) (1 / 8), ρ z
          ≤ ∫ z in Metric.ball ((3 / 4 : ℝ) • u) (1 / 8),
              ‖h + Real.sqrt e • z‖ ^ (p - 2) * ρ z := by
        rw [← integral_const_mul]
        exact setIntegral_mono_on hint1 ((hKint h e he).integrableOn)
          measurableSet_ball hptw
      have hZK : (∫ z in Metric.ball ((3 / 4 : ℝ) • u) (1 / 8),
            ‖h + Real.sqrt e • z‖ ^ (p - 2) * ρ z)
          ≤ ∫ z, ‖h + Real.sqrt e • z‖ ^ (p - 2) * ρ z :=
        setIntegral_le_integral (hKint h e he)
          (Filter.Eventually.of_forall fun z => mul_nonneg (hnm0 _) (hρ0 z))
      have hc0 : (0 : ℝ) ≤ min ((5 / 64 : ℝ) ^ (p / 2 - 1)) ((2 : ℝ) ^ (p / 2 - 1))
          * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) := mul_nonneg hB1.le hWq.le
      have hmbd : m * min ((5 / 64 : ℝ) ^ (p / 2 - 1)) ((2 : ℝ) ^ (p / 2 - 1))
            * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)
          ≤ min ((5 / 64 : ℝ) ^ (p / 2 - 1)) ((2 : ℝ) ^ (p / 2 - 1))
            * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)
            * ∫ z in Metric.ball ((3 / 4 : ℝ) • u) (1 / 8), ρ z := by
        calc m * min ((5 / 64 : ℝ) ^ (p / 2 - 1)) ((2 : ℝ) ^ (p / 2 - 1))
              * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)
            = (min ((5 / 64 : ℝ) ^ (p / 2 - 1)) ((2 : ℝ) ^ (p / 2 - 1))
              * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)) * m := by ring
          _ ≤ (min ((5 / 64 : ℝ) ^ (p / 2 - 1)) ((2 : ℝ) ^ (p / 2 - 1))
              * (e + ‖h‖ ^ 2) ^ (p / 2 - 1))
              * ∫ z in Metric.ball ((3 / 4 : ℝ) • u) (1 / 8), ρ z :=
              mul_le_mul_of_nonneg_left (hmZ u hu1) hc0
      refine le_trans ?_ (le_trans hmbd (le_trans hstep hZK))
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) hWq.le
    · -- the upper bound, by scaling
      rw [hscale h e he]
      have ha2 : ‖(Real.sqrt e)⁻¹ • h‖ ≤ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht), inv_mul_le_iff₀ ht]
        linarith
      have h1 := hIbd _ ha2
      have hI0 : (0 : ℝ) ≤ ∫ z, ‖(Real.sqrt e)⁻¹ • h + z‖ ^ (p - 2) * ρ z :=
        integral_nonneg fun z => mul_nonneg (hnm0 _) (hρ0 z)
      have hsq : Real.sqrt e ^ (p - 2) = e ^ (p / 2 - 1) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul he.le]
        congr 1
        ring
      obtain ⟨-, hs2⟩ := hsand e (e + ‖h‖ ^ 2) (1 / 5) 1 (by norm_num) he hW0
        (by linarith) (by nlinarith [sq_nonneg ‖h‖])
      have hts : Real.sqrt e ^ (p - 2)
          ≤ max ((1 / 5 : ℝ) ^ (p / 2 - 1)) ((1 : ℝ) ^ (p / 2 - 1))
            * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) := by rw [hsq]; exact hs2
      have hmax0 : (0 : ℝ) ≤ max ((1 / 5 : ℝ) ^ (p / 2 - 1)) ((1 : ℝ) ^ (p / 2 - 1)) :=
        le_trans (Real.rpow_nonneg (by norm_num) _) (le_max_left _ _)
      calc Real.sqrt e ^ (p - 2) * ∫ z, ‖(Real.sqrt e)⁻¹ • h + z‖ ^ (p - 2) * ρ z
          ≤ (max ((1 / 5 : ℝ) ^ (p / 2 - 1)) ((1 : ℝ) ^ (p / 2 - 1))
              * (e + ‖h‖ ^ 2) ^ (p / 2 - 1))
            * (M * ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 4, ‖y‖ ^ (p - 2)) :=
            mul_le_mul hts h1 hI0 (mul_nonneg hmax0 hWq.le)
        _ = (M * (∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 4, ‖y‖ ^ (p - 2))
              * max ((1 / 5 : ℝ) ^ (p / 2 - 1)) ((1 : ℝ) ^ (p / 2 - 1)))
            * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hWq.le
  · -- `|h| > 2√e`
    have hhn : 0 < ‖h‖ := by linarith
    have hsqe : Real.sqrt e ^ 2 < (‖h‖ / 2) ^ 2 :=
      pow_lt_pow_left₀ (by linarith) ht.le (by norm_num)
    have hWh : e + ‖h‖ ^ 2 ≤ 5 / 4 * ‖h‖ ^ 2 := by
      rw [ht2] at hsqe
      nlinarith [hsqe]
    have hWh2 : ‖h‖ ^ 2 ≤ e + ‖h‖ ^ 2 := by linarith
    have hptw : ∀ z : EuclideanSpace ℝ (Fin n),
        (min ((1 / 5 : ℝ) ^ (p / 2 - 1)) ((9 / 4 : ℝ) ^ (p / 2 - 1))
            * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) * ρ z
          ≤ ‖h + Real.sqrt e • z‖ ^ (p - 2) * ρ z)
        ∧ (‖h + Real.sqrt e • z‖ ^ (p - 2) * ρ z
          ≤ max ((1 / 5 : ℝ) ^ (p / 2 - 1)) ((9 / 4 : ℝ) ^ (p / 2 - 1))
            * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) * ρ z) := by
      intro z
      by_cases hz : 1 < ‖z‖
      · rw [hρzero z hz]
        simp
      · have hzn : ‖z‖ ≤ 1 := not_lt.1 hz
        have hsn := hzn1 z hzn
        have hlow : ‖h‖ - Real.sqrt e ≤ ‖h + Real.sqrt e • z‖ := by
          have hid : h = (h + Real.sqrt e • z) - Real.sqrt e • z := by abel
          have hns := norm_sub_le (h + Real.sqrt e • z) (Real.sqrt e • z)
          rw [← hid] at hns
          linarith
        have hup : ‖h + Real.sqrt e • z‖ ≤ ‖h‖ + Real.sqrt e := by
          calc ‖h + Real.sqrt e • z‖ ≤ ‖h‖ + ‖Real.sqrt e • z‖ := norm_add_le _ _
            _ ≤ ‖h‖ + Real.sqrt e := by linarith
        have hhalf : ‖h‖ / 2 ≤ ‖h + Real.sqrt e • z‖ := by linarith
        have hup2 : ‖h + Real.sqrt e • z‖ ≤ 3 / 2 * ‖h‖ := by linarith
        have hxpos : (0 : ℝ) < ‖h + Real.sqrt e • z‖ :=
          lt_of_lt_of_le (by positivity) hhalf
        have hx0 : (0 : ℝ) < ‖h + Real.sqrt e • z‖ ^ 2 := by positivity
        have hsq1 : (‖h‖ / 2) ^ 2 ≤ ‖h + Real.sqrt e • z‖ ^ 2 :=
          pow_le_pow_left₀ (by positivity) hhalf 2
        have hsq2 : ‖h + Real.sqrt e • z‖ ^ 2 ≤ (3 / 2 * ‖h‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hup2 2
        have he1 : (‖h‖ / 2) ^ 2 = 1 / 4 * ‖h‖ ^ 2 := by ring
        have he2 : (3 / 2 * ‖h‖) ^ 2 = 9 / 4 * ‖h‖ ^ 2 := by ring
        have hlo : (1 / 5 : ℝ) * (e + ‖h‖ ^ 2) ≤ ‖h + Real.sqrt e • z‖ ^ 2 := by
          rw [he1] at hsq1
          linarith
        have hhi : ‖h + Real.sqrt e • z‖ ^ 2 ≤ 9 / 4 * (e + ‖h‖ ^ 2) := by
          rw [he2] at hsq2
          linarith
        obtain ⟨hs1, hs2⟩ := hsand (‖h + Real.sqrt e • z‖ ^ 2) (e + ‖h‖ ^ 2)
          (1 / 5) (9 / 4) (by norm_num) hx0 hW0 hlo hhi
        rw [← hker]
        exact ⟨mul_le_mul_of_nonneg_right hs1 (hρ0 z),
          mul_le_mul_of_nonneg_right hs2 (hρ0 z)⟩
    constructor
    · have hstep : min ((1 / 5 : ℝ) ^ (p / 2 - 1)) ((9 / 4 : ℝ) ^ (p / 2 - 1))
            * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) * ∫ z, ρ z
          ≤ ∫ z, ‖h + Real.sqrt e • z‖ ^ (p - 2) * ρ z := by
        rw [← integral_const_mul]
        exact integral_mono (hρintble.const_mul _) (hKint h e he) (fun z => (hptw z).1)
      rw [hρint, mul_one] at hstep
      refine le_trans ?_ hstep
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) hWq.le
    · have hstep : (∫ z, ‖h + Real.sqrt e • z‖ ^ (p - 2) * ρ z)
          ≤ max ((1 / 5 : ℝ) ^ (p / 2 - 1)) ((9 / 4 : ℝ) ^ (p / 2 - 1))
            * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) * ∫ z, ρ z := by
        rw [← integral_const_mul]
        exact integral_mono (hKint h e he) (hρintble.const_mul _) (fun z => (hptw z).2)
      rw [hρint, mul_one] at hstep
      refine le_trans hstep ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hWq.le
