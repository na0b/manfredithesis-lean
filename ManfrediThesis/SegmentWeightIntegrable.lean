import ManfrediThesis.Preamble
open MeasureTheory

/-- The weight `(ε + |·|²)^(p/2-1)` is interval-integrable along any segment of
`ℝⁿ`.  This is the companion of `MidpointGradientWeightBound`, which bounds the
same integral from below without asserting that it is finite.  The only content
is the degenerate corner `ε = 0`, `1 < p < 2`, where the integrand is unbounded
and integrability holds precisely because `p > 1`. -/
theorem SegmentWeightIntegrable :
    ∀ (n : ℕ) (p : ℝ), 1 < p →
      ∀ (ε : ℝ) (a b : EuclideanSpace ℝ (Fin n)), 0 ≤ ε →
        IntervalIntegrable
          (fun t : ℝ => (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1))
          volume 0 1 := by
  intro n p hp ε a b hε
  rcases eq_or_lt_of_le hε with hε0 | hεpos
  · -- ε = 0
    rw [← hε0]
    rcases le_or_gt 2 p with hp2 | hp2
    · -- (b) the exponent is nonnegative, so the weight is continuous
      apply Continuous.intervalIntegrable
      have hcont : Continuous (fun t : ℝ => 0 + ‖t • a + (1 - t) • b‖ ^ 2) := by fun_prop
      exact hcont.rpow_const fun t => Or.inr (by linarith)
    · -- 1 < p < 2
      have hr : (-1 : ℝ) < p - 2 := by linarith
      have hrne : p - 2 ≠ 0 := by linarith
      -- the factorisation, when the segment meets the origin
      have segment_sq_eq : ∀ (t₀ : ℝ), t₀ • a + (1 - t₀) • b = 0 → ∀ t : ℝ,
          ‖t • a + (1 - t) • b‖ ^ 2 = |t - t₀| ^ 2 * ‖a - b‖ ^ 2 := by
        intro t₀ h0 t
        have e : t • a + (1 - t) • b = (t - t₀) • (a - b) := by
          have e2 : t • a + (1 - t) • b
              = (t₀ • a + (1 - t₀) • b) + ((t - t₀) • a - (t - t₀) • b) := by module
          rw [e2, h0, zero_add, smul_sub]
        rw [e, norm_smul, Real.norm_eq_abs]
        ring
      have weight_factorises : ∀ s c : ℝ, 0 ≤ s →
          (0 + s ^ 2 * c ^ 2) ^ (p / 2 - 1) = s ^ (p - 2) * (c ^ 2) ^ (p / 2 - 1) := by
        intro s c hs
        have hs2 : s ^ (2:ℕ) = s ^ (2:ℝ) := by rw [← Real.rpow_natCast s 2]; norm_num
        rw [zero_add, hs2, Real.mul_rpow (Real.rpow_nonneg hs 2) (by positivity),
          ← Real.rpow_mul hs, show (2:ℝ) * (p / 2 - 1) = p - 2 by ring]
      have seam : ∀ t₀ : ℝ, t₀ • a + (1 - t₀) • b = 0 →
          (fun t : ℝ => (0 + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1))
            = fun t : ℝ => (‖a - b‖ ^ 2) ^ (p / 2 - 1) * |t - t₀| ^ (p - 2) := by
        intro t₀ h0
        funext t
        rw [segment_sq_eq t₀ h0 t, weight_factorises _ _ (abs_nonneg (t - t₀))]
        ring
      by_cases hex : ∃ t₀ : ℝ, t₀ • a + (1 - t₀) • b = 0
      · obtain ⟨t₀, h0⟩ := hex
        -- it suffices to integrate `|t - t₀| ^ (p - 2)` on `[0,1]`
        have hprobe : IntervalIntegrable (fun t : ℝ => |t - t₀| ^ (p - 2)) volume 0 1 := by
          by_cases hin : 0 ≤ t₀ ∧ t₀ ≤ 1
          · obtain ⟨ht0, ht1⟩ := hin
            have hlow : IntervalIntegrable (fun t => |t - t₀| ^ (p - 2)) volume 0 t₀ := by
              have h := (intervalIntegral.intervalIntegrable_rpow' (a := t₀) (b := 0) hr).comp_sub_left t₀
              simp only [sub_self, sub_zero] at h
              refine h.congr ?_
              intro t ht
              rw [Set.uIoc_of_le ht0] at ht
              have hle : t ≤ t₀ := ht.2
              have habs : |t - t₀| = t₀ - t := by
                rw [abs_sub_comm, abs_of_nonneg (by linarith)]
              simp [habs]
            have hup : IntervalIntegrable (fun t => |t - t₀| ^ (p - 2)) volume t₀ 1 := by
              have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1 - t₀) hr).comp_sub_right t₀
              simp only [zero_add, sub_add_cancel] at h
              refine h.congr ?_
              intro t ht
              rw [Set.uIoc_of_le ht1] at ht
              have hge : t₀ < t := ht.1
              have habs : |t - t₀| = t - t₀ := abs_of_nonneg (by linarith)
              simp [habs]
            exact hlow.trans hup
          · -- `t₀` outside `[0,1]`: the integrand is continuous there
            apply ContinuousOn.intervalIntegrable
            refine ContinuousOn.rpow_const ?_ ?_
            · exact (continuous_abs.comp (continuous_id.sub continuous_const)).continuousOn
            · intro t ht
              refine Or.inl ?_
              rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
              have : t ≠ t₀ := by
                rcases not_and_or.1 hin with h | h
                · push Not at h; exact fun hh => absurd (hh ▸ ht.1) (by linarith)
                · push Not at h; exact fun hh => absurd (hh ▸ ht.2) (by linarith)
              simpa [abs_eq_zero, sub_eq_zero] using this
        rw [seam t₀ h0]
        exact hprobe.const_mul _
      · -- the segment never meets the origin, so the base is positive
        apply Continuous.intervalIntegrable
        have hcont : Continuous (fun t : ℝ => 0 + ‖t • a + (1 - t) • b‖ ^ 2) := by fun_prop
        refine hcont.rpow_const fun t => Or.inl ?_
        have hne : t • a + (1 - t) • b ≠ 0 := fun hh => hex ⟨t, hh⟩
        have : 0 < ‖t • a + (1 - t) • b‖ := norm_pos_iff.2 hne
        positivity
  · -- (a) ε > 0: the weight is continuous
    apply Continuous.intervalIntegrable
    have hcont : Continuous (fun t : ℝ => ε + ‖t • a + (1 - t) • b‖ ^ 2) := by fun_prop
    have hpos : ∀ t : ℝ, 0 < ε + ‖t • a + (1 - t) • b‖ ^ 2 := by
      intro t; positivity
    exact hcont.rpow_const fun t => Or.inl (hpos t).ne'
