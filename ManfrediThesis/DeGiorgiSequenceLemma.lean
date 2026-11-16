import ManfrediThesis.Preamble
open MeasureTheory
theorem DeGiorgiSequenceLemma (c ε b : ℝ) (y : ℕ → ℝ)
    (hc : 0 < c) (hε : 0 < ε) (hb : 1 < b)
    (hy : ∀ h : ℕ, 0 ≤ y h)
    (hrec : ∀ h : ℕ, y (h + 1) ≤ c * b ^ (h : ℝ) * y h ^ (1 + ε))
    (h0 : y 0 ≤ c ^ (-(1 : ℝ) / ε) * b ^ (-(1 : ℝ) / ε ^ 2)) :
    Filter.Tendsto y Filter.atTop (nhds (0 : ℝ)) := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  have hεne : ε ≠ 0 := ne_of_gt hε
  set θ : ℝ := c ^ (-(1 : ℝ) / ε) * b ^ (-(1 : ℝ) / ε ^ 2) with hθdef
  have hθ : 0 ≤ θ := by
    rw [hθdef]
    exact mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg hb0.le _)
  -- the threshold identity: c * θ ^ ε = b ^ (-1/ε), with exact equality
  have hkey : c * θ ^ ε = b ^ (-(1 : ℝ) / ε) := by
    rw [hθdef, Real.mul_rpow (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg hb0.le _),
        ← Real.rpow_mul hc.le, ← Real.rpow_mul hb0.le]
    have e1 : -(1 : ℝ) / ε * ε = -1 := by field_simp
    have e2 : -(1 : ℝ) / ε ^ 2 * ε = -(1 : ℝ) / ε := by field_simp
    rw [e1, e2, Real.rpow_neg_one, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul]
  -- the induction invariant
  have hinv : ∀ h : ℕ, y h ≤ θ * b ^ (-(h : ℝ) / ε) := by
    intro h
    induction h with
    | zero => simpa using h0
    | succ k ih =>
      have hmono : y k ^ (1 + ε) ≤ (θ * b ^ (-(k : ℝ) / ε)) ^ (1 + ε) :=
        Real.rpow_le_rpow (hy k) ih (by linarith)
      have hcb : (0 : ℝ) ≤ c * b ^ (k : ℝ) := by positivity
      have h1 : y (k + 1) ≤ c * b ^ (k : ℝ) * (θ * b ^ (-(k : ℝ) / ε)) ^ (1 + ε) :=
        le_trans (hrec k) (mul_le_mul_of_nonneg_left hmono hcb)
      have hpow : (θ * b ^ (-(k : ℝ) / ε)) ^ (1 + ε)
          = θ * θ ^ ε * b ^ (-(k : ℝ) / ε * (1 + ε)) := by
        rw [Real.mul_rpow hθ (Real.rpow_nonneg hb0.le _), ← Real.rpow_mul hb0.le,
            Real.rpow_add' hθ (by positivity), Real.rpow_one]
      have hexpo : (k : ℝ) + -(k : ℝ) / ε * (1 + ε) = -(k : ℝ) / ε := by field_simp; ring
      have hfin : -(1 : ℝ) / ε + -(k : ℝ) / ε = -((k : ℝ) + 1) / ε := by field_simp; ring
      have hexp : c * b ^ (k : ℝ) * (θ * b ^ (-(k : ℝ) / ε)) ^ (1 + ε)
          = θ * b ^ (-((k : ℝ) + 1) / ε) := by
        calc c * b ^ (k : ℝ) * (θ * b ^ (-(k : ℝ) / ε)) ^ (1 + ε)
            = θ * (c * θ ^ ε * (b ^ (k : ℝ) * b ^ (-(k : ℝ) / ε * (1 + ε)))) := by
              rw [hpow]; ring
          _ = θ * (b ^ (-(1 : ℝ) / ε) * b ^ ((k : ℝ) + -(k : ℝ) / ε * (1 + ε))) := by
              rw [hkey, ← Real.rpow_add hb0]
          _ = θ * (b ^ (-(1 : ℝ) / ε) * b ^ (-(k : ℝ) / ε)) := by rw [hexpo]
          _ = θ * b ^ (-((k : ℝ) + 1) / ε) := by rw [← Real.rpow_add hb0, hfin]
      rw [hexp] at h1
      push_cast
      exact h1
  -- conclude by comparison with a geometric sequence
  set q : ℝ := b ^ (-(1 : ℝ) / ε) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hb0 _
  have hneg : -(1 : ℝ) / ε < 0 := div_neg_of_neg_of_pos (by norm_num) hε
  have hq1 : q < 1 := by rw [hq]; exact Real.rpow_lt_one_of_one_lt_of_neg hb hneg
  have hrw : ∀ h : ℕ, θ * b ^ (-(h : ℝ) / ε) = θ * q ^ h := by
    intro h
    congr 1
    rw [hq, ← Real.rpow_natCast (b ^ (-(1 : ℝ) / ε)) h, ← Real.rpow_mul hb0.le]
    congr 1
    field_simp
  have hgeo : Filter.Tendsto (fun h : ℕ => θ * q ^ h) Filter.atTop (nhds 0) := by
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
    simpa using h2.const_mul θ
  refine squeeze_zero hy (fun h => ?_) hgeo
  rw [← hrw h]
  exact hinv h
