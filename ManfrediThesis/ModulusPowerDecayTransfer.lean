import ManfrediThesis.Preamble

/-- The decay-rate transfer of §5's second clause: if the modulus of (Q6) obeys
a power bound `σ(t) ≤ c_σ t^δ`, then the modulus `σ₂` assembled from `σ₀` and
`σ₁` by the absorption step obeys `σ₂(t) ≤ t^{δ'}` for all small `t`, with the
exponent `δ'` depending only on `p`, `α` and `δ`.

The quantifier order is the whole content, and it is pm-0043's requirement:
`δ'` is bound **before** `c_σ`, `C₁`, `K`, `γ₄` and `c`, so it is a function of
`p, α, δ` alone, while the radius threshold `R₁'` is bound after them and is
allowed to carry the whole dependence.  That is the thesis' own "a radius
threshold that does depend on `c`". -/
theorem ModulusPowerDecayTransfer :
    ∀ (p α δ : ℝ), 1 < p → 0 < α → α ≤ 1 → 0 < δ →
      ∃ δ' : ℝ, 0 < δ' ∧
        ∀ (cσ C₁ K γ₄ c : ℝ) (σ σ₀ σ₁ : ℝ → ℝ),
          0 < cσ → 0 ≤ C₁ → 0 < K → 0 < γ₄ → 0 < c →
          (∀ t : ℝ, 0 ≤ t → σ t ≤ cσ * t ^ δ) →
          (∀ t : ℝ, 0 < t → t ≤ 1 →
              σ₀ t = K * ((p - 1) / p * σ (t + C₁ * t ^ α)
                + 4 * γ₄ * C₁ * t ^ α)) →
          (∀ t : ℝ, 0 < t → t ≤ 1 → σ₁ t = K * (1 / p * σ (t + C₁ * t ^ α))) →
          (∀ t : ℝ, 0 ≤ σ₀ t) → (∀ t : ℝ, 0 ≤ σ₁ t) →
          ∃ R₁' : ℝ, 0 < R₁' ∧ R₁' ≤ 1 ∧
            ∀ t : ℝ, 0 < t → t ≤ R₁' →
              c * (σ₀ t + σ₀ t ^ (p / 2) + σ₁ t ^ (p / 2)) ≤ t ^ δ' := by
  intro p α δ hp hα0 hα1 hδ0
  have hp0 : (0:ℝ) < p := by linarith
  have hmd0 : (0:ℝ) < min δ 1 := lt_min hδ0 one_pos
  have hmp0 : (0:ℝ) < min 1 (p/2) := lt_min one_pos (by positivity)
  set β := α * min δ 1 with hβdef
  have hβ0 : 0 < β := mul_pos hα0 hmd0
  set γ := β * min 1 (p/2) with hγdef
  have hγ0 : 0 < γ := mul_pos hβ0 hmp0
  refine ⟨γ/2, by positivity, ?_⟩
  intro cσ C₁ K γ₄ c σ σ₀ σ₁ hcσ hC₁ hK hγ₄ hc hrate hf0 hf1 hnn0 hnn1
  have hbase : (0:ℝ) < 1 + C₁ := by linarith
  have hbδ : (0:ℝ) < (1 + C₁) ^ δ := Real.rpow_pos_of_pos hbase δ
  have hD0 : (0:ℝ) ≤ cσ * (1 + C₁) ^ δ := by positivity
  have hE0 : (0:ℝ) ≤ 4 * γ₄ * C₁ := by positivity
  set K₁ := K * (cσ * (1 + C₁) ^ δ + 4 * γ₄ * C₁) with hK1def
  have hK1nn : (0:ℝ) ≤ K₁ := by rw [hK1def]; positivity
  have hK1p : (0:ℝ) ≤ K₁ ^ (p/2) := Real.rpow_nonneg hK1nn _
  set K₂ := c * (K₁ + 2 * K₁ ^ (p/2)) with hK2def
  have hK2nn : (0:ℝ) ≤ K₂ := by rw [hK2def]; positivity
  have hden : (0:ℝ) < K₂ + 1 := by linarith
  have hinv : (0:ℝ) < 1 / (K₂ + 1) := by positivity
  set ρ := (1 / (K₂ + 1)) ^ (2/γ) with hρdef
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hinv _
  refine ⟨min 1 ρ, lt_min one_pos hρ0, min_le_left _ _, ?_⟩
  intro t ht htR
  have ht1 : t ≤ 1 := le_trans htR (min_le_left _ _)
  have htρ : t ≤ ρ := le_trans htR (min_le_right _ _)
  have htα0 : (0:ℝ) ≤ t ^ α := Real.rpow_nonneg ht.le _
  have htβ0 : (0:ℝ) ≤ t ^ β := Real.rpow_nonneg ht.le _
  have htγ0 : (0:ℝ) ≤ t ^ γ := Real.rpow_nonneg ht.le _
  -- Step 2: the power bound on σ, then on σ₀ and σ₁ separately
  have hta : t ≤ t ^ α := by
    have h := Real.rpow_le_rpow_of_exponent_ge ht ht1 hα1
    rwa [Real.rpow_one] at h
  have hsum : t + C₁ * t ^ α ≤ (1 + C₁) * t ^ α := by nlinarith [hta, hC₁]
  have hsum0 : (0:ℝ) ≤ t + C₁ * t ^ α := by positivity
  have htαβ : t ^ α ≤ t ^ β := by
    refine Real.rpow_le_rpow_of_exponent_ge ht ht1 ?_
    rw [hβdef]
    exact mul_le_of_le_one_right hα0.le (min_le_right _ _)
  have hσle : σ (t + C₁ * t ^ α) ≤ cσ * (1 + C₁) ^ δ * t ^ β := by
    have h1 := hrate (t + C₁ * t ^ α) hsum0
    have h2 : (t + C₁ * t ^ α) ^ δ ≤ ((1 + C₁) * t ^ α) ^ δ :=
      Real.rpow_le_rpow hsum0 hsum hδ0.le
    have h3 : ((1 + C₁) * t ^ α) ^ δ = (1 + C₁) ^ δ * t ^ (α * δ) := by
      rw [Real.mul_rpow hbase.le htα0, ← Real.rpow_mul ht.le]
    have h4 : t ^ (α * δ) ≤ t ^ β := by
      refine Real.rpow_le_rpow_of_exponent_ge ht ht1 ?_
      rw [hβdef]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) hα0.le
    calc σ (t + C₁ * t ^ α) ≤ cσ * (t + C₁ * t ^ α) ^ δ := h1
      _ ≤ cσ * ((1 + C₁) ^ δ * t ^ (α * δ)) := by
          rw [← h3]; exact mul_le_mul_of_nonneg_left h2 hcσ.le
      _ ≤ cσ * ((1 + C₁) ^ δ * t ^ β) := by
          refine mul_le_mul_of_nonneg_left ?_ hcσ.le
          exact mul_le_mul_of_nonneg_left h4 hbδ.le
      _ = cσ * (1 + C₁) ^ δ * t ^ β := by ring
  have hc0 : (p - 1) / p ≤ 1 := by rw [div_le_one hp0]; linarith
  have hc0nn : (0:ℝ) ≤ (p - 1) / p := by positivity
  have hc1 : 1 / p ≤ 1 := by rw [div_le_one hp0]; linarith
  have hc1nn : (0:ℝ) ≤ 1 / p := by positivity
  have hDt0 : (0:ℝ) ≤ cσ * (1 + C₁) ^ δ * t ^ β := by positivity
  have h0le : σ₀ t ≤ K₁ * t ^ β := by
    rw [hf0 t ht ht1, hK1def]
    have e1 : (p - 1) / p * σ (t + C₁ * t ^ α) ≤ cσ * (1 + C₁) ^ δ * t ^ β :=
      le_trans (mul_le_mul_of_nonneg_left hσle hc0nn)
        (mul_le_of_le_one_left hDt0 hc0)
    have e2 : 4 * γ₄ * C₁ * t ^ α ≤ 4 * γ₄ * C₁ * t ^ β :=
      mul_le_mul_of_nonneg_left htαβ hE0
    have e3 : (p - 1) / p * σ (t + C₁ * t ^ α) + 4 * γ₄ * C₁ * t ^ α
        ≤ (cσ * (1 + C₁) ^ δ + 4 * γ₄ * C₁) * t ^ β := by
      have e : (cσ * (1 + C₁) ^ δ + 4 * γ₄ * C₁) * t ^ β
          = cσ * (1 + C₁) ^ δ * t ^ β + 4 * γ₄ * C₁ * t ^ β := by ring
      rw [e]; linarith
    calc K * ((p - 1) / p * σ (t + C₁ * t ^ α) + 4 * γ₄ * C₁ * t ^ α)
        ≤ K * ((cσ * (1 + C₁) ^ δ + 4 * γ₄ * C₁) * t ^ β) :=
          mul_le_mul_of_nonneg_left e3 hK.le
      _ = K * (cσ * (1 + C₁) ^ δ + 4 * γ₄ * C₁) * t ^ β := by ring
  have h1le : σ₁ t ≤ K₁ * t ^ β := by
    rw [hf1 t ht ht1, hK1def]
    have e1 : 1 / p * σ (t + C₁ * t ^ α) ≤ cσ * (1 + C₁) ^ δ * t ^ β :=
      le_trans (mul_le_mul_of_nonneg_left hσle hc1nn)
        (mul_le_of_le_one_left hDt0 hc1)
    have e2 : (0:ℝ) ≤ 4 * γ₄ * C₁ * t ^ β := by positivity
    have e3 : 1 / p * σ (t + C₁ * t ^ α)
        ≤ (cσ * (1 + C₁) ^ δ + 4 * γ₄ * C₁) * t ^ β := by
      have e : (cσ * (1 + C₁) ^ δ + 4 * γ₄ * C₁) * t ^ β
          = cσ * (1 + C₁) ^ δ * t ^ β + 4 * γ₄ * C₁ * t ^ β := by ring
      rw [e]; linarith
    calc K * (1 / p * σ (t + C₁ * t ^ α))
        ≤ K * ((cσ * (1 + C₁) ^ δ + 4 * γ₄ * C₁) * t ^ β) :=
          mul_le_mul_of_nonneg_left e3 hK.le
      _ = K * (cσ * (1 + C₁) ^ δ + 4 * γ₄ * C₁) * t ^ β := by ring
  -- Step 3: the three terms of the assembled modulus
  have hβγ : t ^ β ≤ t ^ γ := by
    refine Real.rpow_le_rpow_of_exponent_ge ht ht1 ?_
    rw [hγdef]
    exact mul_le_of_le_one_right hβ0.le (min_le_left _ _)
  have hpow : ∀ x : ℝ, 0 ≤ x → x ≤ K₁ * t ^ β → x ^ (p/2) ≤ K₁ ^ (p/2) * t ^ γ := by
    intro x hx hxle
    have h2 : (K₁ * t ^ β) ^ (p/2) = K₁ ^ (p/2) * t ^ (β * (p/2)) := by
      rw [Real.mul_rpow hK1nn htβ0, ← Real.rpow_mul ht.le]
    have h3 : t ^ (β * (p/2)) ≤ t ^ γ := by
      refine Real.rpow_le_rpow_of_exponent_ge ht ht1 ?_
      rw [hγdef]
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) hβ0.le
    calc x ^ (p/2) ≤ (K₁ * t ^ β) ^ (p/2) :=
          Real.rpow_le_rpow hx hxle (by positivity)
      _ = K₁ ^ (p/2) * t ^ (β * (p/2)) := h2
      _ ≤ K₁ ^ (p/2) * t ^ γ := mul_le_mul_of_nonneg_left h3 hK1p
  have hA : σ₀ t ≤ K₁ * t ^ γ :=
    le_trans h0le (mul_le_mul_of_nonneg_left hβγ hK1nn)
  have hB : σ₀ t ^ (p/2) ≤ K₁ ^ (p/2) * t ^ γ := hpow _ (hnn0 t) h0le
  have hC : σ₁ t ^ (p/2) ≤ K₁ ^ (p/2) * t ^ γ := hpow _ (hnn1 t) h1le
  have hs : σ₀ t + σ₀ t ^ (p/2) + σ₁ t ^ (p/2)
      ≤ (K₁ + 2 * K₁ ^ (p/2)) * t ^ γ := by
    have e : (K₁ + 2 * K₁ ^ (p/2)) * t ^ γ
        = K₁ * t ^ γ + K₁ ^ (p/2) * t ^ γ + K₁ ^ (p/2) * t ^ γ := by ring
    rw [e]; linarith
  have hK2t : c * (σ₀ t + σ₀ t ^ (p/2) + σ₁ t ^ (p/2)) ≤ K₂ * t ^ γ := by
    rw [hK2def]
    calc c * (σ₀ t + σ₀ t ^ (p/2) + σ₁ t ^ (p/2))
        ≤ c * ((K₁ + 2 * K₁ ^ (p/2)) * t ^ γ) :=
          mul_le_mul_of_nonneg_left hs hc.le
      _ = c * (K₁ + 2 * K₁ ^ (p/2)) * t ^ γ := by ring
  -- Step 4: the threshold
  have hsplit : t ^ γ = t ^ (γ/2) * t ^ (γ/2) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have htγ20 : (0:ℝ) ≤ t ^ (γ/2) := Real.rpow_nonneg ht.le _
  have hρpow : t ^ (γ/2) ≤ 1 / (K₂ + 1) := by
    have h1 : t ^ (γ/2) ≤ ρ ^ (γ/2) :=
      Real.rpow_le_rpow ht.le htρ (by positivity)
    have h2 : ρ ^ (γ/2) = 1 / (K₂ + 1) := by
      rw [hρdef, ← Real.rpow_mul hinv.le,
        show 2 / γ * (γ / 2) = 1 by field_simp]
      exact Real.rpow_one _
    rw [← h2]; exact h1
  have hfin : K₂ * t ^ (γ/2) ≤ 1 := by
    have h1 : K₂ * t ^ (γ/2) ≤ K₂ * (1 / (K₂ + 1)) :=
      mul_le_mul_of_nonneg_left hρpow hK2nn
    have h2 : K₂ * (1 / (K₂ + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one hden]; linarith
    linarith
  calc c * (σ₀ t + σ₀ t ^ (p/2) + σ₁ t ^ (p/2)) ≤ K₂ * t ^ γ := hK2t
    _ = K₂ * t ^ (γ/2) * t ^ (γ/2) := by rw [hsplit]; ring
    _ ≤ 1 * t ^ (γ/2) := mul_le_mul_of_nonneg_right hfin htγ20
    _ = t ^ (γ/2) := one_mul _
