import ManfrediThesis.Preamble
set_option maxHeartbeats 1600000
open MeasureTheory

/-- The convergence step of the degenerate limit transfer: the `L^p` distances
`X_m = (∫_{B_R(x₀)}‖G_m - g‖^p)^{1/p}` tend to `0`.

Conventions, restated here because a helper inherits none of its parent's.
`e_m = 1/(m+1)` is the regularisation parameter, `G_m` the gradient of the
approximating solution and `g` the limit gradient; `X_m` is the `L^p` distance
just displayed, `I_m` the weighted energy
`∫_{B_R(x₀)}(e_m + ‖G_m‖² + ‖g‖²)^{p/2-1}‖G_m - g‖²`, and `δ_m` the dual norm
of the field difference, all three carried here as plain sequences `ℕ → ℝ`
with only the defining equation for `I_m` and the `p`-th power identity for
`X_m` assumed.  Every power of a positive real is the real power, written
exactly as the structure conditions print it --- in particular the weight
`(e + ‖a‖² + ‖b‖²)^{p/2-1}`, whose exponent is negative when `p < 2`, is never
normalised away.  `E₁` is the uniform energy bound of the previous step.

The hypotheses are the two inequalities the parent has established --- for
every `m`, the weighted energy is integrable and `c₃I_m ≤ δ_mX_m` --- together
with `δ_m → 0`, the uniform bound `∫(e_m + ‖G_m‖² + ‖g‖²)^{p/2} ≤ E₁` with its
integrability, and the elementary facts the two cases need.

The route is Step 5 of the parent's manuscript argument, and it is genuinely
two cases.

*Case `p ≥ 2`.*  Here `p/2 - 1 ≥ 0`, so from `‖G_m - g‖² ≤ 2(e_m + ‖G_m‖² + ‖g‖²)`
one gets
`(e_m + ‖G_m‖² + ‖g‖²)^{p/2-1} ≥ 2^{-(p/2-1)}‖G_m - g‖^{p-2}` pointwise, hence
`I_m ≥ 2^{-(p/2-1)}X_m^{p}` after integrating and using
`(t²)^{p/2-1}t² = t^{p}`.  Combining with `c₃I_m ≤ δ_mX_m` gives
`c₃2^{-(p/2-1)}X_m^{p} ≤ δ_mX_m`, so `X_m^{p-1} ≤ 2^{p/2-1}δ_m/c₃` and
`X_m ≤ (2^{p/2-1}δ_m/c₃)^{1/(p-1)} → 0` because `p - 1 > 0` and `δ_m → 0`.

*Case `1 < p < 2`.*  Now `p/2 - 1 < 0` and no pointwise lower bound of that kind
is available.  Instead write
`‖G_m - g‖^{p} = \bigl(Θ_m‖G_m - g‖²\bigr)^{p/2}Θ_m^{-p/2}` with
`Θ_m = (e_m + ‖G_m‖² + ‖g‖²)^{p/2-1} > 0`, and apply Hölder with the conjugate
pair `(2/p, 2/(2-p))`: the first factor contributes `I_m^{p/2}` and the second
`\bigl(∫(e_m + ‖G_m‖² + ‖g‖²)^{p/2}\bigr)^{(2-p)/2} ≤ E₁^{(2-p)/2}`.  So
`X_m^{p} ≤ I_m^{p/2}E₁^{(2-p)/2}`, and feeding `I_m ≤ δ_mX_m/c₃` in gives
`X_m^{p} ≤ (δ_mX_m/c₃)^{p/2}E₁^{(2-p)/2}`, i.e.
`X_m^{p/2} ≤ (δ_m/c₃)^{p/2}E₁^{(2-p)/2}`, whence
`X_m ≤ (δ_m/c₃)E₁^{(2-p)/p} → 0`.

In both cases `X_m ≥ 0`, so the squeeze between `0` and a null sequence gives
`X_m → 0`. -/
theorem MollifiedGradientDistanceTendstoZero :
    ∀ (n : ℕ) (p : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (G : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (c₃ E₁ : ℝ) (X Iq δ : ℕ → ℝ),
      0 < c₃ → (0:ℝ) < p → (0:ℝ) < p - 1 → 0 ≤ E₁ →
      (∀ x y : EuclideanSpace ℝ (Fin n),
        ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) →
      (∀ m : ℕ, (0 : ℝ) < 1 / ((m : ℝ) + 1)) →
      Iq = (fun m : ℕ =>
        ∫ x in Metric.ball x₀ R,
          (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖G m x - g x‖ ^ 2) →
      (∀ m : ℕ, (∫ x in Metric.ball x₀ R, ‖G m x - g x‖ ^ p) = X m ^ p) →
      (∀ m : ℕ, 0 ≤ X m) → (∀ m : ℕ, 0 ≤ δ m) →
      (∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin n)),
        (0:ℝ) < 1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) →
      (∀ m : ℕ, IntegrableOn (fun x => ‖G m x - g x‖ ^ p)
        (Metric.ball x₀ R) volume) →
      (∀ t s : ℝ, 0 ≤ t → (t ^ 2 : ℝ) ^ (s / 2) = t ^ s) →
      (∀ t : ℝ, 0 ≤ t → ((t ^ 2) ^ (p / 2 - 1)) * t ^ 2 = t ^ p) →
      (∀ m : ℕ, IntegrableOn (fun x =>
        (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2))
        (Metric.ball x₀ R) volume) →
      (∀ m : ℕ, (∫ x in Metric.ball x₀ R,
        (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2)) ≤ E₁) →
      (∀ m : ℕ, IntegrableOn (fun x =>
          (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖G m x - g x‖ ^ 2) (Metric.ball x₀ R) volume
        ∧ c₃ * Iq m ≤ δ m * X m) →
      Filter.Tendsto δ Filter.atTop (nhds 0) →
      Filter.Tendsto X Filter.atTop (nhds 0) := by
  intro n p x₀ R g G c₃ E₁ X Iq δ hc₃0 hp0 hp10 hE₁0 hsq2 hem0 hIqdef hXp hXnn
    hδnn hWp hDint hid2 hid h5bi h5b h6 h7
  rcases le_or_gt 2 p with hp2 | hp2
  · -- the case `p ≥ 2`
    have hq0 : (0:ℝ) ≤ p / 2 - 1 := by linarith
    have hc2 : (0:ℝ) < (2:ℝ) ^ (-(p / 2 - 1)) := Real.rpow_pos_of_pos (by norm_num) _
    have hlow : ∀ m : ℕ, (2:ℝ) ^ (-(p / 2 - 1)) * X m ^ p ≤ Iq m := by
      intro m
      have hptw : ∀ x : EuclideanSpace ℝ (Fin n),
          (2:ℝ) ^ (-(p / 2 - 1)) * ‖G m x - g x‖ ^ p
            ≤ (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
              * ‖G m x - g x‖ ^ 2 := by
        intro x
        have hD2 : ‖G m x - g x‖ ^ 2
            ≤ 2 * (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) := by
          have h := hsq2 (G m x) (-(g x))
          rw [show G m x + -(g x) = G m x - g x from by abel, norm_neg] at h
          have := hem0 m
          linarith
        have hbase : ‖G m x - g x‖ ^ 2 / 2
            ≤ 1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2 := by linarith
        have hmono : ((‖G m x - g x‖ ^ 2) / 2) ^ (p / 2 - 1)
            ≤ (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1) :=
          Real.rpow_le_rpow (by positivity) hbase hq0
        have hsplit : ((‖G m x - g x‖ ^ 2) / 2) ^ (p / 2 - 1)
            = (2:ℝ) ^ (-(p / 2 - 1)) * (‖G m x - g x‖ ^ 2) ^ (p / 2 - 1) := by
          rw [div_eq_mul_inv, Real.mul_rpow (sq_nonneg _) (by norm_num),
            Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
          ring
        calc (2:ℝ) ^ (-(p / 2 - 1)) * ‖G m x - g x‖ ^ p
            = (2:ℝ) ^ (-(p / 2 - 1)) * ((‖G m x - g x‖ ^ 2) ^ (p / 2 - 1)
                * ‖G m x - g x‖ ^ 2) := by rw [hid _ (norm_nonneg _)]
          _ = (((‖G m x - g x‖ ^ 2) / 2) ^ (p / 2 - 1)) * ‖G m x - g x‖ ^ 2 := by
              rw [hsplit]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hmono (sq_nonneg _)
      have hint1 : IntegrableOn (fun x => (2:ℝ) ^ (-(p / 2 - 1))
          * ‖G m x - g x‖ ^ p) (Metric.ball x₀ R) volume := (hDint m).const_mul _
      have hmo := integral_mono hint1 (h6 m).1 hptw
      rw [integral_const_mul] at hmo
      rw [hIqdef]
      rw [← hXp m]
      exact hmo
    have hXb : ∀ m : ℕ, X m
        ≤ (δ m / (c₃ * (2:ℝ) ^ (-(p / 2 - 1)))) ^ (1 / (p - 1)) := by
      intro m
      have hK0 : (0:ℝ) < c₃ * (2:ℝ) ^ (-(p / 2 - 1)) := by positivity
      have hinv0 : (0:ℝ) < 1 / (p - 1) := div_pos one_pos hp10
      rcases eq_or_lt_of_le (hXnn m) with hx | hx
      · rw [← hx]
        exact Real.rpow_nonneg (div_nonneg (hδnn m) hK0.le) _
      · have h1 : c₃ * ((2:ℝ) ^ (-(p / 2 - 1)) * X m ^ p) ≤ c₃ * Iq m :=
          mul_le_mul_of_nonneg_left (hlow m) hc₃0.le
        have h2 := le_trans h1 (h6 m).2
        have h3 : X m ^ (p - 1) * X m = X m ^ p := by
          have h := Real.rpow_add hx (p - 1) 1
          rw [Real.rpow_one, show p - 1 + 1 = p by ring] at h
          exact h.symm
        have h4 : (c₃ * (2:ℝ) ^ (-(p / 2 - 1)) * X m ^ (p - 1)) * X m
            ≤ δ m * X m := by
          calc (c₃ * (2:ℝ) ^ (-(p / 2 - 1)) * X m ^ (p - 1)) * X m
              = c₃ * ((2:ℝ) ^ (-(p / 2 - 1)) * X m ^ p) := by rw [← h3]; ring
            _ ≤ δ m * X m := h2
        have h5 : c₃ * (2:ℝ) ^ (-(p / 2 - 1)) * X m ^ (p - 1) ≤ δ m :=
          le_of_mul_le_mul_right h4 hx
        have h6' : X m ^ (p - 1) ≤ δ m / (c₃ * (2:ℝ) ^ (-(p / 2 - 1))) := by
          rw [le_div_iff₀ hK0]
          linarith [h5]
        have h7' : (X m ^ (p - 1)) ^ (1 / (p - 1)) = X m := by
          rw [← Real.rpow_mul hx.le, mul_one_div, div_self (ne_of_gt hp10),
            Real.rpow_one]
        calc X m = (X m ^ (p - 1)) ^ (1 / (p - 1)) := h7'.symm
          _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) h6' hinv0.le
    have hto : Filter.Tendsto
        (fun m : ℕ => (δ m / (c₃ * (2:ℝ) ^ (-(p / 2 - 1)))) ^ (1 / (p - 1)))
        Filter.atTop (nhds 0) := by
      have hinv0 : (0:ℝ) < 1 / (p - 1) := div_pos one_pos hp10
      have h1 : Filter.Tendsto
          (fun m : ℕ => δ m / (c₃ * (2:ℝ) ^ (-(p / 2 - 1))))
          Filter.atTop (nhds 0) := by
        have h := h7.div_const (c₃ * (2:ℝ) ^ (-(p / 2 - 1)))
        rw [zero_div] at h
        exact h
      have h2 : Filter.Tendsto (fun t : ℝ => t ^ (1 / (p - 1)))
          (nhds 0) (nhds ((0:ℝ) ^ (1 / (p - 1)))) :=
        (Real.continuousAt_rpow_const (0:ℝ) _ (Or.inr hinv0.le)).tendsto
      rw [Real.zero_rpow (ne_of_gt hinv0)] at h2
      exact (h2.comp h1).congr fun m => rfl
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto
      hXnn hXb
  · -- the case `1 < p < 2`
    have h2p0 : (0:ℝ) < 2 - p := by linarith
    have hconj : Real.HolderConjugate (2 / p) (2 / (2 - p)) := by
      rw [Real.holderConjugate_iff]
      refine ⟨?_, ?_⟩
      · rw [lt_div_iff₀ hp0]
        linarith
      · rw [inv_div, inv_div]
        ring
    have hp20 : (0:ℝ) < p / 2 := by linarith
    have hIqnn : ∀ m : ℕ, 0 ≤ Iq m := by
      intro m
      rw [hIqdef]
      exact integral_nonneg fun x =>
        mul_nonneg (Real.rpow_nonneg (hWp m x).le _) (sq_nonneg _)
    have hhol : ∀ m : ℕ, X m ^ p ≤ Iq m ^ (p / 2) * E₁ ^ ((2 - p) / 2) := by
      intro m
      have hprod : ∀ x : EuclideanSpace ℝ (Fin n),
          (((1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
              * ‖G m x - g x‖ ^ 2) ^ (p / 2))
            * (((1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2))
              ^ ((2 - p) / 2))
            = ‖G m x - g x‖ ^ p := by
        intro x
        have hW := hWp m x
        rw [Real.mul_rpow (Real.rpow_nonneg hW.le _) (sq_nonneg _),
          hid2 _ p (norm_nonneg _)]
        simp only [← Real.rpow_mul hW.le]
        rw [show ((1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2)
                ^ ((p / 2 - 1) * (p / 2)) * ‖G m x - g x‖ ^ p)
              * (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2)
                ^ ((p / 2) * ((2 - p) / 2))
            = ((1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2)
                ^ ((p / 2 - 1) * (p / 2))
              * (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2)
                ^ ((p / 2) * ((2 - p) / 2))) * ‖G m x - g x‖ ^ p from by ring,
          ← Real.rpow_add hW,
          show (p / 2 - 1) * (p / 2) + (p / 2) * ((2 - p) / 2) = 0 by ring,
          Real.rpow_zero, one_mul]
      have hfmeas : AEStronglyMeasurable (fun x =>
          ((1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖G m x - g x‖ ^ 2) ^ (p / 2))
          (volume.restrict (Metric.ball x₀ R)) := by
        have hc : Continuous (fun t : ℝ => t ^ (p / 2)) :=
          continuous_id.rpow_const (fun t => Or.inr hp20.le)
        exact hc.comp_aestronglyMeasurable (h6 m).1.aestronglyMeasurable
      have hgmeas : AEStronglyMeasurable (fun x =>
          ((1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2))
            ^ ((2 - p) / 2)) (volume.restrict (Metric.ball x₀ R)) := by
        have hc : Continuous (fun t : ℝ => t ^ ((2 - p) / 2)) :=
          continuous_id.rpow_const (fun t => Or.inr (by positivity))
        exact hc.comp_aestronglyMeasurable (h5bi m).aestronglyMeasurable
      have hfmem : MemLp (fun x =>
          ((1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖G m x - g x‖ ^ 2) ^ (p / 2)) (ENNReal.ofReal (2 / p))
          (volume.restrict (Metric.ball x₀ R)) := by
        refine (integrable_norm_rpow_iff hfmeas ?_ ENNReal.ofReal_ne_top).1 ?_
        · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
          positivity
        · rw [ENNReal.toReal_ofReal (by positivity)]
          refine (h6 m).1.congr (Filter.Eventually.of_forall fun x => ?_)
          have hb : (0:ℝ) ≤ (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2)
              ^ (p / 2 - 1) * ‖G m x - g x‖ ^ 2 :=
            mul_nonneg (Real.rpow_nonneg (hWp m x).le _) (sq_nonneg _)
          show _ = ‖_ ^ (p / 2)‖ ^ (2 / p)
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hb _),
            ← Real.rpow_mul hb, show p / 2 * (2 / p) = 1 by field_simp,
            Real.rpow_one]
      have hgmem : MemLp (fun x =>
          ((1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2))
            ^ ((2 - p) / 2)) (ENNReal.ofReal (2 / (2 - p)))
          (volume.restrict (Metric.ball x₀ R)) := by
        refine (integrable_norm_rpow_iff hgmeas ?_ ENNReal.ofReal_ne_top).1 ?_
        · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
          positivity
        · rw [ENNReal.toReal_ofReal (by positivity)]
          refine (h5bi m).congr (Filter.Eventually.of_forall fun x => ?_)
          have hb : (0:ℝ) ≤ (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2)
              ^ (p / 2) := Real.rpow_nonneg (hWp m x).le _
          show _ = ‖_ ^ ((2 - p) / 2)‖ ^ (2 / (2 - p))
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hb _),
            ← Real.rpow_mul hb,
            show (2 - p) / 2 * (2 / (2 - p)) = 1 by field_simp,
            Real.rpow_one]
      have hH := integral_mul_le_Lp_mul_Lq_of_nonneg
        (μ := volume.restrict (Metric.ball x₀ R)) hconj
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg
          (mul_nonneg (Real.rpow_nonneg (hWp m x).le _) (sq_nonneg _)) _)
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg
          (Real.rpow_nonneg (hWp m x).le _) _)
        hfmem hgmem
      have hleft : (∫ x in Metric.ball x₀ R,
          ((1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
              * ‖G m x - g x‖ ^ 2) ^ (p / 2)
            * ((1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2))
              ^ ((2 - p) / 2)) = X m ^ p := by
        rw [← hXp m]
        exact integral_congr_ae (Filter.Eventually.of_forall hprod)
      have hr1 : (∫ x in Metric.ball x₀ R,
          (((1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖G m x - g x‖ ^ 2) ^ (p / 2)) ^ (2 / p)) = Iq m := by
        rw [hIqdef]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have hb : (0:ℝ) ≤ (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2)
            ^ (p / 2 - 1) * ‖G m x - g x‖ ^ 2 :=
          mul_nonneg (Real.rpow_nonneg (hWp m x).le _) (sq_nonneg _)
        show (_ ^ (p / 2)) ^ (2 / p) = _
        rw [← Real.rpow_mul hb, show p / 2 * (2 / p) = 1 by field_simp,
          Real.rpow_one]
      have hr2 : (∫ x in Metric.ball x₀ R,
          (((1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2))
            ^ ((2 - p) / 2)) ^ (2 / (2 - p)))
          = ∫ x in Metric.ball x₀ R,
            (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have hb : (0:ℝ) ≤ (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2)
            ^ (p / 2) := Real.rpow_nonneg (hWp m x).le _
        show (_ ^ ((2 - p) / 2)) ^ (2 / (2 - p)) = _
        rw [← Real.rpow_mul hb,
          show (2 - p) / 2 * (2 / (2 - p)) = 1 by field_simp, Real.rpow_one]
      rw [hleft, hr1, hr2, show 1 / (2 / p) = p / 2 by field_simp,
        show 1 / (2 / (2 - p)) = (2 - p) / 2 by field_simp] at hH
      refine le_trans hH (mul_le_mul_of_nonneg_left ?_
        (Real.rpow_nonneg (hIqnn m) _))
      refine Real.rpow_le_rpow (integral_nonneg fun x =>
        Real.rpow_nonneg (hWp m x).le _) (h5b m) (by positivity)
    have hXb : ∀ m : ℕ,
        X m ≤ (((δ m / c₃) ^ (p / 2)) * E₁ ^ ((2 - p) / 2)) ^ (2 / p) := by
      intro m
      have hB0 : (0:ℝ) ≤ ((δ m / c₃) ^ (p / 2)) * E₁ ^ ((2 - p) / 2) :=
        mul_nonneg (Real.rpow_nonneg (div_nonneg (hδnn m) hc₃0.le) _)
          (Real.rpow_nonneg hE₁0 _)
      rcases eq_or_lt_of_le (hXnn m) with hx | hx
      · rw [← hx]
        exact Real.rpow_nonneg hB0 _
      · have hIle : Iq m ≤ δ m * X m / c₃ := by
          rw [le_div_iff₀ hc₃0]
          linarith [(h6 m).2]
        have hstep : X m ^ p
            ≤ ((δ m / c₃) ^ (p / 2) * X m ^ (p / 2)) * E₁ ^ ((2 - p) / 2) := by
          refine le_trans (hhol m) (mul_le_mul_of_nonneg_right ?_
            (Real.rpow_nonneg hE₁0 _))
          have h1 : Iq m ^ (p / 2) ≤ (δ m * X m / c₃) ^ (p / 2) :=
            Real.rpow_le_rpow (hIqnn m) hIle hp20.le
          refine le_trans h1 (le_of_eq ?_)
          rw [show δ m * X m / c₃ = (δ m / c₃) * X m by ring,
            Real.mul_rpow (div_nonneg (hδnn m) hc₃0.le) hx.le]
        have hsplit : X m ^ (p / 2) * X m ^ (p / 2) = X m ^ p := by
          rw [← Real.rpow_add hx]
          congr 1
          ring
        have hxp2 : (0:ℝ) < X m ^ (p / 2) := Real.rpow_pos_of_pos hx _
        have hfin : X m ^ (p / 2) ≤ (δ m / c₃) ^ (p / 2) * E₁ ^ ((2 - p) / 2) := by
          have h2 : X m ^ (p / 2) * X m ^ (p / 2)
              ≤ ((δ m / c₃) ^ (p / 2) * E₁ ^ ((2 - p) / 2)) * X m ^ (p / 2) := by
            rw [hsplit]
            calc X m ^ p
                ≤ ((δ m / c₃) ^ (p / 2) * X m ^ (p / 2)) * E₁ ^ ((2 - p) / 2) :=
                  hstep
              _ = ((δ m / c₃) ^ (p / 2) * E₁ ^ ((2 - p) / 2)) * X m ^ (p / 2) := by
                  ring
          exact le_of_mul_le_mul_right h2 hxp2
        have hback : (X m ^ (p / 2)) ^ (2 / p) = X m := by
          rw [← Real.rpow_mul hx.le, show p / 2 * (2 / p) = 1 by field_simp,
            Real.rpow_one]
        calc X m = (X m ^ (p / 2)) ^ (2 / p) := hback.symm
          _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) hfin
              (by positivity)
    have hto : Filter.Tendsto
        (fun m : ℕ => (((δ m / c₃) ^ (p / 2)) * E₁ ^ ((2 - p) / 2)) ^ (2 / p))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun m : ℕ => δ m / c₃) Filter.atTop (nhds 0) := by
        have h := h7.div_const c₃
        rw [zero_div] at h
        exact h
      have h2 : Filter.Tendsto (fun t : ℝ => t ^ (p / 2))
          (nhds 0) (nhds ((0:ℝ) ^ (p / 2))) :=
        (Real.continuousAt_rpow_const (0:ℝ) _ (Or.inr hp20.le)).tendsto
      rw [Real.zero_rpow (ne_of_gt hp20)] at h2
      have h3 : Filter.Tendsto
          (fun m : ℕ => ((δ m / c₃) ^ (p / 2)) * E₁ ^ ((2 - p) / 2))
          Filter.atTop (nhds 0) := by
        have h := ((h2.comp h1).congr fun m => rfl).mul_const (E₁ ^ ((2 - p) / 2))
        rw [zero_mul] at h
        exact h
      have h4 : Filter.Tendsto (fun t : ℝ => t ^ (2 / p))
          (nhds 0) (nhds ((0:ℝ) ^ (2 / p))) :=
        (Real.continuousAt_rpow_const (0:ℝ) _ (Or.inr (by positivity))).tendsto
      rw [Real.zero_rpow (by positivity)] at h4
      exact (h4.comp h3).congr fun m => rfl
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto
      hXnn hXb
