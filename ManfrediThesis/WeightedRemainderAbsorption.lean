import ManfrediThesis.Preamble
import ManfrediThesis.WeightedRemainderAbsorptionSubquadratic
open MeasureTheory
set_option maxHeartbeats 1600000

/-- The absorption step that turns the weighted inequality (4.8) / (5.9) for the
remainder `G - Gv` into the pure `L^p` bound of Lemma 4.1 / Lemma 5.1.  The
threshold `b₀` and the constant `c` depend only on `p`.  The conclusion is
stated in the single form `c * (a + a^(p/2) + b^(p/2))`, which covers both of
the paper's regimes: the linear bound `2^(p/2) a` of the `p ≥ 2` route and the
printed `a^(p/2)(6+6a)^(1-p/2) + 6 b^(p/2)(1+a)` of the `1 < p < 2` route. -/
theorem WeightedRemainderAbsorption :
    ∀ p : ℝ, 1 < p →
      ∃ b₀ c : ℝ, 0 < b₀ ∧ 0 < c ∧
        ∀ (n : ℕ) (ε a b : ℝ) (B : Set (EuclideanSpace ℝ (Fin n)))
          (G Gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 ≤ ε → ε ≤ 1 → 0 ≤ a → 0 ≤ b → b ≤ b₀ →
          MeasurableSet B → volume B ≠ ⊤ →
          MemLp G (ENNReal.ofReal p) (volume.restrict B) →
          MemLp Gv (ENNReal.ofReal p) (volume.restrict B) →
          MemLp (fun x => G x - Gv x) (ENNReal.ofReal p) (volume.restrict B) →
          (∫ x in B, (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p / 2 - 1) * ‖G x - Gv x‖ ^ 2)
              ≤ a * (∫ x in B, (1 + ‖G x‖ ^ 2) ^ (p / 2))
                + b * ∫ x in B, ‖G x - Gv x‖ ^ p →
          (∫ x in B, ‖G x - Gv x‖ ^ p)
              ≤ c * (a + a ^ (p / 2) + b ^ (p / 2))
                * ∫ x in B, (1 + ‖G x‖ ^ 2) ^ (p / 2) := by
  intro p hp
  rcases le_or_gt 2 p with hp2 | hp2
  ·
    have hp0 : (0:ℝ) < p := by linarith
    have hpne : p ≠ 0 := ne_of_gt hp0
    -- the pointwise superquadratic bound (probe theorem 6)
    have pointwise_superquadratic : ∀ Q d : ℝ, 0 < Q → 0 ≤ d → d ^ 2 ≤ 2 * Q →
        (2:ℝ) ^ (1 - p / 2) * d ^ p ≤ Q ^ (p / 2 - 1) * d ^ 2 := by
      intro Q d hQ hd hdQ
      have h2 : (0:ℝ) ≤ p / 2 - 1 := by linarith
      have hd2 : d ^ (2:ℕ) = d ^ (2:ℝ) := by rw [← Real.rpow_natCast d 2]; norm_num
      have step : d ^ (p - 2) ≤ (2 * Q) ^ (p / 2 - 1) := by
        have e : (d ^ (2:ℝ)) ^ (p / 2 - 1) = d ^ (p - 2) := by
          rw [← Real.rpow_mul hd]; ring_nf
        rw [← e]
        exact Real.rpow_le_rpow (by positivity) (by rw [← hd2]; exact hdQ) h2
      have e2 : (2 * Q) ^ (p / 2 - 1) = (2:ℝ) ^ (p / 2 - 1) * Q ^ (p / 2 - 1) :=
        Real.mul_rpow (by norm_num) hQ.le
      rw [e2] at step
      have hpne2 : (p - 2) + 2 ≠ 0 := by intro h; linarith
      have hsplit : d ^ p = d ^ (p - 2) * d ^ (2:ℝ) := by
        rw [← Real.rpow_add' hd hpne2]; ring_nf
      have key : d ^ p ≤ (2:ℝ) ^ (p / 2 - 1) * Q ^ (p / 2 - 1) * d ^ (2:ℝ) := by
        rw [hsplit]; exact mul_le_mul_of_nonneg_right step (Real.rpow_nonneg hd 2)
      have hpow : (2:ℝ) ^ (1 - p / 2) * ((2:ℝ) ^ (p / 2 - 1)) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; norm_num
      calc (2:ℝ) ^ (1 - p / 2) * d ^ p
          ≤ (2:ℝ) ^ (1 - p / 2) * ((2:ℝ) ^ (p / 2 - 1) * Q ^ (p / 2 - 1) * d ^ (2:ℝ)) :=
            mul_le_mul_of_nonneg_left key (by positivity)
        _ = Q ^ (p / 2 - 1) * d ^ (2:ℝ) := by
            rw [show (2:ℝ) ^ (1 - p / 2) * ((2:ℝ) ^ (p / 2 - 1) * Q ^ (p / 2 - 1) * d ^ (2:ℝ))
              = ((2:ℝ) ^ (1 - p / 2) * (2:ℝ) ^ (p / 2 - 1)) * (Q ^ (p / 2 - 1) * d ^ (2:ℝ)) by ring,
              hpow, one_mul]
        _ = Q ^ (p / 2 - 1) * d ^ 2 := by rw [← hd2]
    refine ⟨(2:ℝ) ^ (-(p/2)), (2:ℝ) ^ (p/2), by positivity, by positivity, ?_⟩
    intro n ε a b B G Gv hε0 hε1 ha hb hbb0 hBms hBfin hGLp hGvLp hdLp hyp
    have hfin : IsFiniteMeasure (volume.restrict B) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hBfin⟩
    have htoR : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
    have hne0 : ENNReal.ofReal p ≠ 0 := by simp [ENNReal.ofReal_eq_zero]; linarith
    -- X and Y are integrable
    have hXint : Integrable (fun x => ‖G x - Gv x‖ ^ p) (volume.restrict B) := by
      simpa [htoR] using hdLp.integrable_norm_rpow hne0 (by simp)
    have hGint : Integrable (fun x => ‖G x‖ ^ p) (volume.restrict B) := by
      simpa [htoR] using hGLp.integrable_norm_rpow hne0 (by simp)
    have hGvint : Integrable (fun x => ‖Gv x‖ ^ p) (volume.restrict B) := by
      simpa [htoR] using hGvLp.integrable_norm_rpow hne0 (by simp)
    -- pointwise facts
    have hd0 : ∀ x, (0:ℝ) ≤ ‖G x - Gv x‖ := fun x => norm_nonneg _
    have hQ0 : ∀ x, (0:ℝ) ≤ ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2 := by
      intro x; have := sq_nonneg ‖G x‖; have := sq_nonneg ‖Gv x‖; linarith
    have hdQ : ∀ x, ‖G x - Gv x‖ ^ 2 ≤ 2 * (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) := by
      intro x
      have h1 : ‖G x - Gv x‖ ≤ ‖G x‖ + ‖Gv x‖ := norm_sub_le _ _
      have h2 : ‖G x - Gv x‖ ^ 2 ≤ (‖G x‖ + ‖Gv x‖) ^ 2 := by
        nlinarith [hd0 x, h1, norm_nonneg (G x), norm_nonneg (Gv x)]
      nlinarith [sq_nonneg (‖G x‖ - ‖Gv x‖), hε0, h2]
    have hpt : ∀ x, (2:ℝ) ^ (1 - p/2) * ‖G x - Gv x‖ ^ p
        ≤ (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1) * ‖G x - Gv x‖ ^ 2 := by
      intro x
      rcases eq_or_lt_of_le (hQ0 x) with h | h
      · have hd : ‖G x - Gv x‖ = 0 := by nlinarith [hdQ x, hd0 x]
        rw [hd, Real.zero_rpow hpne]
        simp
      · exact pointwise_superquadratic _ _ h (hd0 x) (hdQ x)
    -- the middle quantity is integrable: it is at most 2 * Q^(p/2) <= 2*3^(p/2)(1+|G|^p+|Gv|^p)
    have hmaj : ∀ x, (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1) * ‖G x - Gv x‖ ^ 2
        ≤ 2 * (3:ℝ) ^ (p/2) * (1 + ‖G x‖ ^ p + ‖Gv x‖ ^ p) := by
      intro x
      set Q := ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2 with hQd
      have hQnn : 0 ≤ Q := hQ0 x
      have h1 : Q ^ (p/2 - 1) * ‖G x - Gv x‖ ^ 2 ≤ 2 * Q ^ (p/2) := by
        rcases eq_or_lt_of_le hQnn with h | h
        · have hd : ‖G x - Gv x‖ = 0 := by nlinarith [hdQ x, hd0 x]
          rw [hd, ← h]
          simp [Real.zero_rpow, show p/2 ≠ 0 by intro hh; linarith]
        · have e : Q ^ (p/2 - 1) * Q = Q ^ (p/2) := by
            have h1 : Q ^ ((p/2 - 1) + 1) = Q ^ (p/2 - 1) * Q ^ (1:ℝ) := Real.rpow_add h _ _
            rw [Real.rpow_one] at h1
            rw [← h1]; congr 1; ring
          rw [← e]
          have := hdQ x
          nlinarith [Real.rpow_nonneg hQnn (p/2 - 1)]
      have h2 : Q ^ (p/2) ≤ (3:ℝ) ^ (p/2) * (1 + ‖G x‖ ^ p + ‖Gv x‖ ^ p) := by
        have hb3 : Q ≤ 3 * max 1 (max (‖G x‖ ^ 2) (‖Gv x‖ ^ 2)) := by
          have m1 : (1:ℝ) ≤ max 1 (max (‖G x‖ ^ 2) (‖Gv x‖ ^ 2)) := le_max_left _ _
          have m2 : ‖G x‖ ^ 2 ≤ max 1 (max (‖G x‖ ^ 2) (‖Gv x‖ ^ 2)) :=
            le_trans (le_max_left _ _) (le_max_right _ _)
          have m3 : ‖Gv x‖ ^ 2 ≤ max 1 (max (‖G x‖ ^ 2) (‖Gv x‖ ^ 2)) :=
            le_trans (le_max_right _ _) (le_max_right _ _)
          linarith
        have hM0 : (0:ℝ) ≤ max 1 (max (‖G x‖ ^ 2) (‖Gv x‖ ^ 2)) :=
          le_trans zero_le_one (le_max_left _ _)
        calc Q ^ (p/2) ≤ (3 * max 1 (max (‖G x‖ ^ 2) (‖Gv x‖ ^ 2))) ^ (p/2) :=
              Real.rpow_le_rpow hQnn hb3 (by positivity)
          _ = (3:ℝ) ^ (p/2) * (max 1 (max (‖G x‖ ^ 2) (‖Gv x‖ ^ 2))) ^ (p/2) :=
              Real.mul_rpow (by norm_num) hM0
          _ ≤ (3:ℝ) ^ (p/2) * (1 + ‖G x‖ ^ p + ‖Gv x‖ ^ p) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hGp : ‖G x‖ ^ p = (‖G x‖ ^ 2) ^ (p/2) := by
                rw [show ‖G x‖ ^ (2:ℕ) = ‖G x‖ ^ (2:ℝ) by rw [← Real.rpow_natCast]; norm_num,
                  ← Real.rpow_mul (norm_nonneg _)]
                ring_nf
              have hGvp : ‖Gv x‖ ^ p = (‖Gv x‖ ^ 2) ^ (p/2) := by
                rw [show ‖Gv x‖ ^ (2:ℕ) = ‖Gv x‖ ^ (2:ℝ) by rw [← Real.rpow_natCast]; norm_num,
                  ← Real.rpow_mul (norm_nonneg _)]
                ring_nf
              rcases le_total (max (‖G x‖ ^ 2) (‖Gv x‖ ^ 2)) 1 with hc | hc
              · rw [max_eq_left hc, Real.one_rpow]
                nlinarith [Real.rpow_nonneg (norm_nonneg (G x)) p,
                  Real.rpow_nonneg (norm_nonneg (Gv x)) p]
              · rw [max_eq_right hc]
                rcases le_total (‖Gv x‖ ^ 2) (‖G x‖ ^ 2) with hc2 | hc2
                · rw [max_eq_left hc2, ← hGp]
                  nlinarith [Real.rpow_nonneg (norm_nonneg (Gv x)) p,
                    Real.rpow_nonneg (norm_nonneg (G x)) p]
                · rw [max_eq_right hc2, ← hGvp]
                  nlinarith [Real.rpow_nonneg (norm_nonneg (Gv x)) p,
                    Real.rpow_nonneg (norm_nonneg (G x)) p]
      linarith
    have hIint : Integrable (fun x => (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1)
        * ‖G x - Gv x‖ ^ 2) (volume.restrict B) := by
      have hmeas : AEStronglyMeasurable (fun x => (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1)
          * ‖G x - Gv x‖ ^ 2) (volume.restrict B) := by
        refine AEStronglyMeasurable.mul ?_ ?_
        · exact (Real.continuous_rpow_const (by linarith : (0:ℝ) ≤ p/2 - 1)).comp_aestronglyMeasurable
            (((hGLp.aestronglyMeasurable.norm.pow 2).const_add ε).add
              (hGvLp.aestronglyMeasurable.norm.pow 2))
        · exact (hdLp.aestronglyMeasurable.norm.pow 2)
      refine Integrable.mono' ((hGint.add hGvint).add
        (integrable_const (1:ℝ)) |>.const_mul (2 * (3:ℝ) ^ (p/2))) hmeas ?_
      filter_upwards with x
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (hQ0 x) _) (by positivity))]
      have h := hmaj x
      calc (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1) * ‖G x - Gv x‖ ^ 2
          ≤ 2 * (3:ℝ) ^ (p/2) * (1 + ‖G x‖ ^ p + ‖Gv x‖ ^ p) := h
        _ = 2 * (3:ℝ) ^ (p/2) * (‖G x‖ ^ p + ‖Gv x‖ ^ p + 1) := by ring
    -- integrate the pointwise bound
    have hXnn : 0 ≤ ∫ x in B, ‖G x - Gv x‖ ^ p :=
      integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p
    have hYnn : 0 ≤ ∫ x in B, (1 + ‖G x‖ ^ 2) ^ (p / 2) :=
      integral_nonneg fun x => Real.rpow_nonneg (by positivity) _
    have hmono : (2:ℝ) ^ (1 - p/2) * (∫ x in B, ‖G x - Gv x‖ ^ p)
        ≤ ∫ x in B, (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1) * ‖G x - Gv x‖ ^ 2 := by
      rw [← integral_const_mul]
      exact integral_mono (hXint.const_mul _) hIint (fun x => hpt x)
    -- absorb
    have hhalf : (2:ℝ) ^ (1 - p/2) = 2 * (2:ℝ) ^ (-(p/2)) := by
      rw [show (1:ℝ) - p/2 = 1 + -(p/2) by ring, Real.rpow_add (by norm_num)]
      norm_num
    have hcan : (2:ℝ) ^ (-(p/2)) * (2:ℝ) ^ (p/2) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; norm_num
    have hbX : b * (∫ x in B, ‖G x - Gv x‖ ^ p)
        ≤ (2:ℝ) ^ (-(p/2)) * ∫ x in B, ‖G x - Gv x‖ ^ p :=
      mul_le_mul_of_nonneg_right hbb0 hXnn
    have hkey : (2:ℝ) ^ (-(p/2)) * (∫ x in B, ‖G x - Gv x‖ ^ p)
        ≤ a * ∫ x in B, (1 + ‖G x‖ ^ 2) ^ (p / 2) := by
      rw [hhalf] at hmono
      linarith [hmono, hyp, hbX]
    have hXle : (∫ x in B, ‖G x - Gv x‖ ^ p)
        ≤ (2:ℝ) ^ (p/2) * a * ∫ x in B, (1 + ‖G x‖ ^ 2) ^ (p / 2) := by
      have h := mul_le_mul_of_nonneg_left hkey (by positivity : (0:ℝ) ≤ (2:ℝ) ^ (p/2))
      calc (∫ x in B, ‖G x - Gv x‖ ^ p)
          = ((2:ℝ) ^ (p/2) * (2:ℝ) ^ (-(p/2))) * ∫ x in B, ‖G x - Gv x‖ ^ p := by
            rw [mul_comm ((2:ℝ) ^ (p/2)), hcan, one_mul]
        _ = (2:ℝ) ^ (p/2) * ((2:ℝ) ^ (-(p/2)) * ∫ x in B, ‖G x - Gv x‖ ^ p) := by ring
        _ ≤ (2:ℝ) ^ (p/2) * (a * ∫ x in B, (1 + ‖G x‖ ^ 2) ^ (p / 2)) := h
        _ = (2:ℝ) ^ (p/2) * a * ∫ x in B, (1 + ‖G x‖ ^ 2) ^ (p / 2) := by ring
    -- enlarge `a` to `a + a^(p/2) + b^(p/2)`
    have hath : (0:ℝ) ≤ a ^ (p/2) := Real.rpow_nonneg ha _
    have hbth : (0:ℝ) ≤ b ^ (p/2) := Real.rpow_nonneg hb _
    have henl : (2:ℝ) ^ (p/2) * a ≤ (2:ℝ) ^ (p/2) * (a + a ^ (p/2) + b ^ (p/2)) := by
      have : a ≤ a + a ^ (p/2) + b ^ (p/2) := by linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    calc (∫ x in B, ‖G x - Gv x‖ ^ p)
        ≤ (2:ℝ) ^ (p/2) * a * ∫ x in B, (1 + ‖G x‖ ^ 2) ^ (p / 2) := hXle
      _ ≤ (2:ℝ) ^ (p/2) * (a + a ^ (p/2) + b ^ (p/2))
            * ∫ x in B, (1 + ‖G x‖ ^ 2) ^ (p / 2) :=
          mul_le_mul_of_nonneg_right henl hYnn
  ·
    exact WeightedRemainderAbsorptionSubquadratic p hp hp2
