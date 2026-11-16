import ManfrediThesis.Preamble
open MeasureTheory
set_option maxHeartbeats 1600000

/-- The subquadratic case `1 < p < 2` of the absorption step: the weighted
inequality (4.8) / (5.9) for the remainder `G - Gv` implies the pure `L^p`
bound of Lemma 4.1 / Lemma 5.1, with a threshold `b₀` and a constant `c`
depending only on `p`.

Conventions, restated here because a helper inherits none of its parent's.
`B` is a measurable set of finite volume, `G` and `Gv` are the two gradient
fields and `G - Gv` the remainder, all three in `L^p(B)`; every power of a
positive real is the real power, and the weight
`(ε + ‖G‖² + ‖Gv‖²)^{p/2-1}` is written exactly as it is printed, so that at
`ε = 0` and `G = Gv = 0` it is `0` for `p ≠ 2` rather than `+∞`.  The
conclusion is stated in the single form `c(a + a^{p/2} + b^{p/2})`, which is
what the consumers use; it is NOT the paper's printed closed form
`a^{p/2}(6+6a)^{1-p/2} + 6b^{p/2}(1+a)`, which is false for `p > 2`, and the
constant here is the one the statement names and nothing else.

The route, which is the one place where `p < 2` is used.  For `p < 2` the
exponent `p/2 - 1` is negative, so the weight cannot be bounded below by a
constant and the superquadratic pointwise inequality is unavailable.  Instead
Hölder's inequality with the conjugate pair `(2/p, 2/(2-p))` splits
\[
\int_B\|G-Gv\|^p
 = \int_B\Bigl(w^{\frac p2-1}\|G-Gv\|^2\Bigr)^{\frac p2}
     \Bigl(w^{\frac{p}{2}}\Bigr)^{1-\frac p2}\cdot(\text{a power of }w)
\]
into the weighted left-hand side of the hypothesis to the power `p/2` and a
factor controlled by `∫_B(1+‖G‖²)^{p/2}` plus `∫_B\|G-Gv\|^p` itself, using
`w = ε + ‖G‖² + ‖Gv‖² ≤ 3(1 + ‖G‖²) + 2‖G-Gv‖²` pointwise and `ε ≤ 1`.
Feeding the hypothesis into the first factor and absorbing the resulting
`b^{p/2}`-multiple of `∫_B\|G-Gv\|^p` on the left --- legitimate once
`b ≤ b₀` with `b₀` chosen from `p` alone --- gives the asserted bound, with the
elementary absorption inequality `X ≤ C(A + B)^{p/2}(DY + EX)^{1-p/2}
⟹ X ≤ c(a + a^{p/2} + b^{p/2})Y` applied at the end. -/
theorem WeightedRemainderAbsorptionSubquadratic :
    ∀ p : ℝ, 1 < p → p < 2 →
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
  intro p hp hp2
  have hp0 : (0:ℝ) < p := by linarith
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hth0 : (0:ℝ) < p / 2 := by linarith
  have hth1 : p / 2 < 1 := by linarith
  have holder_pair : Real.HolderConjugate (2 / p) (2 / (2 - p)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ (by linarith)]; linarith
    · have h1 : (2 / p)⁻¹ = p / 2 := by field_simp
      have h2 : (2 / (2 - p))⁻¹ = (2 - p) / 2 := by rw [inv_div]
      rw [h1, h2]; ring
  have young_param : ∀ u v lam th : ℝ, 0 ≤ u → 0 ≤ v → 0 < lam → 0 < th → th < 1 →
    u ^ th * v ^ (1 - th)
      ≤ th * (u / lam) + (1 - th) * (lam ^ (th / (1 - th)) * v) := by
    intro u v lam th hu hv hlam hth0 hth1
    have key := Real.geom_mean_le_arith_mean2_weighted hth0.le (by linarith : (0:ℝ) ≤ 1 - th)
      (by positivity : (0:ℝ) ≤ u / lam) (by positivity : (0:ℝ) ≤ lam ^ (th / (1 - th)) * v)
      (by ring)
    refine le_trans (le_of_eq ?_) key
    have h1 : (u / lam) ^ th = u ^ th * lam ^ (-th) := by
      rw [Real.div_rpow hu hlam.le, Real.rpow_neg hlam.le]
      ring
    have h2 : (lam ^ (th / (1 - th)) * v) ^ (1 - th)
        = lam ^ th * v ^ (1 - th) := by
      rw [Real.mul_rpow (by positivity) hv]
      rw [← Real.rpow_mul hlam.le]
      have hne : (1 : ℝ) - th ≠ 0 := by linarith
      congr 2
      field_simp
    rw [h1, h2]
    have : lam ^ (-th) * lam ^ th = 1 := by
      rw [← Real.rpow_add hlam]; simp
    calc u ^ th * v ^ (1 - th)
        = (u ^ th * lam ^ (-th)) * (lam ^ th * v ^ (1 - th)) := by
          rw [mul_assoc, ← mul_assoc (lam ^ (-th)), this, one_mul]
      _ = _ := rfl
  have split_four : ∀ th X Y a b : ℝ, 0 < th → th < 1 → 0 ≤ X → 0 ≤ Y → 0 ≤ a → 0 ≤ b →
    (a * Y + b * X) ^ th * ((3:ℝ) ^ th * Y + (2:ℝ) ^ th * X) ^ (1 - th)
      ≤ (3:ℝ) ^ (th * (1 - th)) * (a ^ th * Y)
        + (2:ℝ) ^ (th * (1 - th)) * ((a * Y) ^ th * X ^ (1 - th))
        + (3:ℝ) ^ (th * (1 - th)) * (b ^ th * (X ^ th * Y ^ (1 - th)))
        + (2:ℝ) ^ (th * (1 - th)) * (b ^ th * X) := by
    intro th X Y a b hth0 hth1 hX hY ha hb
    have h1th : (0:ℝ) ≤ 1 - th := by linarith
    have hA : (a * Y + b * X) ^ th ≤ (a * Y) ^ th + (b * X) ^ th :=
      Real.rpow_add_le_add_rpow (by positivity) (by positivity) hth0.le hth1.le
    have hB : ((3:ℝ) ^ th * Y + (2:ℝ) ^ th * X) ^ (1 - th)
        ≤ ((3:ℝ) ^ th * Y) ^ (1 - th) + ((2:ℝ) ^ th * X) ^ (1 - th) :=
      Real.rpow_add_le_add_rpow (by positivity) (by positivity) h1th (by linarith)
    have hprod : (a * Y + b * X) ^ th * ((3:ℝ) ^ th * Y + (2:ℝ) ^ th * X) ^ (1 - th)
        ≤ ((a * Y) ^ th + (b * X) ^ th)
          * (((3:ℝ) ^ th * Y) ^ (1 - th) + ((2:ℝ) ^ th * X) ^ (1 - th)) :=
      mul_le_mul hA hB (by positivity) (by positivity)
    -- normalise the two constant powers
    have c3 : ((3:ℝ) ^ th) ^ (1 - th) = (3:ℝ) ^ (th * (1 - th)) := by
      rw [← Real.rpow_mul (by norm_num)]
    have c2 : ((2:ℝ) ^ th) ^ (1 - th) = (2:ℝ) ^ (th * (1 - th)) := by
      rw [← Real.rpow_mul (by norm_num)]
    have hYsum : Y ^ th * Y ^ (1 - th) = Y := by
      rw [← Real.rpow_add' hY (by norm_num)]
      simp
    have hXsum : X ^ th * X ^ (1 - th) = X := by
      rw [← Real.rpow_add' hX (by norm_num)]
      simp
    have e1 : (a * Y) ^ th * ((3:ℝ) ^ th * Y) ^ (1 - th)
        = (3:ℝ) ^ (th * (1 - th)) * (a ^ th * Y) := by
      rw [Real.mul_rpow ha hY, Real.mul_rpow (by positivity) hY, c3]
      calc a ^ th * Y ^ th * ((3:ℝ) ^ (th * (1 - th)) * Y ^ (1 - th))
          = (3:ℝ) ^ (th * (1 - th)) * (a ^ th * (Y ^ th * Y ^ (1 - th))) := by ring
        _ = _ := by rw [hYsum]
    have e2 : (a * Y) ^ th * ((2:ℝ) ^ th * X) ^ (1 - th)
        = (2:ℝ) ^ (th * (1 - th)) * ((a * Y) ^ th * X ^ (1 - th)) := by
      rw [Real.mul_rpow (by positivity) hX, c2]; ring
    have e3 : (b * X) ^ th * ((3:ℝ) ^ th * Y) ^ (1 - th)
        = (3:ℝ) ^ (th * (1 - th)) * (b ^ th * (X ^ th * Y ^ (1 - th))) := by
      rw [Real.mul_rpow hb hX, Real.mul_rpow (by positivity) hY, c3]; ring
    have e4 : (b * X) ^ th * ((2:ℝ) ^ th * X) ^ (1 - th)
        = (2:ℝ) ^ (th * (1 - th)) * (b ^ th * X) := by
      rw [Real.mul_rpow hb hX, Real.mul_rpow (by positivity) hX, c2]
      calc b ^ th * X ^ th * ((2:ℝ) ^ (th * (1 - th)) * X ^ (1 - th))
          = (2:ℝ) ^ (th * (1 - th)) * (b ^ th * (X ^ th * X ^ (1 - th))) := by ring
        _ = _ := by rw [hXsum]
    calc (a * Y + b * X) ^ th * ((3:ℝ) ^ th * Y + (2:ℝ) ^ th * X) ^ (1 - th)
        ≤ ((a * Y) ^ th + (b * X) ^ th)
          * (((3:ℝ) ^ th * Y) ^ (1 - th) + ((2:ℝ) ^ th * X) ^ (1 - th)) := hprod
      _ = (a * Y) ^ th * ((3:ℝ) ^ th * Y) ^ (1 - th)
            + (a * Y) ^ th * ((2:ℝ) ^ th * X) ^ (1 - th)
            + (b * X) ^ th * ((3:ℝ) ^ th * Y) ^ (1 - th)
            + (b * X) ^ th * ((2:ℝ) ^ th * X) ^ (1 - th) := by ring
      _ = _ := by rw [e1, e2, e3, e4]
  have absorption_core : ∀ th X Y a b lam2 lam3 : ℝ,
    0 < th → th < 1 → 0 ≤ X → 0 ≤ Y → 0 ≤ a → 0 ≤ b → b ≤ 1 → 0 < lam2 → 0 < lam3 →
    (2:ℝ) ^ (th * (1 - th)) * ((1 - th) * lam2 ^ (th / (1 - th))) ≤ 1 / 4 →
    (3:ℝ) ^ (th * (1 - th)) * (th / lam3) ≤ 1 / 4 →
    (2:ℝ) ^ (th * (1 - th)) * b ^ th ≤ 1 / 4 →
    X ≤ (a * Y + b * X) ^ th * ((3:ℝ) ^ th * Y + (2:ℝ) ^ th * X) ^ (1 - th) →
    X ≤ 4 * ((3:ℝ) ^ (th * (1 - th)) * a ^ th
              + (2:ℝ) ^ (th * (1 - th)) * (th / lam2) * a
              + (3:ℝ) ^ (th * (1 - th)) * ((1 - th) * lam3 ^ (th / (1 - th))) * b ^ th) * Y := by
    intro th X Y a b lam2 lam3 hth0 hth1 hX hY ha hb hb1 hlam2 hlam3 h2 h3 h4 hyp
    have h1th : (0:ℝ) < 1 - th := by linarith
    have hbth1 : b ^ th ≤ 1 := Real.rpow_le_one hb hb1 hth0.le
    have hbth0 : 0 ≤ b ^ th := Real.rpow_nonneg hb th
    have hsplit := split_four th X Y a b hth0 hth1 hX hY ha hb
    -- T2 by Young at u = a*Y, v = X
    have hY2 := young_param (a * Y) X lam2 th (by positivity) hX hlam2 hth0 hth1
    -- T3 by Young at u = X, v = Y
    have hY3 := young_param X Y lam3 th hX hY hlam3 hth0 hth1
    have c2pos : (0:ℝ) < (2:ℝ) ^ (th * (1 - th)) := by positivity
    have c3pos : (0:ℝ) < (3:ℝ) ^ (th * (1 - th)) := by positivity
    -- the three X-coefficients, each at most X/4
    have k2 : (2:ℝ) ^ (th * (1 - th)) * ((a * Y) ^ th * X ^ (1 - th))
        ≤ (2:ℝ) ^ (th * (1 - th)) * (th * (a * Y / lam2))
          + (2:ℝ) ^ (th * (1 - th)) * ((1 - th) * (lam2 ^ (th / (1 - th)) * X)) := by
      have := mul_le_mul_of_nonneg_left hY2 c2pos.le
      linarith [this]
    have k3 : (3:ℝ) ^ (th * (1 - th)) * (b ^ th * (X ^ th * Y ^ (1 - th)))
        ≤ (3:ℝ) ^ (th * (1 - th)) * (b ^ th * (th * (X / lam3)))
          + (3:ℝ) ^ (th * (1 - th)) * (b ^ th * ((1 - th) * (lam3 ^ (th / (1 - th)) * Y))) := by
      have h := mul_le_mul_of_nonneg_left hY3 (by positivity : (0:ℝ) ≤ (3:ℝ) ^ (th * (1 - th)) * b ^ th)
      nlinarith [h]
    -- bound each X-term by X/4
    have b2 : (2:ℝ) ^ (th * (1 - th)) * ((1 - th) * (lam2 ^ (th / (1 - th)) * X)) ≤ X / 4 := by
      have : (2:ℝ) ^ (th * (1 - th)) * ((1 - th) * (lam2 ^ (th / (1 - th)) * X))
          = ((2:ℝ) ^ (th * (1 - th)) * ((1 - th) * lam2 ^ (th / (1 - th)))) * X := by ring
      rw [this]
      nlinarith [hX, h2]
    have b3 : (3:ℝ) ^ (th * (1 - th)) * (b ^ th * (th * (X / lam3))) ≤ X / 4 := by
      have e : (3:ℝ) ^ (th * (1 - th)) * (b ^ th * (th * (X / lam3)))
          = ((3:ℝ) ^ (th * (1 - th)) * (th / lam3)) * b ^ th * X := by
        field_simp
      rw [e]
      have h1 : ((3:ℝ) ^ (th * (1 - th)) * (th / lam3)) * b ^ th
          ≤ ((3:ℝ) ^ (th * (1 - th)) * (th / lam3)) * 1 := by
        apply mul_le_mul_of_nonneg_left hbth1 (by positivity)
      nlinarith [hX, h3, h1]
    have b4 : (2:ℝ) ^ (th * (1 - th)) * (b ^ th * X) ≤ X / 4 := by
      have e : (2:ℝ) ^ (th * (1 - th)) * (b ^ th * X)
          = ((2:ℝ) ^ (th * (1 - th)) * b ^ th) * X := by ring
      rw [e]; nlinarith [hX, h4]
    -- the Y-terms
    have y2 : (2:ℝ) ^ (th * (1 - th)) * (th * (a * Y / lam2))
        = (2:ℝ) ^ (th * (1 - th)) * (th / lam2) * a * Y := by field_simp
    have y3 : (3:ℝ) ^ (th * (1 - th)) * (b ^ th * ((1 - th) * (lam3 ^ (th / (1 - th)) * Y)))
        = (3:ℝ) ^ (th * (1 - th)) * ((1 - th) * lam3 ^ (th / (1 - th))) * b ^ th * Y := by ring
    have y1 : (3:ℝ) ^ (th * (1 - th)) * (a ^ th * Y)
        = (3:ℝ) ^ (th * (1 - th)) * a ^ th * Y := by ring
    rw [y2] at k2
    rw [y3] at k3
    rw [y1] at hsplit
    nlinarith [hsplit, hyp, k2, k3, b2, b3, b4]
  have absorption_exists : ∀ th : ℝ, 0 < th → th < 1 →
    ∃ b₀ c : ℝ, 0 < b₀ ∧ b₀ ≤ 1 ∧ 0 < c ∧
      ∀ X Y a b : ℝ, 0 ≤ X → 0 ≤ Y → 0 ≤ a → 0 ≤ b → b ≤ b₀ →
        X ≤ (a * Y + b * X) ^ th * ((3:ℝ) ^ th * Y + (2:ℝ) ^ th * X) ^ (1 - th) →
        X ≤ c * (a + a ^ th + b ^ th) * Y := by
    intro th hth0 hth1
    have h1th : (0:ℝ) < 1 - th := by linarith
    obtain ⟨c2, hc2d, hc2pos, hc2one⟩ :
        ∃ c2 : ℝ, c2 = (2:ℝ) ^ (th * (1 - th)) ∧ 0 < c2 ∧ 1 ≤ c2 :=
      ⟨_, rfl, by positivity, Real.one_le_rpow (by norm_num) (by positivity)⟩
    obtain ⟨c3, hc3d, hc3pos⟩ : ∃ c3 : ℝ, c3 = (3:ℝ) ^ (th * (1 - th)) ∧ 0 < c3 :=
      ⟨_, rfl, by positivity⟩
    obtain ⟨lam2, hlam2d, hlam2⟩ :
        ∃ lam2 : ℝ, lam2 = (1 / (4 * c2 * (1 - th))) ^ ((1 - th) / th) ∧ 0 < lam2 :=
      ⟨_, rfl, by positivity⟩
    obtain ⟨lam3, hlam3d, hlam3⟩ : ∃ lam3 : ℝ, lam3 = 4 * c3 * th ∧ 0 < lam3 :=
      ⟨_, rfl, by positivity⟩
    obtain ⟨b₀, hb0d, hb0pos, hb0one⟩ :
        ∃ b₀ : ℝ, b₀ = (1 / (8 * c2)) ^ (1 / th) ∧ 0 < b₀ ∧ b₀ ≤ 1 := by
      refine ⟨_, rfl, by positivity, ?_⟩
      apply Real.rpow_le_one (by positivity) _ (by positivity)
      rw [div_le_one (by positivity)]; linarith
    refine ⟨b₀, 4 * max c3 (max (c2 * (th / lam2)) (c3 * ((1 - th) * lam3 ^ (th / (1 - th))))),
      hb0pos, hb0one, ?_, ?_⟩
    · have h := le_max_left c3 (max (c2 * (th / lam2)) (c3 * ((1 - th) * lam3 ^ (th / (1 - th)))))
      linarith
    · intro X Y a b hX hY ha hb hbb0 hyp
      have hb1 : b ≤ 1 := le_trans hbb0 hb0one
      have h2 : c2 * ((1 - th) * lam2 ^ (th / (1 - th))) ≤ 1 / 4 := by
        have e : lam2 ^ (th / (1 - th)) = 1 / (4 * c2 * (1 - th)) := by
          rw [hlam2d, ← Real.rpow_mul (by positivity),
            show (1 - th) / th * (th / (1 - th)) = 1 by field_simp]
          exact Real.rpow_one _
        rw [e]
        field_simp
        norm_num
      have h3 : c3 * (th / lam3) ≤ 1 / 4 := by
        rw [hlam3d]
        field_simp
        norm_num
      have h4 : c2 * b ^ th ≤ 1 / 4 := by
        have hmono : b ^ th ≤ b₀ ^ th := Real.rpow_le_rpow hb hbb0 hth0.le
        have e : b₀ ^ th = 1 / (8 * c2) := by
          rw [hb0d, ← Real.rpow_mul (by positivity), show 1 / th * th = 1 by field_simp]
          exact Real.rpow_one _
        rw [e] at hmono
        have h5 : c2 * b ^ th ≤ c2 * (1 / (8 * c2)) := mul_le_mul_of_nonneg_left hmono hc2pos.le
        have e2 : c2 * (1 / (8 * c2)) = 1 / 8 := by field_simp
        rw [e2] at h5; linarith
      rw [hc2d] at h2 h4
      rw [hc3d] at h3
      have core := absorption_core th X Y a b lam2 lam3 hth0 hth1 hX hY ha hb hb1 hlam2 hlam3 h2 h3 h4 hyp
      rw [← hc2d, ← hc3d] at core
      have hath : 0 ≤ a ^ th := Real.rpow_nonneg ha th
      have hbth : 0 ≤ b ^ th := Real.rpow_nonneg hb th
      set M : ℝ := max c3 (max (c2 * (th / lam2)) (c3 * ((1 - th) * lam3 ^ (th / (1 - th))))) with hM
      have hM1 : c3 ≤ M := le_max_left _ _
      have hM2 : c2 * (th / lam2) ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
      have hM3 : c3 * ((1 - th) * lam3 ^ (th / (1 - th))) ≤ M :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      have t1 : c3 * a ^ th ≤ M * a ^ th := mul_le_mul_of_nonneg_right hM1 hath
      have t2 : c2 * (th / lam2) * a ≤ M * a := mul_le_mul_of_nonneg_right hM2 ha
      have t3 : c3 * ((1 - th) * lam3 ^ (th / (1 - th))) * b ^ th ≤ M * b ^ th :=
        mul_le_mul_of_nonneg_right hM3 hbth
      nlinarith [core, t1, t2, t3, hY, hX]
  have pointwise_subquadratic : ∀ Q d : ℝ, 0 < Q → 0 ≤ d →
    d ^ p = (Q ^ (p / 2 - 1) * d ^ 2) ^ (p / 2) * Q ^ ((2 - p) * p / 4) := by
    intro Q d hQ hd
    have hd2 : d ^ (2:ℕ) = d ^ (2:ℝ) := by rw [← Real.rpow_natCast d 2]; norm_num
    have eA : (Q ^ (p / 2 - 1) * d ^ (2:ℝ)) ^ (p / 2)
        = Q ^ ((p / 2 - 1) * (p / 2)) * d ^ p := by
      rw [Real.mul_rpow (Real.rpow_nonneg hQ.le _) (Real.rpow_nonneg hd 2),
        ← Real.rpow_mul hQ.le, ← Real.rpow_mul hd, show (2:ℝ) * (p / 2) = p by ring]
    have eB : Q ^ ((p / 2 - 1) * (p / 2)) * Q ^ ((2 - p) * p / 4) = 1 := by
      rw [← Real.rpow_add hQ, show (p / 2 - 1) * (p / 2) + (2 - p) * p / 4 = 0 by ring,
        Real.rpow_zero]
    rw [hd2, eA]
    calc d ^ p = d ^ p * 1 := by ring
      _ = d ^ p * (Q ^ ((p / 2 - 1) * (p / 2)) * Q ^ ((2 - p) * p / 4)) := by rw [eB]
      _ = Q ^ ((p / 2 - 1) * (p / 2)) * d ^ p * Q ^ ((2 - p) * p / 4) := by ring
  have Q_subadditive : ∀ Q Gn d : ℝ, Q ≤ 3 * (1 + Gn) + 2 * d ^ 2 → 0 ≤ Gn → 0 ≤ d → 0 ≤ Q →
    Q ^ (p / 2) ≤ (3:ℝ) ^ (p / 2) * (1 + Gn) ^ (p / 2) + (2:ℝ) ^ (p / 2) * d ^ p := by
    intro Q Gn d hQ hGn hd hQ0
    have hd2 : d ^ (2:ℕ) = d ^ (2:ℝ) := by rw [← Real.rpow_natCast d 2]; norm_num
    have h1 : Q ^ (p / 2) ≤ (3 * (1 + Gn) + 2 * d ^ 2) ^ (p / 2) :=
      Real.rpow_le_rpow hQ0 hQ (by linarith)
    have h2 : (3 * (1 + Gn) + 2 * d ^ 2) ^ (p / 2)
        ≤ (3 * (1 + Gn)) ^ (p / 2) + (2 * d ^ 2) ^ (p / 2) :=
      Real.rpow_add_le_add_rpow (by positivity) (by positivity) (by linarith) (by linarith)
    have e1 : (3 * (1 + Gn)) ^ (p / 2) = (3:ℝ) ^ (p / 2) * (1 + Gn) ^ (p / 2) :=
      Real.mul_rpow (by norm_num) (by linarith)
    have e2 : (2 * d ^ 2) ^ (p / 2) = (2:ℝ) ^ (p / 2) * d ^ p := by
      rw [Real.mul_rpow (by norm_num) (by positivity), hd2, ← Real.rpow_mul hd,
        show (2:ℝ) * (p / 2) = p by ring]
    rw [e1, e2] at h2
    linarith
  obtain ⟨b₀, c, hb0pos, hb0one, hcpos, habs⟩ := absorption_exists (p/2) hth0 hth1
  refine ⟨b₀, c, hb0pos, hcpos, ?_⟩
  intro n ε a b B G Gv hε0 hε1 ha hb hbb0 hBms hBfin hGLp hGvLp hdLp hyp
  have hfin : IsFiniteMeasure (volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hBfin⟩
  have htoR : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hne0 : ENNReal.ofReal p ≠ 0 := by simp [ENNReal.ofReal_eq_zero]; linarith
  have hXint : Integrable (fun x => ‖G x - Gv x‖ ^ p) (volume.restrict B) := by
    simpa [htoR] using hdLp.integrable_norm_rpow hne0 (by simp)
  have hGint : Integrable (fun x => ‖G x‖ ^ p) (volume.restrict B) := by
    simpa [htoR] using hGLp.integrable_norm_rpow hne0 (by simp)
  have hGvint : Integrable (fun x => ‖Gv x‖ ^ p) (volume.restrict B) := by
    simpa [htoR] using hGvLp.integrable_norm_rpow hne0 (by simp)
  -- pointwise facts
  have hd0 : ∀ x, (0:ℝ) ≤ ‖G x - Gv x‖ := fun x => norm_nonneg _
  have hQ0 : ∀ x, (0:ℝ) ≤ ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2 := by
    intro x; nlinarith [sq_nonneg ‖G x‖, sq_nonneg ‖Gv x‖, hε0]
  have hdQ : ∀ x, ‖G x - Gv x‖ ^ 2 ≤ 2 * (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) := by
    intro x
    have h1 : ‖G x - Gv x‖ ≤ ‖G x‖ + ‖Gv x‖ := norm_sub_le _ _
    have h2 : ‖G x - Gv x‖ ^ 2 ≤ (‖G x‖ + ‖Gv x‖) ^ 2 := by
      nlinarith [hd0 x, h1, norm_nonneg (G x), norm_nonneg (Gv x)]
    nlinarith [sq_nonneg (‖G x‖ - ‖Gv x‖), hε0, h2]
  -- Q^(p/2) is dominated by an integrable function
  have hQmaj : ∀ x, (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2)
      ≤ (3:ℝ) ^ (p/2) * (1 + ‖G x‖ ^ p + ‖Gv x‖ ^ p) := by
    intro x
    have hQnn := hQ0 x
    have hb3 : ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2 ≤ 3 * max 1 (max (‖G x‖ ^ 2) (‖Gv x‖ ^ 2)) := by
      have m1 : (1:ℝ) ≤ max 1 (max (‖G x‖ ^ 2) (‖Gv x‖ ^ 2)) := le_max_left _ _
      have m2 : ‖G x‖ ^ 2 ≤ max 1 (max (‖G x‖ ^ 2) (‖Gv x‖ ^ 2)) :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      have m3 : ‖Gv x‖ ^ 2 ≤ max 1 (max (‖G x‖ ^ 2) (‖Gv x‖ ^ 2)) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      linarith
    have hM0 : (0:ℝ) ≤ max 1 (max (‖G x‖ ^ 2) (‖Gv x‖ ^ 2)) :=
      le_trans zero_le_one (le_max_left _ _)
    calc (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2)
        ≤ (3 * max 1 (max (‖G x‖ ^ 2) (‖Gv x‖ ^ 2))) ^ (p/2) :=
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
  have hIQ : ∀ x, (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1) * ‖G x - Gv x‖ ^ 2
      ≤ 2 * (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2) := by
    intro x
    have hQnn := hQ0 x
    rcases eq_or_lt_of_le hQnn with h | h
    · have hd : ‖G x - Gv x‖ = 0 := by nlinarith [hdQ x, hd0 x]
      rw [hd, ← h]
      simp [Real.zero_rpow, show p/2 ≠ 0 by intro hh; linarith,
        show p/2 - 1 ≠ 0 by intro hh; linarith]
    · have e : (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1) * (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2)
          = (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2) := by
        have h1 := Real.rpow_add h (p/2 - 1) 1
        rw [Real.rpow_one] at h1
        rw [← h1]; congr 1; ring
      rw [← e]
      nlinarith [hdQ x, Real.rpow_nonneg hQnn (p/2 - 1)]
  -- measurability of the powers of Q
  have hQae : AEMeasurable (fun x => ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) (volume.restrict B) :=
    ((hGLp.aestronglyMeasurable.aemeasurable.norm.pow_const 2).const_add ε).add
      (hGvLp.aestronglyMeasurable.aemeasurable.norm.pow_const 2)
  have hQmeas : ∀ r : ℝ, AEStronglyMeasurable
      (fun x => (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ r) (volume.restrict B) :=
    fun r => (hQae.pow_const r).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable (fun x => ‖G x - Gv x‖ ^ 2) (volume.restrict B) :=
    hdLp.aestronglyMeasurable.norm.pow 2
  -- integrability of Q^(p/2) and of Q^(p/2-1) * d^2
  have hQhalfint : Integrable (fun x => (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2))
      (volume.restrict B) := by
    refine Integrable.mono' ((hGint.add hGvint).add (integrable_const (1:ℝ))
      |>.const_mul ((3:ℝ) ^ (p/2))) (hQmeas (p/2)) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hQ0 x) _)]
    have h := hQmaj x
    calc (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2)
        ≤ (3:ℝ) ^ (p/2) * (1 + ‖G x‖ ^ p + ‖Gv x‖ ^ p) := h
      _ = (3:ℝ) ^ (p/2) * (‖G x‖ ^ p + ‖Gv x‖ ^ p + 1) := by ring
  have hIint : Integrable (fun x => (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1)
      * ‖G x - Gv x‖ ^ 2) (volume.restrict B) := by
    refine Integrable.mono' (hQhalfint.const_mul 2)
      (((hQmeas (p/2 - 1))).mul hdmeas) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (hQ0 x) _) (by positivity))]
    exact hIQ x
  -- `Y` is integrable
  have hYmaj : ∀ x, (1 + ‖G x‖ ^ 2) ^ (p/2) ≤ (2:ℝ) ^ (p/2) * (1 + ‖G x‖ ^ p) := by
    intro x
    have hb2 : 1 + ‖G x‖ ^ 2 ≤ 2 * max 1 (‖G x‖ ^ 2) := by
      have m1 : (1:ℝ) ≤ max 1 (‖G x‖ ^ 2) := le_max_left _ _
      have m2 : ‖G x‖ ^ 2 ≤ max 1 (‖G x‖ ^ 2) := le_max_right _ _
      linarith
    have hM0 : (0:ℝ) ≤ max 1 (‖G x‖ ^ 2) := le_trans zero_le_one (le_max_left _ _)
    have hGp : ‖G x‖ ^ p = (‖G x‖ ^ 2) ^ (p/2) := by
      rw [show ‖G x‖ ^ (2:ℕ) = ‖G x‖ ^ (2:ℝ) by rw [← Real.rpow_natCast]; norm_num,
        ← Real.rpow_mul (norm_nonneg _)]
      ring_nf
    calc (1 + ‖G x‖ ^ 2) ^ (p/2) ≤ (2 * max 1 (‖G x‖ ^ 2)) ^ (p/2) :=
          Real.rpow_le_rpow (by positivity) hb2 (by positivity)
      _ = (2:ℝ) ^ (p/2) * (max 1 (‖G x‖ ^ 2)) ^ (p/2) := Real.mul_rpow (by norm_num) hM0
      _ ≤ (2:ℝ) ^ (p/2) * (1 + ‖G x‖ ^ p) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rcases le_total (‖G x‖ ^ 2) 1 with hc | hc
          · rw [max_eq_left hc, Real.one_rpow]
            nlinarith [Real.rpow_nonneg (norm_nonneg (G x)) p]
          · rw [max_eq_right hc, ← hGp]
            nlinarith [Real.rpow_nonneg (norm_nonneg (G x)) p]
  have hYint : Integrable (fun x => (1 + ‖G x‖ ^ 2) ^ (p/2)) (volume.restrict B) := by
    refine Integrable.mono' (((integrable_const (1:ℝ)).add hGint).const_mul ((2:ℝ) ^ (p/2)))
      (((aemeasurable_const.add
        (hGLp.aestronglyMeasurable.aemeasurable.norm.pow_const 2)).pow_const
        (p/2)).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    have h := hYmaj x
    calc (1 + ‖G x‖ ^ 2) ^ (p/2) ≤ (2:ℝ) ^ (p/2) * (1 + ‖G x‖ ^ p) := h
      _ = (2:ℝ) ^ (p/2) * (1 + ‖G x‖ ^ p) := rfl
  -- the second Hoelder factor, integrated
  have hJ : (∫ x in B, (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2))
      ≤ (3:ℝ) ^ (p/2) * (∫ x in B, (1 + ‖G x‖ ^ 2) ^ (p/2))
        + (2:ℝ) ^ (p/2) * ∫ x in B, ‖G x - Gv x‖ ^ p := by
    have hpt : ∀ x, (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2)
        ≤ (3:ℝ) ^ (p/2) * (1 + ‖G x‖ ^ 2) ^ (p/2) + (2:ℝ) ^ (p/2) * ‖G x - Gv x‖ ^ p := by
      intro x
      refine Q_subadditive _ (‖G x‖ ^ 2) _ ?_ (by positivity) (hd0 x) (hQ0 x)
      have h1 : ‖Gv x‖ ≤ ‖G x‖ + ‖G x - Gv x‖ := by
        have : ‖Gv x‖ = ‖G x - (G x - Gv x)‖ := by congr 1; abel
        rw [this]; exact norm_sub_le _ _
      have h2 : ‖Gv x‖ ^ 2 ≤ 2 * ‖G x‖ ^ 2 + 2 * ‖G x - Gv x‖ ^ 2 := by
        nlinarith [h1, norm_nonneg (Gv x), norm_nonneg (G x), hd0 x,
          sq_nonneg (‖G x‖ - ‖G x - Gv x‖)]
      nlinarith [hε1, h2, sq_nonneg ‖G x‖]
    have hsint : Integrable (fun x => (3:ℝ) ^ (p/2) * (1 + ‖G x‖ ^ 2) ^ (p/2)
        + (2:ℝ) ^ (p/2) * ‖G x - Gv x‖ ^ p) (volume.restrict B) :=
      (hYint.const_mul _).add (hXint.const_mul _)
    have hsum : (∫ x in B, ((3:ℝ) ^ (p/2) * (1 + ‖G x‖ ^ 2) ^ (p/2)
          + (2:ℝ) ^ (p/2) * ‖G x - Gv x‖ ^ p))
        = (3:ℝ) ^ (p/2) * (∫ x in B, (1 + ‖G x‖ ^ 2) ^ (p/2))
          + (2:ℝ) ^ (p/2) * ∫ x in B, ‖G x - Gv x‖ ^ p := by
      rw [integral_add (hYint.const_mul _) (hXint.const_mul _), integral_const_mul,
        integral_const_mul]
    calc (∫ x in B, (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2))
        ≤ ∫ x in B, ((3:ℝ) ^ (p/2) * (1 + ‖G x‖ ^ 2) ^ (p/2)
            + (2:ℝ) ^ (p/2) * ‖G x - Gv x‖ ^ p) :=
          integral_mono hQhalfint hsint (fun x => hpt x)
      _ = _ := hsum
  -- the two nonnegative integrals
  have hXnn : 0 ≤ ∫ x in B, ‖G x - Gv x‖ ^ p :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p
  have hYnn : 0 ≤ ∫ x in B, (1 + ‖G x‖ ^ 2) ^ (p / 2) :=
    integral_nonneg fun x => Real.rpow_nonneg (by positivity) _
  have hInn : 0 ≤ ∫ x in B, (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1) * ‖G x - Gv x‖ ^ 2 :=
    integral_nonneg fun x => mul_nonneg (Real.rpow_nonneg (hQ0 x) _) (by positivity)
  have hJnn : 0 ≤ ∫ x in B, (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2) :=
    integral_nonneg fun x => Real.rpow_nonneg (hQ0 x) _
  -- HOELDER
  have hfnn : ∀ x, (0:ℝ)
      ≤ ((ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1) * ‖G x - Gv x‖ ^ 2) ^ (p/2) :=
    fun x => Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg (hQ0 x) _) (by positivity)) _
  have hgnn : ∀ x, (0:ℝ) ≤ (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ ((2 - p) * p / 4) :=
    fun x => Real.rpow_nonneg (hQ0 x) _
  have hfg : ∀ x, ((ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1) * ‖G x - Gv x‖ ^ 2) ^ (p/2)
      * (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ ((2 - p) * p / 4) = ‖G x - Gv x‖ ^ p := by
    intro x
    rcases eq_or_lt_of_le (hQ0 x) with h | h
    · have hd : ‖G x - Gv x‖ = 0 := by nlinarith [hdQ x, hd0 x]
      rw [hd, ← h]
      simp [Real.zero_rpow, show p/2 ≠ 0 by intro hh; linarith,
        show p/2 - 1 ≠ 0 by intro hh; linarith, hpne,
        show (2 - p) * p / 4 ≠ 0 by intro hh; nlinarith]
    · exact (pointwise_subquadratic _ _ h (hd0 x)).symm
  have hfP : ∀ x, (((ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1) * ‖G x - Gv x‖ ^ 2) ^ (p/2))
        ^ (2/p)
      = (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1) * ‖G x - Gv x‖ ^ 2 := by
    intro x
    rw [← Real.rpow_mul (mul_nonneg (Real.rpow_nonneg (hQ0 x) _) (by positivity)),
      show p/2 * (2/p) = 1 by field_simp]
    exact Real.rpow_one _
  have hgQ : ∀ x, ((ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ ((2 - p) * p / 4)) ^ (2/(2 - p))
      = (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2) := by
    intro x
    have h2p : (2:ℝ) - p ≠ 0 := by intro h; linarith
    rw [← Real.rpow_mul (hQ0 x), show (2 - p) * p / 4 * (2/(2 - p)) = p/2 by
      field_simp
      ring]
  have hfmeas : AEStronglyMeasurable
      (fun x => ((ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1) * ‖G x - Gv x‖ ^ 2) ^ (p/2))
      (volume.restrict B) :=
    (((hQae.pow_const (p/2 - 1)).mul
      (hdLp.aestronglyMeasurable.aemeasurable.norm.pow_const 2)).pow_const (p/2)).aestronglyMeasurable
  have hgmeas : AEStronglyMeasurable
      (fun x => (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ ((2 - p) * p / 4)) (volume.restrict B) :=
    (hQae.pow_const _).aestronglyMeasurable
  have hfLp : MemLp (fun x => ((ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1) * ‖G x - Gv x‖ ^ 2)
      ^ (p/2)) (ENNReal.ofReal (2/p)) (volume.restrict B) := by
    rw [← integrable_norm_rpow_iff hfmeas
      (by rw [Ne, ENNReal.ofReal_eq_zero]; push Not; positivity) (by simp)]
    rw [ENNReal.toReal_ofReal (by positivity)]
    refine hIint.congr ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (hfnn x), hfP x]
  have hgLp : MemLp (fun x => (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ ((2 - p) * p / 4))
      (ENNReal.ofReal (2/(2 - p))) (volume.restrict B) := by
    rw [← integrable_norm_rpow_iff hgmeas
      (by rw [Ne, ENNReal.ofReal_eq_zero]; push Not; positivity) (by simp)]
    rw [ENNReal.toReal_ofReal (by positivity)]
    refine hQhalfint.congr ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (hgnn x), hgQ x]
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg holder_pair
    (Filter.Eventually.of_forall hfnn) (Filter.Eventually.of_forall hgnn) hfLp hgLp
  rw [integral_congr_ae (Filter.Eventually.of_forall hfg),
    integral_congr_ae (Filter.Eventually.of_forall hfP),
    integral_congr_ae (Filter.Eventually.of_forall hgQ),
    show 1 / (2/p) = p/2 by field_simp,
    show 1 / (2/(2 - p)) = 1 - p/2 by field_simp] at hH
  -- combine with the two bounds and absorb
  have hmono1 : (∫ x in B, (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2 - 1) * ‖G x - Gv x‖ ^ 2) ^ (p/2)
      ≤ (a * (∫ x in B, (1 + ‖G x‖ ^ 2) ^ (p/2))
          + b * ∫ x in B, ‖G x - Gv x‖ ^ p) ^ (p/2) :=
    Real.rpow_le_rpow hInn hyp hth0.le
  have hmono2 : (∫ x in B, (ε + ‖G x‖ ^ 2 + ‖Gv x‖ ^ 2) ^ (p/2)) ^ (1 - p/2)
      ≤ ((3:ℝ) ^ (p/2) * (∫ x in B, (1 + ‖G x‖ ^ 2) ^ (p/2))
          + (2:ℝ) ^ (p/2) * ∫ x in B, ‖G x - Gv x‖ ^ p) ^ (1 - p/2) :=
    Real.rpow_le_rpow hJnn hJ (by linarith)
  have hfinal : (∫ x in B, ‖G x - Gv x‖ ^ p)
      ≤ (a * (∫ x in B, (1 + ‖G x‖ ^ 2) ^ (p/2))
          + b * ∫ x in B, ‖G x - Gv x‖ ^ p) ^ (p/2)
        * ((3:ℝ) ^ (p/2) * (∫ x in B, (1 + ‖G x‖ ^ 2) ^ (p/2))
          + (2:ℝ) ^ (p/2) * ∫ x in B, ‖G x - Gv x‖ ^ p) ^ (1 - p/2) := by
    refine le_trans hH (mul_le_mul hmono1 hmono2 (Real.rpow_nonneg hJnn _) ?_)
    exact Real.rpow_nonneg (by positivity) _
  exact habs _ _ a b hXnn hYnn ha hb hbb0 hfinal
