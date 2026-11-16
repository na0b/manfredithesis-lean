import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MeanReplacementLp
open MeasureTheory

/-- From a comparison bundle -- the gradient `g_v` of a `W^{1,p}` comparison map
on `B_R(x₀)` satisfying the oscillation estimate (4.16) and the smallness
(4.17) -- together with the Morrey bound (4.15), the Campanato decay (4.19) for
`∇u`.  This is the passage (4.18) to (4.19) of the thesis. -/
theorem CampanatoDecayFromBundle :
    ∀ (n : ℕ) (p α δ' τ : ℝ), 2 ≤ n → 1 < p → 0 < α → α ≤ 1 → 0 < δ' →
      0 < τ → τ < p * α * δ' / ((n : ℝ) + p * α) →
      ∃ lam₀ R₂ : ℝ, 0 < lam₀ ∧ lam₀ < p ∧ 0 < R₂ ∧ R₂ ≤ 1 ∧
       ∀ c₁ c₃ : ℝ, 0 < c₁ → 0 < c₃ →
        ∃ c₁₀ : ℝ, 0 < c₁₀ ∧
        ∀ (ε : ℝ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (R₁ : ℝ),
          0 ≤ ε → ε ≤ 1 → IsOpen Ω → IsOpen Ω' → closure Ω' ⊆ Ω → 0 < R₁ →
          MemW1pOn n p Ω u g →
          (∀ x₀ ∈ Ω', ∀ R : ℝ, 0 < R → R ≤ R₁ →
            R ^ (-(n : ℝ)) * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2)
              ≤ c₁ * R ^ (-τ)) →
          (∀ x₀ ∈ Ω', ∀ R : ℝ, 0 < R → R ≤ R₁ → Metric.closedBall x₀ R ⊆ Ω →
            ∃ (v : EuclideanSpace ℝ (Fin n) → ℝ)
              (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
              MemW1pOn n p (Metric.ball x₀ R) v gv ∧
              (∀ ρ : ℝ, 0 < ρ → ρ ≤ R / 4 →
                (∫ x in Metric.ball x₀ ρ,
                    ‖gv x - (volume (Metric.ball x₀ ρ)).toReal⁻¹
                      • ∫ y in Metric.ball x₀ ρ, gv y‖ ^ p)
                  ≤ c₃ * (ρ / R) ^ (p * α) * ρ ^ (n : ℝ)
                    * (R ^ (-(n : ℝ))
                      * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2))) ∧
              (∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p)
                ≤ R ^ (δ' + (n : ℝ))
                  * (R ^ (-(n : ℝ))
                    * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2))) →
          ∀ x₀ ∈ Ω', ∀ R ρ : ℝ, 0 < R → R ≤ min R₁ R₂ →
            Metric.closedBall x₀ R ⊆ Ω → 0 < ρ →
            2 * ρ ≤ R ^ (1 + δ' / ((n : ℝ) + p * α)) →
            (∫ x in Metric.ball x₀ ρ,
                ‖g x - (volume (Metric.ball x₀ ρ)).toReal⁻¹
                  • ∫ y in Metric.ball x₀ ρ, g y‖ ^ p)
              ≤ c₁₀ * ρ ^ ((n : ℝ) + lam₀) := by
  intro n p α δ' τ hn hp hα hα1 hδ' hτ hadm
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hn
  have hden : (0:ℝ) < (n:ℝ) + p * α := by positivity
  set θ : ℝ := δ' / ((n:ℝ) + p * α) with hθdef
  have hθ : 0 < θ := by rw [hθdef]; positivity
  have hθ1 : (0:ℝ) < 1 + θ := by linarith
  have hpαθ : p * α * θ = p * α * δ' / ((n:ℝ) + p * α) := by
    rw [hθdef]; ring
  set η : ℝ := p * α * θ - τ with hηdef
  have hη : 0 < η := by rw [hηdef, hpαθ]; linarith
  set lam₀ : ℝ := η / (1 + θ) with hlamdef
  have hlam0 : 0 < lam₀ := by rw [hlamdef]; positivity
  have hlamp : lam₀ < p := by
    rw [hlamdef, div_lt_iff₀ hθ1, hηdef]
    nlinarith [mul_pos hp0 hα, mul_pos (mul_pos hp0 hα) hθ]
  -- the δ' identity: n θ + p α θ = δ'
  have hδ'id : (n:ℝ) * θ + p * α * θ = δ' := by
    rw [hθdef]; field_simp
  have pow2 : ∀ X Y : ℝ, 0 ≤ X → 0 ≤ Y → (X + Y) ^ p ≤ 2 ^ (p - 1) * (X ^ p + Y ^ p) := by
    intro X Y hX hY
    have h := NNReal.rpow_add_le_mul_rpow_add_rpow X.toNNReal Y.toNNReal hp.le
    have h2 := (NNReal.coe_le_coe (r₁ := (X.toNNReal + Y.toNNReal) ^ p)
      (r₂ := 2 ^ (p - 1) * (X.toNNReal ^ p + Y.toNNReal ^ p))).2 h
    push_cast [Real.coe_toNNReal _ hX, Real.coe_toNNReal _ hY] at h2
    exact h2
  have hpne0 : (ENNReal.ofReal p) ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have hpnet : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoR : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  set R₂ : ℝ := min 1 (2 ^ (-(1/θ))) with hR₂def
  have hR₂pos : 0 < R₂ := by
    rw [hR₂def]; exact lt_min one_pos (Real.rpow_pos_of_pos (by norm_num) _)
  have hR₂le1 : R₂ ≤ 1 := by rw [hR₂def]; exact min_le_left _ _
  refine ⟨lam₀, R₂, hlam0, hlamp, hR₂pos, hR₂le1, ?_⟩
  intro c₁ c₃ hc₁ hc₃
  set c₁₀ : ℝ := 2 ^ p * (2 ^ (p - 1) * c₁ * (c₃ * 2 ^ (-(p * α) - (n:ℝ)) + 1))
      * 2 ^ ((n:ℝ) + lam₀) with hc₁₀def
  have hc₁₀ : 0 < c₁₀ := by rw [hc₁₀def]; positivity
  refine ⟨c₁₀, hc₁₀, ?_⟩
  intro ε Ω Ω' u g R₁ _hε0 _hε1 _hΩ _hΩ' _hcl hR₁ hu hM hBundle x₀ hx₀ R ρ hR hRmin hball hρ hρR
  have hR1 : R ≤ R₁ := le_trans hRmin (min_le_left _ _)
  have hRR₂ : R ≤ R₂ := le_trans hRmin (min_le_right _ _)
  have hRle1 : R ≤ 1 := le_trans hRR₂ hR₂le1
  have hRle2 : R ≤ 2 ^ (-(1/θ)) := le_trans hRR₂ (by rw [hR₂def]; exact min_le_right _ _)
  -- Step 1: the comparison radius attached to ρ
  have h2ρ : (0:ℝ) < 2 * ρ := by linarith
  set R' : ℝ := (2 * ρ) ^ (1 / (1 + θ)) with hR'def
  have hR'pos : 0 < R' := Real.rpow_pos_of_pos h2ρ _
  have hR'pow : R' ^ (1 + θ) = 2 * ρ := by
    rw [hR'def, ← Real.rpow_mul h2ρ.le, one_div, inv_mul_cancel₀ (ne_of_gt hθ1), Real.rpow_one]
  have hR'leR : R' ≤ R := by
    have h := Real.rpow_le_rpow h2ρ.le hρR (by positivity : (0:ℝ) ≤ 1/(1+θ))
    rw [← Real.rpow_mul hR.le, mul_one_div, div_self (ne_of_gt hθ1), Real.rpow_one] at h
    exact h
  have hR'le1 : R' ≤ 1 := le_trans hR'leR hRle1
  have hR'le2 : R' ≤ 2 ^ (-(1/θ)) := le_trans hR'leR hRle2
  have hρR' : ρ ≤ R' / 4 := by
    have h1 : R' ^ (1 + θ) = R' * R' ^ θ := by
      rw [Real.rpow_add hR'pos, Real.rpow_one]
    have h2 : R' ^ θ ≤ 1/2 := by
      have h := Real.rpow_le_rpow hR'pos.le hR'le2 hθ.le
      rwa [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
        show -(1/θ) * θ = -1 by field_simp, Real.rpow_neg_one,
        show ((2:ℝ))⁻¹ = 1/2 by norm_num] at h
    have h3 : 2 * ρ ≤ R' / 2 := by
      rw [← hR'pow, h1]
      nlinarith [hR'pos, h2]
    linarith
  have hρleR' : ρ ≤ R' := by linarith
  have hR'R₁ : R' ≤ R₁ := le_trans hR'leR hR1
  have hballR' : Metric.closedBall x₀ R' ⊆ Ω :=
    subset_trans (Metric.closedBall_subset_closedBall hR'leR) hball
  obtain ⟨v, gv, hvW, h416, h417⟩ := hBundle x₀ hx₀ R' hR'pos hR'R₁ hballR'
  have hbρR' : Metric.ball x₀ ρ ⊆ Metric.ball x₀ R' := Metric.ball_subset_ball hρleR'
  have hbR'Ω : Metric.ball x₀ R' ⊆ Ω := subset_trans Metric.ball_subset_closedBall hballR'
  have hbρΩ : Metric.ball x₀ ρ ⊆ Ω := subset_trans hbρR' hbR'Ω
  have hfinρ : IsFiniteMeasure (volume.restrict (Metric.ball x₀ ρ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hfinR' : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R')) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hgΩ : MemLp g (ENNReal.ofReal p) (volume.restrict Ω) := hu.2.2
  have hgρ : MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ ρ)) :=
    hgΩ.mono_measure (Measure.restrict_mono hbρΩ le_rfl)
  have hgR' : MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R')) :=
    hgΩ.mono_measure (Measure.restrict_mono hbR'Ω le_rfl)
  have hgvR' : MemLp gv (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R')) := hvW.2.2
  have hgvρ : MemLp gv (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ ρ)) :=
    hgvR'.mono_measure (Measure.restrict_mono hbρR' le_rfl)
  set Λ : ℝ := R' ^ (-(n:ℝ)) * ∫ x in Metric.ball x₀ R', (1 + ‖g x‖ ^ 2) ^ (p / 2) with hΛdef
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛdef]
    exact mul_nonneg (Real.rpow_pos_of_pos hR'pos _).le
      (integral_nonneg fun x => Real.rpow_nonneg (by positivity) _)
  have hΛle : Λ ≤ c₁ * R' ^ (-τ) := hM x₀ hx₀ R' hR'pos hR'R₁
  set cv : EuclideanSpace ℝ (Fin n) :=
    (volume (Metric.ball x₀ ρ)).toReal⁻¹ • ∫ y in Metric.ball x₀ ρ, gv y with hcvdef
  have h16 := h416 ρ hρ hρR'
  -- integrability of the three p-th powers
  have hintgc : Integrable (fun x => ‖g x - cv‖ ^ p)
      (volume.restrict (Metric.ball x₀ ρ)) := by
    have h := ((hgρ.sub (memLp_const cv)).integrable_norm_rpow hpne0 hpnet)
    rwa [htoR] at h
  have hintgvc : Integrable (fun x => ‖gv x - cv‖ ^ p)
      (volume.restrict (Metric.ball x₀ ρ)) := by
    have h := ((hgvρ.sub (memLp_const cv)).integrable_norm_rpow hpne0 hpnet)
    rwa [htoR] at h
  have hintggvρ : Integrable (fun x => ‖g x - gv x‖ ^ p)
      (volume.restrict (Metric.ball x₀ ρ)) := by
    have h := ((hgρ.sub hgvρ).integrable_norm_rpow hpne0 hpnet)
    rwa [htoR] at h
  have hintggvR' : Integrable (fun x => ‖g x - gv x‖ ^ p)
      (volume.restrict (Metric.ball x₀ R')) := by
    have h := ((hgR'.sub hgvR').integrable_norm_rpow hpne0 hpnet)
    rwa [htoR] at h
  -- Step 2: the splitting (4.18)
  have hsplit : (∫ x in Metric.ball x₀ ρ, ‖g x - cv‖ ^ p)
      ≤ 2 ^ (p - 1) * ((∫ x in Metric.ball x₀ ρ, ‖gv x - cv‖ ^ p)
        + ∫ x in Metric.ball x₀ R', ‖g x - gv x‖ ^ p) := by
    have hpt : ∀ x, ‖g x - cv‖ ^ p
        ≤ 2 ^ (p-1) * (‖gv x - cv‖ ^ p + ‖g x - gv x‖ ^ p) := by
      intro x
      refine le_trans (Real.rpow_le_rpow (norm_nonneg _) ?_ hp0.le)
        (pow2 _ _ (norm_nonneg _) (norm_nonneg _))
      calc ‖g x - cv‖ = ‖(gv x - cv) + (g x - gv x)‖ := by congr 1; abel
        _ ≤ ‖gv x - cv‖ + ‖g x - gv x‖ := norm_add_le _ _
    have hmono := integral_mono hintgc ((hintgvc.add hintggvρ).const_mul _) hpt
    rw [integral_const_mul] at hmono
    simp only [Pi.add_apply] at hmono
    rw [integral_add hintgvc hintggvρ] at hmono
    refine le_trans hmono (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _))
    have hle : (∫ x in Metric.ball x₀ ρ, ‖g x - gv x‖ ^ p)
        ≤ ∫ x in Metric.ball x₀ R', ‖g x - gv x‖ ^ p :=
      setIntegral_mono_set hintggvR'
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)
        (Filter.Eventually.of_forall fun x hx => hbρR' hx)
    linarith
  -- Step 3: the substitution ρ = ½ R'^{1+θ}
  have hR'ne : R' ≠ 0 := ne_of_gt hR'pos
  have hinv2 : ∀ z : ℝ, ((2:ℝ)⁻¹) ^ z = 2 ^ (-z) := fun z => by
    rw [Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
  set Kc : ℝ := c₃ * 2 ^ (-(p*α) - (n:ℝ)) + 1 with hKcdef
  have hKc : 0 < Kc := by rw [hKcdef]; positivity
  have hρeq : ρ = R' ^ (1 + θ) * 2⁻¹ := by rw [hR'pow]; ring
  have hratio : ρ / R' = R' ^ θ * 2⁻¹ := by
    have h1 : R' ^ (1 + θ) = R' * R' ^ θ := by rw [Real.rpow_add hR'pos, Real.rpow_one]
    rw [hρeq, h1]
    field_simp
  have hpowA : (ρ/R') ^ (p*α) = R' ^ (θ * (p*α)) * 2 ^ (-(p*α)) := by
    rw [hratio, Real.mul_rpow (Real.rpow_nonneg hR'pos.le _) (by norm_num), hinv2,
      ← Real.rpow_mul hR'pos.le]
  have hpowB : ρ ^ (n:ℝ) = R' ^ ((1+θ) * (n:ℝ)) * 2 ^ (-(n:ℝ)) := by
    rw [hρeq, Real.mul_rpow (Real.rpow_nonneg hR'pos.le _) (by norm_num), hinv2,
      ← Real.rpow_mul hR'pos.le]
  have hA : c₃ * (ρ/R') ^ (p*α) * ρ ^ (n:ℝ)
      = c₃ * 2 ^ (-(p*α) - (n:ℝ)) * R' ^ ((n:ℝ) + (n:ℝ)*θ + η + τ) := by
    rw [hpowA, hpowB,
      show (-(p*α) - (n:ℝ)) = (-(p*α)) + (-(n:ℝ)) from by ring,
      Real.rpow_add (by norm_num : (0:ℝ) < 2),
      show (n:ℝ) + (n:ℝ)*θ + η + τ = θ*(p*α) + (1+θ)*(n:ℝ) from by rw [hηdef]; ring,
      Real.rpow_add hR'pos]
    ring
  have hB : R' ^ (δ' + (n:ℝ)) = R' ^ ((n:ℝ) + (n:ℝ)*θ + η + τ) := by
    congr 1
    rw [hηdef, ← hδ'id]; ring
  have hsum : c₃ * (ρ/R') ^ (p*α) * ρ ^ (n:ℝ) + R' ^ (δ' + (n:ℝ))
      = Kc * R' ^ ((n:ℝ) + (n:ℝ)*θ + η + τ) := by
    rw [hA, hB, hKcdef]; ring
  have hAB : (∫ x in Metric.ball x₀ ρ, ‖gv x - cv‖ ^ p)
      + (∫ x in Metric.ball x₀ R', ‖g x - gv x‖ ^ p)
      ≤ (c₃ * (ρ/R') ^ (p*α) * ρ ^ (n:ℝ) + R' ^ (δ' + (n:ℝ))) * Λ := by
    rw [show (c₃ * (ρ/R') ^ (p*α) * ρ ^ (n:ℝ) + R' ^ (δ' + (n:ℝ))) * Λ
        = c₃ * (ρ/R') ^ (p*α) * ρ ^ (n:ℝ) * Λ + R' ^ (δ' + (n:ℝ)) * Λ from by ring]
    linarith [h16, h417]
  have hΛbound : (c₃ * (ρ/R') ^ (p*α) * ρ ^ (n:ℝ) + R' ^ (δ' + (n:ℝ))) * Λ
      ≤ Kc * c₁ * R' ^ ((n:ℝ) + (n:ℝ)*θ + η) := by
    rw [hsum]
    calc Kc * R' ^ ((n:ℝ) + (n:ℝ)*θ + η + τ) * Λ
        ≤ Kc * R' ^ ((n:ℝ) + (n:ℝ)*θ + η + τ) * (c₁ * R' ^ (-τ)) :=
          mul_le_mul_of_nonneg_left hΛle (by positivity)
      _ = Kc * c₁ * R' ^ ((n:ℝ) + (n:ℝ)*θ + η) := by
          rw [show Kc * R' ^ ((n:ℝ) + (n:ℝ)*θ + η + τ) * (c₁ * R' ^ (-τ))
              = Kc * c₁ * (R' ^ ((n:ℝ) + (n:ℝ)*θ + η + τ) * R' ^ (-τ)) from by ring,
            ← Real.rpow_add hR'pos,
            show (n:ℝ) + (n:ℝ)*θ + η + τ + -τ = (n:ℝ) + (n:ℝ)*θ + η from by ring]
  have hRp : R' ^ ((n:ℝ) + (n:ℝ)*θ + η) = 2 ^ ((n:ℝ) + lam₀) * ρ ^ ((n:ℝ) + lam₀) := by
    have e1 : R' ^ ((n:ℝ) + (n:ℝ)*θ + η) = R' ^ ((1+θ) * (n:ℝ)) * R' ^ η := by
      rw [← Real.rpow_add hR'pos]; congr 1; ring
    have e2 : R' ^ ((1+θ) * (n:ℝ)) = (2*ρ) ^ (n:ℝ) := by
      rw [Real.rpow_mul hR'pos.le, hR'pow]
    have e3 : R' ^ η = (2*ρ) ^ lam₀ := by
      rw [hR'def, ← Real.rpow_mul h2ρ.le]
      congr 1
      rw [hlamdef]; field_simp
    rw [e1, e2, e3, ← Real.rpow_add h2ρ, Real.mul_rpow (by norm_num) hρ.le]
  -- Step 4: from the mean of gv to the mean of ∇u
  have hmr := MeanReplacementLp n p (Metric.ball x₀ ρ) g cv hp measurableSet_ball
    (Metric.isOpen_ball.measure_pos volume ⟨x₀, Metric.mem_ball_self hρ⟩)
    (measure_ball_lt_top).ne hgρ
  have hfin : (∫ x in Metric.ball x₀ ρ, ‖g x - cv‖ ^ p)
      ≤ 2 ^ (p-1) * (Kc * c₁ * (2 ^ ((n:ℝ) + lam₀) * ρ ^ ((n:ℝ) + lam₀))) := by
    refine le_trans hsplit (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _))
    rw [← hRp]
    exact le_trans hAB hΛbound
  refine le_trans hmr ?_
  calc 2 ^ p * ∫ x in Metric.ball x₀ ρ, ‖g x - cv‖ ^ p
      ≤ 2 ^ p * (2 ^ (p-1) * (Kc * c₁ * (2 ^ ((n:ℝ) + lam₀) * ρ ^ ((n:ℝ) + lam₀)))) :=
        mul_le_mul_of_nonneg_left hfin (Real.rpow_nonneg (by norm_num) _)
    _ = c₁₀ * ρ ^ ((n:ℝ) + lam₀) := by rw [hc₁₀def, hKcdef]; ring
