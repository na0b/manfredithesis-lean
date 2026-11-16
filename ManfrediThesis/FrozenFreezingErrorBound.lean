import ManfrediThesis.Preamble
open MeasureTheory

/-- The thesis' (4.7) and (4.8): the two freezing errors, bounded through (F3)
by the modulus at the Hölder scale, give the absorption step's hypothesis.  The
two moduli `σ₀` and `σ₁` are produced first, with the five properties the
absorption step consumes, and are functions of `α`, `C₁`, `K` and `σ` alone --
in particular not of `ε` or of any of the data -- which is the quantifier order
Lemma 4.1's statement prescribes.  Thesis l. 1112-1152. -/
theorem FrozenFreezingErrorBound :
    ∀ (n : ℕ) (p α C₁ K Cσ : ℝ) (σ : ℝ → ℝ),
      1 ≤ n → 1 < p → 0 < α → α ≤ 1 → 0 ≤ C₁ → 0 < K →
      Continuous σ → Monotone σ → σ 0 = 0 → (∀ t : ℝ, σ t ≤ Cσ) →
      ∃ (C₂ : ℝ) (σ₀ σ₁ : ℝ → ℝ), 0 < C₂ ∧
        (∀ t : ℝ, 0 < t →
          σ₀ t = K * (σ (t + C₁ * t ^ α) + C₂ * σ (t + 2*C₁ * t ^ α))) ∧
        (∀ t : ℝ, 0 < t → σ₁ t = K * (C₂ * σ (t + 2*C₁ * t ^ α))) ∧
        (∀ t : ℝ, 0 ≤ σ₀ t) ∧ (∀ t : ℝ, 0 ≤ σ₁ t) ∧
        (∃ C : ℝ, ∀ t : ℝ, σ₀ t ≤ C ∧ σ₁ t ≤ C) ∧
        Continuous σ₀ ∧ Continuous σ₁ ∧ Monotone σ₀ ∧ Monotone σ₁ ∧
        σ₀ 0 = 0 ∧ σ₁ 0 = 0 ∧
        ∀ (ε z₀ R : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
          (fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
          (f0 : EuclideanSpace ℝ (Fin n) → ℝ)
          (u v : EuclideanSpace ℝ (Fin n) → ℝ)
          (g gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 < R →
          MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) →
          MemLp gv (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) →
          IntegrableOn (fun x => f0 (g x)) (Metric.ball x₀ R) volume →
          IntegrableOn (fun x => f0 (gv x)) (Metric.ball x₀ R) volume →
          IntegrableOn (fun x => fdens x (u x) (g x)) (Metric.ball x₀ R) volume →
          IntegrableOn (fun x => fdens x (v x) (gv x)) (Metric.ball x₀ R) volume →
          (∀ x ∈ Metric.ball x₀ R, ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)),
            |fdens x z h - f0 h| ≤ (1 + ‖h‖ ^ 2) ^ (p / 2) * σ (dist x x₀ + |z - z₀|)) →
          (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), |u x - z₀| ≤ C₁ * R ^ α) →
          (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), |v x - z₀| ≤ C₁ * R ^ α) →
          (∫ x in Metric.ball x₀ R, fdens x (u x) (g x))
            ≤ ∫ x in Metric.ball x₀ R, fdens x (v x) (gv x) →
          (∫ x in Metric.ball x₀ R,
              (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2)
            ≤ K * ((∫ x in Metric.ball x₀ R, f0 (g x))
                    - ∫ x in Metric.ball x₀ R, f0 (gv x)) →
          (∫ x in Metric.ball x₀ R,
              (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2)
            ≤ σ₀ R * (∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2))
              + σ₁ R * ∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p := by
  intro n p α C₁ K Cσ σ hn hp hα0 hα1 hC₁ hK hσc hσm hσ0 hσb
  have hCσ0 : 0 ≤ Cσ := by have := hσb 0; rw [hσ0] at this; exact this
  have hp0 : (0:ℝ) < p := by linarith
  have hqsub : ∀ q X Y : ℝ, 0 < q → 0 ≤ X → 0 ≤ Y →
      (X + Y) ^ q ≤ max 1 (2 ^ (q-1)) * (X ^ q + Y ^ q) := by
    intro q X Y hq hX hY
    have hsum : (0:ℝ) ≤ X ^ q + Y ^ q :=
      add_nonneg (Real.rpow_nonneg hX _) (Real.rpow_nonneg hY _)
    rcases le_or_gt q 1 with h1 | h1
    · have hbase : (X + Y) ^ q ≤ X ^ q + Y ^ q := by
        have h := NNReal.rpow_add_le_add_rpow X.toNNReal Y.toNNReal hq.le h1
        have h2 := (NNReal.coe_le_coe (r₁ := (X.toNNReal + Y.toNNReal) ^ q)
          (r₂ := X.toNNReal ^ q + Y.toNNReal ^ q)).2 h
        push_cast [Real.coe_toNNReal _ hX, Real.coe_toNNReal _ hY] at h2
        exact h2
      nlinarith [le_max_left (1:ℝ) ((2:ℝ) ^ (q-1)), hsum]
    · have hbase : (X + Y) ^ q ≤ 2 ^ (q-1) * (X ^ q + Y ^ q) := by
        have h := NNReal.rpow_add_le_mul_rpow_add_rpow X.toNNReal Y.toNNReal h1.le
        have h2 := (NNReal.coe_le_coe (r₁ := (X.toNNReal + Y.toNNReal) ^ q)
          (r₂ := 2 ^ (q-1) * (X.toNNReal ^ q + Y.toNNReal ^ q))).2 h
        push_cast [Real.coe_toNNReal _ hX, Real.coe_toNNReal _ hY] at h2
        exact h2
      nlinarith [le_max_right (1:ℝ) ((2:ℝ) ^ (q-1)), hsum]
  have hsq : ∀ t : ℝ, 0 ≤ t → (t ^ 2) ^ (p/2) = t ^ p := by
    intro t ht
    rw [show (t:ℝ) ^ 2 = t ^ ((2:ℕ):ℝ) from by rw [Real.rpow_natCast], ← Real.rpow_mul ht]
    congr 1
    push_cast
    ring
  set C₂ : ℝ := max 1 ((2:ℝ) ^ (p/2 - 1)) * (2:ℝ) ^ (p/2) with hC₂def
  have hC₂0 : 0 < C₂ := by
    rw [hC₂def]
    exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.rpow_pos_of_pos two_pos _)
  -- the two inner scales
  have hscale : ∀ c : ℝ, 0 ≤ c → Continuous (fun t : ℝ => t + c * t ^ α) := by
    intro c hc
    have h1 : Continuous fun t : ℝ => t ^ α :=
      continuous_iff_continuousAt.mpr fun t => Real.continuousAt_rpow_const t α (Or.inr hα0.le)
    exact continuous_id.add (continuous_const.mul h1)
  have hscale0 : ∀ c : ℝ, (0:ℝ) + c * (0:ℝ) ^ α = 0 := by
    intro c
    rw [Real.zero_rpow (ne_of_gt hα0)]
    ring
  have hscalemono : ∀ c : ℝ, 0 ≤ c → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      s + c * s ^ α ≤ t + c * t ^ α := by
    intro c hc s t hs hst
    have h1 : s ^ α ≤ t ^ α := Real.rpow_le_rpow hs hst hα0.le
    nlinarith
  have hscalenn : ∀ c : ℝ, 0 ≤ c → ∀ t : ℝ, 0 ≤ t → 0 ≤ t + c * t ^ α := by
    intro c hc t ht
    have := Real.rpow_nonneg ht α
    nlinarith
  refine ⟨C₂,
    fun t => if t ≤ 0 then 0 else K * (σ (t + C₁ * t ^ α) + C₂ * σ (t + 2*C₁ * t ^ α)),
    fun t => if t ≤ 0 then 0 else K * (C₂ * σ (t + 2*C₁ * t ^ α)),
    hC₂0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    dsimp only
    rw [if_neg (not_le.2 ht)]
  · intro t ht
    dsimp only
    rw [if_neg (not_le.2 ht)]
  · intro t
    dsimp only
    by_cases h : t ≤ 0
    · simp [h]
    · rw [if_neg h]
      rw [not_le] at h
      have h1 : (0:ℝ) ≤ σ (t + C₁ * t ^ α) := by
        rw [← hσ0]; exact hσm (hscalenn C₁ hC₁ t h.le)
      have h2 : (0:ℝ) ≤ σ (t + 2*C₁ * t ^ α) := by
        rw [← hσ0]; exact hσm (hscalenn (2*C₁) (by linarith) t h.le)
      positivity
  · intro t
    dsimp only
    by_cases h : t ≤ 0
    · simp [h]
    · rw [if_neg h]
      rw [not_le] at h
      have h2 : (0:ℝ) ≤ σ (t + 2*C₁ * t ^ α) := by
        rw [← hσ0]; exact hσm (hscalenn (2*C₁) (by linarith) t h.le)
      positivity
  · refine ⟨K * ((1 + C₂) * Cσ), fun t => ?_⟩
    dsimp only
    constructor
    · by_cases h : t ≤ 0
      · rw [if_pos h]; positivity
      · rw [if_neg h]
        have h1 := hσb (t + C₁ * t ^ α)
        have h2 := hσb (t + 2*C₁ * t ^ α)
        nlinarith [mul_nonneg hK.le (sub_nonneg.2 h1),
          mul_nonneg (mul_nonneg hK.le hC₂0.le) (sub_nonneg.2 h2),
          mul_nonneg hK.le hCσ0]
    · by_cases h : t ≤ 0
      · rw [if_pos h]; positivity
      · rw [if_neg h]
        have h2 := hσb (t + 2*C₁ * t ^ α)
        nlinarith [mul_nonneg (mul_nonneg hK.le hC₂0.le) (sub_nonneg.2 h2),
          mul_nonneg hK.le hCσ0]
  · refine Continuous.if_le continuous_const ?_ continuous_id continuous_const ?_
    · have hA : Continuous fun t : ℝ => σ (t + C₁ * t ^ α) := hσc.comp (hscale C₁ hC₁)
      have hB : Continuous fun t : ℝ => σ (t + 2*C₁ * t ^ α) :=
        hσc.comp (hscale (2*C₁) (by linarith))
      exact (hA.add (hB.const_mul C₂)).const_mul K
    · intro t ht
      subst ht
      rw [hscale0 C₁, hscale0 (2*C₁), hσ0]
      ring
  · refine Continuous.if_le continuous_const ?_ continuous_id continuous_const ?_
    · exact ((hσc.comp (hscale (2*C₁) (by linarith))).const_mul C₂).const_mul K
    · intro t ht
      subst ht
      rw [hscale0 (2*C₁), hσ0]
      ring
  · intro s t hst
    dsimp only
    by_cases hs : s ≤ 0
    · rw [if_pos hs]
      by_cases ht : t ≤ 0
      · rw [if_pos ht]
      · rw [if_neg ht]
        rw [not_le] at ht
        have h1 : (0:ℝ) ≤ σ (t + C₁ * t ^ α) := by
          rw [← hσ0]; exact hσm (hscalenn C₁ hC₁ t ht.le)
        have h2 : (0:ℝ) ≤ σ (t + 2*C₁ * t ^ α) := by
          rw [← hσ0]; exact hσm (hscalenn (2*C₁) (by linarith) t ht.le)
        positivity
    · rw [not_le] at hs
      rw [if_neg (not_le.2 hs), if_neg (not_le.2 (lt_of_lt_of_le hs hst))]
      have h1 := hσm (hscalemono C₁ hC₁ s t hs.le hst)
      have h2 := hσm (hscalemono (2*C₁) (by linarith) s t hs.le hst)
      nlinarith [mul_nonneg hK.le (sub_nonneg.2 h1),
        mul_nonneg (mul_nonneg hK.le hC₂0.le) (sub_nonneg.2 h2)]
  · intro s t hst
    dsimp only
    by_cases hs : s ≤ 0
    · rw [if_pos hs]
      by_cases ht : t ≤ 0
      · rw [if_pos ht]
      · rw [if_neg ht]
        rw [not_le] at ht
        have h2 : (0:ℝ) ≤ σ (t + 2*C₁ * t ^ α) := by
          rw [← hσ0]; exact hσm (hscalenn (2*C₁) (by linarith) t ht.le)
        positivity
    · rw [not_le] at hs
      rw [if_neg (not_le.2 hs), if_neg (not_le.2 (lt_of_lt_of_le hs hst))]
      have h2 := hσm (hscalemono (2*C₁) (by linarith) s t hs.le hst)
      nlinarith [mul_nonneg (mul_nonneg hK.le hC₂0.le) (sub_nonneg.2 h2)]
  · simp
  · simp
  · -- the integral chain
    intro ε z₀ R x₀ fdens f0 u v g gv hR hgLp hgvLp hI1 hI2 hI3 hI4 hF3 hu6 hv6 h51 h43
    dsimp only
    have hRpos : ¬ (R ≤ 0) := not_le.2 hR
    rw [if_neg hRpos, if_neg hRpos]
    have hfin : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    -- the weight `(1 + |·|²)^{p/2}` is integrable along an `L^p` field
    have hwle : ∀ s : ℝ, 0 ≤ s → (1 + s ^ 2) ^ (p/2) ≤ (1 + s) ^ p := by
      intro s hs
      have h1 : (1 : ℝ) + s ^ 2 ≤ (1 + s) ^ 2 := by nlinarith
      have h2 : ((1:ℝ) + s ^ 2) ^ (p/2) ≤ ((1 + s) ^ 2) ^ (p/2) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
      rwa [hsq (1 + s) (by linarith)] at h2
    have hwint : ∀ h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        MemLp h (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) →
        IntegrableOn (fun x => (1 + ‖h x‖ ^ 2) ^ (p/2)) (Metric.ball x₀ R) volume := by
      intro h hh
      have hone : MemLp (fun x => (1:ℝ) + ‖h x‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R)) := (memLp_const (1:ℝ)).add hh.norm
      have hpow := hone.norm_rpow_div (ENNReal.ofReal p)
      rw [ENNReal.toReal_ofReal hp0.le,
        ENNReal.div_self (ne_of_gt (ENNReal.ofReal_pos.2 hp0)) ENNReal.ofReal_ne_top] at hpow
      have hint1 : Integrable (fun x => ((1:ℝ) + ‖h x‖) ^ p)
          (volume.restrict (Metric.ball x₀ R)) := by
        have hh2 := memLp_one_iff_integrable.1 hpow
        refine hh2.congr ?_
        filter_upwards with x
        rw [Real.norm_of_nonneg (by positivity)]
      have hmeasw : AEStronglyMeasurable (fun x => (1 + ‖h x‖ ^ 2) ^ (p/2))
          (volume.restrict (Metric.ball x₀ R)) := by
        have hc : Continuous fun z : ℝ => (1 + z ^ 2) ^ (p/2) := by
          have h1 : Continuous fun z : ℝ => 1 + z ^ 2 := by fun_prop
          exact h1.rpow_const fun z => Or.inr (by positivity)
        exact hc.comp_aestronglyMeasurable hh.norm.aestronglyMeasurable
      refine hint1.mono' hmeasw ?_
      filter_upwards with x
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact hwle ‖h x‖ (norm_nonneg _)
    have hwg := hwint g hgLp
    have hwgv := hwint gv hgvLp
    have hdiffLp : MemLp (fun x => g x - gv x) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ R)) := hgLp.sub hgvLp
    have hpne0 : (ENNReal.ofReal p) ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
    have hwdiff : IntegrableOn (fun x => ‖g x - gv x‖ ^ p) (Metric.ball x₀ R) volume := by
      have h := hdiffLp.integrable_norm_rpow hpne0 ENNReal.ofReal_ne_top
      rwa [ENNReal.toReal_ofReal hp0.le] at h
    -- (6e)
    have h6e : (∫ x in Metric.ball x₀ R, (1 + ‖gv x‖ ^ 2) ^ (p/2))
        ≤ C₂ * ((∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p/2))
          + ∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p) := by
      have hptw : ∀ x : EuclideanSpace ℝ (Fin n),
          (1 + ‖gv x‖ ^ 2) ^ (p/2)
            ≤ C₂ * ((1 + ‖g x‖ ^ 2) ^ (p/2) + ‖g x - gv x‖ ^ p) := by
        intro x
        have htri : ‖gv x‖ ≤ ‖g x‖ + ‖g x - gv x‖ := by
          have h := norm_sub_le (g x) (g x - gv x)
          simpa using h
        have hb : (1:ℝ) + ‖gv x‖ ^ 2
            ≤ 2 * (1 + ‖g x‖ ^ 2) + 2 * ‖g x - gv x‖ ^ 2 := by
          nlinarith [norm_nonneg (g x), norm_nonneg (gv x), norm_nonneg (g x - gv x),
            sq_nonneg (‖g x‖ - ‖g x - gv x‖)]
        have h1 : ((1:ℝ) + ‖gv x‖ ^ 2) ^ (p/2)
            ≤ (2 * (1 + ‖g x‖ ^ 2) + 2 * ‖g x - gv x‖ ^ 2) ^ (p/2) :=
          Real.rpow_le_rpow (by positivity) hb (by positivity)
        have h2 := hqsub (p/2) (2 * (1 + ‖g x‖ ^ 2)) (2 * ‖g x - gv x‖ ^ 2)
          (by positivity) (by positivity) (by positivity)
        have h3 : ((2:ℝ) * (1 + ‖g x‖ ^ 2)) ^ (p/2)
            = (2:ℝ) ^ (p/2) * (1 + ‖g x‖ ^ 2) ^ (p/2) :=
          Real.mul_rpow (by norm_num) (by positivity)
        have h4 : ((2:ℝ) * ‖g x - gv x‖ ^ 2) ^ (p/2)
            = (2:ℝ) ^ (p/2) * ‖g x - gv x‖ ^ p := by
          rw [Real.mul_rpow (by norm_num) (by positivity), hsq _ (norm_nonneg _)]
        rw [h3, h4] at h2
        have hC₂eq : C₂ = max 1 ((2:ℝ) ^ (p/2 - 1)) * (2:ℝ) ^ (p/2) := hC₂def
        rw [hC₂eq]
        calc ((1:ℝ) + ‖gv x‖ ^ 2) ^ (p/2)
            ≤ (2 * (1 + ‖g x‖ ^ 2) + 2 * ‖g x - gv x‖ ^ 2) ^ (p/2) := h1
          _ ≤ max 1 ((2:ℝ) ^ (p/2 - 1))
              * ((2:ℝ) ^ (p/2) * (1 + ‖g x‖ ^ 2) ^ (p/2)
                 + (2:ℝ) ^ (p/2) * ‖g x - gv x‖ ^ p) := h2
          _ = max 1 ((2:ℝ) ^ (p/2 - 1)) * (2:ℝ) ^ (p/2)
              * ((1 + ‖g x‖ ^ 2) ^ (p/2) + ‖g x - gv x‖ ^ p) := by ring
      have hmaj : IntegrableOn
          (fun x => C₂ * ((1 + ‖g x‖ ^ 2) ^ (p/2) + ‖g x - gv x‖ ^ p))
          (Metric.ball x₀ R) volume := (hwg.add hwdiff).const_mul C₂
      have h := integral_mono hwgv hmaj (fun x => hptw x)
      rw [integral_const_mul, integral_add hwg hwdiff] at h
      exact h
    -- the two freezing errors
    have hRnn : (0:ℝ) ≤ C₁ * R ^ α := by positivity
    have hbrk : ∀ (w : EuclideanSpace ℝ (Fin n) → ℝ)
        (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (cc : ℝ),
        IntegrableOn (fun x => fdens x (w x) (h x)) (Metric.ball x₀ R) volume →
        IntegrableOn (fun x => f0 (h x)) (Metric.ball x₀ R) volume →
        IntegrableOn (fun x => (1 + ‖h x‖ ^ 2) ^ (p/2)) (Metric.ball x₀ R) volume →
        (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), |w x - z₀| ≤ cc) →
        0 ≤ cc →
        |(∫ x in Metric.ball x₀ R, fdens x (w x) (h x))
            - ∫ x in Metric.ball x₀ R, f0 (h x)|
          ≤ σ (R + cc) * ∫ x in Metric.ball x₀ R, (1 + ‖h x‖ ^ 2) ^ (p/2) := by
      intro w h cc hIa hIb hIw hw hcc
      have hD : IntegrableOn (fun x => fdens x (w x) (h x) - f0 (h x))
          (Metric.ball x₀ R) volume := hIa.sub hIb
      rw [← integral_sub hIa hIb, ← integral_const_mul]
      refine le_trans abs_integral_le_integral_abs ?_
      refine integral_mono_ae hD.abs (hIw.const_mul (σ (R + cc))) ?_
      filter_upwards [hw, ae_restrict_mem measurableSet_ball] with x hwx hxB
      have h1 := hF3 x hxB (w x) (h x)
      have hd : dist x x₀ ≤ R := le_of_lt (Metric.mem_ball.1 hxB)
      have h2 : σ (dist x x₀ + |w x - z₀|) ≤ σ (R + cc) := hσm (by linarith)
      have h3 : (0:ℝ) ≤ (1 + ‖h x‖ ^ 2) ^ (p/2) := Real.rpow_nonneg (by positivity) _
      calc |fdens x (w x) (h x) - f0 (h x)|
          ≤ (1 + ‖h x‖ ^ 2) ^ (p/2) * σ (dist x x₀ + |w x - z₀|) := h1
        _ ≤ (1 + ‖h x‖ ^ 2) ^ (p/2) * σ (R + cc) := mul_le_mul_of_nonneg_left h2 h3
        _ = σ (R + cc) * (1 + ‖h x‖ ^ 2) ^ (p/2) := by ring
    have hA := hbrk u g (C₁ * R ^ α) hI3 hI1 hwg hu6 hRnn
    have hB := hbrk v gv (2*C₁ * R ^ α) hI4 hI2 hwgv
      (by filter_upwards [hv6] with x hx; nlinarith) (by positivity)
    have hσA : (0:ℝ) ≤ σ (R + C₁ * R ^ α) := by
      rw [← hσ0]; exact hσm (by nlinarith)
    have hσB : (0:ℝ) ≤ σ (R + 2*C₁ * R ^ α) := by
      rw [← hσ0]; exact hσm (by nlinarith)
    have hIg0 : (0:ℝ) ≤ ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p/2) :=
      integral_nonneg fun x => Real.rpow_nonneg (by positivity) _
    have hIw0 : (0:ℝ) ≤ ∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p :=
      integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    have h1 : (∫ x in Metric.ball x₀ R, f0 (g x))
          - ∫ x in Metric.ball x₀ R, fdens x (u x) (g x)
        ≤ σ (R + C₁ * R ^ α) * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p/2) := by
      have := le_abs_self ((∫ x in Metric.ball x₀ R, fdens x (u x) (g x))
        - ∫ x in Metric.ball x₀ R, f0 (g x))
      have h' := abs_sub_comm ((∫ x in Metric.ball x₀ R, fdens x (u x) (g x)))
        ((∫ x in Metric.ball x₀ R, f0 (g x)))
      rw [h'] at hA
      linarith [le_abs_self ((∫ x in Metric.ball x₀ R, f0 (g x))
        - ∫ x in Metric.ball x₀ R, fdens x (u x) (g x)), hA]
    have h2 : (∫ x in Metric.ball x₀ R, fdens x (v x) (gv x))
          - ∫ x in Metric.ball x₀ R, f0 (gv x)
        ≤ σ (R + 2*C₁ * R ^ α) * ∫ x in Metric.ball x₀ R, (1 + ‖gv x‖ ^ 2) ^ (p/2) :=
      le_trans (le_abs_self _) hB
    have h3 : σ (R + 2*C₁ * R ^ α)
          * (∫ x in Metric.ball x₀ R, (1 + ‖gv x‖ ^ 2) ^ (p/2))
        ≤ σ (R + 2*C₁ * R ^ α) * (C₂ * ((∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p/2))
            + ∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p)) :=
      mul_le_mul_of_nonneg_left h6e hσB
    have hgap : (∫ x in Metric.ball x₀ R, f0 (g x))
          - ∫ x in Metric.ball x₀ R, f0 (gv x)
        ≤ (σ (R + C₁ * R ^ α) + C₂ * σ (R + 2*C₁ * R ^ α))
            * (∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p/2))
          + C₂ * σ (R + 2*C₁ * R ^ α)
            * ∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p := by
      nlinarith [h1, h2, h3, h51]
    have hKgap : K * ((∫ x in Metric.ball x₀ R, f0 (g x))
          - ∫ x in Metric.ball x₀ R, f0 (gv x))
        ≤ K * ((σ (R + C₁ * R ^ α) + C₂ * σ (R + 2*C₁ * R ^ α))
            * (∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p/2))
          + C₂ * σ (R + 2*C₁ * R ^ α)
            * ∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p) :=
      mul_le_mul_of_nonneg_left hgap hK.le
    nlinarith [h43, hKgap]
