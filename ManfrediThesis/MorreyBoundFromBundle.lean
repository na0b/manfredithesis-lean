import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MorreyBoundOn
import ManfrediThesis.CampanatoIterationLemma
open MeasureTheory

/-- Part (i) of Theorem 3 (and of Theorem 5), on the middle domain `Ω''`: from
the decay (4.11) for the comparison maps and the smallness `(⋆)` of the
remainder, the Morrey bound `‖∇u‖_{L^{p,n-τ}(Ω'')} ≤ N₁`.  This is the thesis'
passage (4.12) → (4.13) → (4.14) → (i), run through the iteration lemma. -/
theorem MorreyBoundFromBundle :
    ∀ (n : ℕ) (p τ c₀ W d R₁ : ℝ) (σ₂ : ℝ → ℝ),
      2 ≤ n → 1 < p → 0 < τ → τ < (n : ℝ) → 0 < c₀ → 0 ≤ W → 0 < d → 0 < R₁ →
      Continuous σ₂ → Monotone σ₂ → σ₂ 0 = 0 → (∀ t : ℝ, 0 ≤ σ₂ t) →
      ∃ N₁ : ℝ, 0 ≤ N₁ ∧
        ∀ (ε : ℝ) (Ω Ω'' : Set (EuclideanSpace ℝ (Fin n)))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 ≤ ε → ε ≤ 1 → IsOpen Ω → IsOpen Ω'' →
          Bornology.IsBounded Ω'' → closure Ω'' ⊆ Ω →
          (∀ x ∈ Ω'', ∀ y, y ∉ Ω → d ≤ dist x y) →
          MemW1pOn n p Ω u g →
          ((∫ x in Ω, |u x| ^ p) + ∫ x in Ω, ‖g x‖ ^ p) ≤ W ^ p →
          (∀ x₀ ∈ Ω'', ∀ R : ℝ, 0 < R → R ≤ R₁ → Metric.closedBall x₀ R ⊆ Ω →
            ∃ (v : EuclideanSpace ℝ (Fin n) → ℝ)
              (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
              MemW1pOn n p (Metric.ball x₀ R) v gv ∧
              (∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
                (∫ x in Metric.ball x₀ ρ, (ε + ‖gv x‖ ^ 2) ^ (p / 2))
                  ≤ c₀ * (ρ / R) ^ (n : ℝ)
                    * ∫ x in Metric.ball x₀ R, (ε + ‖gv x‖ ^ 2) ^ (p / 2)) ∧
              (∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p)
                ≤ σ₂ R * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2)) →
          MorreyBoundOn n p ((n : ℝ) - τ) Ω'' (fun x => ‖g x‖) N₁ := by
  intro n p τ c₀ W d R₁ σ₂ hn hp hτ hτn hc₀ hW hd hR₁ hσc hσm hσ0 hσnn
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  have hp2 : (0:ℝ) < p / 2 := by linarith
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hntriv : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, hnpos⟩ (1 : ℝ), ?_⟩⟩
    intro hcon
    have h := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w ⟨0, hnpos⟩) hcon
    simp at h
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
  have hnτ : (0:ℝ) < (n:ℝ) - τ := by linarith
  -- the subadditivity constant
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
  set κ : ℝ := max 1 (2 ^ (p/2 - 1)) with hκdef
  have hκ1 : (1:ℝ) ≤ κ := by rw [hκdef]; exact le_max_left _ _
  have hκ : 0 < κ := lt_of_lt_of_le one_pos hκ1
  set c₁ : ℝ := κ * 2 ^ (p/2) with hc₁def
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]; exact mul_pos hκ (Real.rpow_pos_of_pos two_pos _)
  set c₂ : ℝ := c₀ * c₁ ^ 2 with hc₂def
  have hc₂ : 0 < c₂ := by rw [hc₂def]; positivity
  set c₃ : ℝ := c₀ * c₁ ^ 2 + c₁ with hc₃def
  have hc₃ : 0 < c₃ := by rw [hc₃def]; positivity
  set c₃' : ℝ := κ * c₃ with hc₃'def
  have hc₃' : 0 < c₃' := by rw [hc₃'def]; exact mul_pos hκ hc₃
  set A : ℝ := max c₂ c₃' with hAdef
  have hA : 0 < A := by rw [hAdef]; exact lt_of_lt_of_le hc₂ (le_max_left _ _)
  obtain ⟨δ₀, C, hδ₀, hC, hiter⟩ := CampanatoIterationLemma A (n:ℝ) ((n:ℝ) - τ) hA hnR hnτ
    (by linarith)
  -- a radius where σ₂ is below δ₀
  obtain ⟨R₂, hR₂pos, hR₂σ⟩ : ∃ R₂ : ℝ, 0 < R₂ ∧ σ₂ R₂ < δ₀ := by
    have h0 : σ₂ 0 < δ₀ := by rw [hσ0]; exact hδ₀
    have hev : ∀ᶠ t in nhds (0:ℝ), σ₂ t < δ₀ :=
      (hσc.tendsto 0).eventually_lt_const h0
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ζ, hζ, hball⟩ := hev
    exact ⟨ζ/2, by linarith, hball (by rw [Real.dist_eq]; rw [sub_zero]; rw [abs_of_pos (by linarith)]; linarith)⟩
  -- the ball volume and the remaining constants
  set ωn : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal with hωdef
  have hω : 0 < ωn := by
    rw [hωdef]
    refine ENNReal.toReal_pos (ne_of_gt ?_) measure_ball_lt_top.ne
    exact Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self one_pos⟩
  have hballvol : ∀ (y : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 ≤ t →
      (volume (Metric.ball y t)).toReal = ωn * t ^ ((n:ℝ)) := by
    intro y t ht
    rw [Measure.addHaar_ball volume y ht, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg ht _),
      show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n by simp, ← hωdef,
      ← Real.rpow_natCast t n]
    ring
  set c₄ : ℝ := c₃' * (1 + σ₂ R₂) * ωn * (1 + R₂ ^ τ) with hc₄def
  have hc₄ : 0 < c₄ := by
    rw [hc₄def]
    have h1 : (0:ℝ) < 1 + σ₂ R₂ := by linarith [hσnn R₂]
    have h2 : (0:ℝ) < 1 + R₂ ^ τ := by
      have := Real.rpow_pos_of_pos hR₂pos τ; linarith
    exact mul_pos (mul_pos (mul_pos hc₃' h1) hω) h2
  set Rs : ℝ := min R₁ (min R₂ (d/16)) with hRsdef
  have hRs : 0 < Rs := by
    rw [hRsdef]; exact lt_min hR₁ (lt_min hR₂pos (by linarith))
  have hRsR₁ : Rs ≤ R₁ := by rw [hRsdef]; exact min_le_left _ _
  have hRsR₂ : Rs ≤ R₂ := le_trans (by rw [hRsdef]; exact min_le_right _ _) (min_le_left _ _)
  have hRsd : Rs ≤ d/16 := le_trans (by rw [hRsdef]; exact min_le_right _ _) (min_le_right _ _)
  set A₁ : ℝ := C * Rs ^ (-((n:ℝ)-τ))
      * (2 ^ (p/2) * (ωn * Rs ^ ((n:ℝ)) + W ^ p) + c₄ * Rs ^ ((n:ℝ)-τ)) with hA₁def
  have hWp : (0:ℝ) ≤ W ^ p := Real.rpow_nonneg hW _
  have hA₁0 : 0 ≤ A₁ := by
    rw [hA₁def]
    refine mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hRs.le _)) ?_
    have h1 : (0:ℝ) ≤ 2 ^ (p/2) * (ωn * Rs ^ ((n:ℝ)) + W ^ p) := by
      refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_
      exact add_nonneg (mul_nonneg hω.le (Real.rpow_nonneg hRs.le _)) hWp
    have h2 : (0:ℝ) ≤ c₄ * Rs ^ ((n:ℝ)-τ) := mul_nonneg hc₄.le (Real.rpow_nonneg hRs.le _)
    linarith
  set N₁ : ℝ := (max A₁ (W ^ p * Rs ^ (-((n:ℝ)-τ)))) ^ (1/p) with hN₁def
  have hmax0 : (0:ℝ) ≤ max A₁ (W ^ p * Rs ^ (-((n:ℝ)-τ))) := le_trans hA₁0 (le_max_left _ _)
  have hN₁ : 0 ≤ N₁ := Real.rpow_nonneg hmax0 _
  have hN₁pow : N₁ ^ p = max A₁ (W ^ p * Rs ^ (-((n:ℝ)-τ))) := by
    rw [hN₁def, ← Real.rpow_mul hmax0, one_div, inv_mul_cancel₀ (ne_of_gt hp0), Real.rpow_one]
  refine ⟨N₁, hN₁, ?_⟩
  intro ε Ω Ω'' u g hε0 hε1 hΩ hΩ'' hbdd hcl hsep hu hWb hbundle
  -- the two elementary comparisons
  have hE1 : ∀ a b : EuclideanSpace ℝ (Fin n),
      (ε + ‖a‖ ^ 2) ^ (p/2) ≤ c₁ * ((ε + ‖b‖ ^ 2) ^ (p/2) + ‖a - b‖ ^ p) := by
    intro a b
    have hab : ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
      have h0 := norm_add_le b (a - b)
      rwa [show b + (a - b) = a from by abel] at h0
    have hsqle : ‖a‖ ^ 2 ≤ (‖b‖ + ‖a - b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hab 2
    rw [show (‖b‖ + ‖a - b‖) ^ 2 = ‖b‖ ^ 2 + 2 * ‖b‖ * ‖a - b‖ + ‖a - b‖ ^ 2 from by ring]
      at hsqle
    have hcross : 2 * ‖b‖ * ‖a - b‖ ≤ ‖b‖ ^ 2 + ‖a - b‖ ^ 2 := two_mul_le_add_sq _ _
    have hb : ε + ‖a‖ ^ 2 ≤ 2 * ((ε + ‖b‖ ^ 2) + ‖a - b‖ ^ 2) := by linarith
    calc (ε + ‖a‖ ^ 2) ^ (p/2)
        ≤ (2 * ((ε + ‖b‖ ^ 2) + ‖a - b‖ ^ 2)) ^ (p/2) :=
          Real.rpow_le_rpow (add_nonneg hε0 (sq_nonneg _)) hb hp2.le
      _ = 2 ^ (p/2) * ((ε + ‖b‖ ^ 2) + ‖a - b‖ ^ 2) ^ (p/2) :=
          Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 ^ (p/2) * (κ * ((ε + ‖b‖ ^ 2) ^ (p/2) + (‖a - b‖ ^ 2) ^ (p/2))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
          rw [hκdef]
          exact hqsub (p/2) _ _ hp2 (add_nonneg hε0 (sq_nonneg _)) (sq_nonneg _)
      _ = c₁ * ((ε + ‖b‖ ^ 2) ^ (p/2) + ‖a - b‖ ^ p) := by
          rw [hsq (‖a - b‖) (norm_nonneg _), hc₁def]; ring
  have hE2 : ∀ a : EuclideanSpace ℝ (Fin n),
      (1 + ‖a‖ ^ 2) ^ (p/2) ≤ κ * ((ε + ‖a‖ ^ 2) ^ (p/2) + 1) := by
    intro a
    have hb : (1:ℝ) + ‖a‖ ^ 2 ≤ (ε + ‖a‖ ^ 2) + 1 := by linarith
    calc (1 + ‖a‖ ^ 2) ^ (p/2) ≤ ((ε + ‖a‖ ^ 2) + 1) ^ (p/2) :=
          Real.rpow_le_rpow (by positivity) hb hp2.le
      _ ≤ κ * ((ε + ‖a‖ ^ 2) ^ (p/2) + (1:ℝ) ^ (p/2)) := by
          rw [hκdef]
          exact hqsub (p/2) _ _ hp2 (add_nonneg hε0 (sq_nonneg _)) zero_le_one
      _ = κ * ((ε + ‖a‖ ^ 2) ^ (p/2) + 1) := by rw [Real.one_rpow]
  -- integrability toolkit
  have hpne0 : (ENNReal.ofReal p) ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have hpnet : (ENNReal.ofReal p) ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  have htoR : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hgΩ : MemLp g (ENNReal.ofReal p) (volume.restrict Ω) := hu.2.2
  have hgpΩ : IntegrableOn (fun x => ‖g x‖ ^ p) Ω volume := by
    have h := hgΩ.integrable_norm_rpow hpne0 hpnet
    rwa [htoR] at h
  have hgW : (∫ x in Ω, ‖g x‖ ^ p) ≤ W ^ p := by
    have h0 : (0:ℝ) ≤ ∫ x in Ω, |u x| ^ p :=
      integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
    linarith
  have hκ2 : κ ≤ 2 ^ (p/2) := by
    rw [hκdef]
    refine max_le ?_ (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
    calc (1:ℝ) = 2 ^ (0:ℝ) := (Real.rpow_zero 2).symm
      _ ≤ 2 ^ (p/2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp2.le
  have hdomg : ∀ c : ℝ, 0 ≤ c → c ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin n),
      (c + ‖h‖ ^ 2) ^ (p/2) ≤ 2 ^ (p/2) * (1 + ‖h‖ ^ p) := by
    intro c hc0 hc1 h
    have h1 : c + ‖h‖ ^ 2 ≤ 1 + ‖h‖ ^ 2 := by linarith
    have hgp0 : (0:ℝ) ≤ ‖h‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
    calc (c + ‖h‖ ^ 2) ^ (p/2) ≤ (1 + ‖h‖ ^ 2) ^ (p/2) :=
          Real.rpow_le_rpow (add_nonneg hc0 (sq_nonneg _)) h1 hp2.le
      _ ≤ κ * ((1:ℝ) ^ (p/2) + (‖h‖ ^ 2) ^ (p/2)) := by
          rw [hκdef]; exact hqsub (p/2) _ _ hp2 zero_le_one (sq_nonneg _)
      _ = κ * (1 + ‖h‖ ^ p) := by rw [Real.one_rpow, hsq (‖h‖) (norm_nonneg _)]
      _ ≤ 2 ^ (p/2) * (1 + ‖h‖ ^ p) := mul_le_mul_of_nonneg_right hκ2 (by linarith)
  have hcontrp : Continuous fun s : ℝ => s ^ (p/2) :=
    continuous_iff_continuousAt.mpr fun s =>
      Real.continuousAt_rpow_const s (p/2) (Or.inr hp2.le)
  have hmeasg : ∀ (c : ℝ) (s : Set (EuclideanSpace ℝ (Fin n)))
      (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      AEStronglyMeasurable G (volume.restrict s) →
      AEStronglyMeasurable (fun x => (c + ‖G x‖ ^ 2) ^ (p/2)) (volume.restrict s) := by
    intro c s G hG
    exact (hcontrp.comp ((continuous_const.add (continuous_pow 2)) :
      Continuous fun t : ℝ => c + t ^ 2)).comp_aestronglyMeasurable hG.norm
  have hintb : ∀ c : ℝ, 0 ≤ c → c ≤ 1 → ∀ (y : EuclideanSpace ℝ (Fin n)) (t : ℝ)
      (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      MemLp G (ENNReal.ofReal p) (volume.restrict (Metric.ball y t)) →
      IntegrableOn (fun x => (c + ‖G x‖ ^ 2) ^ (p/2)) (Metric.ball y t) volume := by
    intro c hc0 hc1 y t G hG
    have hfin : IsFiniteMeasure (volume.restrict (Metric.ball y t)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have hGp : IntegrableOn (fun x => ‖G x‖ ^ p) (Metric.ball y t) volume := by
      have h := hG.integrable_norm_rpow hpne0 hpnet
      rwa [htoR] at h
    refine Integrable.mono' (g := fun x => 2 ^ (p/2) * (1 + ‖G x‖ ^ p))
      (((integrable_const (1:ℝ)).add hGp).const_mul _) (hmeasg c _ G hG.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (add_nonneg hc0 (sq_nonneg _)) _)]
    exact hdomg c hc0 hc1 (G x)
  -- g restricted to any ball inside Ω
  have hgball : ∀ (y : EuclideanSpace ℝ (Fin n)) (t : ℝ), Metric.ball y t ⊆ Ω →
      MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball y t)) :=
    fun y t hsub => hgΩ.mono_measure (Measure.restrict_mono hsub le_rfl)
  -- the finiteness bound (F)
  have hFbd : ∀ (y : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 < t →
      Metric.closedBall y t ⊆ Ω →
      (∫ x in Metric.ball y t, (ε + ‖g x‖ ^ 2) ^ (p/2))
        ≤ 2 ^ (p/2) * (ωn * t ^ ((n:ℝ)) + W ^ p) := by
    intro y t ht hsubc
    have hsub : Metric.ball y t ⊆ Ω := subset_trans Metric.ball_subset_closedBall hsubc
    have hfin : IsFiniteMeasure (volume.restrict (Metric.ball y t)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have hGp : IntegrableOn (fun x => ‖g x‖ ^ p) (Metric.ball y t) volume :=
      hgpΩ.mono_set hsub
    have h1 := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x =>
        Real.rpow_nonneg (add_nonneg hε0 (sq_nonneg _)) (p/2))
      (((integrable_const (1:ℝ)).add hGp).const_mul (2 ^ (p/2)))
      (Filter.Eventually.of_forall fun x => hdomg ε hε0 hε1 (g x))
    rw [integral_const_mul] at h1
    simp only [Pi.add_apply] at h1
    rw [integral_add (integrable_const (1:ℝ)) hGp, integral_const,
      Measure.real_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
      hballvol y t ht.le] at h1
    refine le_trans h1 ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
    have h2 : (∫ x in Metric.ball y t, ‖g x‖ ^ p) ≤ W ^ p :=
      le_trans (setIntegral_mono_set hgpΩ
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)
        (Filter.Eventually.of_forall fun x hx => hsub hx)) hgW
    linarith
  -- the arithmetic of Steps 3 and 4, isolated from the measure theory
  have harith : ∀ Ip Ir Jp Jr K L r s vol : ℝ,
      0 ≤ Ir → 0 ≤ K → 0 ≤ r → r ≤ 1 → 0 ≤ s → 0 ≤ vol →
      Ip ≤ c₁ * (Jp + K) → Jp ≤ c₀ * r * Jr → Jr ≤ c₁ * (Ir + K) →
      K ≤ s * L → L ≤ κ * Ir + κ * vol →
      Ip ≤ c₂ * r * Ir + c₃' * s * Ir + c₃' * s * vol := by
    intro Ip Ir Jp Jr K L r s vol hIr0 hK0 hr0 hr1 hs0 hvol0 hIp hJp hJr hKs hL
    have s1 : c₀ * r * Jr ≤ c₀ * r * (c₁ * (Ir + K)) :=
      mul_le_mul_of_nonneg_left hJr (mul_nonneg hc₀.le hr0)
    have s3 : Ip ≤ c₁ * (c₀ * r * (c₁ * (Ir + K)) + K) :=
      le_trans hIp (mul_le_mul_of_nonneg_left (by linarith) hc₁.le)
    have s4 : c₁ * (c₀ * r * (c₁ * (Ir + K)) + K)
        = c₂ * r * Ir + c₂ * (r * K) + c₁ * K := by rw [hc₂def]; ring
    have s5 : r * K ≤ K := by
      have := mul_le_mul_of_nonneg_right hr1 hK0
      linarith
    have s6 : c₂ * (r * K) ≤ c₂ * K := mul_le_mul_of_nonneg_left s5 hc₂.le
    have s7 : Ip ≤ c₂ * r * Ir + c₃ * K := by rw [hc₃def] at *; linarith
    have s8 : c₃ * K ≤ c₃ * (s * L) := mul_le_mul_of_nonneg_left hKs hc₃.le
    have s9 : c₃ * (s * L) ≤ c₃ * (s * (κ * Ir + κ * vol)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL hs0) hc₃.le
    have s10 : c₃ * (s * (κ * Ir + κ * vol)) = c₃' * s * Ir + c₃' * s * vol := by
      rw [hc₃'def]; ring
    linarith
  -- (4.14): the Morrey decay, via the iteration lemma
  have h414 : ∀ x₀ ∈ Ω'', ∀ R ρ : ℝ, 0 < R → R ≤ min R₁ R₂ →
      Metric.closedBall x₀ R ⊆ Ω → 0 < ρ → ρ ≤ R →
      (∫ x in Metric.ball x₀ ρ, (ε + ‖g x‖ ^ 2) ^ (p/2))
        ≤ C * (ρ / R) ^ ((n:ℝ) - τ)
          * ((∫ x in Metric.ball x₀ R, (ε + ‖g x‖ ^ 2) ^ (p/2)) + c₄ * R ^ ((n:ℝ) - τ)) := by
    intro x₀ hx₀ R ρ hR hRmin hballR hρ hρR
    have hRR₁ : R ≤ R₁ := le_trans hRmin (min_le_left _ _)
    have hRR₂ : R ≤ R₂ := le_trans hRmin (min_le_right _ _)
    have hballsub : ∀ t : ℝ, t ≤ R → Metric.ball x₀ t ⊆ Ω := fun t ht =>
      subset_trans (Metric.ball_subset_ball ht)
        (subset_trans Metric.ball_subset_closedBall hballR)
    have hIint : ∀ t : ℝ, t ≤ R →
        IntegrableOn (fun x => (ε + ‖g x‖ ^ 2) ^ (p/2)) (Metric.ball x₀ t) volume :=
      fun t ht => hintb ε hε0 hε1 x₀ t g (hgball x₀ t (hballsub t ht))
    set F : ℝ → ℝ := fun t => if t ≤ 0 then 0
      else ∫ x in Metric.ball x₀ (min t R), (ε + ‖g x‖ ^ 2) ^ (p/2) with hFdef
    have hFval : ∀ t : ℝ, 0 < t → t ≤ R →
        F t = ∫ x in Metric.ball x₀ t, (ε + ‖g x‖ ^ 2) ^ (p/2) := by
      intro t ht htR
      rw [hFdef]
      simp only [not_le.2 ht, if_false, min_eq_left htR]
    have hF0 : ∀ t : ℝ, 0 ≤ F t := by
      intro t
      rw [hFdef]
      by_cases h : t ≤ 0
      · simp only [h, if_true]
        exact le_refl 0
      · simp only [h, if_false]
        exact integral_nonneg fun x => Real.rpow_nonneg (add_nonneg hε0 (sq_nonneg _)) _
    have hFmono : ∀ a b : ℝ, a ≤ b → F a ≤ F b := by
      intro a b hab
      by_cases ha : a ≤ 0
      · have : F a = 0 := by rw [hFdef]; simp only [ha, if_true]
        rw [this]; exact hF0 b
      · have hb : ¬ b ≤ 0 := fun h => ha (le_trans hab h)
        have e1 : F a = ∫ x in Metric.ball x₀ (min a R), (ε + ‖g x‖ ^ 2) ^ (p/2) := by
          rw [hFdef]; simp only [ha, if_false]
        have e2 : F b = ∫ x in Metric.ball x₀ (min b R), (ε + ‖g x‖ ^ 2) ^ (p/2) := by
          rw [hFdef]; simp only [hb, if_false]
        rw [e1, e2]
        exact setIntegral_mono_set (hIint (min b R) (min_le_right _ _))
          (Filter.Eventually.of_forall fun x =>
            Real.rpow_nonneg (add_nonneg hε0 (sq_nonneg _)) _)
          (Filter.Eventually.of_forall fun x hx =>
            Metric.ball_subset_ball (min_le_min hab le_rfl) hx)
    have hFrec : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ R →
        F a ≤ A * ((a / b) ^ ((n:ℝ)) + σ₂ R) * F b + c₄ * b ^ ((n:ℝ) - τ) := by
      intro a b ha hab hbR
      have hb : 0 < b := lt_of_lt_of_le ha hab
      have hbR₁ : b ≤ R₁ := le_trans hbR hRR₁
      have hbR₂ : b ≤ R₂ := le_trans hbR hRR₂
      have hballb : Metric.closedBall x₀ b ⊆ Ω :=
        subset_trans (Metric.closedBall_subset_closedBall hbR) hballR
      obtain ⟨v, gv, hvW, h411, hstar⟩ := hbundle x₀ hx₀ b hb hbR₁ hballb
      have hab' : Metric.ball x₀ a ⊆ Metric.ball x₀ b := Metric.ball_subset_ball hab
      have hgvb : MemLp gv (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ b)) := hvW.2.2
      have hgva : MemLp gv (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ a)) :=
        hgvb.mono_measure (Measure.restrict_mono hab' le_rfl)
      have hgb : MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ b)) :=
        hgball x₀ b (hballsub b hbR)
      have hga : MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ a)) :=
        hgball x₀ a (hballsub a (le_trans hab hbR))
      have hIgva : IntegrableOn (fun x => (ε + ‖gv x‖ ^ 2) ^ (p/2)) (Metric.ball x₀ a) volume :=
        hintb ε hε0 hε1 x₀ a gv hgva
      have hIgvb : IntegrableOn (fun x => (ε + ‖gv x‖ ^ 2) ^ (p/2)) (Metric.ball x₀ b) volume :=
        hintb ε hε0 hε1 x₀ b gv hgvb
      have hI1gb : IntegrableOn (fun x => (1 + ‖g x‖ ^ 2) ^ (p/2)) (Metric.ball x₀ b) volume :=
        hintb 1 zero_le_one le_rfl x₀ b g hgb
      have hIwb : IntegrableOn (fun x => ‖g x - gv x‖ ^ p) (Metric.ball x₀ b) volume := by
        have h := ((hgb.sub hgvb).integrable_norm_rpow hpne0 hpnet)
        rwa [htoR] at h
      have hIwa : IntegrableOn (fun x => ‖g x - gv x‖ ^ p) (Metric.ball x₀ a) volume :=
        hIwb.mono_set hab'
      have hwnn : ∀ x : EuclideanSpace ℝ (Fin n), (0:ℝ) ≤ ‖g x - gv x‖ ^ p :=
        fun x => Real.rpow_nonneg (norm_nonneg _) _
      have hKab : (∫ x in Metric.ball x₀ a, ‖g x - gv x‖ ^ p)
          ≤ ∫ x in Metric.ball x₀ b, ‖g x - gv x‖ ^ p :=
        setIntegral_mono_set hIwb (Filter.Eventually.of_forall hwnn)
          (Filter.Eventually.of_forall fun x hx => hab' hx)
      -- (3a)
      have h3a : (∫ x in Metric.ball x₀ a, (ε + ‖g x‖ ^ 2) ^ (p/2))
          ≤ c₁ * ((∫ x in Metric.ball x₀ a, (ε + ‖gv x‖ ^ 2) ^ (p/2))
            + ∫ x in Metric.ball x₀ b, ‖g x - gv x‖ ^ p) := by
        have h1 := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x =>
            Real.rpow_nonneg (add_nonneg hε0 (sq_nonneg _)) (p/2))
          ((hIgva.add hIwa).const_mul c₁)
          (Filter.Eventually.of_forall fun x => hE1 (g x) (gv x))
        rw [integral_const_mul] at h1
        simp only [Pi.add_apply] at h1
        rw [integral_add hIgva hIwa] at h1
        refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hc₁.le)
        linarith
      -- (3c)
      have h3c : (∫ x in Metric.ball x₀ b, (ε + ‖gv x‖ ^ 2) ^ (p/2))
          ≤ c₁ * ((∫ x in Metric.ball x₀ b, (ε + ‖g x‖ ^ 2) ^ (p/2))
            + ∫ x in Metric.ball x₀ b, ‖g x - gv x‖ ^ p) := by
        have hpt : ∀ x : EuclideanSpace ℝ (Fin n), (ε + ‖gv x‖ ^ 2) ^ (p/2)
            ≤ c₁ * ((ε + ‖g x‖ ^ 2) ^ (p/2) + ‖g x - gv x‖ ^ p) := by
          intro x
          have h := hE1 (gv x) (g x)
          rwa [norm_sub_rev (gv x) (g x)] at h
        have h1 := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x =>
            Real.rpow_nonneg (add_nonneg hε0 (sq_nonneg _)) (p/2))
          (((hIint b hbR).add hIwb).const_mul c₁) (Filter.Eventually.of_forall hpt)
        rw [integral_const_mul] at h1
        simp only [Pi.add_apply] at h1
        rw [integral_add (hIint b hbR) hIwb] at h1
        exact h1
      -- (E2) integrated
      have hE2i : (∫ x in Metric.ball x₀ b, (1 + ‖g x‖ ^ 2) ^ (p/2))
          ≤ κ * (∫ x in Metric.ball x₀ b, (ε + ‖g x‖ ^ 2) ^ (p/2)) + κ * (ωn * b ^ ((n:ℝ))) := by
        have hfin : IsFiniteMeasure (volume.restrict (Metric.ball x₀ b)) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
        have h1 := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (by positivity) (p/2))
          (((hIint b hbR).add (integrable_const (1:ℝ))).const_mul κ)
          (Filter.Eventually.of_forall fun x => hE2 (g x))
        rw [integral_const_mul] at h1
        simp only [Pi.add_apply] at h1
        rw [integral_add (hIint b hbR) (integrable_const (1:ℝ)), integral_const,
          Measure.real_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
          hballvol x₀ b hb.le] at h1
        linarith
      -- assemble through the arithmetic lemma
      have hr0 : (0:ℝ) ≤ (a / b) ^ ((n:ℝ)) := Real.rpow_nonneg (div_nonneg ha.le hb.le) _
      have hr1 : (a / b) ^ ((n:ℝ)) ≤ 1 :=
        Real.rpow_le_one (div_nonneg ha.le hb.le) (by rw [div_le_one hb]; exact hab) hnR.le
      have hIr0 : (0:ℝ) ≤ ∫ x in Metric.ball x₀ b, (ε + ‖g x‖ ^ 2) ^ (p/2) :=
        integral_nonneg fun x => Real.rpow_nonneg (add_nonneg hε0 (sq_nonneg _)) _
      have hK0 : (0:ℝ) ≤ ∫ x in Metric.ball x₀ b, ‖g x - gv x‖ ^ p :=
        integral_nonneg fun x => hwnn x
      have hvol0 : (0:ℝ) ≤ ωn * b ^ ((n:ℝ)) :=
        mul_nonneg hω.le (Real.rpow_nonneg hb.le _)
      have hmain := harith _ _ _ _ _ _ _ _ _ hIr0 hK0 hr0 hr1 (hσnn b) hvol0
        h3a (h411 a ha hab) h3c (hstar) hE2i
      rw [hFval a ha (le_trans hab hbR), hFval b hb hbR]
      -- now bound the two σ₂ terms
      have hσb : σ₂ b ≤ σ₂ R := hσm hbR
      have hA1 : c₂ ≤ A := by rw [hAdef]; exact le_max_left _ _
      have hA2 : c₃' ≤ A := by rw [hAdef]; exact le_max_right _ _
      have hstep1 : c₂ * (a/b) ^ ((n:ℝ))
            * (∫ x in Metric.ball x₀ b, (ε + ‖g x‖ ^ 2) ^ (p/2))
          + c₃' * σ₂ b * (∫ x in Metric.ball x₀ b, (ε + ‖g x‖ ^ 2) ^ (p/2))
          ≤ A * ((a/b) ^ ((n:ℝ)) + σ₂ R)
            * (∫ x in Metric.ball x₀ b, (ε + ‖g x‖ ^ 2) ^ (p/2)) := by
        have e : A * ((a/b) ^ ((n:ℝ)) + σ₂ R)
            * (∫ x in Metric.ball x₀ b, (ε + ‖g x‖ ^ 2) ^ (p/2))
            = A * (a/b) ^ ((n:ℝ)) * (∫ x in Metric.ball x₀ b, (ε + ‖g x‖ ^ 2) ^ (p/2))
              + A * σ₂ R * (∫ x in Metric.ball x₀ b, (ε + ‖g x‖ ^ 2) ^ (p/2)) := by ring
        rw [e]
        have t1 : c₂ * (a/b) ^ ((n:ℝ)) ≤ A * (a/b) ^ ((n:ℝ)) :=
          mul_le_mul_of_nonneg_right hA1 hr0
        have t2 : c₃' * σ₂ b ≤ A * σ₂ R :=
          mul_le_mul hA2 hσb (hσnn b) (le_trans hc₃'.le hA2)
        exact add_le_add (mul_le_mul_of_nonneg_right t1 hIr0)
          (mul_le_mul_of_nonneg_right t2 hIr0)
      have hstep2 : c₃' * σ₂ b * (ωn * b ^ ((n:ℝ))) ≤ c₄ * b ^ ((n:ℝ) - τ) := by
        have hsplit : b ^ ((n:ℝ)) = b ^ τ * b ^ ((n:ℝ) - τ) := by
          rw [← Real.rpow_add hb]; congr 1; ring
        have hbτ : b ^ τ ≤ R₂ ^ τ := Real.rpow_le_rpow hb.le hbR₂ hτ.le
        have hσ2 : σ₂ b ≤ σ₂ R₂ := hσm hbR₂
        have hnτ0 : (0:ℝ) ≤ b ^ ((n:ℝ) - τ) := Real.rpow_nonneg hb.le _
        have hcc : c₃' * σ₂ b * (ωn * b ^ τ) ≤ c₄ := by
          rw [hc₄def]
          have u1 : c₃' * σ₂ b ≤ c₃' * (1 + σ₂ R₂) := by
            refine mul_le_mul_of_nonneg_left ?_ hc₃'.le
            linarith
          have u2 : ωn * b ^ τ ≤ ωn * (1 + R₂ ^ τ) := by
            refine mul_le_mul_of_nonneg_left ?_ hω.le
            linarith [Real.rpow_nonneg hb.le τ]
          calc c₃' * σ₂ b * (ωn * b ^ τ)
              ≤ c₃' * (1 + σ₂ R₂) * (ωn * (1 + R₂ ^ τ)) :=
                mul_le_mul u1 u2 (mul_nonneg hω.le (Real.rpow_nonneg hb.le _))
                  (mul_nonneg hc₃'.le (by linarith [hσnn R₂]))
            _ = c₃' * (1 + σ₂ R₂) * ωn * (1 + R₂ ^ τ) := by ring
        calc c₃' * σ₂ b * (ωn * b ^ ((n:ℝ)))
            = (c₃' * σ₂ b * (ωn * b ^ τ)) * b ^ ((n:ℝ) - τ) := by rw [hsplit]; ring
          _ ≤ c₄ * b ^ ((n:ℝ) - τ) := mul_le_mul_of_nonneg_right hcc hnτ0
      linarith
    -- the iteration lemma
    have hδR : σ₂ R < δ₀ := lt_of_le_of_lt (hσm hRR₂) hR₂σ
    have key := hiter (σ₂ R) c₄ R F (hσnn R) hδR hc₄ hR hF0 hFmono hFrec ρ R hρ hρR le_rfl
    rwa [hFval ρ hρ hρR, hFval R hR le_rfl] at key
  -- Step 6: part (i) on Ω''
  have hΩ''Ω : Ω'' ⊆ Ω := subset_trans subset_closure hcl
  have habs : ∀ y : EuclideanSpace ℝ (Fin n), |‖g y‖| ^ p = ‖g y‖ ^ p :=
    fun y => by rw [abs_of_nonneg (norm_nonneg _)]
  have hRsmin : Rs ≤ min R₁ R₂ := le_min hRsR₁ hRsR₂
  have hgnn : ∀ y : EuclideanSpace ℝ (Fin n), (0:ℝ) ≤ ‖g y‖ ^ p :=
    fun y => Real.rpow_nonneg (norm_nonneg _) _
  refine ⟨(hgΩ.mono_measure (Measure.restrict_mono hΩ''Ω le_rfl)).norm, ?_⟩
  intro x₁ hx₁ ρ hρ _hρdiam
  have hballRs : Metric.closedBall x₁ Rs ⊆ Ω := by
    intro z hz
    by_contra hzΩ
    have h1 := hsep x₁ hx₁ z hzΩ
    rw [Metric.mem_closedBall] at hz
    rw [dist_comm] at h1
    linarith
  have hρnτ : (0:ℝ) ≤ ρ ^ ((n:ℝ) - τ) := Real.rpow_nonneg hρ.le _
  have hmeasset : MeasurableSet (Ω'' ∩ Metric.ball x₁ ρ) :=
    hΩ''.measurableSet.inter measurableSet_ball
  rcases le_or_gt ρ Rs with hcase | hcase
  · -- small radii
    have hsub2 : Metric.ball x₁ ρ ⊆ Ω :=
      subset_trans (Metric.ball_subset_ball hcase)
        (subset_trans Metric.ball_subset_closedBall hballRs)
    have hIball : IntegrableOn (fun y => ‖g y‖ ^ p) (Metric.ball x₁ ρ) volume :=
      hgpΩ.mono_set hsub2
    have hA : (∫ y in Ω'' ∩ Metric.ball x₁ ρ, |‖g y‖| ^ p)
        ≤ ∫ y in Metric.ball x₁ ρ, ‖g y‖ ^ p := by
      rw [setIntegral_congr_fun hmeasset (fun y _ => habs y)]
      exact setIntegral_mono_set hIball (Filter.Eventually.of_forall hgnn)
        (Filter.Eventually.of_forall fun y hy => hy.2)
    have hB : (∫ y in Metric.ball x₁ ρ, ‖g y‖ ^ p)
        ≤ ∫ y in Metric.ball x₁ ρ, (ε + ‖g y‖ ^ 2) ^ (p/2) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall hgnn)
        (hintb ε hε0 hε1 x₁ ρ g (hgball x₁ ρ hsub2))
        (Filter.Eventually.of_forall fun y => ?_)
      show ‖g y‖ ^ p ≤ (ε + ‖g y‖ ^ 2) ^ (p/2)
      rw [← hsq (‖g y‖) (norm_nonneg _)]
      exact Real.rpow_le_rpow (sq_nonneg _) (by linarith) hp2.le
    have hD := h414 x₁ hx₁ Rs ρ hRs hRsmin hballRs hρ hcase
    have hE := hFbd x₁ Rs hRs hballRs
    have hdivr : (ρ / Rs) ^ ((n:ℝ) - τ) = Rs ^ (-((n:ℝ) - τ)) * ρ ^ ((n:ℝ) - τ) := by
      rw [Real.div_rpow hρ.le hRs.le, Real.rpow_neg hRs.le]
      ring
    have hCr : (0:ℝ) ≤ C * (ρ / Rs) ^ ((n:ℝ) - τ) :=
      mul_nonneg hC.le (Real.rpow_nonneg (div_nonneg hρ.le hRs.le) _)
    have hF : (∫ y in Metric.ball x₁ ρ, (ε + ‖g y‖ ^ 2) ^ (p/2)) ≤ A₁ * ρ ^ ((n:ℝ) - τ) := by
      refine le_trans hD ?_
      calc C * (ρ / Rs) ^ ((n:ℝ) - τ)
            * ((∫ x in Metric.ball x₁ Rs, (ε + ‖g x‖ ^ 2) ^ (p/2)) + c₄ * Rs ^ ((n:ℝ) - τ))
          ≤ C * (ρ / Rs) ^ ((n:ℝ) - τ)
            * (2 ^ (p/2) * (ωn * Rs ^ ((n:ℝ)) + W ^ p) + c₄ * Rs ^ ((n:ℝ) - τ)) :=
            mul_le_mul_of_nonneg_left (by linarith) hCr
        _ = A₁ * ρ ^ ((n:ℝ) - τ) := by rw [hA₁def, hdivr]; ring
    have hN : A₁ ≤ N₁ ^ p := by rw [hN₁pow]; exact le_max_left _ _
    calc (∫ y in Ω'' ∩ Metric.ball x₁ ρ, |‖g y‖| ^ p)
        ≤ A₁ * ρ ^ ((n:ℝ) - τ) := le_trans hA (le_trans hB hF)
      _ ≤ N₁ ^ p * ρ ^ ((n:ℝ) - τ) := mul_le_mul_of_nonneg_right hN hρnτ
  · -- large radii
    have hA : (∫ y in Ω'' ∩ Metric.ball x₁ ρ, |‖g y‖| ^ p) ≤ ∫ y in Ω, ‖g y‖ ^ p := by
      rw [setIntegral_congr_fun hmeasset (fun y _ => habs y)]
      exact setIntegral_mono_set hgpΩ (Filter.Eventually.of_forall hgnn)
        (Filter.Eventually.of_forall fun y hy => hΩ''Ω hy.1)
    have hRsρ : Rs ^ ((n:ℝ) - τ) ≤ ρ ^ ((n:ℝ) - τ) :=
      Real.rpow_le_rpow hRs.le hcase.le hnτ.le
    have hRsp : (0:ℝ) < Rs ^ ((n:ℝ) - τ) := Real.rpow_pos_of_pos hRs _
    have hρp : (0:ℝ) < ρ ^ ((n:ℝ) - τ) := Real.rpow_pos_of_pos hρ _
    have hinv : W ^ p ≤ W ^ p * Rs ^ (-((n:ℝ) - τ)) * ρ ^ ((n:ℝ) - τ) := by
      have h1 : (1:ℝ) ≤ ρ ^ ((n:ℝ) - τ) / Rs ^ ((n:ℝ) - τ) := (one_le_div hRsp).2 hRsρ
      calc W ^ p = W ^ p * 1 := (mul_one _).symm
        _ ≤ W ^ p * (ρ ^ ((n:ℝ) - τ) / Rs ^ ((n:ℝ) - τ)) :=
            mul_le_mul_of_nonneg_left h1 hWp
        _ = W ^ p * Rs ^ (-((n:ℝ) - τ)) * ρ ^ ((n:ℝ) - τ) := by
            rw [Real.rpow_neg hRs.le, div_eq_mul_inv]; ring
    have hN : W ^ p * Rs ^ (-((n:ℝ) - τ)) ≤ N₁ ^ p := by rw [hN₁pow]; exact le_max_right _ _
    calc (∫ y in Ω'' ∩ Metric.ball x₁ ρ, |‖g y‖| ^ p)
        ≤ ∫ y in Ω, ‖g y‖ ^ p := hA
      _ ≤ W ^ p := hgW
      _ ≤ W ^ p * Rs ^ (-((n:ℝ) - τ)) * ρ ^ ((n:ℝ) - τ) := hinv
      _ ≤ N₁ ^ p * ρ ^ ((n:ℝ) - τ) := mul_le_mul_of_nonneg_right hN hρnτ
