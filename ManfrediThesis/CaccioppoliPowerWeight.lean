import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.DifferentiatedEquationWeak
import ManfrediThesis.WeakGradientSmoothMul
import ManfrediThesis.WeakGradientVectorComp
import ManfrediThesis.PowerWeightWeakFormIdentity
import ManfrediThesis.PowerWeightCaccioppoliCore
open MeasureTheory
set_option maxHeartbeats 200000

/-- Inequality (3.3): a Caccioppoli inequality for the powers
`w^{(p+t)/4}` of `w = ε + |∇u|²`. -/
theorem CaccioppoliPowerWeight :
    ∀ (n : ℕ) (p r : ℝ), 2 ≤ n → 1 < p → 0 < r →
      ∃ c : ℝ, 0 < c ∧
        ∀ (ε γ₀ γ₁ t : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
          (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (ζ : EuclideanSpace ℝ (Fin n) → ℝ),
          0 < ε → 0 < γ₀ → γ₁ ≤ r * γ₀ → 0 < t → IsOpen Ω →
          EllipticStructureQ12 n p ε γ₀ γ₁ Ω (fun _ _ h => A h) →
          CitedRegularityEpsPos n p ε γ₀ γ₁ Ω A →
          IsWeakSolutionOn n p Ω (fun _ _ h => A h) (fun _ _ _ => 0) u g →
          (∀ i : Fin n, MemW1pLocOn n 2 Ω (fun x => g x i) (Dg i)) →
          ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
          (∫ x in Ω, ((p + t) / 4) ^ 2 * (ε + ‖g x‖ ^ 2) ^ ((p + t) / 2 - 2)
              * (∑ i, (2 * ∑ k, g x k * Dg k x i) ^ 2) * ζ x ^ 2)
            ≤ c * ∫ x in Ω, (ε + ‖g x‖ ^ 2) ^ ((p + t) / 2)
                * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 := by
  intro n p r hn hp hr
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  refine ⟨(n : ℝ) ^ 2 * p ^ 2 * r ^ 2, by positivity, ?_⟩
  intro ε γ₀ γ₁ t Ω A u g Dg ζ hε hγ₀ hγ₁r ht hΩ hQ hC1 hsol hDg hζsm hζcs hζΩ
  -- the weight `w`, the field `∇w`, and the two integrals
  obtain ⟨w, hwdef⟩ : ∃ w : EuclideanSpace ℝ (Fin n) → ℝ,
      w = fun x => ε + ‖g x‖ ^ 2 := ⟨_, rfl⟩
  have hweq : ∀ x, w x = ε + ‖g x‖ ^ 2 := fun x => by rw [hwdef]
  have hwpos : ∀ x, 0 < w x := by
    intro x
    rw [hweq x]
    have := sq_nonneg ‖g x‖
    linarith
  obtain ⟨Dw, hDwdef⟩ : ∃ Dw : EuclideanSpace ℝ (Fin n) → Fin n → ℝ,
      Dw = fun x i => 2 * ∑ k, g x k * Dg k x i := ⟨_, rfl⟩
  have hDweq : ∀ x i, Dw x i = 2 * ∑ k, g x k * Dg k x i := fun x i => by rw [hDwdef]
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ x in Ω,
      w x ^ ((p + t) / 2 - 2) * (∑ i, (Dw x i) ^ 2) * ζ x ^ 2 := ⟨_, rfl⟩
  obtain ⟨J, hJdef⟩ : ∃ J : ℝ, J = ∫ x in Ω,
      w x ^ ((p + t) / 2)
        * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := by
    rw [hIdef]
    refine integral_nonneg fun x => ?_
    have h1 : (0 : ℝ) ≤ w x ^ ((p + t) / 2 - 2) :=
      le_of_lt (Real.rpow_pos_of_pos (hwpos x) _)
    have h2 : (0 : ℝ) ≤ ∑ i, (Dw x i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have h3 : (0 : ℝ) ≤ ζ x ^ 2 := sq_nonneg _
    positivity
  have hJ0 : 0 ≤ J := by
    rw [hJdef]
    refine integral_nonneg fun x => ?_
    have h1 : (0 : ℝ) ≤ w x ^ ((p + t) / 2) :=
      le_of_lt (Real.rpow_pos_of_pos (hwpos x) _)
    have h2 : (0 : ℝ) ≤ ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    positivity
  -- the assertion is `s² I ≤ c J`
  have hLHS : (∫ x in Ω, ((p + t) / 4) ^ 2 * (ε + ‖g x‖ ^ 2) ^ ((p + t) / 2 - 2)
        * (∑ i, (2 * ∑ k, g x k * Dg k x i) ^ 2) * ζ x ^ 2)
      = ((p + t) / 4) ^ 2 * I := by
    rw [hIdef, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ((p + t) / 4) ^ 2 * (ε + ‖g x‖ ^ 2) ^ ((p + t) / 2 - 2)
          * (∑ i, (2 * ∑ k, g x k * Dg k x i) ^ 2) * ζ x ^ 2
        = ((p + t) / 4) ^ 2
          * (w x ^ ((p + t) / 2 - 2) * (∑ i, (Dw x i) ^ 2) * ζ x ^ 2)
    rw [hweq x, show (∑ i, (Dw x i) ^ 2)
        = ∑ i, (2 * ∑ k, g x k * Dg k x i) ^ 2 from
      Finset.sum_congr rfl (fun i _ => by rw [hDweq x i])]
    ring
  have hRHS : (∫ x in Ω, (ε + ‖g x‖ ^ 2) ^ ((p + t) / 2)
        * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) = J := by
    rw [hJdef]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (ε + ‖g x‖ ^ 2) ^ ((p + t) / 2)
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2
        = w x ^ ((p + t) / 2)
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2
    rw [hweq x]
  rw [hLHS, hRHS]
  -- Step 0: the degenerate case `Ω = ∅`
  rcases Set.eq_empty_or_nonempty Ω with hΩe | hΩne
  · have h1 : I = 0 := by rw [hIdef, hΩe]; simp
    have h2 : J = 0 := by rw [hJdef, hΩe]; simp
    rw [h1, h2, mul_zero, mul_zero]
  -- Step 1: `γ₀ ≤ γ₁`
  have hγ : γ₀ ≤ γ₁ := by
    obtain ⟨i0⟩ : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
    obtain ⟨e, hedef⟩ : ∃ e : EuclideanSpace ℝ (Fin n),
        e = EuclideanSpace.single i0 (1 : ℝ) := ⟨_, rfl⟩
    have hen : ‖e‖ = 1 := by rw [hedef]; simp
    have hen2 : ‖e‖ ^ 2 = 1 := by rw [hen]; norm_num
    have hguard : ε + ‖e‖ ^ 2 ≠ 0 := by rw [hen2]; positivity
    have hneb : Filter.NeBot (ae (volume.restrict Ω)) := by
      refine ae_neBot.2 ?_
      simp only [ne_eq, Measure.restrict_eq_zero]
      exact (hΩ.measure_pos volume hΩne).ne'
    obtain ⟨x, ⟨hx1, hx2⟩, hxΩ⟩ :=
      ((ae_restrict_of_ae (hQ.Q1.and hQ.Q2)).and
        (ae_restrict_mem hΩ.measurableSet)).exists
    have hQ1 := hx1 hxΩ 0 e e hguard
    have hQ2 := hx2 hxΩ 0 e i0 i0 hguard
    have hsum : (∑ i, (fderiv ℝ (fun h => A h) e e) i * e i)
        = (fderiv ℝ (fun h => A h) e e) i0 := by
      rw [hedef]
      simp
    rw [hsum, hen2, mul_one] at hQ1
    rw [← hedef, hen2] at hQ2
    have hpow : (0 : ℝ) < (ε + 1) ^ (p / 2 - 1) :=
      Real.rpow_pos_of_pos (by linarith) _
    have hle : (fderiv ℝ (fun h => A h) e e) i0 ≤ γ₁ * (ε + 1) ^ (p / 2 - 1) :=
      le_trans (le_abs_self _) hQ2
    exact le_of_mul_le_mul_right (by linarith) hpow
  -- (7): the two-sided estimate of Steps 2-7
  have h7 : γ₀ * ((1 + t) / 4) * I ≤ γ₁ * (n : ℝ) * (Real.sqrt I * Real.sqrt J) :=
    PowerWeightCaccioppoliCore n p hn hp ε γ₀ γ₁ t Ω A u g Dg ζ hε hγ₀ hγ ht hΩ
      hΩne hQ hC1 hsol hDg hζsm hζcs hζΩ w hweq hwpos Dw hDweq I hIdef J hJdef
  -- Step 8: the conclusion
  have hγ₁0 : 0 < γ₁ := lt_of_lt_of_le hγ₀ hγ
  rcases eq_or_lt_of_le hI0 with hIeq | hIpos
  · rw [← hIeq, mul_zero]
    have h1 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * p ^ 2 * r ^ 2 := by positivity
    exact mul_nonneg h1 hJ0
  · have hsI : 0 < Real.sqrt I := Real.sqrt_pos.2 hIpos
    have hII : Real.sqrt I * Real.sqrt I = I := Real.mul_self_sqrt hI0
    have hJJ : Real.sqrt J * Real.sqrt J = J := Real.mul_self_sqrt hJ0
    have hcoef : 0 < γ₀ * ((1 + t) / 4) := mul_pos hγ₀ (by linarith)
    have hstep : γ₀ * ((1 + t) / 4) * Real.sqrt I ≤ γ₁ * (n : ℝ) * Real.sqrt J := by
      refine le_of_mul_le_mul_right ?_ hsI
      calc γ₀ * ((1 + t) / 4) * Real.sqrt I * Real.sqrt I
          = γ₀ * ((1 + t) / 4) * I := by rw [mul_assoc, hII]
        _ ≤ γ₁ * (n : ℝ) * (Real.sqrt I * Real.sqrt J) := h7
        _ = γ₁ * (n : ℝ) * Real.sqrt J * Real.sqrt I := by ring
    obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = γ₁ * (n : ℝ) / (γ₀ * ((1 + t) / 4)) := ⟨_, rfl⟩
    have hK0 : 0 ≤ K := by
      rw [hKdef]
      exact le_of_lt (div_pos (mul_pos hγ₁0 hnR0) hcoef)
    have hsI2 : Real.sqrt I ≤ K * Real.sqrt J := by
      rw [hKdef, div_mul_eq_mul_div, le_div_iff₀ hcoef]
      calc Real.sqrt I * (γ₀ * ((1 + t) / 4))
          = γ₀ * ((1 + t) / 4) * Real.sqrt I := by ring
        _ ≤ γ₁ * (n : ℝ) * Real.sqrt J := hstep
    have hIle : I ≤ K ^ 2 * J := by
      rw [← hII]
      calc Real.sqrt I * Real.sqrt I
          ≤ (K * Real.sqrt J) * (K * Real.sqrt J) :=
            mul_le_mul hsI2 hsI2 (Real.sqrt_nonneg I)
              (mul_nonneg hK0 (Real.sqrt_nonneg J))
        _ = K ^ 2 * (Real.sqrt J * Real.sqrt J) := by ring
        _ = K ^ 2 * J := by rw [hJJ]
    -- the constant comparison
    have hKc : ((p + t) / 4) ^ 2 * K ^ 2 ≤ (n : ℝ) ^ 2 * p ^ 2 * r ^ 2 := by
      have hgr : γ₁ / γ₀ ≤ r := by
        rw [div_le_iff₀ hγ₀]
        linarith
      have hgr0 : 0 < γ₁ / γ₀ := div_pos hγ₁0 hγ₀
      have ht1 : (0 : ℝ) < 1 + t := by linarith
      have hpt : (p + t) / (1 + t) ≤ p := by
        rw [div_le_iff₀ ht1]
        nlinarith
      have hpt0 : 0 < (p + t) / (1 + t) := div_pos (by linarith) ht1
      have hKeq : ((p + t) / 4) * K = (n : ℝ) * (γ₁ / γ₀) * ((p + t) / (1 + t)) := by
        rw [hKdef]
        have h1 : γ₀ ≠ 0 := ne_of_gt hγ₀
        have h2 : (1 : ℝ) + t ≠ 0 := ne_of_gt ht1
        field_simp
      calc ((p + t) / 4) ^ 2 * K ^ 2 = (((p + t) / 4) * K) ^ 2 := by ring
        _ = ((n : ℝ) * (γ₁ / γ₀) * ((p + t) / (1 + t))) ^ 2 := by rw [hKeq]
        _ ≤ ((n : ℝ) * r * p) ^ 2 := by
            refine pow_le_pow_left₀
              (mul_nonneg (mul_nonneg hnR0.le hgr0.le) hpt0.le) ?_ 2
            refine mul_le_mul (mul_le_mul_of_nonneg_left hgr hnR0.le) hpt hpt0.le
              (mul_nonneg hnR0.le hr.le)
        _ = (n : ℝ) ^ 2 * p ^ 2 * r ^ 2 := by ring
    calc ((p + t) / 4) ^ 2 * I
        ≤ ((p + t) / 4) ^ 2 * (K ^ 2 * J) := by
          refine mul_le_mul_of_nonneg_left hIle ?_
          positivity
      _ = (((p + t) / 4) ^ 2 * K ^ 2) * J := by ring
      _ ≤ ((n : ℝ) ^ 2 * p ^ 2 * r ^ 2) * J := mul_le_mul_of_nonneg_right hKc hJ0
