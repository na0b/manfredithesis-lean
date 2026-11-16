import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.SobolevExponentTwoBall
import ManfrediThesis.WeakGradientSmoothMul
import ManfrediThesis.MoserReverseHolderStep
import ManfrediThesis.MoserExponentIteration
open MeasureTheory
set_option maxHeartbeats 800000

/-- Moser's local boundedness estimate.  If every power `v ^ θ` with `θ > 1`
lies in `W^{1,2}_loc(B_R)` and satisfies a Caccioppoli inequality with one
constant `Q` serving all `θ`, then `v` is bounded on `B_{R/2}` by the `L²` mean
of `v` on `B_R`, with a constant depending only on `n` and `Q`. -/
theorem MoserLocalBoundedness :
    ∀ (n : ℕ) (Q : ℝ), 2 ≤ n → 0 < Q → CitedSobolevPoincareBall n →
      ∃ C : ℝ, 0 < C ∧
        ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
          (v : EuclideanSpace ℝ (Fin n) → ℝ)
          (gv : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 < R → Measurable v → (∀ x, 0 ≤ v x) →
          IntegrableOn (fun y => v y ^ 2) (Metric.ball x₀ R) →
          (∀ θ : ℝ, 1 < θ →
            MemW1pLocOn n 2 (Metric.ball x₀ R) (fun x => v x ^ θ) (gv θ)) →
          (∀ θ : ℝ, 1 < θ → ∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
            ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
            tsupport ζ ⊆ Metric.ball x₀ R →
            (∫ x in Metric.ball x₀ R, ‖gv θ x‖ ^ 2 * ζ x ^ 2)
              ≤ Q * ∫ x in Metric.ball x₀ R, (v x ^ θ) ^ 2
                  * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) →
          ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))),
            v x ≤ C * (R ^ (-(n : ℝ))
              * ∫ y in Metric.ball x₀ R, v y ^ 2) ^ (1 / 2 : ℝ) := by
  intro n Q hn hQ hSPB
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hntriv : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, hnpos⟩ (1 : ℝ), ?_⟩⟩
    intro hc
    have h := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w ⟨0, hnpos⟩) hc
    simp at h
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℝ,
      ω = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := ⟨_, rfl⟩
  have hω : 0 < ω := by
    rw [hωdef]
    refine ENNReal.toReal_pos ?_ measure_ball_lt_top.ne
    exact (Metric.isOpen_ball.measure_pos volume
      ⟨0, Metric.mem_ball_self one_pos⟩).ne'
  have hballvol : ∀ (y : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 ≤ r →
      (volume (Metric.ball y r)).toReal = ω * r ^ n := by
    intro y r hr
    rw [Measure.addHaar_ball volume y hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity),
      show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n by simp, ← hωdef]
    ring
  -- the Sobolev exponent and constant, both functions of `n` alone
  obtain ⟨χ, CS, hχ1, hCS0, hSob⟩ := SobolevExponentTwoBall n hn hSPB
  have hχ0 : (0 : ℝ) < χ - 1 := by linarith
  -- Step 1a: the one-dimensional cut-off profile, an absolute construction
  obtain ⟨ψ, Λ, hψsm, hΛ1, hψ0, hψle1, hψlo, hψhi, hψd⟩ :
      ∃ (ψ : ℝ → ℝ) (Λ : ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ ∧ 1 ≤ Λ ∧
        (∀ t, 0 ≤ ψ t) ∧ (∀ t, ψ t ≤ 1) ∧
        (∀ t, t ≤ 3 / 8 → ψ t = 1) ∧ (∀ t, 5 / 8 ≤ t → ψ t = 0) ∧
        (∀ t, |deriv ψ t| ≤ Λ) := by
    obtain ⟨ψ0, hψ0sm, hψ0nn, hψ0le, hψ0lo, hψ0hi⟩ :
        ∃ ψ0 : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ0 ∧ (∀ t, 0 ≤ ψ0 t) ∧ (∀ t, ψ0 t ≤ 1) ∧
          (∀ t, t ≤ 3 / 8 → ψ0 t = 1) ∧ (∀ t, 5 / 8 ≤ t → ψ0 t = 0) := by
      refine ⟨fun t => Real.smoothTransition (5 / 2 - 4 * t), ?_,
        fun t => Real.smoothTransition.nonneg _,
        fun t => Real.smoothTransition.le_one _,
        fun t ht => Real.smoothTransition.one_of_one_le (by linarith),
        fun t ht => Real.smoothTransition.zero_of_nonpos (by linarith)⟩
      exact Real.smoothTransition.contDiff.comp
        (contDiff_const.sub (contDiff_const.mul contDiff_id))
    obtain ⟨Λ, hΛ1, hΛb⟩ : ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ t, |deriv ψ0 t| ≤ Λ := by
      have hdc : Continuous (deriv ψ0) := hψ0sm.continuous_deriv (by simp)
      have habs : Continuous (fun t => |deriv ψ0 t|) := hdc.abs
      have hcpt : IsCompact (Set.Icc (3 / 8 : ℝ) (5 / 8 : ℝ)) := isCompact_Icc
      obtain ⟨t₀, ht₀mem, ht₀max⟩ := hcpt.exists_isMaxOn
        (Set.nonempty_Icc.2 (by norm_num)) habs.continuousOn
      refine ⟨max |deriv ψ0 t₀| 1, le_max_right _ _, fun t => ?_⟩
      by_cases ht : t ∈ Set.Icc (3 / 8 : ℝ) (5 / 8 : ℝ)
      · exact le_trans (ht₀max ht) (le_max_left _ _)
      · have hzero : deriv ψ0 t = 0 := by
          rcases not_and_or.1 (fun h => ht ⟨h.1, h.2⟩) with hlt | hgt
          · have hlt' : t < 3 / 8 := by
              rcases lt_or_ge t (3 / 8 : ℝ) with h | h
              · exact h
              · exact absurd h hlt
            have hmem : {s : ℝ | s < 3 / 8} ∈ nhds t :=
              (isOpen_lt continuous_id continuous_const).mem_nhds hlt'
            have hc : ψ0 =ᶠ[nhds t] fun _ => (1 : ℝ) := by
              filter_upwards [hmem] with s hs
              exact hψ0lo s (le_of_lt hs)
            rw [hc.deriv_eq, deriv_const]
          · have hgt' : 5 / 8 < t := by
              rcases lt_or_ge (5 / 8 : ℝ) t with h | h
              · exact h
              · exact absurd h hgt
            have hmem : {s : ℝ | 5 / 8 < s} ∈ nhds t :=
              (isOpen_lt continuous_const continuous_id).mem_nhds hgt'
            have hc : ψ0 =ᶠ[nhds t] fun _ => (0 : ℝ) := by
              filter_upwards [hmem] with s hs
              exact hψ0hi s (le_of_lt hs)
            rw [hc.deriv_eq, deriv_const]
        rw [hzero, abs_zero]
        have h1 : (0 : ℝ) ≤ 1 := by norm_num
        exact le_trans h1 (le_max_right _ _)
    exact ⟨ψ0, Λ, hψ0sm, hΛ1, hψ0nn, hψ0le, hψ0lo, hψ0hi, hΛb⟩
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  -- the constants of the proof
  obtain ⟨σ₁, hσ₁def⟩ : ∃ s : ℝ, s = χ / (2 * (χ - 1)) := ⟨_, rfl⟩
  obtain ⟨σ₂, hσ₂def⟩ : ∃ s : ℝ, s = χ / (2 * (χ - 1) ^ 2) := ⟨_, rfl⟩
  have hσ₁0 : 0 < σ₁ := by
    rw [hσ₁def]; exact div_pos (by linarith) (by linarith)
  have hσ₂0 : 0 < σ₂ := by
    rw [hσ₂def]
    refine div_pos (by linarith) ?_
    positivity
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ,
      D = max (CS * (2 * Q + 2) ^ (1 / 2 : ℝ) * (2 * Λ)) 1 := ⟨_, rfl⟩
  have hD1 : 1 ≤ D := by rw [hDdef]; exact le_max_right _ _
  have hD0 : 0 < D := by linarith
  have hDge : CS * (2 * Q + 2) ^ (1 / 2 : ℝ) * (2 * Λ) ≤ D := by
    rw [hDdef]; exact le_max_left _ _
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = (2 * D) ^ σ₁ * 2 ^ σ₂ := ⟨_, rfl⟩
  have hE0 : 0 < E := by
    rw [hEdef]
    exact mul_pos (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨E ^ 2 * 2 ^ (10 * σ₁) * ω ^ (-(1 / 2) : ℝ), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 2 ^ (10 * σ₁) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0 : ℝ) < ω ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hω _
    positivity
  intro x₀ R v gv hR hvmeas hvnn hv2 hloc hcacc
  have hmRv : (volume (Metric.ball x₀ R)).toReal = ω * R ^ n := hballvol x₀ R hR.le
  have hmR0 : 0 < (volume (Metric.ball x₀ R)).toReal := by
    rw [hmRv]; exact mul_pos hω (pow_pos hR n)
  -- the normalised means and the a.e. bound predicate
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ → ℝ → ℝ, Y = fun s ρ =>
      ((volume (Metric.ball x₀ R)).toReal⁻¹
        * ∫ x in Metric.ball x₀ ρ, v x ^ (2 * s)) ^ (1 / (2 * s)) := ⟨_, rfl⟩
  obtain ⟨Bnd, hBnddef⟩ : ∃ Bnd : ℝ → ℝ → Prop, Bnd = fun ρ A =>
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ)), v x ≤ A := ⟨_, rfl⟩
  have hYeq : ∀ s ρ : ℝ, Y s ρ = ((volume (Metric.ball x₀ R)).toReal⁻¹
      * ∫ x in Metric.ball x₀ ρ, v x ^ (2 * s)) ^ (1 / (2 * s)) := by
    intro s ρ
    rw [hYdef]
  have hvrpow : ∀ x, v x ^ (2 * (1 : ℝ)) = v x ^ 2 := by
    intro x
    rw [show (2 : ℝ) * 1 = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have hY1R : Y 1 R
      = ((volume (Metric.ball x₀ R)).toReal⁻¹
        * ∫ x in Metric.ball x₀ R, v x ^ 2) ^ (1 / 2 : ℝ) := by
    rw [hYeq 1 R, integral_congr_ae (Filter.Eventually.of_forall hvrpow)]
    norm_num
  have hI0 : (0 : ℝ) ≤ ∫ x in Metric.ball x₀ R, v x ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hcb : ∀ ρ : ℝ, 0 < ρ → ρ < R →
      IsCompact (Metric.closedBall x₀ ρ) ∧ Metric.closedBall x₀ ρ ⊆ Metric.ball x₀ R := by
    intro ρ hρ hρR
    refine ⟨isCompact_closedBall _ _, fun y hy => ?_⟩
    exact Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hy) hρR)
  have hintpow : ∀ (s ρ : ℝ), 1 < s → 0 < ρ → ρ < R →
      IntegrableOn (fun x => v x ^ (2 * s)) (Metric.ball x₀ ρ) volume := by
    as_aux_lemma =>
    intro s ρ hρ0 hρ hρR
    obtain ⟨hcpt, hsub⟩ := hcb ρ hρ hρR
    obtain ⟨-, hmem⟩ := hloc s hρ0
    obtain ⟨hf, -⟩ := hmem (Metric.closedBall x₀ ρ) hcpt hsub
    have h1 : Integrable (fun x => ‖v x ^ s‖ ^ (ENNReal.ofReal 2).toReal)
        (volume.restrict (Metric.closedBall x₀ ρ)) :=
      hf.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp] at h1
    have h2 : IntegrableOn (fun x => v x ^ (2 * s)) (Metric.closedBall x₀ ρ) volume := by
      refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
      show ‖v x ^ s‖ ^ (2 : ℝ) = v x ^ (2 * s)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hvnn x) _),
        ← Real.rpow_mul (hvnn x)]
      congr 1
      ring
    exact h2.mono_set Metric.ball_subset_closedBall
  have hYnn : ∀ s ρ : ℝ, 0 < s → 0 ≤ Y s ρ := by
    intro s ρ hs
    rw [hYeq s ρ]
    refine Real.rpow_nonneg (mul_nonneg (by positivity) ?_) _
    exact integral_nonneg fun x => Real.rpow_nonneg (hvnn x) _
  -- Step 0: the degenerate case
  by_cases hdeg : (∫ x in Metric.ball x₀ R, v x ^ 2) = 0
  · have hae : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), v x = 0 := by
      have hint : IntegrableOn (fun x => v x ^ 2) (Metric.ball x₀ R) volume := hv2
      have h := (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun x => sq_nonneg (v x)) hint).1 hdeg
      filter_upwards [h] with x hx
      have h2 : v x ^ 2 = 0 := hx
      have := hvnn x
      nlinarith [sq_nonneg (v x)]
    have hsub : volume.restrict (Metric.ball x₀ (R / 2))
        ≤ volume.restrict (Metric.ball x₀ R) :=
      Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl
    filter_upwards [Filter.Eventually.filter_mono (ae_mono hsub) hae] with x hx
    rw [hx, hdeg]
    have h1 : (0 : ℝ) ≤ E ^ 2 * 2 ^ (10 * σ₁) * ω ^ (-(1 / 2) : ℝ) := by
      have h2 : (0 : ℝ) < 2 ^ (10 * σ₁) := Real.rpow_pos_of_pos (by norm_num) _
      have h3 : (0 : ℝ) < ω ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hω _
      positivity
    rw [mul_zero, Real.zero_rpow (by norm_num)]
    linarith
  have hIpos : 0 < ∫ x in Metric.ball x₀ R, v x ^ 2 :=
    lt_of_le_of_ne hI0 (Ne.symm hdeg)
  have hY2pos : 0 < Y 1 R := by
    rw [hY1R]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hnormsq : ∀ w : EuclideanSpace ℝ (Fin n), ∑ i : Fin n, (w i) ^ 2 = ‖w‖ ^ 2 := by
    intro w
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact (Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])).symm
  have hnpow2 : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ^ (2 : ℝ) = ‖w‖ ^ 2 := by
    intro w
    rw [← Real.rpow_natCast ‖w‖ 2]
    norm_num
  have hsetint : ∀ (S T : Set (EuclideanSpace ℝ (Fin n)))
      (F : EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ x, x ∉ S → F x = 0) → S ⊆ T → (∫ x in T, F x) = ∫ x in S, F x := by
    intro S T F hF hST
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hF x (fun hc => hx (hST hc))),
      setIntegral_eq_integral_of_forall_compl_eq_zero hF]
  -- (1): the reverse-Hölder step, from Steps 1b, 2 and 3.  This is
  -- `MoserReverseHolderStep`, whose docstring records the route (the radial
  -- cut-off between `B_{r'}` and `B_r`, the Sobolev inequality at `v^θ ζ` and
  -- the Caccioppoli hypothesis absorbing the gradient term).
  have h1 := MoserReverseHolderStep n Q hn hQ χ CS hχ1 hCS0 hSob ψ Λ hψsm hΛ1
    hψ0 hψle1 hψlo hψhi hψd D hD0 hDge x₀ R v gv hR hvmeas hvnn hloc hcacc hmR0
    Y hYeq hcb hintpow hnormsq hnpow2 hsetint
  -- monotonicity of the normalised means in the radius
  have hYmono : ∀ (s a b : ℝ), 1 < s → 0 < a → a ≤ b → b < R → Y s a ≤ Y s b := by
    intro s a b hs ha hab hbR
    have hs0 : (0 : ℝ) < s := lt_trans one_pos hs
    have hexp : (0 : ℝ) ≤ 1 / (2 * s) := by
      refine div_nonneg zero_le_one ?_
      linarith
    rw [hYeq s a, hYeq s b]
    refine Real.rpow_le_rpow (mul_nonneg (by positivity)
      (integral_nonneg fun x => Real.rpow_nonneg (hvnn x) _)) ?_ hexp
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set (hintpow s b hs (by linarith) hbR)
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hvnn x) _)
      (LE.le.eventuallyLE (Metric.ball_subset_ball hab))
  -- (2): the exponent iteration, together with the Chebyshev half of the
  -- `L^q`-mean characterisation of the essential supremum that it consumes.
  -- This is `MoserExponentIteration`, whose docstring records the route (the
  -- `θ_j = 2χ^j` / `r_j = ρ' + 2^{-j}(ρ-ρ')` chain, the two geometric exponent
  -- sums `σ₁` and `σ₂`, and the Chebyshev passage from the uniform bound on
  -- `Y (θ_m) ρ'` to the pointwise bound).
  have h2 := MoserExponentIteration n χ σ₁ σ₂ D E hχ1 hσ₁def hσ₂def hEdef hE0
    hD1 x₀ R v hR hvmeas hvnn hmR0 Y Bnd hYeq hBnddef hintpow hYnn h1 hYmono
  -- Step 5: from the `L⁴` mean back to the `L²` mean
  have h5 : ∀ (ρ A : ℝ), 0 ≤ A → 0 < ρ → ρ ≤ 3 * R / 4 → Bnd ρ A →
      Y 2 ρ ≤ A ^ (1 / 2 : ℝ) * (Y 1 R) ^ (1 / 2 : ℝ) := by
    as_aux_lemma =>
    intro ρ A hA hρ hρR hB
    have hρlt : ρ < R := by linarith
    have hsub : Metric.ball x₀ ρ ⊆ Metric.ball x₀ R :=
      Metric.ball_subset_ball (by linarith)
    have hi4 : IntegrableOn (fun x => v x ^ (2 * (2 : ℝ))) (Metric.ball x₀ ρ) volume :=
      hintpow 2 ρ (by norm_num) hρ hρlt
    have hi2 : IntegrableOn (fun x => v x ^ 2) (Metric.ball x₀ ρ) volume :=
      hv2.mono_set hsub
    have hptw : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ)),
        v x ^ (2 * (2 : ℝ)) ≤ A ^ 2 * v x ^ 2 := by
      have hB' : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ)), v x ≤ A := by
        rw [hBnddef] at hB; exact hB
      filter_upwards [hB'] with x hx
      have h1 : v x ^ (2 * (2 : ℝ)) = v x ^ 2 * v x ^ 2 := by
        rw [show (2 : ℝ) * 2 = ((4 : ℕ) : ℝ) from by norm_num,
          Real.rpow_natCast]
        ring
      rw [h1]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact pow_le_pow_left₀ (hvnn x) hx 2
    have hkey : (∫ x in Metric.ball x₀ ρ, v x ^ (2 * (2 : ℝ)))
        ≤ A ^ 2 * ∫ x in Metric.ball x₀ R, v x ^ 2 := by
      refine (integral_mono_ae hi4 (hi2.const_mul _) hptw).trans ?_
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg A)
      exact setIntegral_mono_set hv2
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (LE.le.eventuallyLE hsub)
    -- now the rpow algebra
    have hmRi : (0 : ℝ) < (volume (Metric.ball x₀ R)).toReal⁻¹ := by positivity
    have hstep : (volume (Metric.ball x₀ R)).toReal⁻¹
          * ∫ x in Metric.ball x₀ ρ, v x ^ (2 * (2 : ℝ))
        ≤ (A ^ (1 / 2 : ℝ) * (Y 1 R) ^ (1 / 2 : ℝ)) ^ (2 * (2 : ℝ)) := by
      have e1 : (A ^ (1 / 2 : ℝ)) ^ (2 * (2 : ℝ)) = A ^ 2 := by
        rw [← Real.rpow_mul hA,
          show (1 / 2 : ℝ) * (2 * 2) = ((2 : ℕ) : ℝ) from by norm_num,
          Real.rpow_natCast]
      have e2 : ((Y 1 R) ^ (1 / 2 : ℝ)) ^ (2 * (2 : ℝ))
          = (volume (Metric.ball x₀ R)).toReal⁻¹
            * ∫ x in Metric.ball x₀ R, v x ^ 2 := by
        rw [← Real.rpow_mul hY2pos.le, hY1R, ← Real.rpow_mul (by positivity :
          (0 : ℝ) ≤ (volume (Metric.ball x₀ R)).toReal⁻¹
            * ∫ x in Metric.ball x₀ R, v x ^ 2),
          show (1 / 2 : ℝ) * ((1 / 2) * (2 * 2)) = 1 from by norm_num, Real.rpow_one]
      have h1 : (A ^ (1 / 2 : ℝ) * (Y 1 R) ^ (1 / 2 : ℝ)) ^ (2 * (2 : ℝ))
          = A ^ 2 * ((volume (Metric.ball x₀ R)).toReal⁻¹
            * ∫ x in Metric.ball x₀ R, v x ^ 2) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hA _) (Real.rpow_nonneg hY2pos.le _),
          e1, e2]
      rw [h1, ← mul_assoc, mul_comm (A ^ 2), mul_assoc]
      exact mul_le_mul_of_nonneg_left hkey hmRi.le
    rw [hYeq 2 ρ]
    have hQ0 : (0 : ℝ) ≤ A ^ (1 / 2 : ℝ) * (Y 1 R) ^ (1 / 2 : ℝ) :=
      mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hY2pos.le _)
    refine (Real.rpow_le_rpow (mul_nonneg hmRi.le
      (integral_nonneg fun x => Real.rpow_nonneg (hvnn x) _)) hstep
      (by norm_num)).trans_eq ?_
    rw [← Real.rpow_mul hQ0]
    norm_num
  -- monotonicity of the a.e.-bound predicate, in the bound and in the radius
  have hBmono : ∀ (ρ A A' : ℝ), A ≤ A' → Bnd ρ A → Bnd ρ A' := by
    intro ρ A A' hAA hB
    rw [hBnddef] at hB ⊢
    filter_upwards [hB] with x hx
    linarith
  have hBshrink : ∀ (ρ ρ' A : ℝ), ρ' ≤ ρ → Bnd ρ A → Bnd ρ' A := by
    intro ρ ρ' A hρ hB
    rw [hBnddef] at hB ⊢
    exact Filter.Eventually.filter_mono
      (ae_mono (Measure.restrict_mono (Metric.ball_subset_ball hρ) le_rfl)) hB
  -- (3): a finite bound on `B_{5R/8}`
  obtain ⟨M, hM1, hMB⟩ : ∃ M : ℝ, 1 ≤ M ∧ Bnd (5 * R / 8) M :=
    ⟨max (E * (R / (3 * R / 4 - 5 * R / 8)) ^ σ₁ * Y 2 (3 * R / 4)) 1,
      le_max_right _ _,
      hBmono _ _ _ (le_max_left _ _)
        (h2 (5 * R / 8) (3 * R / 4) (by linarith) (by linarith) le_rfl)⟩
  have hM0 : 0 < M := by linarith
  -- the increasing radii
  obtain ⟨rr, hrrdef⟩ : ∃ rr : ℕ → ℝ,
      rr = fun i => R / 2 + (1 - (1 / 2 : ℝ) ^ i) * (R / 8) := ⟨_, rfl⟩
  have hrreq : ∀ i : ℕ, rr i = R / 2 + (1 - (1 / 2 : ℝ) ^ i) * (R / 8) := by
    intro i; rw [hrrdef]
  have hrr0 : rr 0 = R / 2 := by rw [hrreq 0]; norm_num
  have hrrlo : ∀ i, R / 2 ≤ rr i := by
    intro i
    rw [hrreq i]
    have h1 : (1 / 2 : ℝ) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hrrhi : ∀ i, rr i ≤ 5 * R / 8 := by
    intro i
    rw [hrreq i]
    have h1 : (0 : ℝ) < (1 / 2 : ℝ) ^ i := by positivity
    nlinarith
  have hrrdiff : ∀ i : ℕ, rr (i + 1) - rr i = R / 2 ^ (i + 4) := by
    intro i
    rw [hrreq (i + 1), hrreq i, show i + 4 = (i + 1) + 3 from by omega, pow_add,
      pow_succ, one_div, inv_pow]
    field_simp
    ring
  have hrrlt : ∀ i : ℕ, rr i < rr (i + 1) := by
    intro i
    have h := hrrdiff i
    have h1 : (0 : ℝ) < R / 2 ^ (i + 4) := by positivity
    linarith
  have hrrR : ∀ i : ℕ, R / (rr (i + 1) - rr i) = 2 ^ (i + 4) := by
    intro i
    rw [hrrdiff i]
    have hRne : R ≠ 0 := ne_of_gt hR
    field_simp
  -- the logarithmic increments
  obtain ⟨κf, hκdef⟩ : ∃ κf : ℕ → ℝ, κf = fun i : ℕ =>
      Real.log E + ((i : ℝ) + 4) * σ₁ * Real.log 2
        + (1 / 2) * Real.log (Y 1 R) := ⟨_, rfl⟩
  have hκeq : ∀ i : ℕ, κf i = Real.log E + ((i : ℝ) + 4) * σ₁ * Real.log 2
      + (1 / 2) * Real.log (Y 1 R) := by
    intro i; rw [hκdef]
  -- (5): one step of the radius iteration
  have hstep6 : ∀ (i : ℕ) (A : ℝ), 0 < A → Bnd (rr (i + 1)) A →
      Bnd (rr i) (Real.exp (κf i + (1 / 2) * Real.log A)) := by
    intro i A hA hB
    have h1 := h2 (rr i) (rr (i + 1)) (hrrlo i) (hrrlt i)
      (le_trans (hrrhi (i + 1)) (by linarith))
    have h3 : Y 2 (rr (i + 1)) ≤ A ^ (1 / 2 : ℝ) * (Y 1 R) ^ (1 / 2 : ℝ) :=
      h5 (rr (i + 1)) A hA.le (by linarith [hrrlo (i + 1)])
        (by linarith [hrrhi (i + 1)]) hB
    refine hBmono _ _ _ ?_ h1
    rw [hrrR i]
    have hc0 : (0 : ℝ) ≤ E * ((2 : ℝ) ^ (i + 4)) ^ σ₁ := by positivity
    have hpw : ((2 : ℝ) ^ (i + 4)) ^ σ₁ = (2 : ℝ) ^ (((i : ℝ) + 4) * σ₁) := by
      rw [← Real.rpow_natCast (2 : ℝ) (i + 4), ← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    calc E * ((2 : ℝ) ^ (i + 4)) ^ σ₁ * Y 2 (rr (i + 1))
        ≤ E * ((2 : ℝ) ^ (i + 4)) ^ σ₁ * (A ^ (1 / 2 : ℝ) * (Y 1 R) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 hc0
      _ = Real.exp (κf i + (1 / 2) * Real.log A) := by
          rw [hpw, ← Real.exp_log hE0, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2),
            Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hY2pos,
            ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          rw [hκeq i]
          ring
  -- the induction producing the m-step bound
  have hind : ∀ (m j : ℕ), Bnd (rr j)
      (Real.exp (∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i * κf (j + i)
        + (1 / 2 : ℝ) ^ m * Real.log M)) := by
    intro m
    induction m with
    | zero =>
        intro j
        simp only [Finset.range_zero, Finset.sum_empty, pow_zero, zero_add, one_mul]
        rw [Real.exp_log hM0]
        exact hBshrink _ _ _ (hrrhi j) hMB
    | succ m ih =>
        intro j
        have hA0 : (0 : ℝ) < Real.exp (∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i * κf (j + 1 + i)
          + (1 / 2 : ℝ) ^ m * Real.log M) := Real.exp_pos _
        have h := hstep6 j _ hA0 (ih (j + 1))
        refine hBmono _ _ _ ?_ h
        rw [Real.log_exp]
        refine le_of_eq ?_
        congr 1
        rw [Finset.sum_range_succ' (fun i => (1 / 2 : ℝ) ^ i * κf (j + i)) m, mul_add,
          Finset.mul_sum]
        have he : ∀ i : ℕ, (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ i * κf (j + 1 + i))
            = (1 / 2 : ℝ) ^ (i + 1) * κf (j + (i + 1)) := by
          intro i
          rw [show j + (i + 1) = j + 1 + i from by omega, pow_succ]
          ring
        rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range m) => he i)]
        simp only [pow_zero, one_mul, add_zero, pow_succ]
        ring
  -- the two series
  have hgeo : HasSum (fun i : ℕ => (1 / 2 : ℝ) ^ i) 2 := by
    have h := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    norm_num at h
    exact h
  have hgeo2 : HasSum (fun i : ℕ => (i : ℝ) * (1 / 2 : ℝ) ^ i) 2 := by
    have h := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  have hsumκ : HasSum (fun i : ℕ => (1 / 2 : ℝ) ^ i * κf i)
      (2 * Real.log E + 10 * σ₁ * Real.log 2 + Real.log (Y 1 R)) := by
    have hrw : (fun i : ℕ => (1 / 2 : ℝ) ^ i * κf i)
        = fun i : ℕ =>
          (Real.log E + 4 * σ₁ * Real.log 2 + (1 / 2) * Real.log (Y 1 R))
            * (1 / 2 : ℝ) ^ i
          + (σ₁ * Real.log 2) * ((i : ℝ) * (1 / 2 : ℝ) ^ i) := by
      funext i
      rw [hκeq i]
      ring
    rw [hrw]
    have heq : (Real.log E + 4 * σ₁ * Real.log 2 + (1 / 2) * Real.log (Y 1 R)) * 2
        + (σ₁ * Real.log 2) * 2
        = 2 * Real.log E + 10 * σ₁ * Real.log 2 + Real.log (Y 1 R) := by ring
    rw [← heq]
    exact (hgeo.mul_left _).add (hgeo2.mul_left _)
  have hlim : Filter.Tendsto (fun m : ℕ =>
        Real.exp (∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i * κf i
          + (1 / 2 : ℝ) ^ m * Real.log M)) Filter.atTop
      (nhds (Real.exp (2 * Real.log E + 10 * σ₁ * Real.log 2 + Real.log (Y 1 R)))) := by
    refine (Real.continuous_exp.tendsto _).comp ?_
    have h1 := hsumκ.tendsto_sum_nat
    have h2 : Filter.Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m * Real.log M)
        Filter.atTop (nhds 0) := by
      have h3 := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      simpa using h3.mul_const (Real.log M)
    have h4 := h1.add h2
    rwa [add_zero] at h4
  -- the final bound
  have hfinal : Bnd (R / 2)
      (Real.exp (2 * Real.log E + 10 * σ₁ * Real.log 2 + Real.log (Y 1 R))) := by
    rw [hBnddef]
    have hall : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))), ∀ m : ℕ,
        v x ≤ Real.exp (∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i * κf i
          + (1 / 2 : ℝ) ^ m * Real.log M) := by
      refine ae_all_iff.2 ?_
      intro m
      have h := hind m 0
      rw [hrr0, hBnddef] at h
      simpa using h
    filter_upwards [hall] with x hx
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun m => hx m)
  -- the constant, and the scale-invariant form of the right-hand side
  have hexpid : Real.exp (2 * Real.log E + 10 * σ₁ * Real.log 2 + Real.log (Y 1 R))
      = E ^ 2 * 2 ^ (10 * σ₁) * Y 1 R := by
    have e1 : E ^ 2 = Real.exp (2 * Real.log E) := by
      rw [show (2 : ℝ) * Real.log E = Real.log E + Real.log E from by ring,
        Real.exp_add, Real.exp_log hE0, pow_two]
    have e2 : (2 : ℝ) ^ (10 * σ₁) = Real.exp (10 * σ₁ * Real.log 2) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have e3 : Y 1 R = Real.exp (Real.log (Y 1 R)) := (Real.exp_log hY2pos).symm
    rw [e1, e2]
    conv_rhs => rw [e3]
    rw [← Real.exp_add, ← Real.exp_add]
  have hRHS : (R ^ (-(n : ℝ)) * ∫ y in Metric.ball x₀ R, v y ^ 2) ^ (1 / 2 : ℝ)
      = ω ^ (1 / 2 : ℝ) * Y 1 R := by
    have hid : R ^ (-(n : ℝ)) * ∫ y in Metric.ball x₀ R, v y ^ 2
        = ω * ((volume (Metric.ball x₀ R)).toReal⁻¹
          * ∫ y in Metric.ball x₀ R, v y ^ 2) := by
      rw [hmRv, Real.rpow_neg hR.le, ← Real.rpow_natCast R n]
      have hRn : (R : ℝ) ^ ((n : ℕ) : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hR _)
      have hωne : ω ≠ 0 := ne_of_gt hω
      field_simp
    have hnn2 : (0 : ℝ) ≤ (volume (Metric.ball x₀ R)).toReal⁻¹
        * ∫ y in Metric.ball x₀ R, v y ^ 2 :=
      mul_nonneg (inv_nonneg.2 hmR0.le) hI0
    rw [hid, Real.mul_rpow hω.le hnn2, hY1R]
  rw [hBnddef] at hfinal
  rw [hexpid] at hfinal
  filter_upwards [hfinal] with x hx
  rw [hRHS]
  refine hx.trans (le_of_eq ?_)
  have hωid : ω ^ (-(1 / 2) : ℝ) * ω ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hω]
    norm_num
  calc E ^ 2 * 2 ^ (10 * σ₁) * Y 1 R
      = E ^ 2 * 2 ^ (10 * σ₁) * (ω ^ (-(1 / 2) : ℝ) * ω ^ (1 / 2 : ℝ)) * Y 1 R := by
        rw [hωid]; ring
    _ = E ^ 2 * 2 ^ (10 * σ₁) * ω ^ (-(1 / 2) : ℝ) * (ω ^ (1 / 2 : ℝ) * Y 1 R) := by ring
