import ManfrediThesis.Preamble
import ManfrediThesis.EuclideanCoordinateOperatorBounds
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.SegmentWeightIntegrable
open MeasureTheory

/-- (Q2) integrated along the segment from `0` to `h`.  `EllipticStructureQ12`
constrains only `fderiv (A x z)`; this is the resulting bound on `A` itself.
The constant depends on `p` as well as `n`: for `1 < p < 2` the weight is
singular at the origin and the factor `1/(p-1)` from `∫₀¹ t^(p-2) dt` is
unavoidable. -/
theorem StructureGrowthBound :
    ∀ (n : ℕ) (p : ℝ), 2 ≤ n → 1 < p →
      ∃ c : ℝ, 0 < c ∧
        ∀ (ε γ₀ γ₁ : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
          (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
            EuclideanSpace ℝ (Fin n)),
          0 ≤ ε → 0 < γ₀ → 0 < γ₁ →
          EllipticStructureQ12 n p ε γ₀ γ₁ Ω A →
          ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ∈ Ω →
            ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)),
              ‖A x z h‖ ≤ ‖A x z 0‖
                + c * γ₁ * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖ := by
  intro n p hn hp
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := lt_of_lt_of_le (by norm_num) hn
    exact_mod_cast this
  have hc1pos : (0 : ℝ) < max 1 (1 / (p - 1)) := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨(n : ℝ) * n * max 1 (1 / (p - 1)), by positivity, ?_⟩
  intro ε γ₀ γ₁ Ω A hε hγ₀ hγ₁ hQ
  obtain ⟨hl1, hcoord, hopbnd⟩ := EuclideanCoordinateOperatorBounds n
  -- the set on which the differentiability clause and (Q2) live
  have hD : IsOpen {g : EuclideanSpace ℝ (Fin n) | ε + ‖g‖ ^ 2 ≠ 0} := by
    have hc : Continuous fun g : EuclideanSpace ℝ (Fin n) => ε + ‖g‖ ^ 2 :=
      continuous_const.add (continuous_norm.pow 2)
    exact isOpen_ne.preimage hc
  have hnormsq : ∀ (t : ℝ) (w : EuclideanSpace ℝ (Fin n)),
      ‖t • w‖ ^ 2 = t ^ 2 * ‖w‖ ^ 2 := by
    intro t w
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  -- the endpoint `t = 0` of the segment is a null set
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    refine (MeasureTheory.ae_iff).2 ?_
    have hset : {t : ℝ | ¬ (t ≠ 0)} = ({(0:ℝ)} : Set ℝ) := by ext t; simp
    rw [hset]
    simp
  -- (**): the segment integral of the weight
  have hstar : ∀ hv : EuclideanSpace ℝ (Fin n), hv ≠ 0 →
      (∫ t in (0:ℝ)..1, (ε + ‖t • hv‖ ^ 2) ^ (p / 2 - 1))
        ≤ max 1 (1 / (p - 1)) * (ε + ‖hv‖ ^ 2) ^ (p / 2 - 1) := by
    intro hv hvne
    have hH : 0 < ‖hv‖ := norm_pos_iff.2 hvne
    have hW : 0 < ε + ‖hv‖ ^ 2 := by positivity
    have hint : IntervalIntegrable
        (fun t : ℝ => (ε + ‖t • hv‖ ^ 2) ^ (p / 2 - 1)) volume 0 1 := by
      have h0 := SegmentWeightIntegrable n p hp ε hv 0 hε
      simpa using h0
    rcases le_or_gt 0 (p / 2 - 1) with hs | hs
    · have hptw : ∀ t ∈ Set.Icc (0:ℝ) 1,
          (ε + ‖t • hv‖ ^ 2) ^ (p / 2 - 1) ≤ (ε + ‖hv‖ ^ 2) ^ (p / 2 - 1) := by
        intro t ht
        refine Real.rpow_le_rpow (by positivity) ?_ hs
        rw [hnormsq t hv]
        have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
        nlinarith [sq_nonneg ‖hv‖]
      calc (∫ t in (0:ℝ)..1, (ε + ‖t • hv‖ ^ 2) ^ (p / 2 - 1))
          ≤ ∫ _t in (0:ℝ)..1, (ε + ‖hv‖ ^ 2) ^ (p / 2 - 1) :=
            intervalIntegral.integral_mono_on (by norm_num) hint
              intervalIntegrable_const hptw
        _ = (ε + ‖hv‖ ^ 2) ^ (p / 2 - 1) := by simp
        _ ≤ max 1 (1 / (p - 1)) * (ε + ‖hv‖ ^ 2) ^ (p / 2 - 1) := by
            nlinarith [le_max_left (1:ℝ) (1 / (p - 1)), Real.rpow_nonneg hW.le (p / 2 - 1)]
    · have hr : (-1 : ℝ) < p - 2 := by linarith
      have hrint : IntervalIntegrable (fun t : ℝ => t ^ (p - 2)) volume 0 1 :=
        intervalIntegral.intervalIntegrable_rpow' hr
      have hptw : (fun t : ℝ => (ε + ‖t • hv‖ ^ 2) ^ (p / 2 - 1))
          ≤ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
          fun t : ℝ => (ε + ‖hv‖ ^ 2) ^ (p / 2 - 1) * t ^ (p - 2) := by
        filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Icc]
          with t ht0 htI
        have ht1 : 0 < t := lt_of_le_of_ne htI.1 (Ne.symm ht0)
        have hsq : t ^ 2 ≤ 1 := by nlinarith [htI.1, htI.2]
        have hlb : t ^ 2 * (ε + ‖hv‖ ^ 2) ≤ ε + ‖t • hv‖ ^ 2 := by
          rw [hnormsq t hv]
          nlinarith [hε, hsq]
        have hpos : 0 < t ^ 2 * (ε + ‖hv‖ ^ 2) := by positivity
        calc (ε + ‖t • hv‖ ^ 2) ^ (p / 2 - 1)
            ≤ (t ^ 2 * (ε + ‖hv‖ ^ 2)) ^ (p / 2 - 1) :=
              Real.rpow_le_rpow_of_nonpos hpos hlb hs.le
          _ = (ε + ‖hv‖ ^ 2) ^ (p / 2 - 1) * t ^ (p - 2) := by
              rw [Real.mul_rpow (by positivity) hW.le,
                show (t ^ 2 : ℝ) = t ^ (2:ℝ) by
                  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast],
                ← Real.rpow_mul ht1.le,
                show (2:ℝ) * (p / 2 - 1) = p - 2 by ring]
              ring
      calc (∫ t in (0:ℝ)..1, (ε + ‖t • hv‖ ^ 2) ^ (p / 2 - 1))
          ≤ ∫ t in (0:ℝ)..1, (ε + ‖hv‖ ^ 2) ^ (p / 2 - 1) * t ^ (p - 2) :=
            intervalIntegral.integral_mono_ae_restrict (by norm_num) hint
              (hrint.const_mul _) hptw
        _ = (ε + ‖hv‖ ^ 2) ^ (p / 2 - 1) * (1 / (p - 1)) := by
            rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr),
              show p - 2 + 1 = p - 1 by ring, Real.one_rpow,
              Real.zero_rpow (by linarith)]
            ring
        _ ≤ max 1 (1 / (p - 1)) * (ε + ‖hv‖ ^ 2) ^ (p / 2 - 1) := by
            rw [mul_comm]
            nlinarith [le_max_right (1:ℝ) (1 / (p - 1)),
              Real.rpow_nonneg hW.le (p / 2 - 1)]
  -- Choice of `x`: (Q2) is an a.e.-`x` statement and so is the conclusion
  filter_upwards [hQ.Q2] with x hQ2x
  intro hxΩ z h
  -- Step 0: the case `h = 0`
  by_cases hh : h = 0
  · subst hh
    simp
  -- from here on `h ≠ 0`
  have hH : 0 < ‖h‖ := norm_pos_iff.2 hh
  have hW : 0 < ε + ‖h‖ ^ 2 := by positivity
  have hmem : ∀ t : ℝ, 0 < t →
      t • h ∈ {g : EuclideanSpace ℝ (Fin n) | ε + ‖g‖ ^ 2 ≠ 0} := by
    intro t ht
    have hpos : 0 < ε + ‖t • h‖ ^ 2 := by
      rw [hnormsq t h]
      have : 0 < t ^ 2 * ‖h‖ ^ 2 := by positivity
      linarith
    exact ne_of_gt hpos
  -- the pointwise derivative bound along the segment
  have hΨ'bnd : ∀ t : ℝ, 0 < t →
      ‖fderiv ℝ (A x z) (t • h) h‖
        ≤ ((n : ℝ) * n) * (γ₁ * (ε + ‖t • h‖ ^ 2) ^ (p / 2 - 1)) * ‖h‖ := by
    intro t ht
    refine hopbnd _ _ (by positivity) (fun i j => ?_) h
    exact hQ2x hxΩ z (t • h) i j (hmem t ht)
  -- interval integrability of the derivative
  have hweightint : IntervalIntegrable
      (fun t : ℝ => (ε + ‖t • h‖ ^ 2) ^ (p / 2 - 1)) volume 0 1 := by
    have h0 := SegmentWeightIntegrable n p hp ε h 0 hε
    simpa using h0
  have hΨint : IntervalIntegrable
      (fun t : ℝ => fderiv ℝ (A x z) (t • h) h) volume 0 1 := by
    refine IntervalIntegrable.mono_fun'
      (g := fun t : ℝ => ((n : ℝ) * n) * (γ₁ * ‖h‖)
        * (ε + ‖t • h‖ ^ 2) ^ (p / 2 - 1))
      (hweightint.const_mul _) ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      exact ((measurable_fderiv (𝕜 := ℝ) (f := A x z)).comp
        (measurable_id.smul_const h)).apply_continuousLinearMap h
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      have ht0 : 0 < t := by
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
        exact ht.1
      calc ‖fderiv ℝ (A x z) (t • h) h‖
          ≤ ((n : ℝ) * n) * (γ₁ * (ε + ‖t • h‖ ^ 2) ^ (p / 2 - 1)) * ‖h‖ :=
            hΨ'bnd t ht0
        _ = ((n : ℝ) * n) * (γ₁ * ‖h‖) * (ε + ‖t • h‖ ^ 2) ^ (p / 2 - 1) := by ring
  -- Step 2: the fundamental theorem of calculus along `[0, h]`
  have hFTC : (∫ t in (0:ℝ)..1, fderiv ℝ (A x z) (t • h) h)
      = A x z h - A x z 0 := by
    have hderiv : ∀ t ∈ Set.Ioo (0:ℝ) 1,
        HasDerivAt (fun s : ℝ => A x z (s • h)) (fderiv ℝ (A x z) (t • h) h) t := by
      intro t ht
      have hdA : DifferentiableAt ℝ (A x z) (t • h) :=
        ((hQ.hdiff x hxΩ z).differentiableOn (by norm_num)).differentiableAt
          (hD.mem_nhds (hmem t ht.1))
      have h1 : HasDerivAt (fun s : ℝ => s • h) h t := by
        simpa using (hasDerivAt_id t).smul_const h
      exact hdA.hasFDerivAt.comp_hasDerivAt t h1
    have hcont : ContinuousOn (fun s : ℝ => A x z (s • h)) (Set.Icc (0:ℝ) 1) :=
      ((hQ.hcont x hxΩ z).comp (continuous_id.smul continuous_const)).continuousOn
    have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (by norm_num : (0:ℝ) ≤ 1) hcont hderiv hΨint
    simpa using h2
  -- Step 3: estimating the integral
  have hest : ‖A x z h - A x z 0‖
      ≤ ((n : ℝ) * n * max 1 (1 / (p - 1))) * γ₁ * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖ := by
    have hbound : (∫ t in (0:ℝ)..1, ‖fderiv ℝ (A x z) (t • h) h‖)
        ≤ ∫ t in (0:ℝ)..1, ((n : ℝ) * n) * (γ₁ * ‖h‖)
          * (ε + ‖t • h‖ ^ 2) ^ (p / 2 - 1) := by
      refine intervalIntegral.integral_mono_ae_restrict (by norm_num) hΨint.norm
        (hweightint.const_mul _) ?_
      filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Icc]
        with t ht0 ht
      have h0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      calc ‖fderiv ℝ (A x z) (t • h) h‖
          ≤ ((n : ℝ) * n) * (γ₁ * (ε + ‖t • h‖ ^ 2) ^ (p / 2 - 1)) * ‖h‖ :=
            hΨ'bnd t h0
        _ = ((n : ℝ) * n) * (γ₁ * ‖h‖) * (ε + ‖t • h‖ ^ 2) ^ (p / 2 - 1) := by ring
    calc ‖A x z h - A x z 0‖ = ‖∫ t in (0:ℝ)..1, fderiv ℝ (A x z) (t • h) h‖ := by
          rw [hFTC]
      _ ≤ ∫ t in (0:ℝ)..1, ‖fderiv ℝ (A x z) (t • h) h‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ t in (0:ℝ)..1, ((n : ℝ) * n) * (γ₁ * ‖h‖)
            * (ε + ‖t • h‖ ^ 2) ^ (p / 2 - 1) := hbound
      _ = ((n : ℝ) * n) * (γ₁ * ‖h‖)
            * ∫ t in (0:ℝ)..1, (ε + ‖t • h‖ ^ 2) ^ (p / 2 - 1) := by
          rw [intervalIntegral.integral_const_mul]
      _ ≤ ((n : ℝ) * n) * (γ₁ * ‖h‖)
            * (max 1 (1 / (p - 1)) * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1)) := by
          refine mul_le_mul_of_nonneg_left (hstar h hh) (by positivity)
      _ = ((n : ℝ) * n * max 1 (1 / (p - 1))) * γ₁ * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1)
            * ‖h‖ := by ring
  -- Conclusion
  calc ‖A x z h‖ = ‖A x z 0 + (A x z h - A x z 0)‖ := by abel_nf
    _ ≤ ‖A x z 0‖ + ‖A x z h - A x z 0‖ := norm_add_le _ _
    _ ≤ ‖A x z 0‖ + ((n : ℝ) * n * max 1 (1 / (p - 1))) * γ₁
          * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖ := by linarith [hest]
