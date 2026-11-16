import ManfrediThesis.Preamble
import ManfrediThesis.EuclideanCoordinateOperatorBounds
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.SegmentWeightIntegrable
import ManfrediThesis.MidpointGradientWeightBound
open MeasureTheory

/-- (Q1) integrated along the segment from `b` to `a`: the strict monotonicity
of `A` in its gradient slot.  `EllipticStructureQ12` constrains only
`fderiv (A x z)`, so no monotonicity of `A` itself is available until (Q1) is
integrated; the resulting weight at the endpoints is supplied by
`MidpointGradientWeightBound`. -/
theorem StructureMonotonicityBound :
    ∀ (n : ℕ) (p r : ℝ), 2 ≤ n → 1 < p → 0 < r →
      ∃ C : ℝ, 0 < C ∧
        ∀ (ε γ₀ γ₁ : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
          (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
            EuclideanSpace ℝ (Fin n)),
          0 ≤ ε → 0 < γ₀ → γ₁ ≤ r * γ₀ →
          EllipticStructureQ12 n p ε γ₀ γ₁ Ω A →
          ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ∈ Ω →
            ∀ (z : ℝ) (a b : EuclideanSpace ℝ (Fin n)),
              C * γ₀ * (ε + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2
                ≤ ∑ i, (A x z a i - A x z b i) * (a i - b i) := by
  intro n p r hn hp hr
  -- the constant comes from `MidpointGradientWeightBound`, before any other data
  obtain ⟨C, hC0, hMGW⟩ := MidpointGradientWeightBound p hp
  refine ⟨C, hC0, ?_⟩
  intro ε γ₀ γ₁ Ω A hε hγ₀ hγ hQ
  have hn1 : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  -- the coordinate projections, as continuous linear maps with their equations
  obtain ⟨Pr, hPrf, hPr⟩ : ∃ P : Fin n → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      (∀ i : Fin n, ⇑(P i) = fun w : EuclideanSpace ℝ (Fin n) => w i) ∧
      ∀ (i : Fin n) (w : EuclideanSpace ℝ (Fin n)), P i w = w i :=
    ⟨fun i => (ContinuousLinearMap.proj i).comp
      (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap, fun _ => rfl, fun _ _ => rfl⟩
  obtain ⟨hl1, hcoord, hopbnd⟩ := EuclideanCoordinateOperatorBounds n
  have hD : IsOpen {g : EuclideanSpace ℝ (Fin n) | ε + ‖g‖ ^ 2 ≠ 0} := by
    have hc : Continuous fun g : EuclideanSpace ℝ (Fin n) => ε + ‖g‖ ^ 2 :=
      continuous_const.add (continuous_norm.pow 2)
    exact isOpen_ne.preimage hc
  -- a single point of `ℝ` is a null set
  have haept : ∀ t₀ : ℝ, ∀ᵐ t ∂(volume : Measure ℝ), t ≠ t₀ := by
    intro t₀
    refine (MeasureTheory.ae_iff).2 ?_
    have hset : {t : ℝ | ¬ (t ≠ t₀)} = ({t₀} : Set ℝ) := by ext t; simp
    rw [hset]
    simp
  -- Choice of `x`: both (Q1) and (Q2) are a.e.-`x` statements, and so is the conclusion
  filter_upwards [hQ.Q1, hQ.Q2] with x hQ1x hQ2x
  intro hxΩ z a b
  -- the degenerate case `a = b`
  by_cases hab : a = b
  · subst hab
    simp
  have hξ : a - b ≠ 0 := sub_ne_zero.2 hab
  have hsubco : ∀ i : Fin n, (a - b) i = a i - b i := fun i => rfl
  -- Step 2: the segment and its derivative
  have hφalt : ∀ t : ℝ, t • a + (1 - t) • b = b + t • (a - b) := by
    intro t
    rw [sub_smul, one_smul, smul_sub]
    abel
  have hφd : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => s • a + (1 - s) • b) (a - b) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s • a) a t := by
      simpa using (hasDerivAt_id t).smul_const a
    have h3 : HasDerivAt (fun s : ℝ => 1 - s) (-1 : ℝ) t :=
      HasDerivAt.const_sub (1 : ℝ) (hasDerivAt_id' (x := t))
    have h2 : HasDerivAt (fun s : ℝ => (1 - s) • b) (-b) t := by
      have h4 := h3.smul_const b
      rw [neg_one_smul] at h4
      exact h4
    have h5 := h1.add h2
    rw [← sub_eq_add_neg] at h5
    exact h5
  have hφinj : ∀ t t' : ℝ,
      t • a + (1 - t) • b = t' • a + (1 - t') • b → t = t' := by
    intro t t' hEq
    rw [hφalt t, hφalt t'] at hEq
    have h1 : (t - t') • (a - b) = 0 := by
      rw [sub_smul]
      have := add_left_cancel hEq
      rw [this]
      abel
    rcases smul_eq_zero.1 h1 with h2 | h2
    · linarith [sub_eq_zero.1 h2]
    · exact absurd h2 hξ
  -- the at most one exceptional parameter
  obtain ⟨t₀, ht₀I, ht₀⟩ : ∃ t₀ ∈ Set.Icc (0:ℝ) 1,
      ∀ t ∈ Set.Icc (0:ℝ) 1, t ≠ t₀ → ε + ‖t • a + (1 - t) • b‖ ^ 2 ≠ 0 := by
    have hzero : ∀ t : ℝ, ε + ‖t • a + (1 - t) • b‖ ^ 2 = 0 →
        t • a + (1 - t) • b = 0 := by
      intro t hct
      have h1 : ‖t • a + (1 - t) • b‖ ^ 2 = 0 := by
        nlinarith [sq_nonneg ‖t • a + (1 - t) • b‖]
      have h2 : ‖t • a + (1 - t) • b‖ = 0 :=
        pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1
      exact norm_eq_zero.1 h2
    by_cases hex : ∃ t₁ ∈ Set.Icc (0:ℝ) 1, ε + ‖t₁ • a + (1 - t₁) • b‖ ^ 2 = 0
    · obtain ⟨t₁, ht₁I, ht₁⟩ := hex
      refine ⟨t₁, ht₁I, fun t _ hne hc => hne ?_⟩
      exact hφinj t t₁ (by rw [hzero t hc, hzero t₁ ht₁])
    · exact ⟨0, by norm_num, fun t ht _ hc => absurd ⟨t, ht, hc⟩ hex⟩
  -- the weight and its interval-integrability
  have hwint : IntervalIntegrable
      (fun t : ℝ => (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1)) volume 0 1 :=
    SegmentWeightIntegrable n p hp ε a b hε
  have hwnn : ∀ t : ℝ, 0 ≤ (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1) := by
    intro t
    exact Real.rpow_nonneg (by positivity) _
  -- Step 2 continued: `ψ` and its derivative off `t₀`
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≠ t₀ →
      HasDerivAt (fun s : ℝ => ∑ i, A x z (s • a + (1 - s) • b) i * (a i - b i))
        (∑ i, (fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)) i * (a i - b i)) t := by
    intro t htI hne
    have hmem : t • a + (1 - t) • b ∈ {g : EuclideanSpace ℝ (Fin n) | ε + ‖g‖ ^ 2 ≠ 0} :=
      ht₀ t htI hne
    have hdA : DifferentiableAt ℝ (A x z) (t • a + (1 - t) • b) :=
      ((hQ.hdiff x hxΩ z).differentiableOn (by norm_num)).differentiableAt
        (hD.mem_nhds hmem)
    have hvec : HasDerivAt (fun s : ℝ => A x z (s • a + (1 - s) • b))
        (fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)) t :=
      hdA.hasFDerivAt.comp_hasDerivAt t (hφd t)
    have hterm : ∀ i : Fin n,
        HasDerivAt (fun s : ℝ => A x z (s • a + (1 - s) • b) i * (a i - b i))
          ((fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)) i * (a i - b i)) t := by
      intro i
      have hco0 := (Pr i).hasFDerivAt.comp_hasDerivAt t hvec
      rw [hPrf i] at hco0
      have hco : HasDerivAt (fun s : ℝ => A x z (s • a + (1 - s) • b) i)
          ((fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)) i) t := hco0
      exact hco.mul_const (a i - b i)
    have hsum := HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) => hterm i)
    have heq : (∑ i : Fin n, fun s : ℝ => A x z (s • a + (1 - s) • b) i * (a i - b i))
        = fun s : ℝ => ∑ i, A x z (s • a + (1 - s) • b) i * (a i - b i) := by
      funext s
      rw [Finset.sum_apply]
    rw [heq] at hsum
    exact hsum
  have hcont : ContinuousOn
      (fun s : ℝ => ∑ i, A x z (s • a + (1 - s) • b) i * (a i - b i))
      (Set.Icc (0:ℝ) 1) := by
    refine Continuous.continuousOn ?_
    have hseg : Continuous (fun s : ℝ => s • a + (1 - s) • b) :=
      (continuous_id.smul continuous_const).add
        ((continuous_const.sub continuous_id).smul continuous_const)
    have hAc : Continuous (fun s : ℝ => A x z (s • a + (1 - s) • b)) :=
      (hQ.hcont x hxΩ z).comp hseg
    refine continuous_finsetSum _ fun i _ => ?_
    refine Continuous.mul ?_ continuous_const
    have h4 : Continuous (fun s : ℝ => Pr i (A x z (s • a + (1 - s) • b))) :=
      (Pr i).continuous.comp hAc
    simpa [hPr] using h4
  -- Step 3: `ψ'` is interval-integrable on `[0,1]`
  have hψ'bnd : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≠ t₀ →
      |∑ i, (fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)) i * (a i - b i)|
        ≤ ((n : ℝ) * n * n) * (γ₁ * ‖a - b‖ ^ 2)
          * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1) := by
    intro t htI hne
    have hmem : ε + ‖t • a + (1 - t) • b‖ ^ 2 ≠ 0 := ht₀ t htI hne
    set B := γ₁ * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1) with hBdef
    have hB0 : 0 ≤ B := by
      have hi0 : Fin n := ⟨0, hnpos⟩
      exact le_trans (abs_nonneg _) (hQ2x hxΩ z _ hi0 hi0 hmem)
    have hvb : ‖fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)‖
        ≤ ((n : ℝ) * n) * B * ‖a - b‖ :=
      hopbnd _ B hB0 (fun i j => hQ2x hxΩ z _ i j hmem) (a - b)
    calc |∑ i, (fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)) i * (a i - b i)|
        ≤ ∑ i, |(fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)) i * (a i - b i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ‖fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)‖ * ‖a - b‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          refine mul_le_mul (hcoord _ i) ?_ (abs_nonneg _) (norm_nonneg _)
          rw [← hsubco i]
          exact hcoord (a - b) i
      _ = (n : ℝ) * (‖fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)‖ * ‖a - b‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (n : ℝ) * ((((n : ℝ) * n) * B * ‖a - b‖) * ‖a - b‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hvb (norm_nonneg _)
      _ = ((n : ℝ) * n * n) * (γ₁ * ‖a - b‖ ^ 2)
            * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1) := by
          rw [hBdef]; ring
  have hψ'int : IntervalIntegrable
      (fun t : ℝ => ∑ i, (fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)) i
        * (a i - b i)) volume 0 1 := by
    refine IntervalIntegrable.mono_fun'
      (g := fun t : ℝ => ((n : ℝ) * n * n) * (γ₁ * ‖a - b‖ ^ 2)
        * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1))
      (hwint.const_mul _) ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      have h1 : Measurable (fun t : ℝ => t • a + (1 - t) • b) :=
        (measurable_id.smul_const a).add
          ((measurable_const.sub measurable_id).smul_const b)
      have h3 : Measurable (fun t : ℝ =>
          fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)) :=
        (((measurable_fderiv (𝕜 := ℝ) (f := A x z)).comp h1)).apply_continuousLinearMap (a - b)
      refine Finset.measurable_sum _ fun i _ => ?_
      refine Measurable.mul_const ?_ _
      have h4 : Measurable (fun t : ℝ =>
          Pr i (fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b))) :=
        ((Pr i).continuous.measurable).comp h3
      simpa [hPr] using h4
    · filter_upwards [ae_restrict_of_ae (haept t₀), ae_restrict_mem measurableSet_uIoc]
        with t hne ht
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      rw [Real.norm_eq_abs]
      exact hψ'bnd t ⟨ht.1.le, ht.2⟩ hne
  -- Step 4: the fundamental theorem of calculus, split at `t₀`
  have hFTC : (∫ t in (0:ℝ)..1, ∑ i,
        (fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)) i * (a i - b i))
      = ∑ i, (A x z a i - A x z b i) * (a i - b i) := by
    have hi1 : IntervalIntegrable (fun t : ℝ => ∑ i,
        (fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)) i * (a i - b i))
        volume 0 t₀ :=
      hψ'int.mono_set (by
        rw [Set.uIcc_of_le ht₀I.1, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact Set.Icc_subset_Icc le_rfl ht₀I.2)
    have hi2 : IntervalIntegrable (fun t : ℝ => ∑ i,
        (fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)) i * (a i - b i))
        volume t₀ 1 :=
      hψ'int.mono_set (by
        rw [Set.uIcc_of_le ht₀I.2, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact Set.Icc_subset_Icc ht₀I.1 le_rfl)
    have hA1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht₀I.1
      (hcont.mono (Set.Icc_subset_Icc le_rfl ht₀I.2))
      (fun t ht => hderiv t ⟨ht.1.le, le_trans ht.2.le ht₀I.2⟩ (ne_of_lt ht.2)) hi1
    have hA2 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht₀I.2
      (hcont.mono (Set.Icc_subset_Icc ht₀I.1 le_rfl))
      (fun t ht => hderiv t ⟨le_trans ht₀I.1 ht.1.le, ht.2.le⟩ (ne_of_gt ht.1)) hi2
    have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    rw [hA1, hA2] at hadd
    rw [← hadd]
    simp only [sub_self, sub_zero, zero_smul, one_smul, add_zero, zero_add]
    have hcomb : ∑ i, (A x z a i - A x z b i) * (a i - b i)
        = (∑ i, A x z a i * (a i - b i)) - ∑ i, A x z b i * (a i - b i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hcomb]
    ring
  -- Step 4 continued: integrating (Q1)
  have hQ1int : γ₀ * ‖a - b‖ ^ 2
        * ∫ t in (0:ℝ)..1, (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1)
      ≤ ∫ t in (0:ℝ)..1, ∑ i,
        (fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)) i * (a i - b i) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_ae_restrict (by norm_num)
      (hwint.const_mul _) hψ'int ?_
    filter_upwards [ae_restrict_of_ae (haept t₀), ae_restrict_mem measurableSet_Icc]
      with t hne ht
    have hmem : ε + ‖t • a + (1 - t) • b‖ ^ 2 ≠ 0 := ht₀ t ht hne
    have hq := hQ1x hxΩ z (t • a + (1 - t) • b) (a - b) hmem
    calc γ₀ * ‖a - b‖ ^ 2 * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1)
        = γ₀ * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2 := by ring
      _ ≤ ∑ i, (fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)) i * (a - b) i := hq
      _ = ∑ i, (fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)) i * (a i - b i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hsubco i]
  -- Step 5: removing the factor `1 - t`
  have hstep5 : C * (ε + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1)
      ≤ ∫ t in (0:ℝ)..1, (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1) := by
    have h1 := hMGW n ε a b hn1 hε
    have h2 : (∫ t in (0:ℝ)..1,
          (1 - t) * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1))
        ≤ ∫ t in (0:ℝ)..1, (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1) := by
      have hmul : IntervalIntegrable
          (fun t : ℝ => (1 - t) * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1))
          volume 0 1 := by
        refine IntervalIntegrable.mono_fun'
          (g := fun t : ℝ => (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1))
          hwint ?_ ?_
        · rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
          exact (Continuous.aestronglyMeasurable
            (continuous_const.sub continuous_id)).mul hwint.1.1
        · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
          rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith [ht.2] : (0:ℝ) ≤ 1 - t),
            abs_of_nonneg (hwnn t)]
          nlinarith [hwnn t, ht.1, ht.2]
      refine intervalIntegral.integral_mono_on (by norm_num) hmul hwint ?_
      intro t ht
      nlinarith [hwnn t, ht.1, ht.2]
    linarith
  -- Conclusion
  calc C * γ₀ * (ε + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2
      = γ₀ * ‖a - b‖ ^ 2 * (C * (ε + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1)) := by ring
    _ ≤ γ₀ * ‖a - b‖ ^ 2
          * ∫ t in (0:ℝ)..1, (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1) := by
        refine mul_le_mul_of_nonneg_left hstep5 (by positivity)
    _ ≤ ∫ t in (0:ℝ)..1, ∑ i,
          (fderiv ℝ (A x z) (t • a + (1 - t) • b) (a - b)) i * (a i - b i) := hQ1int
    _ = ∑ i, (A x z a i - A x z b i) * (a i - b i) := hFTC
