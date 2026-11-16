import ManfrediThesis.Preamble
set_option maxHeartbeats 800000
open MeasureTheory

/-- The difference-quotient bound: if an increment of `Fh` along a coordinate
segment is the integral of `Gh` along that segment, and if the shifted
`L^q`-distance `∫_K‖Gh(·+se_k) - Gh‖^q` is at most `c` for every shift with
`|s| ≤ |h|`, then the difference quotient of `Fh` is within `c` of `Gh` in the
same `L^q` sense:
`∫_K‖(Fh(·+he_k) - Fh)/h - Gh‖^q ≤ c`.

Conventions, restated here because a helper inherits none of its parent's.
`e_k` is the `k`-th standard basis vector, so `x + se_k` translates `x` by `s`
in the `k`-th coordinate direction; `∫⁻` is the extended-nonnegative integral
and `‖·‖ₑ` the extended norm, so every quantity below lives in `[0,∞]` and no
finiteness is assumed anywhere; `q` is a real exponent with `q ≥ 1`, and `c`
enters through `ENNReal.ofReal c`.  `Gh'` is a globally measurable
representative of `Gh`, carried as a hypothesis in the two forms the Fubini
step needs --- along the shear `(x,s) ↦ x + se_k` and in the first coordinate
alone --- because the product-measure argument needs a genuinely measurable
integrand.  The three functions `Fh`, `Gh`, `Gh'` are otherwise arbitrary:
nothing here knows that they come from a weakly differentiable function, which
is why the statement is free-standing.

The route fuses Steps 4 and 5 of the parent's argument.  Step 4 is pointwise in
`x`: where the representation holds, subtracting `Gh(x)` and dividing by `h`
gives
`(Fh(x+he_k) - Fh(x))/h - Gh(x) = h^{-1}∫_0^h(Gh(x+se_k) - Gh(x))ds`,
so by the norm inequality for the interval integral together with Jensen's
inequality for the probability measure `|h|^{-1}ds` on the segment --- in the
form `‖|h|^{-1}∫_0^hF‖^q ≤ |h|^{-1}∫_{I_h}‖F‖^q`, valid because `q ≥ 1` makes
`t ↦ t^q` convex ---
`‖(Fh(x+he_k) - Fh(x))/h - Gh(x)‖ₑ^q
  ≤ |h|^{-1}∫_{I_h}‖Gh(x+se_k) - Gh(x)‖ₑ^q ds`
for almost every `x ∈ K`.  Step 5 integrates that over `K` and exchanges the
two integrations by Tonelli --- legitimate because the integrand is
extended-nonnegative and, through the `Gh'` hypotheses, jointly measurable on
the product --- which turns the right-hand side into
`|h|^{-1}∫_{I_h}(∫_K‖Gh(·+se_k) - Gh‖ₑ^q)ds`.  The inner integral is at most
`c` for every `s` in the segment, since `|s| ≤ |h|` there, and
`|h|^{-1}·|I_h| = 1`, so the whole expression is at most `c`. -/
theorem DifferenceQuotientLqBound :
    ∀ (n : ℕ) (q : ℝ), 1 ≤ q →
      ∀ (K : Set (EuclideanSpace ℝ (Fin n))) (k : Fin n),
      ∀ (Fh Gh Gh' : EuclideanSpace ℝ (Fin n) → ℝ), Measurable Gh' →
      ((fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      Gh (p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)))
      =ᵐ[volume.prod volume]
      (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      Gh' (p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)))) →
      ((fun p : EuclideanSpace ℝ (Fin n) × ℝ => Gh p.1)
      =ᵐ[volume.prod volume] (fun p : EuclideanSpace ℝ (Fin n) × ℝ => Gh' p.1)) →
      ∀ h c : ℝ, 0 < |h| →
      (∀ᵐ x ∂(volume.restrict K),
      IntervalIntegrable (fun s => Gh (x + s • EuclideanSpace.single k (1 : ℝ)))
      volume 0 h ∧
      Fh (x + h • EuclideanSpace.single k (1 : ℝ)) - Fh x
      = ∫ s in (0 : ℝ)..h, Gh (x + s • EuclideanSpace.single k (1 : ℝ))) →
      (∀ s : ℝ, |s| ≤ |h| →
      (∫⁻ x in K, ‖Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x‖ₑ ^ q)
      ≤ ENNReal.ofReal c) →
      (∫⁻ x in K,
      ‖(Fh (x + h • EuclideanSpace.single k (1 : ℝ)) - Fh x) / h - Gh x‖ₑ ^ q)
      ≤ ENNReal.ofReal c := by
  intro n q hq K k
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  intro Fh Gh Gh' hGh'm hprod1 hprod2 h c hh0 hrep hcs
  have hne : h ≠ 0 := by rwa [← abs_pos]
  set a : ENNReal := ENNReal.ofReal |h| with hadef
  have ha0 : a ≠ 0 := by
    rw [hadef, Ne, ENNReal.ofReal_eq_zero, not_le]; exact hh0
  have hatop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hIm : MeasurableSet (Set.uIoc 0 h) := measurableSet_Ioc
  have hIvol : volume (Set.uIoc 0 h) = a := by
    rw [Set.uIoc, Real.volume_Ioc, hadef]
    congr 1
    rcases le_or_gt 0 h with hh | hh
    · rw [min_eq_left hh, max_eq_right hh, abs_of_nonneg hh]; ring
    · rw [min_eq_right hh.le, max_eq_left hh.le, abs_of_neg hh]; ring
  have huIoc : ∀ s : ℝ, s ∈ Set.uIoc 0 h → |s| ≤ |h| := by
    intro s hs
    rw [Set.uIoc] at hs
    rcases le_or_gt 0 h with hh | hh
    · rw [min_eq_left hh, max_eq_right hh] at hs
      rw [abs_of_nonneg hh, abs_of_pos hs.1]; exact hs.2
    · rw [min_eq_right hh.le, max_eq_left hh.le] at hs
      rw [abs_of_neg hh, abs_of_nonpos hs.2]; linarith [hs.1]
  have harith : (a⁻¹) ^ q * a ^ (q - 1) = a⁻¹ := by
    rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg, ← ENNReal.rpow_add _ _ ha0 hatop,
      show -q + (q - 1) = -1 by ring, ENNReal.rpow_neg_one]
  -- Jensen / Hölder on the interval `I_h`
  have hjensen : ∀ (μ : Measure ℝ) (F : ℝ → ENNReal), AEMeasurable F μ →
      (∫⁻ s, F s ∂μ) ^ q ≤ (μ Set.univ) ^ (q - 1) * ∫⁻ s, F s ^ q ∂μ := by
    intro μ F hF
    rcases eq_or_lt_of_le hq with h1 | h1
    · rw [← h1]; simp
    · have hconj : q.HolderConjugate q.conjExponent := Real.HolderConjugate.conjExponent h1
      have hsum : 1 / q + 1 / q.conjExponent = 1 := by
        simpa [one_div] using hconj.inv_add_inv_eq_one
      have hkey : 1 / q.conjExponent * q = q - 1 := by
        have h2 : 1 / q.conjExponent = 1 - 1 / q := by linarith
        rw [h2]; field_simp
      have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj hF
        (aemeasurable_const (b := (1 : ENNReal)))
      simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at hH
      calc (∫⁻ s, F s ∂μ) ^ q
          ≤ ((∫⁻ s, F s ^ q ∂μ) ^ (1 / q) * (μ Set.univ) ^ (1 / q.conjExponent)) ^ q :=
            ENNReal.rpow_le_rpow hH hq0.le
        _ = (∫⁻ s, F s ^ q ∂μ) * (μ Set.univ) ^ (q - 1) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul,
              ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one, hkey]
        _ = (μ Set.univ) ^ (q - 1) * ∫⁻ s, F s ^ q ∂μ := mul_comm _ _
  -- Step 4: the pointwise estimate (8)
  have hptw : ∀ᵐ x ∂(volume.restrict K),
      ‖(Fh (x + h • EuclideanSpace.single k (1 : ℝ)) - Fh x) / h - Gh x‖ₑ ^ q
        ≤ a⁻¹ * ∫⁻ s in Set.uIoc 0 h,
            ‖Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x‖ₑ ^ q := by
    filter_upwards [hrep] with x hx
    obtain ⟨hII, hrepx⟩ := hx
    have hIIc : IntervalIntegrable (fun _ : ℝ => Gh x) volume 0 h := intervalIntegrable_const
    have hid : (Fh (x + h • EuclideanSpace.single k (1 : ℝ)) - Fh x) / h - Gh x
        = (∫ s in (0 : ℝ)..h,
            (Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x)) / h := by
      rw [intervalIntegral.integral_sub hII hIIc, intervalIntegral.integral_const,
        ← hrepx, sub_zero, smul_eq_mul]
      field_simp
    have hIIsub : IntervalIntegrable
        (fun s => Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x) volume 0 h :=
      hII.sub hIIc
    have hbd1 : ‖∫ s in (0 : ℝ)..h,
          (Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x)‖ₑ
        ≤ ∫⁻ s in Set.uIoc 0 h,
            ‖Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x‖ₑ := by
      rcases le_or_gt 0 h with hh | hh
      · rw [intervalIntegral.integral_of_le hh, Set.uIoc_of_le hh]
        exact enorm_integral_le_lintegral_enorm _
      · rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hh.le,
          Set.uIoc_of_ge hh.le, enorm_neg]
        exact enorm_integral_le_lintegral_enorm _
    have hmeas1 : AEMeasurable
        (fun s => ‖Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x‖ₑ)
        (volume.restrict (Set.uIoc 0 h)) :=
      ((intervalIntegrable_iff.1 hIIsub).1).enorm
    rw [hid]
    have hnorm : ‖(∫ s in (0 : ℝ)..h,
          (Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x)) / h‖ₑ
        = a⁻¹ * ‖∫ s in (0 : ℝ)..h,
            (Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x)‖ₑ := by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_div, ENNReal.ofReal_div_of_pos hh0,
        ← ofReal_norm, Real.norm_eq_abs, hadef, div_eq_mul_inv, mul_comm]
    rw [hnorm, ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
    calc (a⁻¹) ^ q * ‖∫ s in (0 : ℝ)..h,
            (Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x)‖ₑ ^ q
        ≤ (a⁻¹) ^ q * (∫⁻ s in Set.uIoc 0 h,
            ‖Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x‖ₑ) ^ q := by gcongr
      _ ≤ (a⁻¹) ^ q * (a ^ (q - 1) * ∫⁻ s in Set.uIoc 0 h,
            ‖Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x‖ₑ ^ q) := by
          have hj := hjensen (volume.restrict (Set.uIoc 0 h)) _ hmeas1
          rw [Measure.restrict_apply_univ, hIvol] at hj
          gcongr
      _ = a⁻¹ * ∫⁻ s in Set.uIoc 0 h,
            ‖Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x‖ₑ ^ q := by
          rw [← mul_assoc, harith]
  -- Step 5: Tonelli
  have hTm : Measurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)) :=
    measurable_fst.add (measurable_snd.smul_const _)
  have hmp : AEMeasurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      ‖Gh (p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)) - Gh p.1‖ₑ ^ q)
      (volume.prod volume) := by
    have hm' : Measurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
        ‖Gh' (p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)) - Gh' p.1‖ₑ ^ q) :=
      (((hGh'm.comp hTm).sub (hGh'm.comp measurable_fst)).enorm).pow_const q
    refine hm'.aemeasurable.congr ?_
    filter_upwards [hprod1, hprod2] with p h1 h2
    rw [← h1, ← h2]
  have hmpres : AEMeasurable (Function.uncurry
      (fun (x : EuclideanSpace ℝ (Fin n)) (s : ℝ) =>
        ‖Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x‖ₑ ^ q))
      ((volume.restrict K).prod (volume.restrict (Set.uIoc 0 h))) := by
    rw [Measure.prod_restrict]
    exact hmp.restrict
  calc (∫⁻ x in K,
        ‖(Fh (x + h • EuclideanSpace.single k (1 : ℝ)) - Fh x) / h - Gh x‖ₑ ^ q)
      ≤ ∫⁻ x in K, a⁻¹ * ∫⁻ s in Set.uIoc 0 h,
          ‖Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x‖ₑ ^ q :=
        lintegral_mono_ae hptw
    _ = a⁻¹ * ∫⁻ x in K, ∫⁻ s in Set.uIoc 0 h,
          ‖Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x‖ₑ ^ q :=
        lintegral_const_mul' _ _ (by simp [ENNReal.inv_eq_top, ha0])
    _ = a⁻¹ * ∫⁻ s in Set.uIoc 0 h, ∫⁻ x in K,
          ‖Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x‖ₑ ^ q := by
        rw [lintegral_lintegral_swap hmpres]
    _ ≤ a⁻¹ * ∫⁻ _ in Set.uIoc 0 h, ENNReal.ofReal c := by
        have hle : (∫⁻ s in Set.uIoc 0 h, ∫⁻ x in K,
              ‖Gh (x + s • EuclideanSpace.single k (1 : ℝ)) - Gh x‖ₑ ^ q)
            ≤ ∫⁻ _ in Set.uIoc 0 h, ENNReal.ofReal c := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hIm] with s hs
          exact hcs s (huIoc s hs)
        gcongr
    _ = ENNReal.ofReal c := by
        rw [lintegral_const, Measure.restrict_apply_univ, hIvol, mul_comm _ a,
          ← mul_assoc, ENNReal.inv_mul_cancel ha0 hatop, one_mul]
