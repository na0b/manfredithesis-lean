import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.StructureGrowthBound
open MeasureTheory

/-- The `L^{p'}` datum that the weak-solution identity needs in order to be
tested against `W^{1,p}_0`: a field of `h` alone whose normalisation satisfies
(Q1)-(Q2) on `ℝⁿ`, composed with a gradient in `L^p` of a finite-measure set,
lies in `L^{p'}` there, `p' = p/(p-1)`.  This is the step the thesis leaves
inside its half-sentence at l. 1097-1098. -/
theorem FrozenFieldDualMemLp :
    ∀ (n : ℕ) (p ε γ₀ γ₁ : ℝ), 2 ≤ n → 1 < p → 0 ≤ ε → ε ≤ 1 → 0 < γ₀ → 0 < γ₁ →
      ∀ (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        EllipticStructureQ12 n p ε γ₀ γ₁ Set.univ (fun _ _ h => A h - A 0) →
        ∀ (S : Set (EuclideanSpace ℝ (Fin n)))
          (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          volume S ≠ ⊤ →
          MemLp gv (ENNReal.ofReal p) (volume.restrict S) →
          MemLp (fun x => A (gv x)) (ENNReal.ofReal (p / (p - 1)))
            (volume.restrict S) := by
  intro n p ε γ₀ γ₁ hn hp hε hε1 hγ₀ hγ₁ A hQ S gv hSfin hgv
  have hp0 : (0:ℝ) < p := by linarith
  have hp10 : (0:ℝ) < p - 1 := by linarith
  have hfin : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hSfin⟩
  -- `A` is continuous
  have hAtc : Continuous (fun h : EuclideanSpace ℝ (Fin n) => A h - A 0) :=
    hQ.hcont 0 (Set.mem_univ 0) 0
  have hAcont : Continuous A := by
    have h : Continuous (fun h : EuclideanSpace ℝ (Fin n) => (A h - A 0) + A 0) :=
      hAtc.add continuous_const
    simpa using h
  -- the growth bound for the normalised field, uniform in `x`
  obtain ⟨cG, hcG0, hcG⟩ := StructureGrowthBound n p hn hp
  have hneb : Filter.NeBot (ae (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    refine ae_neBot.2 (fun hc => ?_)
    have hpos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))) Set.univ :=
      isOpen_univ.measure_pos volume ⟨0, trivial⟩
    rw [hc] at hpos
    simp at hpos
  have hAtil : ∀ h : EuclideanSpace ℝ (Fin n),
      ‖A h - A 0‖ ≤ cG * γ₁ * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖ := by
    have hae := hcG ε γ₀ γ₁ Set.univ (fun _ _ h => A h - A 0) hε hγ₀ hγ₁ hQ
    obtain ⟨x, hx⟩ := hae.exists
    intro h
    have h1 := hx (Set.mem_univ x) 0 h
    simpa using h1
  -- the elementary weight bound, with constant one
  have hsqrpow : ∀ (c r : ℝ), 0 ≤ c → ((c ^ 2) ^ r : ℝ) = c ^ (2 * r) := by
    intro c r hc
    rw [show (c ^ 2 : ℝ) = c ^ (2:ℝ) by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]]
    rw [← Real.rpow_mul hc]
  have hwt : ∀ h : EuclideanSpace ℝ (Fin n),
      (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖ ≤ (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2) := by
    intro h
    rcases le_or_gt 2 p with hp2 | hp2
    · have h1 : (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) ≤ (1 + ‖h‖ ^ 2) ^ (p / 2 - 1) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      have h2 : ‖h‖ ≤ (1 + ‖h‖ ^ 2) ^ ((1:ℝ)/2) := by
        have h3 : ((‖h‖ ^ 2 : ℝ)) ^ ((1:ℝ)/2) ≤ (1 + ‖h‖ ^ 2) ^ ((1:ℝ)/2) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
        rwa [hsqrpow ‖h‖ ((1:ℝ)/2) (norm_nonneg h), show (2:ℝ) * ((1:ℝ)/2) = 1 by ring,
          Real.rpow_one] at h3
      calc (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖
          ≤ (1 + ‖h‖ ^ 2) ^ (p / 2 - 1) * ((1 + ‖h‖ ^ 2) ^ ((1:ℝ)/2)) := by
            refine mul_le_mul h1 h2 (norm_nonneg h) (Real.rpow_nonneg (by positivity) _)
        _ = (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2) := by
            rw [← Real.rpow_add (by positivity)]
            congr 1
            ring
    · -- `1 < p < 2`: the exponent is negative
      by_cases hh : h = 0
      · rw [hh]
        simp only [norm_zero, mul_zero]
        exact Real.rpow_nonneg (by norm_num) _
      · have hnp : 0 < ‖h‖ := norm_pos_iff.2 hh
        have hsq : (0:ℝ) < ‖h‖ ^ 2 := by positivity
        have h1 : (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) ≤ (‖h‖ ^ 2) ^ (p / 2 - 1) :=
          Real.rpow_le_rpow_of_nonpos hsq (by linarith) (by linarith)
        have h2 : (‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖ = (‖h‖ ^ 2) ^ ((p - 1) / 2) := by
          rw [hsqrpow ‖h‖ (p / 2 - 1) (norm_nonneg h),
            hsqrpow ‖h‖ ((p - 1) / 2) (norm_nonneg h),
            show (2:ℝ) * ((p - 1) / 2) = 2 * (p / 2 - 1) + 1 by ring,
            Real.rpow_add hnp, Real.rpow_one]
        have h3 : (‖h‖ ^ 2) ^ ((p - 1) / 2) ≤ (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
        calc (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖
            ≤ (‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg h)
          _ = (‖h‖ ^ 2) ^ ((p - 1) / 2) := h2
          _ ≤ (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2) := h3
  -- the pointwise bound on `A` itself
  have hAbd : ∀ h : EuclideanSpace ℝ (Fin n),
      ‖A h‖ ≤ cG * γ₁ * (1 + ‖h‖) ^ (p - 1) + ‖A 0‖ := by
    intro h
    have h1 : ‖A h‖ ≤ ‖A h - A 0‖ + ‖A 0‖ := by
      simpa using norm_add_le (A h - A 0) (A 0)
    have h2 : (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2) ≤ (1 + ‖h‖) ^ (p - 1) := by
      have h3 : (1 + ‖h‖ ^ 2 : ℝ) ≤ (1 + ‖h‖) ^ 2 := by nlinarith [norm_nonneg h]
      have h4 : (1 + ‖h‖ ^ 2 : ℝ) ^ ((p - 1) / 2) ≤ ((1 + ‖h‖) ^ 2) ^ ((p - 1) / 2) :=
        Real.rpow_le_rpow (by positivity) h3 (by linarith)
      rwa [hsqrpow (1 + ‖h‖) ((p - 1) / 2) (by positivity),
        show (2:ℝ) * ((p - 1) / 2) = p - 1 by ring] at h4
    have h5 : ‖A h - A 0‖ ≤ cG * γ₁ * (1 + ‖h‖) ^ (p - 1) := by
      refine le_trans (hAtil h) ?_
      calc cG * γ₁ * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖
          = cG * γ₁ * ((ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖) := by ring
        _ ≤ cG * γ₁ * ((1 + ‖h‖ ^ 2) ^ ((p - 1) / 2)) :=
            mul_le_mul_of_nonneg_left (hwt h) (by positivity)
        _ ≤ cG * γ₁ * ((1 + ‖h‖) ^ (p - 1)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  -- the dominating function lies in `L^{p'}`
  have hF : MemLp (fun x => (1:ℝ) + ‖gv x‖) (ENNReal.ofReal p) (volume.restrict S) :=
    (memLp_const (1:ℝ)).add hgv.norm
  have hdiv : ENNReal.ofReal p / ENNReal.ofReal (p - 1)
      = ENNReal.ofReal (p / (p - 1)) := (ENNReal.ofReal_div_of_pos hp10).symm
  have hG0 : MemLp (fun x => ((1:ℝ) + ‖gv x‖) ^ (p - 1))
      (ENNReal.ofReal (p / (p - 1))) (volume.restrict S) := by
    have h := hF.norm_rpow_div (ENNReal.ofReal (p - 1))
    rw [ENNReal.toReal_ofReal hp10.le, hdiv] at h
    have heq : (fun x => ‖(1:ℝ) + ‖gv x‖‖ ^ (p - 1))
        = fun x => ((1:ℝ) + ‖gv x‖) ^ (p - 1) := by
      funext x
      rw [Real.norm_of_nonneg (by positivity)]
    rwa [heq] at h
  have hG : MemLp (fun x => cG * γ₁ * ((1:ℝ) + ‖gv x‖) ^ (p - 1) + ‖A 0‖)
      (ENNReal.ofReal (p / (p - 1))) (volume.restrict S) :=
    (hG0.const_mul (cG * γ₁)).add (memLp_const _)
  refine hG.mono (hAcont.comp_aestronglyMeasurable hgv.1) ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (by positivity)]
  exact hAbd (gv x)
