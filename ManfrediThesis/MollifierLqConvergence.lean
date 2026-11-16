import ManfrediThesis.Preamble
open MeasureTheory

/-- Mollifications converge in `L^q`: if `ρ m` is a sequence of smooth,
nonnegative, compactly supported probability densities whose supports shrink to
the origin (`tsupport (ρ m) ⊆ closedBall 0 (δ m)` with `δ m → 0`), and if
convolution against each `ρ m` contracts the `L^q` seminorm, then for every
`w ∈ L^q(ℝⁿ)` one has `‖w ∗ ρ m - w‖_{L^q} → 0`.

The contraction clause is taken as a hypothesis rather than proved here: it is
Young's inequality at exponent `1` for a probability density, it is exactly how
each consumer already has it available, and it also has consumers of its own
outside this lemma.

The proof is the standard three-epsilon density argument.  Given `ε > 0`, pick a
continuous compactly supported `v` with `‖w - v‖_{L^q} ≤ ε/3` (density of `C_c`
in `L^q`), split
`w ∗ ρ m - w = (w - v) ∗ ρ m + (v ∗ ρ m - v) + (v - w)`,
bound the outer two terms by `ε/3` each -- the first through the contraction
hypothesis -- and the middle term by the uniform continuity of `v` together with
`tsupport (ρ m) ⊆ closedBall 0 (δ m)` and `δ m → 0`.

This is the `L^q` half of the mollification toolkit shared by the weak-gradient
chain-rule and smooth-approximation nodes; the `W^{1,q}` statements that consume
it are `WeakGradientC1Comp`, `WeakGradientSmoothApprox` and
`WeakGradientVectorComp`, each of which applies it to a function and to the
components of its weak gradient. -/
theorem MollifierLqConvergence :
    ∀ (n : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ q →
      ∀ (ρ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (δ : ℕ → ℝ),
      Filter.Tendsto δ Filter.atTop (nhds 0) →
      (∀ m, ContDiff ℝ (⊤ : ℕ∞) (ρ m)) → (∀ m z, 0 ≤ ρ m z) →
      (∀ m, HasCompactSupport (ρ m)) →
      (∀ m, tsupport (ρ m) ⊆ Metric.closedBall 0 (δ m)) →
      (∀ m, (∫ z, ρ m z) = 1) →
      (∀ u : EuclideanSpace ℝ (Fin n) → ℝ, MemLp u (ENNReal.ofReal q) volume → ∀ m,
        eLpNorm (convolution u (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume)
            (ENNReal.ofReal q) volume
          ≤ eLpNorm u (ENNReal.ofReal q) volume) →
      ∀ w : EuclideanSpace ℝ (Fin n) → ℝ, MemLp w (ENNReal.ofReal q) volume →
      Filter.Tendsto (fun m => eLpNorm
        (fun x => convolution w (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - w x)
        (ENNReal.ofReal q) volume) Filter.atTop (nhds 0) := by
  intro n q _hn hq ρ δ hδlim hρsm hρ0 hρcs hρts hρint contract w hw
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hptop : (ENNReal.ofReal q) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq0.le
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 hq
  have hρc : ∀ m, Continuous (ρ m) := fun m => (hρsm m).continuous
  have hρI : ∀ m, Integrable (ρ m) volume :=
    fun m => (hρc m).integrable_of_hasCompactSupport (hρcs m)
  have hmass : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin n)), ∫ y, ρ m (x - y) = 1 := by
    intro m x
    rw [integral_sub_left_eq_self (ρ m) volume x]; exact hρint m
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact Filter.Eventually.of_forall fun m => le_top
  have hσ0 : ε / 3 ≠ 0 := by
    simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨hε.ne', by norm_num⟩
  have hσtop : ε / 3 ≠ ⊤ := (ENNReal.div_lt_top hεtop (by norm_num)).ne
  have hσ3 : ε / 3 + ε / 3 + ε / 3 ≤ ε := by
    have h : ε / 3 + ε / 3 + ε / 3 = 3 * (ε / 3) := by ring
    rw [h]; exact ENNReal.mul_div_le
  obtain ⟨v, hvcs, hwv, hvc, hvmem⟩ :=
    hw.exists_hasCompactSupport_eLpNorm_sub_le hptop hσ0
  have hwvmem : MemLp (w - v) (ENNReal.ofReal q) volume := hw.sub hvmem
  have hwvloc : LocallyIntegrable (w - v) volume := hwvmem.locallyIntegrable hp1
  have hvloc : LocallyIntegrable v volume := hvmem.locallyIntegrable hp1
  have hce1 : ∀ m, ConvolutionExists (w - v) (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    fun m => (hρcs m).convolutionExists_right _ hwvloc (hρc m)
  have hce2 : ∀ m, ConvolutionExists v (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    fun m => (hρcs m).convolutionExists_right _ hvloc (hρc m)
  have hsplit : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin n)),
      convolution w (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x
        = convolution (w - v) (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x
          + convolution v (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    intro m x
    have h := (hce1 m).add_distrib (hce2 m)
    have hfun : (w - v) + v = w := by funext y; simp
    rw [hfun] at h
    exact congrFun h x
  -- the fixed compact set and the real tolerance
  have hCcpt : IsCompact (Metric.cthickening 1 (tsupport v)) := hvcs.cthickening
  have hCm : MeasurableSet (Metric.cthickening 1 (tsupport v)) := hCcpt.isClosed.measurableSet
  set A : ENNReal := (volume (Metric.cthickening 1 (tsupport v))) ^ (q⁻¹) with hAdef
  have hAtop : A ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hCcpt.measure_lt_top.ne
  obtain ⟨s, hs0, hsA⟩ : ∃ s : ℝ, 0 < s ∧ A * ENNReal.ofReal s ≤ ε / 3 := by
    have hσr : 0 < (ε / 3).toReal := ENNReal.toReal_pos hσ0 hσtop
    have hAr : 0 ≤ A.toReal := ENNReal.toReal_nonneg
    refine ⟨(ε / 3).toReal / (A.toReal + 1), div_pos hσr (by positivity), ?_⟩
    have key : A * ENNReal.ofReal ((ε / 3).toReal / (A.toReal + 1))
        ≤ ENNReal.ofReal ((ε / 3).toReal) := by
      calc A * ENNReal.ofReal ((ε / 3).toReal / (A.toReal + 1))
          = ENNReal.ofReal (A.toReal * ((ε / 3).toReal / (A.toReal + 1))) := by
            rw [ENNReal.ofReal_mul hAr, ENNReal.ofReal_toReal hAtop]
        _ ≤ ENNReal.ofReal ((ε / 3).toReal) :=
            ENNReal.ofReal_le_ofReal (by
              rw [mul_div_assoc', div_le_iff₀ (by positivity)]
              nlinarith [hAr, hσr])
    rwa [ENNReal.ofReal_toReal hσtop] at key
  have hvuc : UniformContinuous v := hvcs.uniformContinuous_of_continuous hvc
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y x : EuclideanSpace ℝ (Fin n),
      ‖y - x‖ ≤ R → |v y - v x| ≤ s := by
    obtain ⟨r, hr0, hr⟩ := Metric.uniformContinuous_iff.1 hvuc s hs0
    refine ⟨r / 2, by positivity, fun y x hd => ?_⟩
    have hlt : dist y x < r := by rw [dist_eq_norm]; linarith
    exact le_of_lt (by simpa [Real.dist_eq] using hr hlt)
  have hev : ∀ᶠ m in Filter.atTop, δ m ≤ min R 1 :=
    hδlim.eventually (eventually_le_nhds (lt_min hR0 one_pos))
  filter_upwards [hev] with m hm
  have hmR : δ m ≤ R := le_trans hm (min_le_left _ _)
  have hm1 : δ m ≤ 1 := le_trans hm (min_le_right _ _)
  have hvint : ∀ x : EuclideanSpace ℝ (Fin n),
      Integrable (fun y => v y * ρ m (x - y)) volume := by
    intro x
    refine (hce2 m x).congr (Filter.Eventually.of_forall fun y => ?_)
    simp [ContinuousLinearMap.lsmul_apply]
  have hconstint : ∀ x : EuclideanSpace ℝ (Fin n),
      Integrable (fun y => v x * ρ m (x - y)) volume :=
    fun x => ((hρI m).comp_sub_left x).const_mul _
  have hbd : ∀ x, |convolution v (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - v x| ≤ s := by
    intro x
    have hrep : convolution v (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - v x
        = ∫ y, (v y - v x) * ρ m (x - y) := by
      have hsp : (fun y => (v y - v x) * ρ m (x - y))
          = fun y => v y * ρ m (x - y) - v x * ρ m (x - y) := by funext y; ring
      rw [hsp, integral_sub (hvint x) (hconstint x), integral_const_mul, hmass m x, mul_one,
        convolution_def]
      simp [ContinuousLinearMap.lsmul_apply]
    rw [hrep]
    have hintA : Integrable (fun y => (v y - v x) * ρ m (x - y)) volume := by
      have hsp : (fun y => (v y - v x) * ρ m (x - y))
          = fun y => v y * ρ m (x - y) - v x * ρ m (x - y) := by funext y; ring
      rw [hsp]; exact (hvint x).sub (hconstint x)
    have hintB : Integrable (fun y => s * ρ m (x - y)) volume :=
      ((hρI m).comp_sub_left x).const_mul _
    calc |∫ y, (v y - v x) * ρ m (x - y)|
        ≤ ∫ y, |(v y - v x) * ρ m (x - y)| := abs_integral_le_integral_abs
      _ ≤ ∫ y, s * ρ m (x - y) := by
          refine integral_mono hintA.abs hintB fun y => ?_
          rw [abs_mul, abs_of_nonneg (hρ0 m _)]
          by_cases hz : ρ m (x - y) = 0
          · simp [hz]
          · have hmem : x - y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (δ m) :=
              hρts m (subset_tsupport _ hz)
            have hn : ‖y - x‖ ≤ R := by
              have h1 : ‖x - y‖ ≤ δ m := by simpa using hmem
              have h2 : ‖y - x‖ = ‖x - y‖ := by rw [← norm_neg]; simp
              rw [h2]; linarith
            exact mul_le_mul_of_nonneg_right (hR y x hn) (hρ0 m _)
      _ = s := by rw [integral_const_mul, hmass m x, mul_one]
  have hvan : ∀ x, x ∉ Metric.cthickening 1 (tsupport v) →
      convolution v (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - v x = 0 := by
    intro x hx
    have hvx : v x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hx (Metric.self_subset_cthickening _ h)
    have hc0 : convolution v (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0 := by
      rw [convolution_def]
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
      by_cases hz : ρ m (x - y) = 0
      · simp [ContinuousLinearMap.lsmul_apply, hz]
      · have hmem : x - y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (δ m) :=
          hρts m (subset_tsupport _ hz)
        have hvy : v y = 0 := by
          by_contra hvy
          refine hx (Metric.mem_cthickening_of_dist_le x y 1 _ (subset_tsupport _ hvy) ?_)
          have h1 : ‖x - y‖ ≤ δ m := by simpa using hmem
          rw [dist_eq_norm]; linarith
        simp [hvy]
    rw [hc0, hvx, sub_zero]
  have hmid : eLpNorm
      (fun x => convolution v (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - v x)
      (ENNReal.ofReal q) volume ≤ ε / 3 := by
    refine le_trans ?_ hsA
    have hind : (Metric.cthickening 1 (tsupport v)).indicator
        (fun x => convolution v (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - v x)
        = fun x => convolution v (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - v x := by
      funext x
      by_cases hx : x ∈ Metric.cthickening 1 (tsupport v)
      · simp [hx]
      · simp [hx, hvan x hx]
    rw [← hind, eLpNorm_indicator_eq_eLpNorm_restrict hCm]
    have hb := eLpNorm_le_of_ae_bound
      (μ := (volume.restrict (Metric.cthickening 1 (tsupport v)))) (p := ENNReal.ofReal q)
      (f := fun x => convolution v (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - v x)
      (C := s) (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hbd x)
    simpa [Measure.restrict_apply_univ, hpt] using hb
  have hdecomp : (fun x => convolution w (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - w x)
      = (convolution (w - v) (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume
          + (fun x => convolution v (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - v x))
        + (v - w) := by
    funext x
    rw [hsplit m x]
    simp
    ring
  have hA1 : AEStronglyMeasurable
      (convolution (w - v) (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume) volume :=
    ((hρcs m).contDiff_convolution_right _ hwvloc (hρsm m)).continuous.aestronglyMeasurable
  have hA2 : AEStronglyMeasurable
      (fun x => convolution v (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - v x) volume :=
    (((hρcs m).contDiff_convolution_right _ hvloc (hρsm m)).continuous.sub hvc).aestronglyMeasurable
  have hA3 : AEStronglyMeasurable (v - w) volume := hvmem.1.sub hw.1
  have hlast : eLpNorm (v - w) (ENNReal.ofReal q) volume ≤ ε / 3 := by
    have hn : v - w = -(w - v) := by funext x; simp
    rw [hn, eLpNorm_neg]; exact hwv
  rw [hdecomp]
  refine le_trans (eLpNorm_add_le (hA1.add hA2) hA3 hp1) ?_
  refine le_trans (add_le_add (eLpNorm_add_le hA1 hA2 hp1) (le_refl _)) ?_
  exact le_trans (add_le_add (add_le_add (le_trans (contract (w - v) hwvmem m) hwv) hmid) hlast)
    hσ3
