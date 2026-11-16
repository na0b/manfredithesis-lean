import ManfrediThesis.Preamble
set_option maxHeartbeats 800000
open MeasureTheory

/-- Continuity of translation in `L^r`: for every real `r ≥ 1`, every
`w ∈ L^r(ℝⁿ)` and every coordinate direction `e_k`,
`‖w(· + s e_k) - w‖_{L^r(ℝⁿ)} → 0` as `s → 0`.

Conventions, restated here because a helper inherits none of its parent's.
`e_k` is the `k`-th standard basis vector, so `x + s e_k` translates `x` by `s`
in the `k`-th coordinate direction; the exponent is `ENNReal.ofReal r`
throughout, so `eLpNorm` is the `L^r` seminorm of the real `r ≥ 1`; the limit
is taken in the full neighbourhood filter of `0`, i.e. over all real `s`,
positive and negative alike.  Nothing in the statement refers to weak
derivatives or to any domain: it is a statement about an arbitrary `L^r`
function on all of `ℝⁿ`.

The route is the standard density argument, which is Step 6 of the parent's
proof.  Fix `ε > 0`.  By the density of the compactly supported continuous
functions in `L^r` (Preamble) choose `v` continuous with compact support and
`‖w - v‖_{L^r} ≤ ε/3`.  Split
`w(·+se_k) - w = \bigl(w(·+se_k) - v(·+se_k)\bigr) + \bigl(v(·+se_k) - v\bigr)
  + (v - w)`
and estimate the three terms by the `L^r` triangle inequality (Minkowski,
Preamble).  The first and the last are each `≤ ε/3`: the last by the choice of
`v`, and the first because translation preserves the `L^r` seminorm, which is
the translation invariance of Lebesgue measure (Preamble) applied to the
measure-preserving map `x ↦ x + s e_k`.  For the middle term, `v` is uniformly
continuous --- being continuous with compact support --- and supported in a
fixed compact set together with all its small translates, so
`‖v(·+se_k) - v‖_∞ → 0` as `s → 0` and the `L^r` seminorm over that fixed
compact set is dominated by a constant multiple of the sup norm; hence the
middle term is `≤ ε/3` for all `|s|` small.  Adding the three gives
`‖w(·+se_k) - w‖_{L^r} ≤ ε` for all small `|s|`, which is the assertion. -/
theorem LpTranslationContinuity :
    ∀ (n : ℕ) (k : Fin n),
      ∀ (r : ℝ), 1 ≤ r → ∀ w : EuclideanSpace ℝ (Fin n) → ℝ,
      MemLp w (ENNReal.ofReal r) volume →
      Filter.Tendsto (fun s : ℝ => eLpNorm
      (fun x => w (x + s • EuclideanSpace.single k (1 : ℝ)) - w x)
      (ENNReal.ofReal r) volume) (nhds 0) (nhds 0) := by
  intro n k
  have hek : ‖EuclideanSpace.single k (1 : ℝ)‖ = 1 := by simp
  have htinv : ∀ (p : ENNReal) (u : EuclideanSpace ℝ (Fin n) → ℝ),
      AEStronglyMeasurable u volume → ∀ c : EuclideanSpace ℝ (Fin n),
      eLpNorm (fun x => u (x + c)) p volume = eLpNorm u p volume :=
    fun p u hu c =>
      eLpNorm_comp_measurePreserving hu (measurePreserving_add_right volume c)
  intro r hr w hw
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
  have hptop : (ENNReal.ofReal r) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr0.le
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.2 hr
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact Filter.Eventually.of_forall fun s => le_top
  have hσ0 : ε / 3 ≠ 0 := by
    simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨hε.ne', by norm_num⟩
  have hσtop : ε / 3 ≠ ⊤ := (ENNReal.div_lt_top hεtop (by norm_num)).ne
  have hσ3 : ε / 3 + ε / 3 + ε / 3 ≤ ε := by
    have h : ε / 3 + ε / 3 + ε / 3 = 3 * (ε / 3) := by ring
    rw [h]; exact ENNReal.mul_div_le
  obtain ⟨v, hvcs, hwv, hvc, hvmem⟩ :=
    hw.exists_hasCompactSupport_eLpNorm_sub_le hptop hσ0
  -- the fixed compact set and the real tolerance
  have hCcpt : IsCompact (Metric.cthickening 1 (tsupport v)) := hvcs.cthickening
  have hCm : MeasurableSet (Metric.cthickening 1 (tsupport v)) := hCcpt.isClosed.measurableSet
  set A : ENNReal := (volume (Metric.cthickening 1 (tsupport v))) ^ (r⁻¹) with hAdef
  have hAtop : A ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hCcpt.measure_lt_top.ne
  obtain ⟨t, ht0, htA⟩ : ∃ t : ℝ, 0 < t ∧ A * ENNReal.ofReal t ≤ ε / 3 := by
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
  -- uniform continuity of `v`
  have hvuc : UniformContinuous v := hvcs.uniformContinuous_of_continuous hvc
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y x : EuclideanSpace ℝ (Fin n),
      ‖y - x‖ ≤ R → |v y - v x| ≤ t := by
    obtain ⟨r0, hr00, hrr⟩ := Metric.uniformContinuous_iff.1 hvuc t ht0
    refine ⟨r0 / 2, by positivity, fun y x hd => ?_⟩
    have hlt : dist y x < r0 := by rw [dist_eq_norm]; linarith
    exact le_of_lt (by simpa [Real.dist_eq] using hrr hlt)
  have hev : ∀ᶠ s : ℝ in nhds 0, |s| ≤ min R 1 := by
    have h := (continuous_abs (G := ℝ)).tendsto 0
    have h0 : |(0 : ℝ)| < min R 1 := by simpa using lt_min hR0 one_pos
    exact h.eventually (eventually_le_nhds h0)
  filter_upwards [hev] with s hs
  have hsR : |s| ≤ R := le_trans hs (min_le_left _ _)
  have hs1 : |s| ≤ 1 := le_trans hs (min_le_right _ _)
  have hnorm : ‖s • EuclideanSpace.single k (1 : ℝ)‖ = |s| := by
    rw [norm_smul, hek, mul_one, Real.norm_eq_abs]
  -- the middle term
  have hmid : eLpNorm
      (fun x => v (x + s • EuclideanSpace.single k (1 : ℝ)) - v x)
      (ENNReal.ofReal r) volume ≤ ε / 3 := by
    refine le_trans ?_ htA
    have hvan : ∀ x, x ∉ Metric.cthickening 1 (tsupport v) →
        v (x + s • EuclideanSpace.single k (1 : ℝ)) - v x = 0 := by
      intro x hx
      have hvx : v x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hx (Metric.self_subset_cthickening _ h)
      have hvy : v (x + s • EuclideanSpace.single k (1 : ℝ)) = 0 := by
        by_contra hne
        refine hx (Metric.mem_cthickening_of_dist_le x
          (x + s • EuclideanSpace.single k (1 : ℝ)) 1 _ (subset_tsupport _ hne) ?_)
        rw [dist_eq_norm]
        simpa [hnorm] using hs1
      rw [hvx, hvy, sub_zero]
    have hind : (Metric.cthickening 1 (tsupport v)).indicator
        (fun x => v (x + s • EuclideanSpace.single k (1 : ℝ)) - v x)
        = fun x => v (x + s • EuclideanSpace.single k (1 : ℝ)) - v x := by
      funext x
      by_cases hx : x ∈ Metric.cthickening 1 (tsupport v)
      · simp [hx]
      · simp [hx, hvan x hx]
    rw [← hind, eLpNorm_indicator_eq_eLpNorm_restrict hCm]
    have hb := eLpNorm_le_of_ae_bound
      (μ := (volume.restrict (Metric.cthickening 1 (tsupport v))))
      (p := ENNReal.ofReal r)
      (f := fun x => v (x + s • EuclideanSpace.single k (1 : ℝ)) - v x) (C := t)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hR _ _ (by simpa [hnorm] using hsR))
    simpa [Measure.restrict_apply_univ, hpt] using hb
  -- assemble
  have hdecomp : (fun x => w (x + s • EuclideanSpace.single k (1 : ℝ)) - w x)
      = ((fun x => (w - v) (x + s • EuclideanSpace.single k (1 : ℝ)))
          + (fun x => v (x + s • EuclideanSpace.single k (1 : ℝ)) - v x))
        + (v - w) := by
    funext x; simp
  have hA1 : AEStronglyMeasurable
      (fun x => (w - v) (x + s • EuclideanSpace.single k (1 : ℝ))) volume := by
    have := (hw.1.sub hvmem.1).comp_measurePreserving
      (measurePreserving_add_right volume (s • EuclideanSpace.single k (1 : ℝ)))
    simpa [Function.comp_def] using this
  have hA2 : AEStronglyMeasurable
      (fun x => v (x + s • EuclideanSpace.single k (1 : ℝ)) - v x) volume := by
    refine AEStronglyMeasurable.sub ?_ hvc.aestronglyMeasurable
    exact (hvc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  have hA3 : AEStronglyMeasurable (v - w) volume := hvmem.1.sub hw.1
  have hfirst : eLpNorm (fun x => (w - v) (x + s • EuclideanSpace.single k (1 : ℝ)))
      (ENNReal.ofReal r) volume ≤ ε / 3 := by
    rw [htinv _ _ (hw.1.sub hvmem.1)]
    exact hwv
  have hlast : eLpNorm (v - w) (ENNReal.ofReal r) volume ≤ ε / 3 := by
    have hn : v - w = -(w - v) := by funext x; simp
    rw [hn, eLpNorm_neg]; exact hwv
  rw [hdecomp]
  refine le_trans (eLpNorm_add_le (hA1.add hA2) hA3 hp1) ?_
  refine le_trans (add_le_add (eLpNorm_add_le hA1 hA2 hp1) (le_refl _)) ?_
  exact le_trans (add_le_add (add_le_add hfirst hmid) hlast) hσ3
