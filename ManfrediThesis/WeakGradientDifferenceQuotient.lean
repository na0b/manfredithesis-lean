import ManfrediThesis.Preamble
import ManfrediThesis.LpTranslationContinuity
import ManfrediThesis.DifferenceQuotientLqBound
import ManfrediThesis.WeakGradientSegmentRepresentation
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.MemW1pLocOn
open MeasureTheory

/-- Difference quotients of a `W^{1,q}_loc` function converge to its weak
gradient in `L^q` of every compact subset. -/
theorem WeakGradientDifferenceQuotient :
    ∀ (n : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ q →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (f : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (K : Set (EuclideanSpace ℝ (Fin n))) (k : Fin n),
        IsOpen Ω → MemW1pLocOn n q Ω f g → IsCompact K → K ⊆ Ω →
        Filter.Tendsto
          (fun h : ℝ => ∫ x in K,
            |(f (x + h • EuclideanSpace.single k (1 : ℝ)) - f x) / h - g x k| ^ q)
          (nhdsWithin 0 {h | h ≠ 0}) (nhds 0) := by
  intro n q _hn hq Ω f g K k hΩ hW hKcpt hKΩ
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hp0 : (ENNReal.ofReal q) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hptop : (ENNReal.ofReal q) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq0.le
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 hq
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hKm : MeasurableSet K := hKcpt.isClosed.measurableSet
  have hproj : ∀ j : Fin n, Continuous (fun y : EuclideanSpace ℝ (Fin n) => y j) :=
    fun j => (continuous_apply j).comp (PiLp.continuous_ofLp 2 _)
  have hcoord : ∀ (w : EuclideanSpace ℝ (Fin n)) (j : Fin n), ‖w j‖ ≤ ‖w‖ := by
    intro w j
    rw [EuclideanSpace.norm_eq, Real.norm_eq_abs,
      show |w j| = Real.sqrt (|w j| ^ 2) by rw [Real.sqrt_sq (abs_nonneg _)]]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (f := fun l => |w l| ^ 2) (fun l _ => sq_nonneg _)
        (Finset.mem_univ j))
  have hek : ‖EuclideanSpace.single k (1 : ℝ)‖ = 1 := by simp
  have htinv : ∀ (p : ENNReal) (u : EuclideanSpace ℝ (Fin n) → ℝ),
      AEStronglyMeasurable u volume → ∀ c : EuclideanSpace ℝ (Fin n),
      eLpNorm (fun x => u (x + c)) p volume = eLpNorm u p volume :=
    fun p u hu c => eLpNorm_comp_measurePreserving hu (measurePreserving_add_right volume c)
  -- Step 1: geometry
  obtain ⟨dd, hdd0, hddsub⟩ := hKcpt.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨d0, hd00, hK3Ω⟩ : ∃ d0 : ℝ, 0 < d0 ∧ Metric.cthickening (3 * d0) K ⊆ Ω := by
    refine ⟨dd / 3, by positivity, ?_⟩
    rw [show 3 * (dd / 3) = dd by ring]; exact hddsub
  have hK3cpt : IsCompact (Metric.cthickening (3 * d0) K) := hKcpt.cthickening
  have hK3m : MeasurableSet (Metric.cthickening (3 * d0) K) :=
    Metric.isClosed_cthickening.measurableSet
  have hKK3 : K ⊆ Metric.cthickening (3 * d0) K := Metric.self_subset_cthickening _
  have hK1K3 : Metric.cthickening d0 K ⊆ Metric.cthickening (3 * d0) K :=
    Metric.cthickening_mono (by linarith) _
  have hfinK3 : IsFiniteMeasure (volume.restrict (Metric.cthickening (3 * d0) K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK3cpt.measure_lt_top⟩
  have hnormsmul : ∀ s : ℝ, ‖s • EuclideanSpace.single k (1 : ℝ)‖ = |s| := by
    intro s; rw [norm_smul, hek, mul_one, Real.norm_eq_abs]
  -- the shift facts (1)
  have hshift0 : ∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ), x ∈ K → |s| ≤ d0 →
      x + s • EuclideanSpace.single k (1 : ℝ) ∈ Metric.cthickening d0 K := by
    intro x s hx hs
    refine Metric.mem_cthickening_of_dist_le _ x d0 _ hx ?_
    rw [dist_eq_norm]
    simpa [hnormsmul] using hs
  have hshift1 : ∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ),
      x ∈ Metric.cthickening d0 K → |s| ≤ d0 →
      x + s • EuclideanSpace.single k (1 : ℝ) ∈ Metric.cthickening (2 * d0) K := by
    intro x s hx hs
    have h1 : x + s • EuclideanSpace.single k (1 : ℝ)
        ∈ Metric.cthickening d0 (Metric.cthickening d0 K) := by
      refine Metric.mem_cthickening_of_dist_le _ x d0 _ hx ?_
      rw [dist_eq_norm]
      simpa [hnormsmul] using hs
    have h2 := Metric.cthickening_cthickening_subset hd00.le hd00.le K h1
    exact Metric.cthickening_mono (by linarith) _ h2
  -- the truncated data
  have hfK3 : MemLp f (ENNReal.ofReal q)
      (volume.restrict (Metric.cthickening (3 * d0) K)) := (hW.2 _ hK3cpt hK3Ω).1
  have hgK3 : MemLp g (ENNReal.ofReal q)
      (volume.restrict (Metric.cthickening (3 * d0) K)) := (hW.2 _ hK3cpt hK3Ω).2
  have hgkK3 : MemLp (fun x => g x k) (ENNReal.ofReal q)
      (volume.restrict (Metric.cthickening (3 * d0) K)) :=
    hgK3.mono ((hproj k).comp_aestronglyMeasurable hgK3.1)
      (Filter.Eventually.of_forall fun x => hcoord _ k)
  have hFhmem : MemLp ((Metric.cthickening (3 * d0) K).indicator f)
      (ENNReal.ofReal q) volume := (memLp_indicator_iff_restrict hK3m).2 hfK3
  have hGhmem : MemLp ((Metric.cthickening (3 * d0) K).indicator (fun x => g x k))
      (ENNReal.ofReal q) volume := (memLp_indicator_iff_restrict hK3m).2 hgkK3
  have hFhint : Integrable ((Metric.cthickening (3 * d0) K).indicator f) volume :=
    (integrable_indicator_iff hK3m).2
      ((hfK3.mono_exponent (ENNReal.one_le_ofReal.2 hq)).integrable le_rfl)
  have hGhint : Integrable ((Metric.cthickening (3 * d0) K).indicator (fun x => g x k))
      volume :=
    (integrable_indicator_iff hK3m).2
      ((hgkK3.mono_exponent (ENNReal.one_le_ofReal.2 hq)).integrable le_rfl)
  have transl : ∀ (r : ℝ), 1 ≤ r → ∀ w : EuclideanSpace ℝ (Fin n) → ℝ,
      MemLp w (ENNReal.ofReal r) volume →
      Filter.Tendsto (fun s : ℝ => eLpNorm
        (fun x => w (x + s • EuclideanSpace.single k (1 : ℝ)) - w x)
        (ENNReal.ofReal r) volume) (nhds 0) (nhds 0) :=
    LpTranslationContinuity n k
  -- Step 6: the modulus `ω`
  have hωle : ∀ s : ℝ, (∫⁻ x in K, ‖(Metric.cthickening (3 * d0) K).indicator
        (fun y => g y k) (x + s • EuclideanSpace.single k (1 : ℝ))
        - (Metric.cthickening (3 * d0) K).indicator (fun y => g y k) x‖ₑ ^ q)
      ≤ (eLpNorm (fun x => (Metric.cthickening (3 * d0) K).indicator (fun y => g y k)
          (x + s • EuclideanSpace.single k (1 : ℝ))
          - (Metric.cthickening (3 * d0) K).indicator (fun y => g y k) x)
          (ENNReal.ofReal q) volume) ^ q := by
    intro s
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop, hpt, ← ENNReal.rpow_mul,
      one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
    exact setLIntegral_le_lintegral _ _
  have hωlim : Filter.Tendsto (fun s : ℝ => ∫⁻ x in K,
      ‖(Metric.cthickening (3 * d0) K).indicator (fun y => g y k)
        (x + s • EuclideanSpace.single k (1 : ℝ))
        - (Metric.cthickening (3 * d0) K).indicator (fun y => g y k) x‖ₑ ^ q)
      (nhds 0) (nhds 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hεq : (0 : ENNReal) < ε ^ (q⁻¹) := by
      rcases eq_or_ne ε ⊤ with rfl | hεtop
      · rw [ENNReal.top_rpow_of_pos (by positivity)]; exact ENNReal.zero_lt_top
      · exact ENNReal.rpow_pos hε hεtop
    filter_upwards [(ENNReal.tendsto_nhds_zero.1
      (transl q hq _ hGhmem)) (ε ^ (q⁻¹)) hεq] with s hs
    calc (∫⁻ x in K, ‖(Metric.cthickening (3 * d0) K).indicator (fun y => g y k)
            (x + s • EuclideanSpace.single k (1 : ℝ))
            - (Metric.cthickening (3 * d0) K).indicator (fun y => g y k) x‖ₑ ^ q)
        ≤ _ := hωle s
      _ ≤ (ε ^ (q⁻¹)) ^ q := ENNReal.rpow_le_rpow hs hq0.le
      _ = ε := by rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
  -- the real-to-lintegral dictionary
  have hcq : Continuous (fun t : ℝ => |t| ^ q) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (Real.continuousAt_rpow_const _ _ (Or.inr hq0.le)).comp continuous_abs.continuousAt
  have hdict : ∀ u : EuclideanSpace ℝ (Fin n) → ℝ,
      AEStronglyMeasurable u (volume.restrict K) →
      (∫ x in K, |u x| ^ q) = (∫⁻ x in K, ‖u x‖ₑ ^ q).toReal := by
    intro u hu
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _)
      (hcq.comp_aestronglyMeasurable hu)]
    refine congrArg ENNReal.toReal (lintegral_congr fun x => ?_)
    rw [← ofReal_norm, Real.norm_eq_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le]
  -- Steps 4 and 5: the difference-quotient bound, given the representation (6).
  -- Stated over abstract `(Fh, Gh)` so that the long truncated expressions appear
  -- only once, at the application site.
  have hstep45 : ∀ (Fh Gh Gh' : EuclideanSpace ℝ (Fin n) → ℝ), Measurable Gh' →
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
        ≤ ENNReal.ofReal c :=
    DifferenceQuotientLqBound n q hq K k
  -- a globally measurable representative of the truncated gradient component,
  -- valid inside the shear `(x, s) ↦ x + s • e_k` on the product measure
  obtain ⟨Gh', hGh'm, hGh'ae, hprod1, hprod2⟩ :
      ∃ Gh' : EuclideanSpace ℝ (Fin n) → ℝ, Measurable Gh' ∧
        (Metric.cthickening (3 * d0) K).indicator (fun y => g y k) =ᵐ[volume] Gh' ∧
        ((fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
            (Metric.cthickening (3 * d0) K).indicator (fun y => g y k)
              (p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)))
          =ᵐ[volume.prod volume]
         (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
            Gh' (p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)))) ∧
        ((fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
            (Metric.cthickening (3 * d0) K).indicator (fun y => g y k) p.1)
          =ᵐ[volume.prod volume]
         (fun p : EuclideanSpace ℝ (Fin n) × ℝ => Gh' p.1)) := by
    set u : EuclideanSpace ℝ (Fin n) → ℝ :=
      (Metric.cthickening (3 * d0) K).indicator (fun y => g y k) with hudef
    have hu : AEStronglyMeasurable u volume := hGhmem.1
    obtain ⟨M, hMmeas, hMnull, hMsub⟩ :
        ∃ M : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet M ∧ volume M = 0 ∧
          {y | u y ≠ hu.mk u y} ⊆ M := by
      have h0 : volume {y | u y ≠ hu.mk u y} = 0 := hu.ae_eq_mk
      obtain ⟨M, hsub, hMmeas, hM0⟩ := exists_measurable_superset_of_null h0
      exact ⟨M, hMmeas, hM0, hsub⟩
    refine ⟨hu.mk u, hu.stronglyMeasurable_mk.measurable, hu.ae_eq_mk, ?_, ?_⟩
    · have hT : Measurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
          p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)) :=
        measurable_fst.add (measurable_snd.smul_const _)
      have hpre : MeasurableSet ((fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
          p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)) ⁻¹' M) := hT hMmeas
      have hnull : (volume.prod volume) ((fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
          p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)) ⁻¹' M) = 0 := by
        rw [Measure.prod_apply_symm hpre]
        have hz : ∀ s : ℝ, volume ((fun x : EuclideanSpace ℝ (Fin n) => (x, s)) ⁻¹'
            ((fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
              p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)) ⁻¹' M)) = 0 := by
          intro s
          rw [show ((fun x : EuclideanSpace ℝ (Fin n) => (x, s)) ⁻¹'
              ((fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
                p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)) ⁻¹' M))
              = (fun x : EuclideanSpace ℝ (Fin n) =>
                  x + s • EuclideanSpace.single k (1 : ℝ)) ⁻¹' M from rfl,
            measure_preimage_add_right volume (s • EuclideanSpace.single k (1 : ℝ)) M,
            hMnull]
        simp only [hz]
        simp
      exact measure_mono_null (fun p hp => hMsub hp) hnull
    · have hnull : (volume.prod volume) (M ×ˢ (Set.univ : Set ℝ)) = 0 := by
        rw [Measure.prod_prod, hMnull, zero_mul]
      refine measure_mono_null (fun p hp => ?_) hnull
      exact ⟨hMsub hp, Set.mem_univ _⟩
  -- Step 3: the integral representation (6).
  -- Proved by the test-function characterisation of a.e. equality on an open set
  -- (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`): both sides of (6) are
  -- integrable, and for every test function supported in `thickening d0 K` their
  -- pairings against it agree, because the 1-D fundamental theorem of calculus
  -- turns the difference `φ(· - h e_k) - φ` into an `s`-integral of `D_k φ(· - s e_k)`
  -- and the weak-gradient identity applies to each shifted test function.
  have hwg : HasWeakGradientOn n Ω f g := hW.1
  have hG'int : Integrable Gh' volume := hGhint.congr hGh'ae
  have step3 : ∀ Fh Gh : EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ y ∈ Metric.cthickening (3 * d0) K, Fh y = f y) →
      (∀ y ∈ Metric.cthickening (3 * d0) K, Gh y = g y k) →
      Integrable Fh volume → Integrable Gh volume →
      ∀ Gh' : EuclideanSpace ℝ (Fin n) → ℝ, Measurable Gh' → Integrable Gh' volume →
      ((fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
          Gh (p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)))
        =ᵐ[volume.prod volume]
       (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
          Gh' (p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)))) →
      ∀ h : ℝ, 0 < |h| → |h| < d0 →
      ∀ᵐ x ∂(volume.restrict K),
        IntervalIntegrable (fun s => Gh (x + s • EuclideanSpace.single k (1 : ℝ)))
          volume 0 h ∧
        Fh (x + h • EuclideanSpace.single k (1 : ℝ)) - Fh x
          = ∫ s in (0 : ℝ)..h, Gh (x + s • EuclideanSpace.single k (1 : ℝ)) :=
    WeakGradientSegmentRepresentation n Ω f g K k d0 hΩ hΩm hKm hd00 hK3Ω
      hshift1 hwg
  have hrep : ∀ h : ℝ, 0 < |h| → |h| < d0 →
      ∀ᵐ x ∂(volume.restrict K),
        IntervalIntegrable
          (fun s => (Metric.cthickening (3 * d0) K).indicator (fun y => g y k)
            (x + s • EuclideanSpace.single k (1 : ℝ))) volume 0 h ∧
        (Metric.cthickening (3 * d0) K).indicator f
            (x + h • EuclideanSpace.single k (1 : ℝ))
          - (Metric.cthickening (3 * d0) K).indicator f x
          = ∫ s in (0 : ℝ)..h, (Metric.cthickening (3 * d0) K).indicator
              (fun y => g y k) (x + s • EuclideanSpace.single k (1 : ℝ)) := by
    intro h hh0 hhd
    exact step3 _ _ (fun y hy => Set.indicator_of_mem hy f)
      (fun y hy => Set.indicator_of_mem hy (fun x => g x k))
      hFhint hGhint Gh' hGh'm hG'int hprod1 h hh0 hhd
  -- Steps 3, 4 and 5, packaged
  have hbound : ∀ (h : ℝ) (c : ℝ), 0 < |h| → |h| < d0 → 0 ≤ c →
      (∀ s : ℝ, |s| ≤ |h| →
        (∫⁻ x in K, ‖(Metric.cthickening (3 * d0) K).indicator (fun y => g y k)
            (x + s • EuclideanSpace.single k (1 : ℝ))
          - (Metric.cthickening (3 * d0) K).indicator (fun y => g y k) x‖ₑ ^ q)
          ≤ ENNReal.ofReal c) →
      (∫⁻ x in K, ‖((Metric.cthickening (3 * d0) K).indicator f
            (x + h • EuclideanSpace.single k (1 : ℝ))
          - (Metric.cthickening (3 * d0) K).indicator f x) / h
        - (Metric.cthickening (3 * d0) K).indicator (fun y => g y k) x‖ₑ ^ q)
        ≤ ENNReal.ofReal c := by
    intro h c hh0 hhd _hc0 hcs
    exact hstep45 _ _ Gh' hGh'm hprod1 hprod2 h c hh0 (hrep h hh0 hhd) hcs
  -- Conclusion
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro σ hσ
  have hev : ∀ᶠ s : ℝ in nhds 0,
      (∫⁻ x in K, ‖(Metric.cthickening (3 * d0) K).indicator (fun y => g y k)
          (x + s • EuclideanSpace.single k (1 : ℝ))
        - (Metric.cthickening (3 * d0) K).indicator (fun y => g y k) x‖ₑ ^ q)
        ≤ ENNReal.ofReal (σ / 2) :=
    (ENNReal.tendsto_nhds_zero.1 hωlim) (ENNReal.ofReal (σ / 2))
      (ENNReal.ofReal_pos.2 (by positivity))
  obtain ⟨η, hη0, hη⟩ := Metric.eventually_nhds_iff.1 hev
  have hev2 : ∀ᶠ h : ℝ in nhdsWithin 0 {h | h ≠ 0}, |h| < min η d0 := by
    have hc := (continuous_abs (G := ℝ)).tendsto 0
    have h0 : |(0 : ℝ)| < min η d0 := by simpa using lt_min hη0 hd00
    exact (hc.eventually (eventually_lt_nhds h0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hev2, self_mem_nhdsWithin] with h hh hne
  have hh0 : 0 < |h| := abs_pos.2 hne
  have hhd : |h| < d0 := lt_of_lt_of_le hh (min_le_right _ _)
  have hhη : |h| < η := lt_of_lt_of_le hh (min_le_left _ _)
  have hcongr : (∫ x in K, |(f (x + h • EuclideanSpace.single k (1 : ℝ)) - f x) / h
        - g x k| ^ q)
      = ∫ x in K, |((Metric.cthickening (3 * d0) K).indicator f
            (x + h • EuclideanSpace.single k (1 : ℝ))
          - (Metric.cthickening (3 * d0) K).indicator f x) / h
        - (Metric.cthickening (3 * d0) K).indicator (fun y => g y k) x| ^ q := by
    refine setIntegral_congr_fun hKm fun x hx => ?_
    rw [Set.indicator_of_mem (hKK3 hx), Set.indicator_of_mem (hKK3 hx),
      Set.indicator_of_mem (hK1K3 (hshift0 x h hx hhd.le))]
  have hmeasFh : AEStronglyMeasurable
      (fun x => (Metric.cthickening (3 * d0) K).indicator f
        (x + h • EuclideanSpace.single k (1 : ℝ))) volume := by
    have := hFhmem.1.comp_measurePreserving
      (measurePreserving_add_right volume (h • EuclideanSpace.single k (1 : ℝ)))
    simpa [Function.comp_def] using this
  have hmeasD : AEStronglyMeasurable
      (fun x => (Metric.cthickening (3 * d0) K).indicator f
          (x + h • EuclideanSpace.single k (1 : ℝ))
        - (Metric.cthickening (3 * d0) K).indicator f x) volume :=
    hmeasFh.sub hFhmem.1
  have hmeasU : AEStronglyMeasurable
      (fun x => ((Metric.cthickening (3 * d0) K).indicator f
            (x + h • EuclideanSpace.single k (1 : ℝ))
          - (Metric.cthickening (3 * d0) K).indicator f x) / h
        - (Metric.cthickening (3 * d0) K).indicator (fun y => g y k) x)
      (volume.restrict K) :=
    ((((continuous_id.div_const h).comp_aestronglyMeasurable hmeasD)).sub
      hGhmem.1).restrict
  rw [Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _),
    hcongr, hdict _ hmeasU]
  have hb := hbound h (σ / 2) hh0 hhd (by positivity) fun s hs =>
    hη (by simpa [Real.dist_eq] using lt_of_le_of_lt hs hhη)
  have h2 := ENNReal.toReal_le_of_le_ofReal (by positivity : (0 : ℝ) ≤ σ / 2) hb
  linarith
