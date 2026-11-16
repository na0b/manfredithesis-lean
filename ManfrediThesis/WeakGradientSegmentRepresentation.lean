import ManfrediThesis.Preamble
import ManfrediThesis.HasWeakGradientOn
set_option maxHeartbeats 800000
open MeasureTheory

/-- The integral representation of an increment of a weakly differentiable
function along a coordinate segment: if `g` is a weak gradient of `f` on `Ω`
and `K` is a compact set with a `3d₀`-collar inside `Ω`, then for every
increment `h` with `0 < |h| < d₀` and for almost every `x ∈ K`,
`s ↦ g^k(x + s e_k)` is interval-integrable on `[0,h]` and
`f(x + h e_k) - f(x) = ∫_0^h g^k(x + s e_k)\,ds`.

Conventions, restated here because a helper inherits none of its parent's.
`e_k` is the `k`-th standard basis vector, so `x + s e_k` is the translate of
`x` by `s` in the `k`-th coordinate direction; `Metric.cthickening r K` is the
closed `r`-collar of `K`.  `HasWeakGradientOn n Ω f g` is the tablet's weak
gradient: an identity against smooth test functions compactly supported in `Ω`,
which says nothing about `f` off `Ω` --- which is why the statement is given
for arbitrary `Fh`, `Gh` agreeing with `f` and `g^k` on the collar
`Metric.cthickening (3d₀) K` rather than for `f` and `g^k` themselves.  That is
exactly what the consumer needs: it applies this with the zero extensions
`Fh = 1_{coll}f` and `Gh = 1_{coll}(g^k)`, which are integrable on all of `ℝⁿ`
while `f` need not be.  The auxiliary `Gh'` is a measurable representative of
`Gh` along the shifted product, carried as a hypothesis because the Fubini step
needs a genuinely measurable integrand; this is a `W^{1,q}` statement, with no
exponent in sight, and nothing here is an `L²` claim.

The route is Step 3 of the parent's argument.  Mollify: let `ρ_j` be a standard
mollifier and `F_j = Fh * ρ_j`.  Each `F_j` is smooth, and on the inner collar
its `k`-th derivative is the mollification of `Gh`, because `y ↦ ρ_j(x - y)` is
an admissible test function for `HasWeakGradientOn` once its support sits inside
`Ω` --- which the collar hypothesis guarantees for `j` large.  For smooth
functions the representation is the fundamental theorem of calculus along the
segment, so
`F_j(x + h e_k) - F_j(x) = ∫_0^h (D_kF_j)(x + s e_k) ds` for every `x`.  Both
sides converge in `L¹` of `K` as `j → ∞`: the left by `L¹` convergence of
mollifications and the translation invariance of Lebesgue measure, the right by
Fubini on `K × [0,h]` --- legitimate because the shifted integrand is
measurable on the product, which is what the `Gh'` hypothesis provides, and
integrable there, which the collar bound and the integrability of `Gh` give.
Passing to an almost-everywhere convergent subsequence on both sides yields the
identity for almost every `x ∈ K`, and the interval integrability of
`s ↦ Gh(x + s e_k)` for almost every such `x` falls out of the same Fubini
argument. -/
theorem WeakGradientSegmentRepresentation :
    ∀ (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
      (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (K : Set (EuclideanSpace ℝ (Fin n))) (k : Fin n) (d0 : ℝ),
      IsOpen Ω → MeasurableSet Ω → MeasurableSet K → 0 < d0 →
      Metric.cthickening (3 * d0) K ⊆ Ω →
      (∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ),
        x ∈ Metric.cthickening d0 K → |s| ≤ d0 →
        x + s • EuclideanSpace.single k (1 : ℝ)
          ∈ Metric.cthickening (2 * d0) K) →
      HasWeakGradientOn n Ω f g →
      ∀ Fh Gh : EuclideanSpace ℝ (Fin n) → ℝ,
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
      = ∫ s in (0 : ℝ)..h, Gh (x + s • EuclideanSpace.single k (1 : ℝ)) := by
  intro n Ω f g K k d0 hΩ hΩm hKm hd00 hK3Ω hshift1 hwg Fh Gh hFeq hGeq hFhint
    hGhint Gh' hGh'm hG'int hprod1 h hh0 hhd
  have hfinI : IsFiniteMeasure (volume.restrict (Set.uIoc 0 h)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Set.uIoc, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  -- the open set on which the representation is proved
  have hWopen : IsOpen (Metric.thickening d0 K) := Metric.isOpen_thickening
  have hKW : K ⊆ Metric.thickening d0 K := Metric.self_subset_thickening hd00 K
  have hWsub : Metric.thickening d0 K ⊆ Metric.cthickening d0 K :=
    Metric.thickening_subset_cthickening _ _
  -- ======== the shear layer ========
  have hTmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)) :=
    measurable_fst.add (measurable_snd.smul_const _)
  have hG'shearm : Measurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      Gh' (p.1 + p.2 • EuclideanSpace.single k (1 : ℝ))) := hGh'm.comp hTmeas
  have hslice : ∀ x : EuclideanSpace ℝ (Fin n),
      Measurable (fun s : ℝ => Gh' (x + s • EuclideanSpace.single k (1 : ℝ))) := fun x =>
    hGh'm.comp ((measurable_id.smul_const (EuclideanSpace.single k (1 : ℝ))).const_add x)
  have hTfin : (∫⁻ x, ∫⁻ s in Set.uIoc 0 h,
      ‖Gh' (x + s • EuclideanSpace.single k (1 : ℝ))‖ₑ) ≠ ⊤ := by
    have hswap : (∫⁻ x, ∫⁻ s in Set.uIoc 0 h,
          ‖Gh' (x + s • EuclideanSpace.single k (1 : ℝ))‖ₑ)
        = ∫⁻ s in Set.uIoc 0 h, ∫⁻ x,
          ‖Gh' (x + s • EuclideanSpace.single k (1 : ℝ))‖ₑ :=
      lintegral_lintegral_swap hG'shearm.enorm.aemeasurable
    have htrans : ∀ s : ℝ,
        (∫⁻ x, ‖Gh' (x + s • EuclideanSpace.single k (1 : ℝ))‖ₑ) = ∫⁻ x, ‖Gh' x‖ₑ :=
      fun s => lintegral_add_right_eq_self (fun x => ‖Gh' x‖ₑ)
        (s • EuclideanSpace.single k (1 : ℝ))
    rw [hswap]
    simp only [htrans]
    rw [lintegral_const, Measure.restrict_apply_univ]
    refine ENNReal.mul_ne_top hG'int.hasFiniteIntegral.ne ?_
    rw [Set.uIoc, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hac : volume.prod (volume.restrict (Set.uIoc 0 h))
      ≪ (volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume : Measure ℝ) :=
    Measure.AbsolutelyContinuous.prod (Measure.AbsolutelyContinuous.rfl)
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hprodeq : (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
        Gh (p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)))
      =ᵐ[volume.prod (volume.restrict (Set.uIoc 0 h))]
      (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
        Gh' (p.1 + p.2 • EuclideanSpace.single k (1 : ℝ))) := by
    exact hprod1.filter_mono hac.ae_le
  have hG'shear : Integrable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      Gh' (p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)))
      (volume.prod (volume.restrict (Set.uIoc 0 h))) := by
    refine ⟨hG'shearm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm,
      lintegral_prod _ hG'shearm.enorm.aemeasurable]
    exact lt_top_iff_ne_top.2 hTfin
  have hGshear : Integrable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      Gh (p.1 + p.2 • EuclideanSpace.single k (1 : ℝ)))
      (volume.prod (volume.restrict (Set.uIoc 0 h))) := hG'shear.congr hprodeq.symm
  -- the interval-integrability conjunct
  have hae : ∀ᵐ x ∂volume, (∫⁻ s in Set.uIoc 0 h,
      ‖Gh' (x + s • EuclideanSpace.single k (1 : ℝ))‖ₑ) < ⊤ := by
    refine ae_lt_top ?_ hTfin
    exact hG'shearm.enorm.lintegral_prod_right'
  have hsec : ∀ᵐ x ∂volume,
      (fun s : ℝ => Gh (x + s • EuclideanSpace.single k (1 : ℝ)))
        =ᵐ[volume] (fun s : ℝ => Gh' (x + s • EuclideanSpace.single k (1 : ℝ))) :=
    Measure.ae_ae_of_ae_prod hprod1
  have hII : ∀ᵐ x ∂volume, IntervalIntegrable
      (fun s => Gh (x + s • EuclideanSpace.single k (1 : ℝ))) volume 0 h := by
    filter_upwards [hae, hsec] with x hx hxsec
    refine intervalIntegrable_iff.2 ?_
    have h1 : IntegrableOn
        (fun s : ℝ => Gh' (x + s • EuclideanSpace.single k (1 : ℝ)))
        (Set.uIoc 0 h) volume := ⟨(hslice x).aestronglyMeasurable, hx⟩
    exact h1.congr (Filter.EventuallyEq.symm (ae_restrict_of_ae hxsec))
  -- ======== the generic Fubini swap ========
  have swapgen : ∀ Φ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ,
      Integrable (Function.uncurry Φ)
        (volume.prod (volume.restrict (Set.uIoc 0 h))) →
      (∫ x, ∫ s in (0:ℝ)..h, Φ x s) = ∫ s in (0:ℝ)..h, ∫ x, Φ x s := by
    intro Φ hint
    rcases le_or_gt 0 h with hh | hh
    · rw [Set.uIoc_of_le hh] at hint
      simp only [intervalIntegral.integral_of_le hh]
      exact integral_integral_swap hint
    · rw [Set.uIoc_of_ge hh.le] at hint
      simp only [intervalIntegral.integral_of_ge hh.le]
      rw [integral_neg, integral_integral_swap hint]
  -- ======== integrability bookkeeping ========
  have hfstint : ∀ D : EuclideanSpace ℝ (Fin n) → ℝ, Integrable D volume →
      Integrable (fun p : EuclideanSpace ℝ (Fin n) × ℝ => D p.1)
        (volume.prod (volume.restrict (Set.uIoc 0 h))) := by
    intro D hD
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.uIoc 0 h)) :=
      integrable_const 1
    have h2 : Integrable (fun p : EuclideanSpace ℝ (Fin n) × ℝ => D p.1 * (1 : ℝ))
        (volume.prod (volume.restrict (Set.uIoc 0 h))) := hD.mul_prod h1
    simpa using h2
  have hbdd : ∀ (D : EuclideanSpace ℝ (Fin n) → ℝ), Integrable D volume →
      ∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous χ → HasCompactSupport χ →
      Integrable (fun x => χ x * D x) volume := by
    intro D hD χ hχc hχcs
    obtain ⟨C, hC⟩ := hχcs.exists_bound_of_continuous hχc
    refine Integrable.mono' (hD.norm.const_mul C)
      (hχc.aestronglyMeasurable.mul hD.1) ?_
    filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  have hVint : Integrable (fun x => ∫ s in (0:ℝ)..h,
      Gh (x + s • EuclideanSpace.single k (1 : ℝ))) volume := by
    have h1 : Integrable (fun x => ∫ s in Set.uIoc 0 h,
        Gh (x + s • EuclideanSpace.single k (1 : ℝ))) volume :=
      hGshear.integral_prod_left
    rcases le_or_gt 0 h with hh | hh
    · rw [Set.uIoc_of_le hh] at h1
      simpa only [intervalIntegral.integral_of_le hh] using h1
    · simp only [intervalIntegral.integral_of_ge hh.le]
      rw [Set.uIoc_of_ge hh.le] at h1
      exact h1.neg
  -- ======== the test-function identity ========
  have key : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Metric.thickening d0 K →
      (∫ x, φ x • ((Fh (x + h • EuclideanSpace.single k (1 : ℝ)) - Fh x)
        - ∫ s in (0:ℝ)..h, Gh (x + s • EuclideanSpace.single k (1 : ℝ)))) = 0 := by
    intro φ hφ hφcs hφW'
    have hφW : tsupport φ ⊆ Metric.cthickening d0 K := hφW'.trans hWsub
    have hφc : Continuous φ := hφ.continuous
    have hDc : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ φ z (EuclideanSpace.single k (1 : ℝ))) :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hDcs : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ φ z (EuclideanSpace.single k (1 : ℝ))) :=
      (hφcs.fderiv ℝ).comp_left
        (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
          L (EuclideanSpace.single k (1 : ℝ))) (by simp)
    have hφshift : ∀ c : ℝ, HasCompactSupport
        (fun y => φ (y - c • EuclideanSpace.single k (1 : ℝ))) := by
      intro c
      have hts : tsupport (fun y => φ (y - c • EuclideanSpace.single k (1 : ℝ)))
          ⊆ (fun y => y - c • EuclideanSpace.single k (1 : ℝ)) ⁻¹' (tsupport φ) := by
        refine closure_minimal (fun y hy => subset_closure hy) ?_
        exact (isClosed_tsupport φ).preimage (continuous_id.sub continuous_const)
      refine IsCompact.of_isClosed_subset ?_ (isClosed_tsupport _) hts
      exact (Homeomorph.subRight
        (c • EuclideanSpace.single k (1 : ℝ))).isCompact_preimage.2 hφcs
    -- the weak-gradient identity at the shifted test function
    have wgshift : ∀ s : ℝ, |s| ≤ |h| →
        (∫ y, Fh y * fderiv ℝ φ (y - s • EuclideanSpace.single k (1 : ℝ))
            (EuclideanSpace.single k (1 : ℝ)))
          = -∫ y, Gh y * φ (y - s • EuclideanSpace.single k (1 : ℝ)) := by
      intro s hs
      have hΩm : MeasurableSet Ω := hΩ.measurableSet
      have hsd : |s| ≤ d0 := le_trans hs hhd.le
      have h23 : Metric.cthickening (2 * d0) K ⊆ Metric.cthickening (3 * d0) K :=
        Metric.cthickening_mono (by linarith) _
      have hψsm : ContDiff ℝ (⊤ : ℕ∞)
          (fun y => φ (y - s • EuclideanSpace.single k (1 : ℝ))) :=
        hφ.comp (contDiff_id.sub contDiff_const)
      have hψts : tsupport (fun y => φ (y - s • EuclideanSpace.single k (1 : ℝ)))
          ⊆ (fun y => y - s • EuclideanSpace.single k (1 : ℝ)) ⁻¹' (tsupport φ) := by
        refine closure_minimal (fun y hy => subset_closure hy) ?_
        exact (isClosed_tsupport φ).preimage (continuous_id.sub continuous_const)
      have hψK3 : tsupport (fun y => φ (y - s • EuclideanSpace.single k (1 : ℝ)))
          ⊆ Metric.cthickening (3 * d0) K := by
        refine hψts.trans fun y hy => ?_
        have h1 : y - s • EuclideanSpace.single k (1 : ℝ) ∈ Metric.cthickening d0 K :=
          hφW hy
        have h2 := hshift1 _ s h1 hsd
        simpa using h23 h2
      have hψΩ : tsupport (fun y => φ (y - s • EuclideanSpace.single k (1 : ℝ))) ⊆ Ω :=
        hψK3.trans hK3Ω
      have hψd : ∀ y, fderiv ℝ
          (fun y' => φ (y' - s • EuclideanSpace.single k (1 : ℝ))) y
          (EuclideanSpace.single k (1 : ℝ))
          = fderiv ℝ φ (y - s • EuclideanSpace.single k (1 : ℝ))
              (EuclideanSpace.single k (1 : ℝ)) := by
        intro y
        have h1 : HasFDerivAt
            (fun y' : EuclideanSpace ℝ (Fin n) =>
              y' - s • EuclideanSpace.single k (1 : ℝ))
            (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y :=
          (hasFDerivAt_id y).sub_const _
        have h2 : HasFDerivAt φ
            (fderiv ℝ φ (y - s • EuclideanSpace.single k (1 : ℝ)))
            (y - s • EuclideanSpace.single k (1 : ℝ)) :=
          (hφ.differentiable (by simp) _).hasFDerivAt
        have h3 : HasFDerivAt
            (fun y' => φ (y' - s • EuclideanSpace.single k (1 : ℝ)))
            ((fderiv ℝ φ (y - s • EuclideanSpace.single k (1 : ℝ))).comp
              (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) y :=
          h2.comp y h1
        rw [h3.fderiv]
        simp
      have hvan : ∀ y, y ∉ Metric.cthickening (3 * d0) K →
          φ (y - s • EuclideanSpace.single k (1 : ℝ)) = 0 ∧
          fderiv ℝ φ (y - s • EuclideanSpace.single k (1 : ℝ))
            (EuclideanSpace.single k (1 : ℝ)) = 0 := by
        intro y hy
        have hyn : y ∉ tsupport
            (fun y' => φ (y' - s • EuclideanSpace.single k (1 : ℝ))) :=
          fun hc => hy (hψK3 hc)
        have h0 : φ (y - s • EuclideanSpace.single k (1 : ℝ)) = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun y' => φ (y' - s • EuclideanSpace.single k (1 : ℝ))) hyn
        refine ⟨h0, ?_⟩
        rw [← hψd y, fderiv_of_notMem_tsupport ℝ hyn]
        simp
      have hWG := hwg _ hψsm (hφshift s) hψΩ k
      have hL1 : (∫ y in Ω, f y * fderiv ℝ
            (fun y' => φ (y' - s • EuclideanSpace.single k (1 : ℝ))) y
            (EuclideanSpace.single k (1 : ℝ)))
          = ∫ y in Ω, Fh y * fderiv ℝ φ (y - s • EuclideanSpace.single k (1 : ℝ))
              (EuclideanSpace.single k (1 : ℝ)) := by
        refine setIntegral_congr_fun hΩm fun y _ => ?_
        rw [hψd y]
        by_cases hyK : y ∈ Metric.cthickening (3 * d0) K
        · rw [hFeq y hyK]
        · rw [(hvan y hyK).2]; ring
      have hL2 : (∫ y in Ω, Fh y *
              fderiv ℝ φ (y - s • EuclideanSpace.single k (1 : ℝ))
              (EuclideanSpace.single k (1 : ℝ)))
          = ∫ y, Fh y * fderiv ℝ φ (y - s • EuclideanSpace.single k (1 : ℝ))
              (EuclideanSpace.single k (1 : ℝ)) := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
        have hyK : y ∉ Metric.cthickening (3 * d0) K := fun hc => hy (hK3Ω hc)
        rw [(hvan y hyK).2]; ring
      have hR1 : (∫ y in Ω, g y k * φ (y - s • EuclideanSpace.single k (1 : ℝ)))
          = ∫ y in Ω, Gh y * φ (y - s • EuclideanSpace.single k (1 : ℝ)) := by
        refine setIntegral_congr_fun hΩm fun y _ => ?_
        by_cases hyK : y ∈ Metric.cthickening (3 * d0) K
        · rw [hGeq y hyK]
        · rw [(hvan y hyK).1]; ring
      have hR2 : (∫ y in Ω, Gh y * φ (y - s • EuclideanSpace.single k (1 : ℝ)))
          = ∫ y, Gh y * φ (y - s • EuclideanSpace.single k (1 : ℝ)) := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
        have hyK : y ∉ Metric.cthickening (3 * d0) K := fun hc => hy (hK3Ω hc)
        rw [(hvan y hyK).1]; ring
      rw [hL1, hL2, hR1, hR2] at hWG
      exact hWG
    -- the two product integrabilities
    have hintF : Integrable (Function.uncurry
        fun (y : EuclideanSpace ℝ (Fin n)) (s : ℝ) =>
          Fh y * fderiv ℝ φ (y - s • EuclideanSpace.single k (1 : ℝ))
            (EuclideanSpace.single k (1 : ℝ)))
        (volume.prod (volume.restrict (Set.uIoc 0 h))) := by
      obtain ⟨C, hC⟩ := hDcs.exists_bound_of_continuous hDc
      have hbase := hfstint Fh hFhint
      refine Integrable.mono' (hbase.norm.const_mul C) ?_ ?_
      · exact hbase.1.mul ((hDc.comp (continuous_fst.sub
          (continuous_snd.smul continuous_const))).aestronglyMeasurable)
      · filter_upwards with p
        simp only [Function.uncurry_def, norm_mul]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
    have hintG : Integrable (Function.uncurry
        fun (x : EuclideanSpace ℝ (Fin n)) (s : ℝ) =>
          φ x * Gh (x + s • EuclideanSpace.single k (1 : ℝ)))
        (volume.prod (volume.restrict (Set.uIoc 0 h))) := by
      obtain ⟨C, hC⟩ := hφcs.exists_bound_of_continuous hφc
      refine Integrable.mono' (hGshear.norm.const_mul C) ?_ ?_
      · exact ((hφc.comp continuous_fst).aestronglyMeasurable).mul hGshear.1
      · filter_upwards with p
        simp only [Function.uncurry_def, norm_mul]
        exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
    -- the translation identity
    have htr : ∀ (D : EuclideanSpace ℝ (Fin n) → ℝ) (c : ℝ),
        (∫ x, φ x * D (x + c • EuclideanSpace.single k (1 : ℝ)))
          = ∫ y, φ (y - c • EuclideanSpace.single k (1 : ℝ)) * D y := by
      intro D c
      have hx := (measurePreserving_add_right volume
          (c • EuclideanSpace.single k (1 : ℝ))).integral_comp
        (MeasurableEquiv.addRight
          (c • EuclideanSpace.single k (1 : ℝ))).measurableEmbedding
        (fun y => φ (y - c • EuclideanSpace.single k (1 : ℝ)) * D y)
      simpa using hx
    -- the 1-D fundamental theorem of calculus for the test function
    have hftc : ∀ y : EuclideanSpace ℝ (Fin n),
        φ (y - h • EuclideanSpace.single k (1 : ℝ)) - φ y
          = -∫ s in (0:ℝ)..h, fderiv ℝ φ (y - s • EuclideanSpace.single k (1 : ℝ))
              (EuclideanSpace.single k (1 : ℝ)) := by
      intro y
      have hd : ∀ s : ℝ, HasDerivAt
          (fun t : ℝ => φ (y - t • EuclideanSpace.single k (1 : ℝ)))
          (-(fderiv ℝ φ (y - s • EuclideanSpace.single k (1 : ℝ))
              (EuclideanSpace.single k (1 : ℝ)))) s := by
        intro s
        have h1 : HasDerivAt (fun t : ℝ => y - t • EuclideanSpace.single k (1 : ℝ))
            (-EuclideanSpace.single k (1 : ℝ)) s := by
          have h0 : HasDerivAt (fun t : ℝ => t • EuclideanSpace.single k (1 : ℝ))
              (EuclideanSpace.single k (1 : ℝ)) s := by
            simpa using (hasDerivAt_id s).smul_const
              (EuclideanSpace.single k (1 : ℝ))
          exact h0.const_sub y
        have h2 : HasFDerivAt φ
            (fderiv ℝ φ (y - s • EuclideanSpace.single k (1 : ℝ)))
            (y - s • EuclideanSpace.single k (1 : ℝ)) :=
          (hφ.differentiable (by simp) _).hasFDerivAt
        have h3 := h2.comp_hasDerivAt s h1
        rw [map_neg] at h3
        exact h3
      have hcont : Continuous (fun s : ℝ =>
          -(fderiv ℝ φ (y - s • EuclideanSpace.single k (1 : ℝ))
            (EuclideanSpace.single k (1 : ℝ)))) :=
        (hDc.comp (continuous_const.sub
          (continuous_id.smul continuous_const))).neg
      have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _ => hd s) (hcont.intervalIntegrable 0 h)
      rw [intervalIntegral.integral_neg] at hI
      simpa using hI.symm
    -- assemble
    simp only [smul_eq_mul]
    have hUint : Integrable
        (fun x => Fh (x + h • EuclideanSpace.single k (1 : ℝ)) - Fh x) volume :=
      (hFhint.comp_add_right _).sub hFhint
    have hsplit : (∫ x, φ x * ((Fh (x + h • EuclideanSpace.single k (1 : ℝ)) - Fh x)
          - ∫ s in (0:ℝ)..h, Gh (x + s • EuclideanSpace.single k (1 : ℝ))))
        = (∫ x, φ x * (Fh (x + h • EuclideanSpace.single k (1 : ℝ)) - Fh x))
          - ∫ x, φ x * ∫ s in (0:ℝ)..h,
              Gh (x + s • EuclideanSpace.single k (1 : ℝ)) := by
      rw [← integral_sub
        (hbdd (fun x => Fh (x + h • EuclideanSpace.single k (1 : ℝ)) - Fh x)
          hUint φ hφc hφcs)
        (hbdd (fun x => ∫ s in (0:ℝ)..h,
          Gh (x + s • EuclideanSpace.single k (1 : ℝ))) hVint φ hφc hφcs)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    rw [hsplit, sub_eq_zero]
    have hA : (∫ x, φ x * (Fh (x + h • EuclideanSpace.single k (1 : ℝ)) - Fh x))
        = ∫ s in (0:ℝ)..h, ∫ y,
            Gh y * φ (y - s • EuclideanSpace.single k (1 : ℝ)) := by
      have e1 : (∫ x, φ x * (Fh (x + h • EuclideanSpace.single k (1 : ℝ)) - Fh x))
          = (∫ x, φ x * Fh (x + h • EuclideanSpace.single k (1 : ℝ)))
            - ∫ x, φ x * Fh x := by
        rw [← integral_sub
          (hbdd (fun x => Fh (x + h • EuclideanSpace.single k (1 : ℝ)))
            (hFhint.comp_add_right _) φ hφc hφcs)
          (hbdd Fh hFhint φ hφc hφcs)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring
      have e2 : (∫ y, φ (y - h • EuclideanSpace.single k (1 : ℝ)) * Fh y)
            - ∫ x, φ x * Fh x
          = ∫ y, (φ (y - h • EuclideanSpace.single k (1 : ℝ)) - φ y) * Fh y := by
        rw [← integral_sub
          (hbdd Fh hFhint (fun y => φ (y - h • EuclideanSpace.single k (1 : ℝ)))
            (hφc.comp (continuous_id.sub continuous_const)) (hφshift h))
          (hbdd Fh hFhint φ hφc hφcs)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        ring
      have e3 : (∫ y, (φ (y - h • EuclideanSpace.single k (1 : ℝ)) - φ y) * Fh y)
          = -∫ y, ∫ s in (0:ℝ)..h, Fh y *
              fderiv ℝ φ (y - s • EuclideanSpace.single k (1 : ℝ))
                (EuclideanSpace.single k (1 : ℝ)) := by
        rw [← integral_neg]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [intervalIntegral.integral_const_mul, hftc y]
        ring
      rw [e1]
      rw [htr Fh h]
      rw [e2]
      rw [e3]
      rw [swapgen _ hintF]
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [wgshift s ?_, neg_neg]
      rcases le_or_gt 0 h with hh | hh
      · rw [Set.uIcc_of_le hh] at hs
        rw [abs_of_nonneg hh, abs_of_nonneg hs.1]; exact hs.2
      · rw [Set.uIcc_of_ge hh.le] at hs
        rw [abs_of_neg hh, abs_of_nonpos hs.2]; linarith [hs.1]
    have hB : (∫ x, φ x * ∫ s in (0:ℝ)..h,
          Gh (x + s • EuclideanSpace.single k (1 : ℝ)))
        = ∫ s in (0:ℝ)..h, ∫ y,
            Gh y * φ (y - s • EuclideanSpace.single k (1 : ℝ)) := by
      have e1 : (∫ x, φ x * ∫ s in (0:ℝ)..h,
            Gh (x + s • EuclideanSpace.single k (1 : ℝ)))
          = ∫ x, ∫ s in (0:ℝ)..h,
              φ x * Gh (x + s • EuclideanSpace.single k (1 : ℝ)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [intervalIntegral.integral_const_mul]
      rw [e1]
      rw [swapgen _ hintG]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [htr Gh s]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      ring
    rw [hA, hB]
  -- ======== conclusion ========
  have hUVint : Integrable (fun x =>
      (Fh (x + h • EuclideanSpace.single k (1 : ℝ)) - Fh x)
        - ∫ s in (0:ℝ)..h, Gh (x + s • EuclideanSpace.single k (1 : ℝ))) volume :=
    ((hFhint.comp_add_right _).sub hFhint).sub hVint
  have hzero := hWopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hUVint.locallyIntegrable.locallyIntegrableOn _)
    (fun φ hφ hφcs hφW => key φ (by exact_mod_cast hφ) hφcs hφW)
  have hfin : ∀ᵐ x ∂volume, x ∈ K →
      Fh (x + h • EuclideanSpace.single k (1 : ℝ)) - Fh x
        = ∫ s in (0:ℝ)..h, Gh (x + s • EuclideanSpace.single k (1 : ℝ)) := by
    filter_upwards [hzero] with x hx hxK
    have h1 := hx (hKW hxK)
    linarith [h1]
  refine (ae_restrict_iff' hKm).2 ?_
  filter_upwards [hII, hfin] with x h1 h2 hxK
  exact ⟨h1, h2 hxK⟩
