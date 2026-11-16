import ManfrediThesis.Preamble
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.WeakGradientC1Comp
open MeasureTheory

/-- The weak gradient of the positive part `(u - c)⁺` is `g` on `{u > c}` and
`0` elsewhere. -/
theorem WeakGradientPositivePart :
    ∀ (n : ℕ) (q c : ℝ), 1 ≤ n → 1 ≤ q →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        IsOpen Ω → volume Ω ≠ ⊤ →
        MemW1pOn n q Ω u g →
        MemW1pOn n q Ω (fun x => max (u x - c) 0)
          (fun x => if c < u x then g x else 0) := by
  intro n q c _hn hq Ω u g hΩ hvol hW
  have hwg := hW.1
  have huLp := hW.2.1
  have hgLp := hW.2.2
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hfin : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hvol⟩
  have hproj : ∀ i : Fin n, Continuous (fun y : EuclideanSpace ℝ (Fin n) => y i) :=
    fun i => (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
  have hcoord : ∀ (w : EuclideanSpace ℝ (Fin n)) (i : Fin n), ‖w i‖ ≤ ‖w‖ := by
    intro w i
    rw [EuclideanSpace.norm_eq, Real.norm_eq_abs,
      show |w i| = Real.sqrt (|w i| ^ 2) by rw [Real.sqrt_sq (abs_nonneg _)]]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (f := fun j => |w j| ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i))
  have hgiLp : ∀ i : Fin n,
      MemLp (fun x => g x i) (ENNReal.ofReal q) (volume.restrict Ω) :=
    fun i => hgLp.mono ((hproj i).comp_aestronglyMeasurable hgLp.1)
      (Filter.Eventually.of_forall fun x => hcoord _ i)
  have hu1 : IntegrableOn u Ω volume :=
    (huLp.mono_exponent (ENNReal.one_le_ofReal.2 hq)).integrable le_rfl
  have hg1 : ∀ i : Fin n, IntegrableOn (fun x => g x i) Ω volume :=
    fun i => ((hgiLp i).mono_exponent (ENNReal.one_le_ofReal.2 hq)).integrable le_rfl
  -- the pointwise bound on the positive part
  have hmaxbd : ∀ t : ℝ, |max (t - c) 0| ≤ |t| + |c| := by
    intro t
    rcases le_or_gt (t - c) 0 with h | h
    · rw [max_eq_right h, abs_zero]; positivity
    · rw [max_eq_left h.le, abs_of_nonneg h.le]
      have h2 : t ≤ |t| := le_abs_self _
      have h3 : -c ≤ |c| := neg_le_abs c
      linarith
  -- Step 0: the two `L^q` memberships
  have hB : MemLp (fun x => max (u x - c) 0) (ENNReal.ofReal q) (volume.restrict Ω) := by
    refine MemLp.mono (g := fun x => ‖u x‖ + |c|) (huLp.norm.add (memLp_const |c|))
      (((continuous_id.sub continuous_const).max
        continuous_const).comp_aestronglyMeasurable huLp.1)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (norm_nonneg _) (abs_nonneg _)), Real.norm_eq_abs]
    exact hmaxbd (u x)
  have hchi : Measurable (fun t : ℝ => if c < t then (1 : ℝ) else 0) :=
    measurable_const.ite (measurableSet_lt measurable_const measurable_id) measurable_const
  have hiteR : AEStronglyMeasurable (fun x => if c < u x then (1 : ℝ) else 0)
      (volume.restrict Ω) :=
    (hchi.comp_aemeasurable huLp.1.aemeasurable).aestronglyMeasurable
  have hC : MemLp (fun x => if c < u x then g x else 0)
      (ENNReal.ofReal q) (volume.restrict Ω) := by
    have heq : (fun x => if c < u x then g x else 0)
        = fun x => (if c < u x then (1 : ℝ) else 0) • g x := by
      funext x; by_cases h : c < u x <;> simp [h]
    rw [heq]
    refine hgLp.mono (hiteR.smul hgLp.1) (Filter.Eventually.of_forall fun x => ?_)
    by_cases h : c < u x <;> simp [h]
  have hsq : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (max s 0) ^ 2) (2 * max t 0) t := by
    intro t
    rcases lt_trichotomy t 0 with ht | ht | ht
    · have hev : (fun s : ℝ => (max s 0) ^ 2) =ᶠ[nhds t] fun _ => (0 : ℝ) := by
        filter_upwards [eventually_lt_nhds ht] with s hs
        rw [max_eq_right hs.le]; ring
      have h0 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
      have := h0.congr_of_eventuallyEq hev
      rwa [max_eq_right ht.le, mul_zero]
    · subst ht
      rw [hasDerivAt_iff_tendsto_slope]
      have hbd : ∀ s : ℝ, ‖slope (fun s : ℝ => (max s 0) ^ 2) 0 s‖ ≤ |s| := by
        intro s
        have hle : (max s 0) ^ 2 ≤ s ^ 2 := by
          rcases le_or_gt s 0 with h | h
          · rw [max_eq_right h]; simpa using sq_nonneg s
          · rw [max_eq_left h.le]
        rcases eq_or_ne s 0 with rfl | hs
        · simp [slope]
        · rw [slope_def_field]
          rw [show ((max s 0) ^ 2 - (max (0:ℝ) 0) ^ 2) / (s - 0) = (max s 0) ^ 2 / s by simp]
          rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (max s 0)^2)]
          rw [div_le_iff₀ (abs_pos.2 hs)]
          calc (max s 0) ^ 2 ≤ s ^ 2 := hle
            _ = |s| * |s| := by rw [← abs_mul, abs_of_nonneg (mul_self_nonneg s)]; ring
      have habs : Filter.Tendsto (fun s : ℝ => |s|) (nhdsWithin 0 {(0:ℝ)}ᶜ) (nhds 0) := by
        have : Filter.Tendsto (fun s : ℝ => |s|) (nhds (0:ℝ)) (nhds 0) := by
          simpa using (continuous_abs (G := ℝ)).tendsto 0
        exact this.mono_left nhdsWithin_le_nhds
      simpa using squeeze_zero_norm hbd habs
    · have hev : (fun s : ℝ => (max s 0) ^ 2) =ᶠ[nhds t] fun s => s ^ 2 := by
        filter_upwards [eventually_gt_nhds ht] with s hs
        rw [max_eq_left hs.le]
      have h0 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa using (hasDerivAt_pow 2 t)
      have := h0.congr_of_eventuallyEq hev
      rwa [max_eq_left ht.le]
  set FF : ℝ → ℝ → ℝ :=
    fun ε t => ((max t 0) ^ 2 - (max (t - ε) 0) ^ 2) / (2 * ε) with hFFdef
  set DD : ℝ → ℝ → ℝ := fun ε t => (max t 0 - max (t - ε) 0) / ε with hDDdef
  have hFd : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, HasDerivAt (FF ε) (DD ε t) t := by
    intro ε hε t
    have hε2 : (0 : ℝ) < 2 * ε := by linarith
    have h2 : HasDerivAt (fun s : ℝ => (max (s - ε) 0) ^ 2) (2 * max (t - ε) 0) t := by
      simpa [Function.comp_def] using (hsq (t - ε)).scomp t ((hasDerivAt_id t).sub_const ε)
    have h3 := ((hsq t).sub h2).div_const (2 * ε)
    have h4 : HasDerivAt (fun x : ℝ => ((max x 0) ^ 2 - (max (x - ε) 0) ^ 2) / (2 * ε))
        ((2 * max t 0 - 2 * max (t - ε) 0) / (2 * ε)) t := by
      simpa [Pi.sub_apply] using h3
    simp only [hFFdef, hDDdef]
    rw [show (max t 0 - max (t - ε) 0) / ε
        = (2 * max t 0 - 2 * max (t - ε) 0) / (2 * ε) by
      rw [div_eq_div_iff hε.ne' hε2.ne']; ring]
    exact h4
  have hDcont : ∀ ε : ℝ, Continuous (DD ε) := by
    intro ε
    simp only [hDDdef]
    exact ((continuous_id.max continuous_const).sub
      ((continuous_id.sub continuous_const).max continuous_const)).div_const ε
  have hDderiv : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, deriv (FF ε) t = DD ε t :=
    fun ε hε t => (hFd ε hε t).deriv
  have hFC1 : ∀ ε : ℝ, 0 < ε → ContDiff ℝ 1 (FF ε) := by
    intro ε hε
    refine contDiff_one_iff_deriv.2 ⟨fun t => (hFd ε hε t).differentiableAt, ?_⟩
    have h : deriv (FF ε) = DD ε := funext fun t => hDderiv ε hε t
    rw [h]; exact hDcont ε
  have hnum : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ,
      0 ≤ max t 0 - max (t - ε) 0 ∧ max t 0 - max (t - ε) 0 ≤ ε := by
    intro ε hε t
    rcases le_or_gt t 0 with h | h
    · rw [max_eq_right h, max_eq_right (by linarith : t - ε ≤ 0)]
      constructor <;> linarith
    · rw [max_eq_left h.le]
      rcases le_or_gt (t - ε) 0 with h2 | h2
      · rw [max_eq_right h2]; constructor <;> linarith
      · rw [max_eq_left h2.le]; constructor <;> linarith
  have hD01 : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, 0 ≤ DD ε t ∧ DD ε t ≤ 1 := by
    intro ε hε t
    simp only [hDDdef]
    exact ⟨div_nonneg (hnum ε hε t).1 hε.le, by rw [div_le_one hε]; exact (hnum ε hε t).2⟩
  have hFnn : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, 0 ≤ FF ε t ∧ FF ε t ≤ max t 0 := by
    intro ε hε t
    have hε2 : (0 : ℝ) < 2 * ε := by linarith
    simp only [hFFdef]
    rcases le_or_gt t 0 with h | h
    · rw [max_eq_right h, max_eq_right (by linarith : t - ε ≤ 0)]
      norm_num
    · rw [max_eq_left h.le]
      rcases le_or_gt (t - ε) 0 with h2 | h2
      · rw [max_eq_right h2]
        refine ⟨div_nonneg (by nlinarith [sq_nonneg t]) hε2.le, ?_⟩
        rw [div_le_iff₀ hε2]
        nlinarith
      · rw [max_eq_left h2.le]
        refine ⟨div_nonneg (by nlinarith) hε2.le, ?_⟩
        rw [div_le_iff₀ hε2]
        nlinarith
  have hF3 : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, |FF ε t - max t 0| ≤ ε / 2 := by
    intro ε hε t
    have hε2 : (0 : ℝ) < 2 * ε := by linarith
    simp only [hFFdef]
    rcases le_or_gt t 0 with h | h
    · rw [max_eq_right h, max_eq_right (by linarith : t - ε ≤ 0)]
      rw [show ((0:ℝ) ^ 2 - (0:ℝ) ^ 2) / (2 * ε) - 0 = 0 by norm_num]
      rw [abs_zero]
      linarith
    · rw [max_eq_left h.le]
      rcases le_or_gt (t - ε) 0 with h2 | h2
      · rw [max_eq_right h2]
        rw [show ((t:ℝ) ^ 2 - (0:ℝ) ^ 2) / (2 * ε) - t = (t ^ 2 - 2 * t * ε) / (2 * ε) by
          rw [eq_div_iff hε2.ne']; field_simp; ring]
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · rw [le_div_iff₀ hε2]; nlinarith
        · rw [div_le_iff₀ hε2]; nlinarith
      · rw [max_eq_left h2.le]
        rw [show ((t:ℝ) ^ 2 - (t - ε) ^ 2) / (2 * ε) - t = -(ε / 2) by
          rw [sub_eq_iff_eq_add, div_eq_iff hε2.ne']; ring]
        rw [abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ ε / 2)]
  have hD4 : ∀ t : ℝ, Filter.Tendsto (fun m : ℕ => DD (1 / ((m : ℝ) + 1)) t)
      Filter.atTop (nhds (if 0 < t then (1 : ℝ) else 0)) := by
    intro t
    rcases le_or_gt t 0 with h | h
    · have hzero : ∀ m : ℕ, DD (1 / ((m : ℝ) + 1)) t = 0 := by
        intro m
        have hm : (0:ℝ) < 1 / ((m : ℝ) + 1) := by positivity
        simp only [hDDdef]
        rw [max_eq_right h, max_eq_right (by linarith : t - 1 / ((m : ℝ) + 1) ≤ 0)]
        simp
      simp only [hzero, if_neg (not_lt.2 h)]
      exact tendsto_const_nhds
    · have hlim : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hev : ∀ᶠ m : ℕ in Filter.atTop, DD (1 / ((m : ℝ) + 1)) t = 1 := by
        filter_upwards [hlim.eventually (eventually_lt_nhds h)] with m hm
        have hm0 : (0:ℝ) < 1 / ((m : ℝ) + 1) := by positivity
        simp only [hDDdef]
        rw [max_eq_left h.le, max_eq_left (by linarith : (0:ℝ) ≤ t - 1 / ((m : ℝ) + 1))]
        rw [div_eq_one_iff_eq hm0.ne']
        ring
      rw [if_pos h]
      exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds
  -- Step 2: the `C^1` chain rule applied to `H_ε`
  have hFcont : ∀ ε : ℝ, 0 < ε → Continuous (FF ε) := fun ε hε => (hFC1 ε hε).continuous
  have hHd : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ,
      HasDerivAt (fun s => FF ε (s - c)) (DD ε (t - c)) t := by
    intro ε hε t
    simpa [Function.comp_def] using (hFd ε hε (t - c)).scomp t ((hasDerivAt_id t).sub_const c)
  have hHC1 : ∀ ε : ℝ, 0 < ε → ContDiff ℝ 1 (fun s => FF ε (s - c)) := by
    intro ε hε
    exact (hFC1 ε hε).comp (contDiff_id.sub contDiff_const)
  have hHderiv : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ,
      deriv (fun s => FF ε (s - c)) t = DD ε (t - c) :=
    fun ε hε t => (hHd ε hε t).deriv
  have W2 : ∀ ε : ℝ, 0 < ε →
      MemW1pOn n q Ω (fun x => FF ε (u x - c)) (fun x => DD ε (u x - c) • g x) := by
    intro ε hε
    have h := WeakGradientC1Comp n q 1 _hn hq zero_le_one Ω u g (fun s => FF ε (s - c))
      hΩ hvol hW (hHC1 ε hε) (fun t => by
        rw [hHderiv ε hε t, abs_of_nonneg (hD01 ε hε (t - c)).1]
        exact (hD01 ε hε (t - c)).2)
    have hfun : (fun x => deriv (fun s => FF ε (s - c)) (u x) • g x)
        = fun x => DD ε (u x - c) • g x := by
      funext x; rw [hHderiv ε hε (u x)]
    rwa [hfun] at h
  refine ⟨?_, hB, hC⟩
  intro φ hφ hφcs hφsupp i
  have hεm : ∀ m : ℕ, (0 : ℝ) < 1 / ((m : ℝ) + 1) := fun m => by positivity
  have hεlim : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- the compact support
  have hKcpt : IsCompact (tsupport φ) := hφcs
  have hKm : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
  have hfinK : IsFiniteMeasure (volume.restrict (tsupport φ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hKcpt.measure_lt_top⟩
  have hres : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      AEStronglyMeasurable f (volume.restrict Ω) →
      AEStronglyMeasurable f (volume.restrict (tsupport φ)) :=
    fun f hf => hf.mono_measure (Measure.restrict_mono hφsupp le_rfl)
  have hφc : Continuous φ := hφ.continuous
  have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφcs : HasCompactSupport
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) := hφcs.fderiv_apply ℝ _
  obtain ⟨Λ, hΛ⟩ := hdφcs.exists_bound_of_continuous hdφ
  obtain ⟨Λ', hΛ'⟩ := hφcs.exists_bound_of_continuous hφc
  have hΛ0 : 0 ≤ Λ := le_trans (norm_nonneg _) (hΛ 0)
  have hΛ'0 : 0 ≤ Λ' := le_trans (norm_nonneg _) (hΛ' 0)
  have huK : IntegrableOn u (tsupport φ) volume := hu1.mono_set hφsupp
  have hgK : IntegrableOn (fun x => g x i) (tsupport φ) volume := (hg1 i).mono_set hφsupp
  -- the Ω-to-K conversion
  have hΩK : ∀ h : EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ x, x ∉ tsupport φ → h x = 0) → (∫ x in Ω, h x) = ∫ x in tsupport φ, h x := by
    intro h hh
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)
        (fun x hx => hh x (fun k => hx (hφsupp k))),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport φ) hh]
  -- integrability of the four integrands on K
  have hdomU : IntegrableOn (fun x => Λ * (|u x| + |c|)) (tsupport φ) volume :=
    ((huK.abs.add (integrable_const _)).const_mul Λ)
  have hintF : ∀ ε : ℝ, 0 < ε →
      IntegrableOn (fun x => FF ε (u x - c) *
        fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) (tsupport φ) volume := by
    intro ε hε
    refine Integrable.mono' hdomU
      ((((hFcont ε hε).comp_aestronglyMeasurable
        ((hres u huLp.1).sub aestronglyMeasurable_const))).mul
          hdφ.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 : |FF ε (u x - c)| ≤ |u x| + |c| := by
      rcases hFnn ε hε (u x - c) with ⟨ha, hb⟩
      rw [abs_of_nonneg ha]
      refine hb.trans ?_
      rcases le_or_gt (u x - c) 0 with h | h
      · rw [max_eq_right h]; positivity
      · rw [max_eq_left h.le]
        have := abs_nonneg (u x); have := abs_nonneg c
        have h2 : u x ≤ |u x| := le_abs_self _
        have h3 : -c ≤ |c| := neg_le_abs c
        linarith
    calc ‖FF ε (u x - c) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))‖
        = |FF ε (u x - c)| * ‖fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))‖ := by
          rw [norm_mul, Real.norm_eq_abs]
      _ ≤ (|u x| + |c|) * Λ := by
          refine mul_le_mul h1 (hΛ x) (norm_nonneg _) (by positivity)
      _ = Λ * (|u x| + |c|) := by ring
  have hintMax : IntegrableOn (fun x => max (u x - c) 0 *
      fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) (tsupport φ) volume := by
    refine Integrable.mono' hdomU
      ((((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
        (hres u huLp.1)).mul hdφ.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 : |max (u x - c) 0| ≤ |u x| + |c| := by
      rcases le_or_gt (u x - c) 0 with h | h
      · rw [max_eq_right h]; simp; positivity
      · rw [max_eq_left h.le, abs_of_nonneg h.le]
        have h2 : u x ≤ |u x| := le_abs_self _
        have h3 : -c ≤ |c| := neg_le_abs c
        linarith
    calc ‖max (u x - c) 0 * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))‖
        = |max (u x - c) 0| * ‖fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))‖ := by
          rw [norm_mul, Real.norm_eq_abs]
      _ ≤ (|u x| + |c|) * Λ := mul_le_mul h1 (hΛ x) (norm_nonneg _) (by positivity)
      _ = Λ * (|u x| + |c|) := by ring
  have hdomG : IntegrableOn (fun x => Λ' * |g x i|) (tsupport φ) volume :=
    hgK.abs.const_mul Λ'
  have hintD : ∀ ε : ℝ, 0 < ε →
      IntegrableOn (fun x => DD ε (u x - c) * g x i * φ x) (tsupport φ) volume := by
    intro ε hε
    refine Integrable.mono' hdomG
      ((((hDcont ε).comp_aestronglyMeasurable
          ((hres u huLp.1).sub aestronglyMeasurable_const)).mul
        (hres _ (hgiLp i).1)).mul hφc.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rcases hD01 ε hε (u x - c) with ⟨ha, hb⟩
    calc ‖DD ε (u x - c) * g x i * φ x‖
        = |DD ε (u x - c)| * |g x i| * ‖φ x‖ := by
          rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 1 * |g x i| * Λ' := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (by rw [abs_of_nonneg ha]; exact hb)
            (abs_nonneg _)) (hΛ' x) (norm_nonneg _) (by positivity)
      _ = Λ' * |g x i| := by ring
  -- the identity (5) for each m, transported to K
  have h5 : ∀ m : ℕ,
      (∫ x in tsupport φ, FF (1 / ((m : ℝ) + 1)) (u x - c) *
        fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
      = -∫ x in tsupport φ, (DD (1 / ((m : ℝ) + 1)) (u x - c) * g x i) * φ x := by
    intro m
    obtain ⟨hwg2, -, -⟩ := W2 (1 / ((m : ℝ) + 1)) (hεm m)
    have h := hwg2 φ hφ hφcs hφsupp i
    rw [show (∫ x in Ω, (DD (1 / ((m : ℝ) + 1)) (u x - c) • g x) i * φ x)
        = ∫ x in Ω, (DD (1 / ((m : ℝ) + 1)) (u x - c) * g x i) * φ x from
      setIntegral_congr_fun hΩm fun x _ => by simp] at h
    rw [hΩK (fun x => FF (1 / ((m : ℝ) + 1)) (u x - c) *
          fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        (fun x hx => by
          have h0 : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx
          simp [h0]),
      hΩK (fun x => (DD (1 / ((m : ℝ) + 1)) (u x - c) * g x i) * φ x)
        (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx]; ring)] at h
    exact h
  -- the left-hand side converges
  have hLlim : Filter.Tendsto
      (fun m : ℕ => ∫ x in tsupport φ, FF (1 / ((m : ℝ) + 1)) (u x - c) *
        fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
      Filter.atTop
      (nhds (∫ x in tsupport φ, max (u x - c) 0 *
        fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))) := by
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm
      (a := fun m : ℕ => 1 / ((m : ℝ) + 1) / 2 * Λ * (volume (tsupport φ)).toReal)
      (fun m => ?_) ?_
    · rw [← integral_sub (hintF _ (hεm m)) hintMax]
      calc ‖∫ x in tsupport φ, (FF (1 / ((m : ℝ) + 1)) (u x - c) *
              fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))
              - max (u x - c) 0 * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))‖
          ≤ ∫ x in tsupport φ, |FF (1 / ((m : ℝ) + 1)) (u x - c) *
              fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))
              - max (u x - c) 0 * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))| := by
            rw [Real.norm_eq_abs]; exact abs_integral_le_integral_abs
        _ ≤ ∫ _x in tsupport φ, 1 / ((m : ℝ) + 1) / 2 * Λ := by
            refine integral_mono ((hintF _ (hεm m)).sub hintMax).abs
              (integrable_const _) fun x => ?_
            rw [← sub_mul, abs_mul]
            refine mul_le_mul (hF3 _ (hεm m) _)
              (by simpa [Real.norm_eq_abs] using hΛ x) (abs_nonneg _) (by positivity)
        _ = 1 / ((m : ℝ) + 1) / 2 * Λ * (volume (tsupport φ)).toReal := by
            rw [setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def]; ring
    · have h0 : Filter.Tendsto
          (fun m : ℕ => 1 / ((m : ℝ) + 1) / 2 * Λ * (volume (tsupport φ)).toReal)
          Filter.atTop (nhds (0 / 2 * Λ * (volume (tsupport φ)).toReal)) :=
        ((hεlim.div_const 2).mul_const Λ).mul_const _
      simpa using h0
  -- the right-hand side converges, by dominated convergence
  have hRlim : Filter.Tendsto
      (fun m : ℕ => ∫ x in tsupport φ,
        (DD (1 / ((m : ℝ) + 1)) (u x - c) * g x i) * φ x)
      Filter.atTop
      (nhds (∫ x in tsupport φ, (if c < u x then g x i else 0) * φ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => Λ' * |g x i|)
      (fun m => (hintD _ (hεm m)).1) hdomG
      (fun m => Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => ?_)
    · rcases hD01 _ (hεm m) (u x - c) with ⟨ha, hb⟩
      calc ‖DD (1 / ((m : ℝ) + 1)) (u x - c) * g x i * φ x‖
          = |DD (1 / ((m : ℝ) + 1)) (u x - c)| * |g x i| * ‖φ x‖ := by
            rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * |g x i| * Λ' := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right
              (by rw [abs_of_nonneg ha]; exact hb) (abs_nonneg _))
              (hΛ' x) (norm_nonneg _) (by positivity)
        _ = Λ' * |g x i| := by ring
    · have h1 := hD4 (u x - c)
      have h2 : (if 0 < u x - c then (1 : ℝ) else 0) = (if c < u x then (1 : ℝ) else 0) := by
        by_cases h : c < u x
        · rw [if_pos (by linarith : 0 < u x - c), if_pos h]
        · rw [if_neg (by simpa [sub_pos] using h), if_neg h]
      rw [h2] at h1
      have h3 := (h1.mul_const (g x i)).mul_const (φ x)
      rw [show (if c < u x then (1 : ℝ) else 0) * g x i * φ x
          = (if c < u x then g x i else 0) * φ x by
        by_cases h : c < u x <;> simp [h]] at h3
      exact h3
  -- conclude
  have hgoalL : (∫ x in Ω, max (u x - c) 0 *
        fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
      = ∫ x in tsupport φ, max (u x - c) 0 *
        fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) :=
    hΩK _ (fun x hx => by
      have h0 : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx
      simp [h0])
  have hgoalR : (∫ x in Ω, (if c < u x then g x else 0) i * φ x)
      = ∫ x in tsupport φ, (if c < u x then g x i else 0) * φ x := by
    rw [show (∫ x in Ω, (if c < u x then g x else 0) i * φ x)
        = ∫ x in Ω, (if c < u x then g x i else 0) * φ x from
      setIntegral_congr_fun hΩm fun x _ => by by_cases h : c < u x <;> simp [h]]
    exact hΩK _ (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx]; ring)
  show (∫ x in Ω, max (u x - c) 0 * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
      = -∫ x in Ω, (if c < u x then g x else 0) i * φ x
  rw [hgoalL, hgoalR]
  refine tendsto_nhds_unique hLlim ?_
  simp only [h5]
  exact hRlim.neg
