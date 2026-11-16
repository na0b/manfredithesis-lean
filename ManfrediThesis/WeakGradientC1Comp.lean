import ManfrediThesis.Preamble
import ManfrediThesis.ConvolutionLqContraction
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.MollifiedWeakGradientIdentity
import ManfrediThesis.MemW1pOn
import Mathlib.Analysis.Calculus.MeanValue
import ManfrediThesis.MollifierLqConvergence
open MeasureTheory

/-- Chain rule: a `C¹` function with bounded derivative composed with a
`W^{1,q}` function is again `W^{1,q}`, with the expected weak gradient. -/
theorem WeakGradientC1Comp :
    ∀ (n : ℕ) (q L : ℝ), 1 ≤ n → 1 ≤ q → 0 ≤ L →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (F : ℝ → ℝ),
        IsOpen Ω → volume Ω ≠ ⊤ →
        MemW1pOn n q Ω u g →
        ContDiff ℝ 1 F → (∀ t : ℝ, |deriv F t| ≤ L) →
        MemW1pOn n q Ω (fun x => F (u x)) (fun x => deriv F (u x) • g x) := by
  intro n q L _hn hq hL Ω u g F hΩ hvol hW hF hL'
  obtain ⟨hwg, huLp, hgLp⟩ := hW
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hfin : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hvol⟩
  have hFdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hFderivC : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hlip : ∀ s t : ℝ, |F s - F t| ≤ L * |s - t| := by
    have hLip : LipschitzWith L.toNNReal F :=
      lipschitzWith_of_nnnorm_deriv_le hFdiff (fun x => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hL, Real.norm_eq_abs]
        exact hL' x)
    intro s t
    simpa [Real.dist_eq, Real.coe_toNNReal _ hL] using hLip.dist_le_mul s t
  -- (B)
  have hB : MemLp (fun x => F (u x)) (ENNReal.ofReal q) (volume.restrict Ω) := by
    refine MemLp.mono (g := fun x => |F 0| + L * ‖u x‖)
      ((memLp_const (|F 0|)).add (huLp.norm.const_mul L))
      (hF.continuous.comp_aestronglyMeasurable huLp.1) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    have h2 := hlip (u x) 0
    simp only [sub_zero] at h2
    have h3 : |F (u x)| ≤ |F 0| + L * |u x| := by
      rcases abs_le.1 h2 with ⟨h4, h5⟩
      refine abs_le.2 ⟨by linarith [neg_abs_le (F 0)], by linarith [le_abs_self (F 0)]⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg hL (norm_nonneg _))),
      Real.norm_eq_abs]
    exact h3
  -- (C)
  have hC : MemLp (fun x => deriv F (u x) • g x) (ENNReal.ofReal q) (volume.restrict Ω) := by
    refine MemLp.mono (g := fun x => L * ‖g x‖) (hgLp.norm.const_mul L)
      ((hFderivC.comp_aestronglyMeasurable huLp.1).smul hgLp.1) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hL (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hL' _) (norm_nonneg _)
  -- L¹ facts
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
  have hu1 : Integrable (Ω.indicator u) volume :=
    (integrable_indicator_iff hΩm).2
      ((huLp.mono_exponent (ENNReal.one_le_ofReal.2 hq)).integrable le_rfl)
  have hg1 : ∀ i : Fin n, Integrable (Ω.indicator (fun x => g x i)) volume :=
    fun i => (integrable_indicator_iff hΩm).2
      (((hgiLp i).mono_exponent (ENNReal.one_le_ofReal.2 hq)).integrable le_rfl)
  -- the `L^1`-norm dictionary
  have l1norm : ∀ h : EuclideanSpace ℝ (Fin n) → ℝ, AEStronglyMeasurable h volume →
      ∫ x, |h x| = (eLpNorm h 1 volume).toReal := by
    intro h hh
    rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm hh]
    simp [Real.norm_eq_abs]
  -- Step 2: on the inner region the derivative of a mollification is the mollified
  -- weak gradient
  have step2 : ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ)
      (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      HasWeakGradientOn n Ω φ gφ → LocallyIntegrable φ volume →
      ∀ (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (d : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ρ → HasCompactSupport ρ →
      tsupport ρ = Metric.closedBall 0 d →
      ∀ x : EuclideanSpace ℝ (Fin n), Metric.closedBall x d ⊆ Ω → ∀ i : Fin n,
      fderiv ℝ (convolution φ ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
          (EuclideanSpace.single i (1 : ℝ))
        = convolution (Ω.indicator (fun z => gφ z i)) ρ
            (ContinuousLinearMap.lsmul ℝ ℝ) volume x :=
    MollifiedWeakGradientIdentity n Ω hΩ
  refine ⟨?_, hB, hC⟩
  -- the weak-gradient identity for the composition
  intro φ hφ hφcs hφsupp i
  -- Step 1: geometry and the mollifier family
  obtain ⟨δ₀, hδ₀0, hδ₀sub⟩ := hφcs.exists_cthickening_subset_open hΩ hφsupp
  have hδpos : ∀ m : ℕ, (0 : ℝ) < δ₀ / (m + 1) := fun m => by positivity
  have hδle : ∀ m : ℕ, δ₀ / (m + 1) ≤ δ₀ := by
    intro m
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) m, hδ₀0]
  have hδlim : Filter.Tendsto (fun m : ℕ => δ₀ / ((m : ℝ) + 1)) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ₀
  set B : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun m =>
    ⟨δ₀ / (m + 1) / 2, δ₀ / (m + 1), by positivity, by linarith [hδpos m]⟩ with hBdef
  set ρ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m => (B m).normed volume with hρdef
  have hρsmooth : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (ρ m) := fun m => (B m).contDiff_normed
  have hρnonneg : ∀ m x, 0 ≤ ρ m x := fun m x => (B m).nonneg_normed x
  have hρint : ∀ m, ∫ z, ρ m z = 1 := fun m => (B m).integral_normed
  have hρts : ∀ m, tsupport (ρ m) = Metric.closedBall 0 (δ₀ / (m + 1)) := by
    intro m
    simpa [hBdef] using
      (B m).tsupport_normed_eq (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
  have hρcs : ∀ m, HasCompactSupport (ρ m) := fun m => (B m).hasCompactSupport_normed
  have hρc : ∀ m, Continuous (ρ m) := fun m => (hρsmooth m).continuous
  have hballsub : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin n)), x ∈ tsupport φ →
      Metric.closedBall x (δ₀ / (m + 1)) ⊆ Ω := by
    intro m x hx y hy
    exact hδ₀sub (Metric.mem_cthickening_of_dist_le y x δ₀ _ hx
      (le_trans (by simpa using hy) (hδle m)))
  -- the zero-extended data
  have hwgbar : HasWeakGradientOn n Ω (Ω.indicator u) g := by
    intro ψ hψ hψcs hψsupp k
    rw [show (∫ y in Ω, (Ω.indicator u) y *
          fderiv ℝ ψ y (EuclideanSpace.single k (1 : ℝ)))
        = ∫ y in Ω, u y * fderiv ℝ ψ y (EuclideanSpace.single k (1 : ℝ)) from
      setIntegral_congr_fun hΩm fun y hy => by rw [Set.indicator_of_mem hy]]
    exact hwg ψ hψ hψcs hψsupp k
  have hubarloc : LocallyIntegrable (Ω.indicator u) volume := hu1.locallyIntegrable
  have hgbarloc : LocallyIntegrable (Ω.indicator (fun y => g y i)) volume :=
    (hg1 i).locallyIntegrable
  have hubarmem : MemLp (Ω.indicator u) 1 volume := memLp_one_iff_integrable.2 hu1
  have hgbarmem : MemLp (Ω.indicator (fun y => g y i)) 1 volume :=
    memLp_one_iff_integrable.2 (hg1 i)
  -- the contraction and the convergence at exponent 1
  have contract1 : ∀ (m : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ), MemLp w 1 volume →
      eLpNorm (convolution w (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume) 1 volume
        ≤ eLpNorm w 1 volume := by
    intro m w hw
    simpa [ENNReal.ofReal_one] using
      ConvolutionLqContraction n 1 le_rfl (ρ m) (hρc m) (hρnonneg m) (hρcs m)
        (hρint m) w
        (by simpa [ENNReal.ofReal_one] using hw)
  have hconvmem : ∀ (m : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ), MemLp w 1 volume →
      LocallyIntegrable w volume →
      Integrable (convolution w (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume) volume := by
    intro m w hw hwl
    refine memLp_one_iff_integrable.1 ⟨((hρcs m).contDiff_convolution_right _ hwl
      (hρsmooth m)).continuous.aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (contract1 m w hw) hw.2
  have converge1 : ∀ w : EuclideanSpace ℝ (Fin n) → ℝ, MemLp w 1 volume →
      Filter.Tendsto (fun m => eLpNorm
        (fun x => convolution w (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - w x)
        1 volume) Filter.atTop (nhds 0) := by
    intro w hw
    have hct : ∀ v : EuclideanSpace ℝ (Fin n) → ℝ,
        MemLp v (ENNReal.ofReal 1) volume → ∀ m,
        eLpNorm (convolution v (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume)
            (ENNReal.ofReal 1) volume ≤ eLpNorm v (ENNReal.ofReal 1) volume := by
      intro v hv m
      simpa [ENNReal.ofReal_one] using
        contract1 m v (by simpa [ENNReal.ofReal_one] using hv)
    simpa [ENNReal.ofReal_one] using
      MollifierLqConvergence n 1 _hn le_rfl ρ (fun m => δ₀ / ((m : ℝ) + 1)) hδlim hρsmooth hρnonneg hρcs
        (fun m => (hρts m).subset) hρint hct w (by simpa [ENNReal.ofReal_one] using hw)
  have l1 : ∀ w : EuclideanSpace ℝ (Fin n) → ℝ, MemLp w 1 volume →
      LocallyIntegrable w volume →
      Filter.Tendsto
        (fun m => ∫ x, |convolution w (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - w x|)
        Filter.atTop (nhds 0) := by
    intro w hw hwl
    have heq : ∀ m,
        (∫ x, |convolution w (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - w x|)
        = (eLpNorm (fun x =>
            convolution w (ρ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - w x)
            1 volume).toReal :=
      fun m => l1norm _ ((hconvmem m w hw hwl).1.sub hw.1)
    simp only [heq]
    simpa [Function.comp_def] using
      (ENNReal.tendsto_toReal (a := 0) (by simp)).comp (converge1 w hw)
  -- the almost-everywhere convergent subsequence
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top
    (p := (1 : ENNReal)) one_ne_zero ENNReal.one_ne_top
    (fun m => (hconvmem m _ hubarmem hubarloc).1) hu1.1
    (converge1 _ hubarmem)).exists_seq_tendsto_ae
  -- Step 3: the identity for the mollification
  have step3 : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
      ∀ G : EuclideanSpace ℝ (Fin n) → ℝ, Continuous G →
      (∀ x ∈ tsupport φ,
        fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)) = G x) →
      (∫ x in tsupport φ, F (f x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        = -∫ x in tsupport φ, (deriv F (f x) * G x) * φ x := by
    intro f hfsm G hGc hfd
    have hFdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
    have hFderivC : Continuous (deriv F) := hF.continuous_deriv le_rfl
    have hFf : ∀ x, HasFDerivAt (fun y => F (f y)) ((deriv F (f x)) • fderiv ℝ f x) x :=
      fun x => HasDerivAt.comp_hasFDerivAt x (hFdiff (f x)).hasDerivAt
        (hfsm.differentiable (by simp) x).hasFDerivAt
    have hFfd : ∀ x, fderiv ℝ (fun y => F (f y)) x = (deriv F (f x)) • fderiv ℝ f x :=
      fun x => (hFf x).fderiv
    have hφc : Continuous φ := hφ.continuous
    have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdφcs : HasCompactSupport
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) := hφcs.fderiv_apply ℝ _
    have hcont1 : Continuous
        (fun x => fderiv ℝ (fun y => F (f y)) x (EuclideanSpace.single i (1 : ℝ))) := by
      have he : (fun x => fderiv ℝ (fun y => F (f y)) x (EuclideanSpace.single i (1 : ℝ)))
          = fun x => deriv F (f x) * (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))) := by
        funext x; rw [hFfd x]; simp
      rw [he]
      exact (hFderivC.comp hfsm.continuous).mul
        ((hfsm.continuous_fderiv (by simp)).clm_apply continuous_const)
    have hFfc : Continuous (fun x => F (f x)) := hF.continuous.comp hfsm.continuous
    have hIBP : (∫ x, F (f x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        = -∫ x, fderiv ℝ (fun y => F (f y)) x (EuclideanSpace.single i (1 : ℝ)) * φ x :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        (f := fun y => F (f y)) (g := φ) (v := EuclideanSpace.single i (1 : ℝ))
        ((hcont1.mul hφc).integrable_of_hasCompactSupport (HasCompactSupport.mul_left hφcs))
        ((hFfc.mul hdφ).integrable_of_hasCompactSupport (HasCompactSupport.mul_left hdφcs))
        ((hFfc.mul hφc).integrable_of_hasCompactSupport (HasCompactSupport.mul_left hφcs))
        (fun x _ => (hFf x).differentiableAt)
        (fun x _ => hφ.differentiable (by simp) x)
    have hLhs : (∫ x in tsupport φ, F (f x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        = ∫ x, F (f x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      have h0 : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx
      simp [h0]
    have hR1 : (∫ x, fderiv ℝ (fun y => F (f y)) x (EuclideanSpace.single i (1 : ℝ)) * φ x)
        = ∫ x, (deriv F (f x) * (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)))) * φ x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [hFfd x]
    have hR2 : (∫ x in tsupport φ,
          (deriv F (f x) * (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)))) * φ x)
        = ∫ x, (deriv F (f x) * (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)))) * φ x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport hx]; ring
    have hR3 : (∫ x in tsupport φ,
          (deriv F (f x) * (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)))) * φ x)
        = ∫ x in tsupport φ, (deriv F (f x) * G x) * φ x :=
      setIntegral_congr_fun (isClosed_tsupport φ).measurableSet fun x hx => by rw [hfd x hx]
    rw [hLhs, hIBP, hR1, ← hR2, hR3]
  -- Steps 4 and 5: passing to the limit
  have limitpass : ∀ ubar gbar : EuclideanSpace ℝ (Fin n) → ℝ,
      Integrable ubar volume → Integrable gbar volume →
      ∀ U Gm : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ j, Continuous (U j)) → (∀ j, Continuous (Gm j)) →
      (∀ j, Integrable (U j) volume) → (∀ j, Integrable (Gm j) volume) →
      Filter.Tendsto (fun j => ∫ x, |U j x - ubar x|) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun j => ∫ x, |Gm j x - gbar x|) Filter.atTop (nhds 0) →
      (∀ᵐ x, Filter.Tendsto (fun j => U j x) Filter.atTop (nhds (ubar x))) →
      (∀ j, (∫ x in tsupport φ,
            F (U j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
          = -∫ x in tsupport φ, (deriv F (U j x) * Gm j x) * φ x) →
      (∫ x in tsupport φ, F (ubar x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        = -∫ x in tsupport φ, (deriv F (ubar x) * gbar x) * φ x := by
    intro ubar gbar hub hgb U Gm hUc hGc hUint hGint hu_l1 hg_l1 hae h5
    have hKcpt : IsCompact (tsupport φ) := hφcs
    have hKm : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
    have hfinK : IsFiniteMeasure (volume.restrict (tsupport φ)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKcpt.measure_lt_top⟩
    have hFdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
    have hFderivC : Continuous (deriv F) := hF.continuous_deriv le_rfl
    have hlip : ∀ s t : ℝ, |F s - F t| ≤ L * |s - t| := by
      have hLip : LipschitzWith L.toNNReal F :=
        lipschitzWith_of_nnnorm_deriv_le hFdiff (fun x => by
          rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hL, Real.norm_eq_abs]
          exact hL' x)
      intro s t
      simpa [Real.dist_eq, Real.coe_toNNReal _ hL] using hLip.dist_le_mul s t
    have hφc : Continuous φ := hφ.continuous
    have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdφcs : HasCompactSupport
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) := hφcs.fderiv_apply ℝ _
    obtain ⟨Λ, hΛ⟩ := hdφcs.exists_bound_of_continuous hdφ
    obtain ⟨Λ', hΛ'⟩ := hφcs.exists_bound_of_continuous hφc
    have hΛ0 : 0 ≤ Λ := le_trans (norm_nonneg _) (hΛ 0)
    have hΛ'0 : 0 ≤ Λ' := le_trans (norm_nonneg _) (hΛ' 0)
    -- integrability on the compact support
    have hintC : ∀ h : EuclideanSpace ℝ (Fin n) → ℝ, Continuous h →
        IntegrableOn h (tsupport φ) volume :=
      fun h hh => hh.continuousOn.integrableOn_compact hKcpt
    have hubK : IntegrableOn ubar (tsupport φ) volume := hub.integrableOn
    have hgbK : IntegrableOn gbar (tsupport φ) volume := hgb.integrableOn
    have hFub : IntegrableOn (fun x => F (ubar x) *
        fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) (tsupport φ) volume := by
      refine Integrable.mono' (g := fun x => Λ * (|F 0| + L * |ubar x|))
        (((integrable_const (|F 0|)).add (hubK.abs.const_mul L)).const_mul Λ)
        ((hF.continuous.comp_aestronglyMeasurable hub.1.restrict).mul
          hdφ.aestronglyMeasurable) ?_
      refine Filter.Eventually.of_forall fun x => ?_
      have h2 := hlip (ubar x) 0
      simp only [sub_zero] at h2
      have h3 : |F (ubar x)| ≤ |F 0| + L * |ubar x| := by
        rcases abs_le.1 h2 with ⟨h4, h5'⟩
        refine abs_le.2 ⟨by linarith [neg_abs_le (F 0)], by linarith [le_abs_self (F 0)]⟩
      calc ‖F (ubar x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))‖
          = |F (ubar x)| * ‖fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))‖ := by
            rw [norm_mul, Real.norm_eq_abs]
        _ ≤ (|F 0| + L * |ubar x|) * Λ := by
            refine mul_le_mul h3 (hΛ x) (norm_nonneg _) ?_
            exact le_trans (abs_nonneg _) h3
        _ = Λ * (|F 0| + L * |ubar x|) := by ring
    have hAj : ∀ j, IntegrableOn (fun x => (deriv F (U j x) * gbar x) * φ x)
        (tsupport φ) volume := by
      intro j
      refine Integrable.mono' (g := fun x => (L * Λ') * |gbar x|)
        (hgbK.abs.const_mul _)
        ((((hFderivC.comp (hUc j)).aestronglyMeasurable).mul hgb.1.restrict).mul
          hφc.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
      calc ‖deriv F (U j x) * gbar x * φ x‖
          = |deriv F (U j x)| * |gbar x| * |φ x| := by
            rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ L * |gbar x| * Λ' := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (hL' _) (abs_nonneg _))
              (by simpa [Real.norm_eq_abs] using hΛ' x) (abs_nonneg _) ?_
            exact mul_nonneg hL (abs_nonneg _)
        _ = L * Λ' * |gbar x| := by ring
    have hA : IntegrableOn (fun x => (deriv F (ubar x) * gbar x) * φ x)
        (tsupport φ) volume := by
      refine Integrable.mono' (g := fun x => (L * Λ') * |gbar x|)
        (hgbK.abs.const_mul _)
        ((((hFderivC.comp_aestronglyMeasurable hub.1.restrict)).mul hgb.1.restrict).mul
          hφc.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
      calc ‖deriv F (ubar x) * gbar x * φ x‖
          = |deriv F (ubar x)| * |gbar x| * |φ x| := by
            rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ L * |gbar x| * Λ' := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (hL' _) (abs_nonneg _))
              (by simpa [Real.norm_eq_abs] using hΛ' x) (abs_nonneg _) ?_
            exact mul_nonneg hL (abs_nonneg _)
        _ = L * Λ' * |gbar x| := by ring
    have hBj : ∀ j, IntegrableOn (fun x => (deriv F (U j x) * Gm j x) * φ x)
        (tsupport φ) volume :=
      fun j => hintC _ (((hFderivC.comp (hUc j)).mul (hGc j)).mul hφc)
    -- (L) the left-hand side converges
    have hLlim : Filter.Tendsto
        (fun j => ∫ x in tsupport φ,
          F (U j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        Filter.atTop
        (nhds (∫ x in tsupport φ,
          F (ubar x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))) := by
      rw [← tendsto_sub_nhds_zero_iff]
      refine squeeze_zero_norm (a := fun j => (L * Λ) * ∫ x, |U j x - ubar x|)
        (fun j => ?_) ?_
      · have hIU : IntegrableOn (fun x =>
            F (U j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
            (tsupport φ) volume := hintC _ ((hF.continuous.comp (hUc j)).mul hdφ)
        rw [← integral_sub hIU hFub]
        calc ‖∫ x in tsupport φ,
                (F (U j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))
                  - F (ubar x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))‖
            ≤ ∫ x in tsupport φ,
                |F (U j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))
                  - F (ubar x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))| := by
              rw [Real.norm_eq_abs]; exact abs_integral_le_integral_abs
          _ ≤ ∫ x in tsupport φ, (L * Λ) * |U j x - ubar x| := by
              refine integral_mono (hIU.sub hFub).abs
                ((((hUint j).sub hub).integrableOn.abs).const_mul _) fun x => ?_
              have e1 : F (U j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))
                  - F (ubar x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))
                  = (F (U j x) - F (ubar x)) *
                    fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) := by ring
              rw [e1, abs_mul]
              calc |F (U j x) - F (ubar x)| *
                    |fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))|
                  ≤ (L * |U j x - ubar x|) * Λ := by
                    refine mul_le_mul (hlip _ _)
                      (by simpa [Real.norm_eq_abs] using hΛ x) (abs_nonneg _) ?_
                    exact mul_nonneg hL (abs_nonneg _)
                _ = (L * Λ) * |U j x - ubar x| := by ring
          _ = (L * Λ) * ∫ x in tsupport φ, |U j x - ubar x| := integral_const_mul _ _
          _ ≤ (L * Λ) * ∫ x, |U j x - ubar x| := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hL hΛ0)
              exact setIntegral_le_integral (((hUint j).sub hub).abs)
                (Filter.Eventually.of_forall fun x => abs_nonneg _)
      · simpa using hu_l1.const_mul (L * Λ)
    -- (R1)
    have hR1 : Filter.Tendsto
        (fun j => ∫ x in tsupport φ, (deriv F (U j x) * (Gm j x - gbar x)) * φ x)
        Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm (a := fun j => (L * Λ') * ∫ x, |Gm j x - gbar x|)
        (fun j => ?_) ?_
      · have hI : IntegrableOn (fun x => (deriv F (U j x) * (Gm j x - gbar x)) * φ x)
            (tsupport φ) volume := by
          have he : (fun x => (deriv F (U j x) * (Gm j x - gbar x)) * φ x)
              = fun x => (deriv F (U j x) * Gm j x) * φ x
                - (deriv F (U j x) * gbar x) * φ x := by funext x; ring
          rw [he]; exact (hBj j).sub (hAj j)
        calc ‖∫ x in tsupport φ, (deriv F (U j x) * (Gm j x - gbar x)) * φ x‖
            ≤ ∫ x in tsupport φ, |(deriv F (U j x) * (Gm j x - gbar x)) * φ x| := by
              rw [Real.norm_eq_abs]; exact abs_integral_le_integral_abs
          _ ≤ ∫ x in tsupport φ, (L * Λ') * |Gm j x - gbar x| := by
              refine integral_mono hI.abs
                ((((hGint j).sub hgb).integrableOn.abs).const_mul _) fun x => ?_
              rw [abs_mul, abs_mul]
              calc |deriv F (U j x)| * |Gm j x - gbar x| * |φ x|
                  ≤ L * |Gm j x - gbar x| * Λ' := by
                    refine mul_le_mul (mul_le_mul_of_nonneg_right (hL' _) (abs_nonneg _))
                      (by simpa [Real.norm_eq_abs] using hΛ' x) (abs_nonneg _) ?_
                    exact mul_nonneg hL (abs_nonneg _)
                _ = (L * Λ') * |Gm j x - gbar x| := by ring
          _ = (L * Λ') * ∫ x in tsupport φ, |Gm j x - gbar x| := integral_const_mul _ _
          _ ≤ (L * Λ') * ∫ x, |Gm j x - gbar x| := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hL hΛ'0)
              exact setIntegral_le_integral (((hGint j).sub hgb).abs)
                (Filter.Eventually.of_forall fun x => abs_nonneg _)
      · simpa using hg_l1.const_mul (L * Λ')
    -- (R2) dominated convergence
    have hR2 : Filter.Tendsto
        (fun j => ∫ x in tsupport φ,
          ((deriv F (U j x) - deriv F (ubar x)) * gbar x) * φ x)
        Filter.atTop (nhds 0) := by
      have hd := tendsto_integral_of_dominated_convergence
        (μ := volume.restrict (tsupport φ))
        (F := fun j (x : EuclideanSpace ℝ (Fin n)) =>
          ((deriv F (U j x) - deriv F (ubar x)) * gbar x) * φ x)
        (f := fun _ => (0 : ℝ))
        (bound := fun x => (2 * L * Λ') * |gbar x|)
        (fun j =>
          ((((hFderivC.comp (hUc j)).aestronglyMeasurable).sub
            (hFderivC.comp_aestronglyMeasurable hub.1.restrict)).mul
              hgb.1.restrict).mul hφc.aestronglyMeasurable)
        (hgbK.abs.const_mul _)
        (fun j => Filter.Eventually.of_forall fun x => by
          calc ‖(deriv F (U j x) - deriv F (ubar x)) * gbar x * φ x‖
              = |deriv F (U j x) - deriv F (ubar x)| * |gbar x| * |φ x| := by
                rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
            _ ≤ (2 * L) * |gbar x| * Λ' := by
                refine mul_le_mul (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
                  (by simpa [Real.norm_eq_abs] using hΛ' x) (abs_nonneg _) ?_
                · have h1 := hL' (U j x)
                  have h2 := hL' (ubar x)
                  rcases abs_le.1 h1 with ⟨a1, b1⟩
                  rcases abs_le.1 h2 with ⟨a2, b2⟩
                  exact abs_le.2 ⟨by linarith, by linarith⟩
                · exact mul_nonneg (by linarith) (abs_nonneg _)
            _ = (2 * L * Λ') * |gbar x| := by ring)
        (by
          filter_upwards [ae_restrict_of_ae hae] with x hx
          have h1 : Filter.Tendsto (fun j => deriv F (U j x)) Filter.atTop
              (nhds (deriv F (ubar x))) := (hFderivC.tendsto _).comp hx
          have h0 : Filter.Tendsto (fun j => deriv F (U j x) - deriv F (ubar x))
              Filter.atTop (nhds 0) := by
            simpa using h1.sub_const (deriv F (ubar x))
          simpa using (h0.mul_const (gbar x)).mul_const (φ x))
      simpa using hd
    -- combine
    have hRsplit : ∀ j, (∫ x in tsupport φ, (deriv F (U j x) * Gm j x) * φ x)
        = (∫ x in tsupport φ, (deriv F (U j x) * (Gm j x - gbar x)) * φ x)
          + ((∫ x in tsupport φ, ((deriv F (U j x) - deriv F (ubar x)) * gbar x) * φ x)
          + (∫ x in tsupport φ, (deriv F (ubar x) * gbar x) * φ x)) := by
      intro j
      have hI1 : IntegrableOn (fun x => (deriv F (U j x) * (Gm j x - gbar x)) * φ x)
          (tsupport φ) volume := by
        have he : (fun x => (deriv F (U j x) * (Gm j x - gbar x)) * φ x)
            = fun x => (deriv F (U j x) * Gm j x) * φ x
              - (deriv F (U j x) * gbar x) * φ x := by funext x; ring
        rw [he]; exact (hBj j).sub (hAj j)
      have hI2 : IntegrableOn (fun x => ((deriv F (U j x) - deriv F (ubar x)) * gbar x) * φ x)
          (tsupport φ) volume := by
        have he : (fun x => ((deriv F (U j x) - deriv F (ubar x)) * gbar x) * φ x)
            = fun x => (deriv F (U j x) * gbar x) * φ x
              - (deriv F (ubar x) * gbar x) * φ x := by funext x; ring
        rw [he]; exact (hAj j).sub hA
      have hIBC : IntegrableOn (fun x =>
          ((deriv F (U j x) - deriv F (ubar x)) * gbar x) * φ x
            + (deriv F (ubar x) * gbar x) * φ x) (tsupport φ) volume := hI2.add hA
      rw [← integral_add hI2 hA, ← integral_add hI1 hIBC]
      refine setIntegral_congr_fun hKm fun x _ => ?_
      ring
    have hRlim : Filter.Tendsto
        (fun j => ∫ x in tsupport φ, (deriv F (U j x) * Gm j x) * φ x)
        Filter.atTop
        (nhds (∫ x in tsupport φ, (deriv F (ubar x) * gbar x) * φ x)) := by
      simp only [hRsplit]
      simpa using hR1.add (hR2.add
        (tendsto_const_nhds (x := ∫ x in tsupport φ, (deriv F (ubar x) * gbar x) * φ x)
          (f := Filter.atTop (α := ℕ))))
    have hLlim2 : Filter.Tendsto
        (fun j => ∫ x in tsupport φ,
          F (U j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        Filter.atTop
        (nhds (-∫ x in tsupport φ, (deriv F (ubar x) * gbar x) * φ x)) := by
      simp only [h5]
      exact hRlim.neg
    exact tendsto_nhds_unique hLlim hLlim2
  -- assembling the goal
  show (∫ x in Ω, F (u x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
      = -∫ x in Ω, (deriv F (u x) • g x) i * φ x
  have hgoalL : (∫ x in Ω, F (u x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
      = ∫ x in tsupport φ,
        F (Ω.indicator u x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω) (fun x hx => by
        have h0 : fderiv ℝ φ x = 0 :=
          fderiv_of_notMem_tsupport ℝ (fun h => hx (hφsupp h))
        simp [h0]),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport φ) (fun x hx => by
        have h0 : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx
        simp [h0])]
    refine setIntegral_congr_fun (isClosed_tsupport φ).measurableSet fun x hx => ?_
    rw [Set.indicator_of_mem (hφsupp hx)]
  have hgoalR : (∫ x in Ω, (deriv F (u x) • g x) i * φ x)
      = ∫ x in tsupport φ,
        (deriv F (Ω.indicator u x) * Ω.indicator (fun y => g y i) x) * φ x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω) (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφsupp h))]; ring),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport φ) (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport hx]; ring)]
    refine setIntegral_congr_fun (isClosed_tsupport φ).measurableSet fun x hx => ?_
    rw [Set.indicator_of_mem (hφsupp hx), Set.indicator_of_mem (hφsupp hx)]
    simp
  rw [hgoalL, hgoalR]
  refine limitpass (Ω.indicator u) (Ω.indicator (fun y => g y i)) hu1 (hg1 i)
    (fun j => convolution (Ω.indicator u) (ρ (ns j))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume)
    (fun j => convolution (Ω.indicator (fun y => g y i)) (ρ (ns j))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume)
    (fun j => ((hρcs (ns j)).contDiff_convolution_right _ hubarloc
      (hρsmooth (ns j))).continuous)
    (fun j => ((hρcs (ns j)).contDiff_convolution_right _ hgbarloc
      (hρsmooth (ns j))).continuous)
    (fun j => hconvmem (ns j) _ hubarmem hubarloc)
    (fun j => hconvmem (ns j) _ hgbarmem hgbarloc)
    ((l1 _ hubarmem hubarloc).comp hns.tendsto_atTop)
    ((l1 _ hgbarmem hgbarloc).comp hns.tendsto_atTop)
    hae (fun j => ?_)
  refine step3 _ ((hρcs (ns j)).contDiff_convolution_right _ hubarloc (hρsmooth (ns j))) _
    ((hρcs (ns j)).contDiff_convolution_right _ hgbarloc (hρsmooth (ns j))).continuous
    (fun x hx => step2 (Ω.indicator u) g hwgbar hubarloc (ρ (ns j))
      (δ₀ / ((ns j : ℝ) + 1)) (hρsmooth (ns j)) (hρcs (ns j)) (hρts (ns j)) x
      (hballsub (ns j) x hx) i)
