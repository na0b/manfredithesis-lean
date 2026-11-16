import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pLocOn
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
open MeasureTheory

/-- A `W^{1,q}_loc` function whose weak gradient agrees almost everywhere with a
continuous field has a representative that is classically differentiable at
every point of the open set, with that continuous field as its gradient.  This
is the `C^1` half of the implication `(i) ⟹ (ii)` in Theorems 4 and 6: the
paper's proof of clause (ii) cites only (4.10), which supplies the Hölder
control on the gradient and nothing about differentiability of `u` itself. -/
theorem WeakGradientContinuousRep :
    ∀ (n : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ q →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g gc : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        IsOpen Ω → MemW1pLocOn n q Ω u g → ContinuousOn gc Ω →
        (∀ᵐ x ∂(volume.restrict Ω), g x = gc x) →
        ∃ w : EuclideanSpace ℝ (Fin n) → ℝ,
          (∀ᵐ x ∂(volume.restrict Ω), u x = w x) ∧
            ∀ x ∈ Ω, DifferentiableAt ℝ w x ∧
              ∀ i : Fin n, fderiv ℝ w x (EuclideanSpace.single i (1 : ℝ)) = gc x i := by
  intro n q hn hq Ω u g gc hΩ hu hgc hae
  classical
  have hn0 : (0:ℝ) < (n : ℝ) := by
    have h1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcoord : ∀ (v : EuclideanSpace ℝ (Fin n)) (i : Fin n), |v i| ≤ ‖v‖ := by
    intro v i
    have h1 : (v i) ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (f := fun m => (v m) ^ 2)
        (fun m _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith [abs_nonneg (v i), norm_nonneg v, sq_abs (v i)]
  have hnorminner : ∀ v : EuclideanSpace ℝ (Fin n), ‖innerSL ℝ v‖ = ‖v‖ := by
    intro v; simp
  -- Step 7: an almost-everywhere equality of functions continuous on an open set
  -- is an equality at every point of it
  have hopen_null : ∀ (V : Set (EuclideanSpace ℝ (Fin n)))
      (F H : EuclideanSpace ℝ (Fin n) → ℝ),
      IsOpen V → ContinuousOn F V → ContinuousOn H V →
      (∀ᵐ y ∂(volume.restrict V), F y = H y) → ∀ y ∈ V, F y = H y := by
    intro V F H hV hF hH hVae y hy
    by_contra hne
    have hd0 : 0 < |F y - H y| := abs_pos.2 (sub_ne_zero.2 hne)
    have hcont : ContinuousOn (fun z => |F z - H z|) V := (hF.sub hH).abs
    have hca : ContinuousAt (fun z => |F z - H z|) y :=
      hcont.continuousAt (hV.mem_nhds hy)
    have hopenlt : IsOpen {t : ℝ | |F y - H y| / 2 < t} :=
      isOpen_lt continuous_const continuous_id
    have hmemnhds : {t : ℝ | |F y - H y| / 2 < t} ∈ nhds |F y - H y| := by
      refine hopenlt.mem_nhds ?_
      show |F y - H y| / 2 < |F y - H y|
      linarith
    have hev : ∀ᶠ z in nhds y, |F y - H y| / 2 < |F z - H z| := hca hmemnhds
    have hVev : ∀ᶠ z in nhds y, z ∈ V := hV.mem_nhds hy
    have hev2 : ∀ᶠ z in nhds y, z ∈ V ∧ |F y - H y| / 2 < |F z - H z| :=
      hVev.and hev
    obtain ⟨V', hV'sub, hV'open, hyV'⟩ := mem_nhds_iff.1 hev2
    have hpos : 0 < volume V' := hV'open.measure_pos volume ⟨y, hyV'⟩
    have hnull : volume ({z | ¬ F z = H z} ∩ V) = 0 := by
      rw [← Measure.restrict_apply' hV.measurableSet]
      exact hVae
    have hsub : V' ⊆ {z | ¬ F z = H z} ∩ V := by
      intro z hz
      obtain ⟨hzV, hzlt⟩ := hV'sub hz
      refine ⟨?_, hzV⟩
      intro hc
      rw [hc] at hzlt
      simp at hzlt
      linarith
    exact absurd (measure_mono_null hsub hnull) hpos.ne'
  -- Steps 2–6: the local construction on a ball whose doubled closed ball lies
  -- in `Ω`, producing a function equal to `u` a.e. there and differentiable at
  -- every point with Fréchet derivative the functional attached to `g_c`
  have hball : ∀ (z : EuclideanSpace ℝ (Fin n)) (σ : ℝ), 0 < σ →
      Metric.closedBall z (2 * σ) ⊆ Ω →
      ∃ W : EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ᵐ y ∂(volume.restrict (Metric.ball z σ)), u y = W y) ∧
          ∀ y ∈ Metric.ball z σ, HasFDerivAt W (innerSL ℝ (gc y)) y := by
    intro z σ hσ hKΩ
    -- Step 2: the truncations, integrable on all of `ℝⁿ`
    obtain ⟨K, hKdef⟩ : ∃ S : Set (EuclideanSpace ℝ (Fin n)),
        S = Metric.closedBall z (2 * σ) := ⟨_, rfl⟩
    have hKcpt : IsCompact K := by rw [hKdef]; exact isCompact_closedBall z (2 * σ)
    have hKsub : K ⊆ Ω := by rw [hKdef]; exact hKΩ
    have hKm : MeasurableSet K := hKcpt.isClosed.measurableSet
    obtain ⟨hULp, -⟩ := hu.2 K hKcpt hKsub
    have hKfin : IsFiniteMeasure (volume.restrict K) := by
      constructor
      rw [Measure.restrict_apply_univ]
      exact hKcpt.measure_lt_top
    have hq1 : (1 : ENNReal) ≤ ENNReal.ofReal q := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hq
    have hUint : IntegrableOn u K volume := MemLp.integrable hq1 hULp
    obtain ⟨uc, hucdef⟩ : ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
        f = K.indicator u := ⟨_, rfl⟩
    obtain ⟨gK, hgKdef⟩ : ∃ f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        f = K.indicator g := ⟨_, rfl⟩
    have hucInt : Integrable uc volume := by
      rw [hucdef]; exact hUint.integrable_indicator hKm
    have hucloc : LocallyIntegrable uc volume := hucInt.locallyIntegrable
    -- Step 3: on a point whose `d`-ball lies in `K`, the derivative of the
    -- mollification of `u` is the mollification of the weak gradient
    have step3 : ∀ (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (d : ℝ),
        ContDiff ℝ (⊤ : ℕ∞) ρ → HasCompactSupport ρ →
        tsupport ρ = Metric.closedBall 0 d →
        ∀ x : EuclideanSpace ℝ (Fin n), Metric.closedBall x d ⊆ K → ∀ i : Fin n,
        fderiv ℝ (convolution uc ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
            (EuclideanSpace.single i (1 : ℝ))
          = convolution (fun y => gK y i) ρ
              (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      intro ρ d hρsm hρcs hρts x hball i
      have hdρc : Continuous (fderiv ℝ ρ) := hρsm.continuous_fderiv (by simp)
      have hdρcs : HasCompactSupport (fderiv ℝ ρ) := hρcs.fderiv ℝ
      have hce : ConvolutionExists uc (fderiv ℝ ρ)
          (ContinuousLinearMap.precompR (EuclideanSpace ℝ (Fin n))
            (ContinuousLinearMap.lsmul ℝ ℝ)) volume :=
        hdρcs.convolutionExists_right _ hucloc hdρc
      have hFD := hρcs.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
        hucloc (hρsm.of_le (by simp)) x
      have hB : fderiv ℝ (convolution uc ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
          (EuclideanSpace.single i (1 : ℝ))
          = ∫ y, uc y * (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)) := by
        have hc := ContinuousLinearMap.integral_comp_comm
          (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))) (hce x)
        simp only [ContinuousLinearMap.apply_apply] at hc
        rw [hFD.fderiv, convolution_def, ← hc]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp [ContinuousLinearMap.precompR_apply]
      -- the translated kernel is a test function for `Ω`
      have hψsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => ρ (x - y)) :=
        hρsm.comp (contDiff_const.sub contDiff_id)
      have hρvan : ∀ w : EuclideanSpace ℝ (Fin n), d < ‖w‖ →
          ρ w = 0 ∧ fderiv ℝ ρ w = 0 := by
        intro w hw
        have hwn : w ∉ tsupport ρ := by
          rw [hρts]; simpa using not_le.2 hw
        exact ⟨image_eq_zero_of_notMem_tsupport hwn, fderiv_of_notMem_tsupport ℝ hwn⟩
      have hnormsub : ∀ y : EuclideanSpace ℝ (Fin n), ‖x - y‖ = dist y x := by
        intro y; rw [dist_eq_norm, ← norm_neg]; simp
      have hψts : tsupport (fun y => ρ (x - y)) ⊆ Metric.closedBall x d := by
        refine closure_minimal (fun y hy => ?_) Metric.isClosed_closedBall
        by_contra hy'
        have hgt : d < ‖x - y‖ := by
          rw [hnormsub y]; simpa using hy'
        exact hy (hρvan _ hgt).1
      have hψcs : HasCompactSupport (fun y => ρ (x - y)) :=
        IsCompact.of_isClosed_subset (isCompact_closedBall x d)
          (isClosed_tsupport _) hψts
      have hψΩ : tsupport (fun y => ρ (x - y)) ⊆ Ω :=
        (hψts.trans hball).trans hKsub
      have hψd : ∀ y, fderiv ℝ (fun y' => ρ (x - y')) y
          (EuclideanSpace.single i (1 : ℝ))
          = -((fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ))) := by
        intro y
        have h1 : HasFDerivAt (fun y' : EuclideanSpace ℝ (Fin n) => x - y')
            (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y :=
          (hasFDerivAt_id y).const_sub x
        have h2 : HasFDerivAt ρ (fderiv ℝ ρ (x - y)) (x - y) :=
          (hρsm.differentiable (by simp) (x - y)).hasFDerivAt
        have h3 : HasFDerivAt (fun y' => ρ (x - y'))
            ((fderiv ℝ ρ (x - y)).comp
              (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) y :=
          h2.comp y h1
        rw [h3.fderiv]
        simp
      have hWG := hu.1 (fun y => ρ (x - y)) hψsm hψcs hψΩ i
      have hL : (∫ y in Ω, u y *
            fderiv ℝ (fun y' => ρ (x - y')) y (EuclideanSpace.single i (1 : ℝ)))
          = -∫ y in Ω, u y * (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [← integral_neg]
        refine setIntegral_congr_fun hΩ.measurableSet fun y _ => ?_
        rw [hψd y]; ring
      rw [hL] at hWG
      have hC : (∫ y in Ω, u y * (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)))
          = ∫ y in Ω, g y i * ρ (x - y) := neg_inj.1 hWG
      -- both sides agree with the integrals over `ℝⁿ` against the truncations
      have hvanK : ∀ y : EuclideanSpace ℝ (Fin n), y ∉ K → d < ‖x - y‖ := by
        intro y hy
        by_contra h
        refine hy (hball ?_)
        rw [Metric.mem_closedBall, ← hnormsub y]
        exact not_lt.1 h
      have hvanΩ : ∀ y : EuclideanSpace ℝ (Fin n), y ∉ Ω → d < ‖x - y‖ :=
        fun y hy => hvanK y (fun hc => hy (hKsub hc))
      have hLfull : (∫ y in Ω,
            u y * (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)))
          = ∫ y, uc y * (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
          rw [(hρvan _ (hvanΩ y hy)).2]; simp)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        by_cases hyK : y ∈ K
        · simp only [hucdef, Set.indicator_of_mem hyK]
        · simp only [hucdef, Set.indicator_of_notMem hyK,
            (hρvan _ (hvanK y hyK)).2]
          simp
      have hRfull : (∫ y in Ω, g y i * ρ (x - y))
          = ∫ y, gK y i * ρ (x - y) := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
          rw [(hρvan _ (hvanΩ y hy)).1]; simp)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        by_cases hyK : y ∈ K
        · simp only [hgKdef, Set.indicator_of_mem hyK]
        · simp only [hgKdef, Set.indicator_of_notMem hyK,
            (hρvan _ (hvanK y hyK)).1]
          simp
      rw [hB, ← hLfull, hC, hRfull, convolution_def]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp [ContinuousLinearMap.lsmul_apply]
    -- the mollifier family at scales `d m = σ / (2(m+1))`
    obtain ⟨dm, hdmdef⟩ : ∃ s : ℕ → ℝ, s = fun m : ℕ => σ / (2 * ((m : ℝ) + 1)) := ⟨_, rfl⟩
    have hdm0 : ∀ m : ℕ, 0 < dm m := by
      intro m
      simp only [hdmdef]
      positivity
    have hdmle : ∀ m : ℕ, dm m ≤ σ / 2 := by
      intro m
      simp only [hdmdef]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h1 : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith only [h1, hσ]
    obtain ⟨Bm, hBmdef⟩ : ∃ f : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)),
        f = fun m => ⟨dm m / 2, dm m, by linarith [hdm0 m], by linarith [hdm0 m]⟩ :=
      ⟨_, rfl⟩
    obtain ⟨rho, hrhodef⟩ : ∃ f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
        f = fun m => (Bm m).normed volume := ⟨_, rfl⟩
    have hrhosm : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (rho m) := by
      intro m; simp only [hrhodef]; exact (Bm m).contDiff_normed
    have hrhocs : ∀ m, HasCompactSupport (rho m) := by
      intro m; simp only [hrhodef]; exact (Bm m).hasCompactSupport_normed
    have hrhots : ∀ m, tsupport (rho m) = Metric.closedBall 0 (dm m) := by
      intro m
      simp only [hrhodef]
      rw [(Bm m).tsupport_normed_eq]
      simp only [hBmdef]
    -- the mollifications and the mollified gradient field
    obtain ⟨Phi, hPhidef⟩ : ∃ f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
        f = fun m => convolution uc (rho m) (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      ⟨_, rfl⟩
    have hPhism : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (Phi m) := by
      intro m
      simp only [hPhidef]
      exact (hrhocs m).contDiff_convolution_right _ hucloc (hrhosm m)
    obtain ⟨V, hVdef⟩ : ∃ f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        f = fun m y => (WithLp.equiv 2 (Fin n → ℝ)).symm
          (fun i => convolution (fun w => gK w i) (rho m)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume y) := ⟨_, rfl⟩
    -- the inner ball on which every `d m`-ball stays inside `K`
    have hinner : ∀ (m : ℕ) (y : EuclideanSpace ℝ (Fin n)),
        y ∈ Metric.ball z σ → Metric.closedBall y (dm m) ⊆ K := by
      intro m y hy w hw
      rw [hKdef, Metric.mem_closedBall]
      rw [Metric.mem_ball] at hy
      rw [Metric.mem_closedBall] at hw
      have ht : dist w z ≤ dist w y + dist y z := dist_triangle _ _ _
      have h1 := hdmle m
      linarith
    -- the derivative of `Φ m` is the functional attached to `V m`
    have hfdid : ∀ (m : ℕ) (y : EuclideanSpace ℝ (Fin n)), y ∈ Metric.ball z σ →
        fderiv ℝ (Phi m) y = innerSL ℝ (V m y) := by
      intro m y hy
      refine ContinuousLinearMap.coe_injective
        ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext ?_)
      intro i
      have h1 : fderiv ℝ (Phi m) y (EuclideanSpace.single i (1 : ℝ))
          = convolution (fun w => gK w i) (rho m)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume y := by
        simp only [hPhidef]
        exact step3 (rho m) (dm m) (hrhosm m) (hrhocs m) (hrhots m) y
          (hinner m y hy) i
      have h2 : innerSL ℝ (V m y) (EuclideanSpace.single i (1 : ℝ))
          = convolution (fun w => gK w i) (rho m)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume y := by
        simp only [hVdef]
        simp [EuclideanSpace.inner_single_right]
      simpa using h1.trans h2.symm
    -- the kernel-first form of the two convolutions, which is what the bump
    -- lemmas of Mathlib are stated for
    have hswapU : ∀ (m : ℕ) (y : EuclideanSpace ℝ (Fin n)),
        Phi m y = convolution ((Bm m).normed volume) uc
          (ContinuousLinearMap.lsmul ℝ ℝ) volume y := by
      intro m y
      simp only [hPhidef, hrhodef]
      rw [convolution_def, convolution_eq_swap]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [ContinuousLinearMap.lsmul_apply]
      ring
    obtain ⟨gKc, hgKcdef⟩ : ∃ f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        f = K.indicator gc := ⟨_, rfl⟩
    have hgKae : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), gK w = gKc w := by
      have h1 : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          w ∈ Ω → g w = gc w := (ae_restrict_iff' hΩ.measurableSet).1 hae
      filter_upwards [h1] with w hw
      by_cases hwK : w ∈ K
      · simp only [hgKdef, hgKcdef, Set.indicator_of_mem hwK, hw (hKsub hwK)]
      · simp only [hgKdef, hgKcdef, Set.indicator_of_notMem hwK]
    have hswapG : ∀ (m : ℕ) (i : Fin n) (y : EuclideanSpace ℝ (Fin n)),
        convolution (fun w => gK w i) (rho m) (ContinuousLinearMap.lsmul ℝ ℝ) volume y
          = convolution ((Bm m).normed volume) (fun w => gKc w i)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume y := by
      intro m i y
      simp only [hrhodef]
      rw [convolution_def, convolution_eq_swap]
      refine integral_congr_ae ?_
      filter_upwards [hgKae] with t ht
      simp only [ContinuousLinearMap.lsmul_apply, ht]
      ring
    -- Step 4: the mollified gradient converges to `g_c` uniformly on `ball z σ`
    have hgKcmeas : ∀ i : Fin n,
        AEStronglyMeasurable (fun w => gKc w i)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      intro i
      have h1 : AEStronglyMeasurable gKc
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        rw [hgKcdef]
        exact (aestronglyMeasurable_indicator_iff hKm).2
          ((hgc.mono hKsub).aestronglyMeasurable hKm)
      exact (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable h1
    have hdmanti : ∀ a b : ℕ, a ≤ b → dm b ≤ dm a := by
      intro a b hab
      simp only [hdmdef]
      have h1 : (0:ℝ) < 2 * ((a : ℝ) + 1) := by positivity
      have h2 : (2 : ℝ) * ((a : ℝ) + 1) ≤ 2 * ((b : ℝ) + 1) := by
        have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.2 hab
        linarith
      rw [div_le_div_iff₀ (by positivity) h1]
      nlinarith only [h2, hσ]
    have hzK : ∀ y : EuclideanSpace ℝ (Fin n), y ∈ Metric.ball z σ → y ∈ K := by
      intro y hy
      rw [hKdef, Metric.mem_closedBall]
      rw [Metric.mem_ball] at hy
      linarith
    have hucont : UniformContinuousOn gc K :=
      hKcpt.uniformContinuousOn_of_continuous (hgc.mono hKsub)
    have step4 : ∀ η : ℝ, 0 < η → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ∀ y ∈ Metric.ball z σ, ‖V m y - gc y‖ ≤ η := by
      intro η hη
      obtain ⟨ε, hεdef⟩ : ∃ t : ℝ, t = η / (Real.sqrt n + 1) := ⟨_, rfl⟩
      have hsq0 : (0:ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
      have hε0 : 0 < ε := by rw [hεdef]; positivity
      obtain ⟨δ, hδ0, hδ⟩ := (Metric.uniformContinuousOn_iff.1 hucont) ε hε0
      obtain ⟨M, hM⟩ := exists_nat_gt (σ / (2 * δ))
      have hdmM : dm M < δ := by
        simp only [hdmdef]
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ (by positivity)] at hM
        nlinarith only [hM, hδ0, hσ]
      refine ⟨M, fun m hm y hy => ?_⟩
      have hdmm : dm m < δ := lt_of_le_of_lt (hdmanti M m hm) hdmM
      have hyK : y ∈ K := hzK y hy
      have hrOut : (Bm m).rOut = dm m := by simp only [hBmdef]
      -- the componentwise bound from Mathlib's bump estimate
      have hcomp : ∀ i : Fin n, |(V m y) i - gc y i| ≤ ε := by
        intro i
        have hball : ∀ x ∈ Metric.ball y (Bm m).rOut,
            dist (gKc x i) (gKc y i) ≤ ε := by
          intro x hx
          rw [hrOut] at hx
          have hxK : x ∈ K :=
            hinner m y hy (Metric.ball_subset_closedBall hx)
          have hdxy : dist x y < δ := lt_trans (Metric.mem_ball.1 hx) hdmm
          have h1 : dist (gc x) (gc y) < ε := hδ x hxK y hyK hdxy
          have h2 : |gc x i - gc y i| ≤ ‖gc x - gc y‖ := by
            have := hcoord (gc x - gc y) i
            have heq : (gc x - gc y) i = gc x i - gc y i := rfl
            rw [heq] at this
            exact this
          have h3 : dist (gKc x i) (gKc y i) = |gc x i - gc y i| := by
            simp only [hgKcdef, Set.indicator_of_mem hxK, Set.indicator_of_mem hyK,
              Real.dist_eq]
          rw [h3]
          rw [dist_eq_norm] at h1
          linarith
        have hmain := (Bm m).dist_normed_convolution_le (hgKcmeas i) hball
        have hVi : (V m y) i
            = convolution ((Bm m).normed volume) (fun w => gKc w i)
                (ContinuousLinearMap.lsmul ℝ ℝ) volume y := by
          rw [← hswapG m i y]
          simp only [hVdef]
          simp
        have hgy : gKc y i = gc y i := by
          simp only [hgKcdef, Set.indicator_of_mem hyK]
        rw [Real.dist_eq] at hmain
        rw [hVi, ← hgy]
        exact hmain
      -- from the `n` component bounds to the vector norm
      have hsum : ‖V m y - gc y‖ ^ 2 ≤ (Real.sqrt n * ε) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, mul_pow, Real.sq_sqrt hn0.le]
        calc ∑ i : Fin n, ((V m y - gc y) i) ^ 2 ≤ ∑ _i : Fin n, ε ^ 2 := by
              refine Finset.sum_le_sum (fun i _ => ?_)
              have hii : (V m y - gc y) i = (V m y) i - gc y i := rfl
              rw [hii]
              have h1 := hcomp i
              nlinarith only [h1, abs_nonneg ((V m y) i - gc y i),
                sq_abs ((V m y) i - gc y i)]
          _ = (n : ℝ) * ε ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hM0 : (0:ℝ) ≤ Real.sqrt n * ε := mul_nonneg hsq0 hε0.le
      have hfin : ‖V m y - gc y‖ ≤ Real.sqrt n * ε := by
        have h1 : Real.sqrt (‖V m y - gc y‖ ^ 2) ≤ Real.sqrt ((Real.sqrt n * ε) ^ 2) :=
          Real.sqrt_le_sqrt hsum
        rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hM0] at h1
      have hlast : Real.sqrt n * ε ≤ η := by
        rw [hεdef]
        rw [mul_div_assoc'] at *
        rw [div_le_iff₀ (by positivity)]
        nlinarith only [hsq0, hη]
      linarith
    -- Step 5: the mollifications converge to `u` almost everywhere
    have hdmlim : Filter.Tendsto dm Filter.atTop (nhds 0) := by
      simp only [hdmdef]
      have h2 := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (σ / 2)
      rw [mul_zero] at h2
      refine h2.congr (fun m => ?_)
      have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    have hrOutlim : Filter.Tendsto (fun m => (Bm m).rOut) Filter.atTop (nhds 0) := by
      simpa only [hBmdef] using hdmlim
    have hratio : ∀ᶠ m in Filter.atTop, (Bm m).rOut ≤ 2 * (Bm m).rIn := by
      refine Filter.Eventually.of_forall (fun m => ?_)
      simp only [hBmdef]
      linarith [hdm0 m]
    have hae5 : ∀ᵐ x₀ ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        Filter.Tendsto (fun m => Phi m x₀) Filter.atTop (nhds (uc x₀)) := by
      have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
        hrOutlim hratio hucloc
      filter_upwards [h] with x₀ hx₀
      exact Filter.Tendsto.congr (fun m => (hswapU m x₀).symm) hx₀
    have hzKball : ∀ y ∈ Metric.ball z σ, uc y = u y := by
      intro y hy
      simp only [hucdef, Set.indicator_of_mem (hzK y hy)]
    have hae5ball : ∀ᵐ y ∂(volume.restrict (Metric.ball z σ)),
        Filter.Tendsto (fun m => Phi m y) Filter.atTop (nhds (u y)) := by
      filter_upwards [ae_restrict_of_ae hae5, ae_restrict_mem measurableSet_ball]
        with y h1 h2
      rwa [hzKball y h2] at h1
    -- Step 6: the uniform limit of the derivatives, and the limit function
    have hTU : TendstoUniformlyOn (fun m => fderiv ℝ (Phi m))
        (fun y => innerSL ℝ (gc y)) Filter.atTop (Metric.ball z σ) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro η hη
      obtain ⟨M, hM⟩ := step4 (η / 2) (by linarith)
      refine Filter.eventually_atTop.2 ⟨M, fun m hm y hy => ?_⟩
      have he : dist (innerSL ℝ (gc y)) (innerSL ℝ (V m y)) = ‖gc y - V m y‖ := by
        rw [dist_eq_norm, ← hnorminner (gc y - V m y)]
        congr 1
        exact (map_sub (innerSL ℝ) (gc y) (V m y)).symm
      rw [hfdid m y hy, he]
      have h1 := hM m hm y hy
      have h2 : ‖gc y - V m y‖ = ‖V m y - gc y‖ := by
        rw [← norm_neg]; simp
      rw [h2]
      linarith
    have hHFD : ∀ (m : ℕ), ∀ y ∈ Metric.ball z σ,
        HasFDerivAt (Phi m) (fderiv ℝ (Phi m) y) y :=
      fun m y _ => ((hPhism m).differentiable (by simp) y).hasFDerivAt
    have hUC : UniformCauchySeqOn (fun m => fderiv ℝ (Phi m)) Filter.atTop
        (Metric.ball z σ) := hTU.uniformCauchySeqOn
    have hNBball : (ae (volume.restrict (Metric.ball z σ))).NeBot := by
      refine ⟨fun hb => ?_⟩
      rw [ae_eq_bot] at hb
      have h1 : volume (Metric.ball z σ) = 0 := by
        simpa using congrArg (fun mm => mm (Metric.ball z σ)) hb
      exact (Metric.measure_ball_pos volume z hσ).ne' h1
    obtain ⟨xs, hxs1, hxs2⟩ :=
      (hae5ball.and (ae_restrict_mem measurableSet_ball)).exists
    have hcauchy : ∀ y ∈ Metric.ball z σ, CauchySeq (fun m => Phi m y) := by
      intro y hy
      exact cauchy_map_of_uniformCauchySeqOn_fderiv Metric.isOpen_ball
        (convex_ball z σ).isPreconnected hUC hHFD hxs2 hy hxs1.cauchySeq
    obtain ⟨W, hWdef⟩ : ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
        f = fun y => Filter.limUnder Filter.atTop (fun m => Phi m y) := ⟨_, rfl⟩
    have hWlim : ∀ y ∈ Metric.ball z σ,
        Filter.Tendsto (fun m => Phi m y) Filter.atTop (nhds (W y)) := by
      intro y hy
      obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (hcauchy y hy)
      have hWy : W y = L := by
        simp only [hWdef]
        exact hL.limUnder_eq
      rw [hWy]
      exact hL
    refine ⟨W, ?_, ?_⟩
    · filter_upwards [hae5ball, ae_restrict_mem measurableSet_ball] with y h1 h2
      exact tendsto_nhds_unique h1 (hWlim y h2)
    · intro y hy
      exact hasFDerivAt_of_tendstoLocallyUniformlyOn Metric.isOpen_ball
        hTU.tendstoLocallyUniformlyOn hHFD hWlim hy
  -- Step 1: a radius at every point of `Ω`
  have hrad : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ Ω →
      ∃ s : ℝ, 0 < s ∧ Metric.closedBall x (2 * s) ⊆ Ω := by
    intro x hx
    obtain ⟨s, hs0, hsub⟩ := Metric.isOpen_iff.1 hΩ x hx
    refine ⟨s / 3, by linarith, ?_⟩
    exact subset_trans (Metric.closedBall_subset_ball (by linarith)) hsub
  choose! r hr0 hrsub using hrad
  have hballsub : ∀ x ∈ Ω, Metric.ball x (r x) ⊆ Ω := by
    intro x hx
    refine subset_trans ?_ (hrsub x hx)
    exact subset_trans Metric.ball_subset_closedBall
      (Metric.closedBall_subset_closedBall (by linarith [hr0 x hx]))
  -- the local functions
  have hWex : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ Ω →
      ∃ W : EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ᵐ y ∂(volume.restrict (Metric.ball x (r x))), u y = W y) ∧
          ∀ y ∈ Metric.ball x (r x), HasFDerivAt W (innerSL ℝ (gc y)) y :=
    fun x hx => hball x (r x) (hr0 x hx) (hrsub x hx)
  choose! W hWae hWder using hWex
  have hWcont : ∀ x ∈ Ω, ContinuousOn (W x) (Metric.ball x (r x)) :=
    fun x hx y hy => ((hWder x hx y hy).continuousAt).continuousWithinAt
  -- Step 8: the local functions agree pointwise on every overlap
  have hoverlap : ∀ x₁ ∈ Ω, ∀ x₂ ∈ Ω,
      ∀ y ∈ Metric.ball x₁ (r x₁) ∩ Metric.ball x₂ (r x₂), W x₁ y = W x₂ y := by
    intro x₁ h1 x₂ h2 y hy
    refine hopen_null (Metric.ball x₁ (r x₁) ∩ Metric.ball x₂ (r x₂)) (W x₁) (W x₂)
      (Metric.isOpen_ball.inter Metric.isOpen_ball)
      ((hWcont x₁ h1).mono Set.inter_subset_left)
      ((hWcont x₂ h2).mono Set.inter_subset_right) ?_ y hy
    have e1 : ∀ᵐ z ∂(volume.restrict
        (Metric.ball x₁ (r x₁) ∩ Metric.ball x₂ (r x₂))), u z = W x₁ z :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hWae x₁ h1)
    have e2 : ∀ᵐ z ∂(volume.restrict
        (Metric.ball x₁ (r x₁) ∩ Metric.ball x₂ (r x₂))), u z = W x₂ z :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hWae x₂ h2)
    filter_upwards [e1, e2] with z hz1 hz2
    rw [← hz1, ← hz2]
  -- the glued function
  obtain ⟨w, hwdef⟩ : ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
      f = fun y => if y ∈ Ω then W y y else 0 := ⟨_, rfl⟩
  have hwW : ∀ x ∈ Ω, ∀ y ∈ Metric.ball x (r x), w y = W x y := by
    intro x hx y hy
    have hyΩ : y ∈ Ω := hballsub x hx hy
    rw [hwdef]
    simp only [if_pos hyΩ]
    exact hoverlap y hyΩ x hx y ⟨Metric.mem_ball_self (hr0 y hyΩ), hy⟩
  refine ⟨w, ?_, ?_⟩
  · -- conclusion (a): `u = w` almost everywhere on `Ω`
    obtain ⟨T, hTc, hTu⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : ↥Ω => Metric.ball (x : EuclideanSpace ℝ (Fin n)) (r x))
      (fun _ => Metric.isOpen_ball)
    have hcov : Ω ⊆ ⋃ i ∈ T, Metric.ball (i : EuclideanSpace ℝ (Fin n)) (r i) := by
      intro y hy
      rw [hTu]
      exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball_self (hr0 y hy)⟩
    rw [ae_iff, Measure.restrict_apply' hΩ.measurableSet]
    have hnullU : volume (⋃ i ∈ T, ({a : EuclideanSpace ℝ (Fin n) | ¬ u a = w a}
        ∩ Metric.ball (i : EuclideanSpace ℝ (Fin n)) (r i))) = 0 := by
      refine (measure_biUnion_null_iff hTc).2 (fun i _ => ?_)
      have hiΩ : (i : EuclideanSpace ℝ (Fin n)) ∈ Ω := i.2
      rw [← Measure.restrict_apply' measurableSet_ball, ← ae_iff]
      filter_upwards [hWae i hiΩ, ae_restrict_mem measurableSet_ball] with y hy1 hy2
      rw [hwW i hiΩ y hy2]
      exact hy1
    refine measure_mono_null ?_ hnullU
    intro y hy
    obtain ⟨i, hiT, hiy⟩ := Set.mem_iUnion₂.1 (hcov hy.2)
    exact Set.mem_iUnion₂.2 ⟨i, hiT, ⟨hy.1, hiy⟩⟩
  · -- conclusion (b): `w` is differentiable with gradient `g_c` at every point
    intro x hx
    have hev : w =ᶠ[nhds x] W x := by
      filter_upwards
        [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hr0 x hx))] with y hy
      exact hwW x hx y hy
    have hd : HasFDerivAt w (innerSL ℝ (gc x)) x :=
      (hWder x hx x (Metric.mem_ball_self (hr0 x hx))).congr_of_eventuallyEq hev
    refine ⟨hd.differentiableAt, fun i => ?_⟩
    rw [hd.fderiv]
    simp [EuclideanSpace.inner_single_right]
