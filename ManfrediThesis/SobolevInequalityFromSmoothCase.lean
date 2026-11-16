import ManfrediThesis.Preamble
import ManfrediThesis.SmoothGradientFieldL2Facts
import ManfrediThesis.MemW1pOn
import ManfrediThesis.WeakGradientSmoothApprox
set_option maxHeartbeats 800000
open MeasureTheory

/-- The approximation passage for a scale-invariant Sobolev-type inequality on a
ball: an inequality
`(∫_{B_ρ}|Φ|^q)^{1/q} ≤ C₁ ρ^a (∫_{B_ρ}|∇Φ|²)^{1/2}`
known for every `C^∞` function `Φ` with compact support inside `B_ρ(x₀)`
extends, with the same constant and the same exponents, to every
`φ ∈ W^{1,2}(B_ρ(x₀))` with weak gradient `g_φ` and compact support inside the
ball.

The statement is generic in the exponent data `(q, a, C₁)`: it is applied once
at the exponent `q = 2n/(n-2)` with `a = 0` and once at `q = 4` with
`a = 1 - n/4`, which is why it is stated for arbitrary admissible `(q, a, C₁)`
rather than for one pair.

The passage is not a formality, because the smooth case controls the `L^q`
average of `Φ` by the `L²` average of its *classical* gradient while the
conclusion controls `φ` by its *weak* gradient `g_φ`, and the
approximating sequence converges only in `L²` on a compact set.  The proof runs
`WeakGradientSmoothApprox` to obtain a compact `K` with
`tsupport φ ⊆ K ⊆ B_ρ(x₀)` and smooth `Φ m` supported in `K` with
`Φ m → φ` and `∇Φ m → g_φ` in `L²(K)`, applies the smooth case to each `Φ m`,
passes to the limit on the right by the `L²` convergence of the gradients, and
on the left by Fatou's lemma along an almost everywhere convergent subsequence
of `Φ m` extracted from the `L²` convergence.  All the integrands vanish off
`K`, which is what lets every integral be read on `B_ρ(x₀)` and on `K`
interchangeably. -/
theorem SobolevInequalityFromSmoothCase :
    ∀ n : ℕ, 2 ≤ n →
      ∀ (q aa C₁ : ℝ), 1 < q → 0 ≤ aa → 0 < C₁ →
      (∀ (x₀ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
        (Φ : EuclideanSpace ℝ (Fin n) → ℝ),
        0 < ρ → ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
        tsupport Φ ⊆ Metric.ball x₀ ρ →
        (∫ x in Metric.ball x₀ ρ, |Φ x| ^ q) ^ (1 / q)
          ≤ C₁ * ρ ^ aa
            * (∫ x in Metric.ball x₀ ρ,
                ‖(WithLp.toLp 2 fun i =>
                    fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
                  EuclideanSpace ℝ (Fin n))‖ ^ 2) ^ (1 / 2 : ℝ)) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
        (φ : EuclideanSpace ℝ (Fin n) → ℝ)
        (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < ρ → MemW1pOn n 2 (Metric.ball x₀ ρ) φ gφ →
        HasCompactSupport φ → tsupport φ ⊆ Metric.ball x₀ ρ →
        (∫ x in Metric.ball x₀ ρ, |φ x| ^ q) ^ (1 / q)
          ≤ C₁ * ρ ^ aa
            * (∫ x in Metric.ball x₀ ρ, ‖gφ x‖ ^ 2) ^ (1 / 2 : ℝ) := by
  intro n hn q aa C₁ hq1 haa0 hC₁0 hsm x₀ ρ φ gφ hρ hW hcs hsupp
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hntriv : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, hnpos⟩ (1 : ℝ), ?_⟩⟩
    intro hc
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hnpos⟩) hc
    simp at h
  have hdictR : ∀ (r : ℝ), 0 < r → ∀ (S : Set (EuclideanSpace ℝ (Fin n)))
      (v : EuclideanSpace ℝ (Fin n) → ℝ),
      MemLp v (ENNReal.ofReal r) (volume.restrict S) →
      (eLpNorm v (ENNReal.ofReal r) (volume.restrict S)).toReal
        = (∫ x in S, |v x| ^ r) ^ (1 / r) := by
    intro r hr S v hv
    rw [hv.eLpNorm_eq_integral_rpow_norm (by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hr) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hr.le]
    simp only [Real.norm_eq_abs, one_div]
  have hdictV : ∀ (r : ℝ), 0 < r → ∀ (S : Set (EuclideanSpace ℝ (Fin n)))
      (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      MemLp v (ENNReal.ofReal r) (volume.restrict S) →
      (eLpNorm v (ENNReal.ofReal r) (volume.restrict S)).toReal
        = (∫ x in S, ‖v x‖ ^ r) ^ (1 / r) := by
    intro r hr S v hv
    rw [hv.eLpNorm_eq_integral_rpow_norm (by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hr) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hr.le]
    simp only [one_div]
  have hexpand : ∀ y : EuclideanSpace ℝ (Fin n),
      ∑ i : Fin n, y i • (EuclideanSpace.single i (1 : ℝ) :
        EuclideanSpace ℝ (Fin n)) = y := by
    intro y
    have h := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr y
    simpa [EuclideanSpace.basisFun_apply] using h
  have hnormsum : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ≤ ∑ i : Fin n, |v i| := by
    intro v
    calc ‖v‖ = ‖∑ i : Fin n, v i • (EuclideanSpace.single i (1 : ℝ) :
              EuclideanSpace ℝ (Fin n))‖ := by rw [hexpand]
      _ ≤ ∑ i : Fin n, ‖v i • (EuclideanSpace.single i (1 : ℝ) :
              EuclideanSpace ℝ (Fin n))‖ := norm_sum_le _ _
      _ = ∑ i : Fin n, |v i| := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
          simp
  -- integrals over a larger set agree when the integrand vanishes off the smaller one
  have hsetint : ∀ (S T : Set (EuclideanSpace ℝ (Fin n)))
      (F : EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ x, x ∉ S → F x = 0) → S ⊆ T → (∫ x in T, F x) = ∫ x in S, F x := by
    intro S T F hF hST
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hF x (fun hc => hx (hST hc))),
      setIntegral_eq_integral_of_forall_compl_eq_zero hF]
  -- the Riesz bridge: the operator norm of `dΦ` is at most the norm of the gradient vector
  have hnpow : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ^ (2 : ℝ) = ‖v‖ ^ 2 := by
    intro v
    rw [← Real.rpow_natCast ‖v‖ 2]
    norm_num
  obtain ⟨hgradcs, hcoord, hsqint, hone2⟩ := SmoothGradientFieldL2Facts n
  have hq0 : (0 : ℝ) < q := lt_trans one_pos hq1
  obtain ⟨K, Φ, hKcpt, hKsub, hφK, hΦsm, hΦcs, hΦK, hL2, hgradL2⟩ :=
    WeakGradientSmoothApprox n 2 (by omega) (by norm_num) (Metric.ball x₀ ρ) φ gφ
      Metric.isOpen_ball hW hcs hsupp
  have hKmeas : MeasurableSet K := hKcpt.measurableSet
  have hKfin : IsFiniteMeasure (volume.restrict K) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact hKcpt.measure_lt_top
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      G = fun m x => (WithLp.toLp 2 fun i =>
        fderiv ℝ (Φ m) x (EuclideanSpace.single i (1 : ℝ)) :
          EuclideanSpace ℝ (Fin n)) := ⟨_, rfl⟩
  have hsmG : ∀ m, (∫ x in Metric.ball x₀ ρ, |Φ m x| ^ q) ^ (1 / q)
      ≤ C₁ * ρ ^ aa * (∫ x in Metric.ball x₀ ρ, ‖G m x‖ ^ 2) ^ (1 / 2 : ℝ) := by
    intro m
    rw [hGdef]
    exact hsm x₀ ρ (Φ m) hρ (hΦsm m) (hΦcs m) ((hΦK m).trans hKsub)
  -- all the integrands vanish off `K`
  have hΦ0 : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin n)), x ∉ K → Φ m x = 0 := fun m x hx =>
    image_eq_zero_of_notMem_tsupport (fun hc => hx ((hΦK m) hc))
  have hφ0 : ∀ x : EuclideanSpace ℝ (Fin n), x ∉ K → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hc => hx (hφK hc))
  have hG0 : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin n)), x ∉ K → G m x = 0 := by
    intro m x hx
    obtain ⟨-, -, hGs⟩ := hgradcs (Φ m) (hΦsm m) (hΦcs m)
    rw [hGdef]
    exact hGs x (fun hc => hx ((hΦK m) hc))
  have hIΦ : ∀ m, (∫ x in Metric.ball x₀ ρ, |Φ m x| ^ q)
      = ∫ x in K, |Φ m x| ^ q := by
    intro m
    refine hsetint K (Metric.ball x₀ ρ) _ ?_ hKsub
    intro x hx
    rw [hΦ0 m x hx]
    simp [Real.zero_rpow (ne_of_gt hq0)]
  have hIφ : (∫ x in Metric.ball x₀ ρ, |φ x| ^ q) = ∫ x in K, |φ x| ^ q := by
    refine hsetint K (Metric.ball x₀ ρ) _ ?_ hKsub
    intro x hx
    rw [hφ0 x hx]
    simp [Real.zero_rpow (ne_of_gt hq0)]
  have hIG : ∀ m, (∫ x in Metric.ball x₀ ρ, ‖G m x‖ ^ 2)
      = ∫ x in K, ‖G m x‖ ^ 2 := by
    intro m
    refine hsetint K (Metric.ball x₀ ρ) _ ?_ hKsub
    intro x hx
    rw [hG0 m x hx]
    simp
  set Gn : ℝ := (∫ x in Metric.ball x₀ ρ, ‖gφ x‖ ^ 2) ^ (1 / 2 : ℝ) with hGndef
  have hGnn : (0 : ℝ) ≤ Gn := by
    rw [hGndef]
    exact Real.rpow_nonneg (integral_nonneg fun x => sq_nonneg _) _
  have hCρ : (0 : ℝ) ≤ C₁ * ρ ^ aa :=
    mul_nonneg hC₁0.le (Real.rpow_nonneg hρ.le _)
  -- (i) the `L²` error between the mollified gradient and `gφ`
  obtain ⟨ep, hep0, hepto, hepb⟩ : ∃ ep : ℕ → ℝ, (∀ m, 0 ≤ ep m) ∧
      Filter.Tendsto ep Filter.atTop (nhds 0) ∧
      ∀ m, (∫ x in K, ‖G m x‖ ^ 2) ^ (1 / 2 : ℝ) ≤ Gn + ep m := by
    have hgφK : MemLp gφ (ENNReal.ofReal 2) (volume.restrict K) :=
      hW.2.2.mono_measure (Measure.restrict_mono hKsub le_rfl)
    have hGmem : ∀ m, MemLp (G m) (ENNReal.ofReal 2) (volume.restrict K) := by
      intro m
      obtain ⟨hGc, hGcs', -⟩ := hgradcs (Φ m) (hΦsm m) (hΦcs m)
      have h1 : MemLp (fun x => (WithLp.toLp 2 fun i =>
            fderiv ℝ (Φ m) x (EuclideanSpace.single i (1 : ℝ)) :
          EuclideanSpace ℝ (Fin n))) (ENNReal.ofReal 2)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
        hGc.memLp_of_hasCompactSupport hGcs'
      rw [hGdef]
      exact h1.restrict _
    have hmeas : ∀ (m : ℕ) (i : Fin n), AEStronglyMeasurable
        (fun x => fderiv ℝ (Φ m) x (EuclideanSpace.single i (1 : ℝ)) - gφ x i)
        (volume.restrict K) := by
      intro m i
      have h1 : Continuous
          (fun x => fderiv ℝ (Φ m) x (EuclideanSpace.single i (1 : ℝ))) :=
        ((hΦsm m).continuous_fderiv (by simp)).clm_apply continuous_const
      have h2 : AEStronglyMeasurable (fun x => gφ x i) (volume.restrict K) := by
        have h3 := (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_aestronglyMeasurable
          hgφK.1
        exact h3
      exact h1.aestronglyMeasurable.sub h2
    have hcmem : ∀ (m : ℕ) (i : Fin n), MemLp
        (fun x => fderiv ℝ (Φ m) x (EuclideanSpace.single i (1 : ℝ)) - gφ x i)
        (ENNReal.ofReal 2) (volume.restrict K) := by
      intro m i
      refine MemLp.mono ((hGmem m).sub hgφK) (hmeas m i) ?_
      refine Filter.Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs]
      refine le_trans ?_ (hcoord (G m x - gφ x) i)
      rw [hGdef]
      simp
    refine ⟨fun m => ∑ i : Fin n,
      (∫ x in K, |fderiv ℝ (Φ m) x (EuclideanSpace.single i (1 : ℝ)) - gφ x i| ^ (2 : ℝ))
        ^ (1 / 2 : ℝ), ?_, ?_, ?_⟩
    · intro m
      refine Finset.sum_nonneg fun i _ => Real.rpow_nonneg ?_ _
      exact integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
    · have h0 : (0 : ℝ) = ∑ _i : Fin n, (0 : ℝ) := by simp
      rw [h0]
      refine tendsto_finsetSum _ fun i _ => ?_
      have h2 : Filter.Tendsto (fun a : ℝ => a ^ (1 / 2 : ℝ)) (nhds 0) (nhds 0) := by
        have h3 := (Real.continuousAt_rpow_const (0 : ℝ) (1 / 2 : ℝ)
          (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 2))).tendsto
        rwa [Real.zero_rpow (by norm_num)] at h3
      exact h2.comp (hgradL2 i)
    · intro m
      have hd1 : (∫ x in K, ‖G m x‖ ^ 2) ^ (1 / 2 : ℝ)
          = (eLpNorm (G m) (ENNReal.ofReal 2) (volume.restrict K)).toReal := by
        rw [hdictV 2 (by norm_num) K (G m) (hGmem m)]
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hnpow _).symm)
      have hd2 : (eLpNorm gφ (ENNReal.ofReal 2) (volume.restrict K)).toReal ≤ Gn := by
        rw [hdictV 2 (by norm_num) K gφ hgφK, hGndef]
        refine Real.rpow_le_rpow (integral_nonneg fun x =>
          Real.rpow_nonneg (norm_nonneg _) _) ?_ (by norm_num)
        rw [integral_congr_ae (Filter.Eventually.of_forall
          fun x => hnpow (gφ x))]
        exact setIntegral_mono_set (hsqint _ gφ hW.2.2)
          (Filter.Eventually.of_forall fun x => sq_nonneg _)
          (LE.le.eventuallyLE hKsub)
      have hmink : eLpNorm (G m) (ENNReal.ofReal 2) (volume.restrict K)
          ≤ eLpNorm gφ (ENNReal.ofReal 2) (volume.restrict K)
            + eLpNorm (fun x => G m x - gφ x) (ENNReal.ofReal 2)
              (volume.restrict K) := by
        have h := eLpNorm_add_le (f := gφ) (g := fun x => G m x - gφ x)
          (μ := volume.restrict K) (p := ENNReal.ofReal 2)
          hgφK.1 ((hGmem m).sub hgφK).1 hone2
        have heq : (gφ + fun x => G m x - gφ x) = G m := by
          funext x
          simp
        rwa [heq] at h
      have hco : eLpNorm (fun x => G m x - gφ x) (ENNReal.ofReal 2) (volume.restrict K)
          ≤ ∑ i : Fin n, eLpNorm
              (fun x => fderiv ℝ (Φ m) x (EuclideanSpace.single i (1 : ℝ)) - gφ x i)
              (ENNReal.ofReal 2) (volume.restrict K) := by
        have hptw : ∀ x, ‖G m x - gφ x‖
            ≤ ∑ i : Fin n,
              |fderiv ℝ (Φ m) x (EuclideanSpace.single i (1 : ℝ)) - gφ x i| := by
          intro x
          refine (hnormsum _).trans_eq ?_
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hGdef]
          simp
        calc eLpNorm (fun x => G m x - gφ x) (ENNReal.ofReal 2) (volume.restrict K)
            ≤ eLpNorm (fun x => ∑ i : Fin n,
                |fderiv ℝ (Φ m) x (EuclideanSpace.single i (1 : ℝ)) - gφ x i|)
                (ENNReal.ofReal 2) (volume.restrict K) := eLpNorm_mono_real hptw
          _ = eLpNorm (∑ i : Fin n, fun x =>
                |fderiv ℝ (Φ m) x (EuclideanSpace.single i (1 : ℝ)) - gφ x i|)
                (ENNReal.ofReal 2) (volume.restrict K) := by
                congr 1
                funext x
                rw [Finset.sum_apply]
          _ ≤ ∑ i : Fin n, eLpNorm (fun x =>
                |fderiv ℝ (Φ m) x (EuclideanSpace.single i (1 : ℝ)) - gφ x i|)
                (ENNReal.ofReal 2) (volume.restrict K) :=
              eLpNorm_sum_le (fun i _ =>
                continuous_abs.comp_aestronglyMeasurable (hmeas m i)) hone2
          _ = ∑ i : Fin n, eLpNorm (fun x =>
                fderiv ℝ (Φ m) x (EuclideanSpace.single i (1 : ℝ)) - gφ x i)
                (ENNReal.ofReal 2) (volume.restrict K) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              simp only [← Real.norm_eq_abs]
              exact eLpNorm_norm _
      -- to reals
      have hfin1 : eLpNorm gφ (ENNReal.ofReal 2) (volume.restrict K) ≠ ⊤ :=
        hgφK.eLpNorm_lt_top.ne
      have hfin2 : ∀ i : Fin n, eLpNorm
          (fun x => fderiv ℝ (Φ m) x (EuclideanSpace.single i (1 : ℝ)) - gφ x i)
          (ENNReal.ofReal 2) (volume.restrict K) ≠ ⊤ := fun i =>
        (hcmem m i).eLpNorm_lt_top.ne
      have hsumfin : (∑ i : Fin n, eLpNorm
          (fun x => fderiv ℝ (Φ m) x (EuclideanSpace.single i (1 : ℝ)) - gφ x i)
          (ENNReal.ofReal 2) (volume.restrict K)) ≠ ⊤ := by
        rw [Ne, ENNReal.sum_eq_top]
        intro hc
        obtain ⟨i, -, hi⟩ := hc
        exact hfin2 i hi
      have hcomb : eLpNorm (G m) (ENNReal.ofReal 2) (volume.restrict K)
          ≤ eLpNorm gφ (ENNReal.ofReal 2) (volume.restrict K)
            + ∑ i : Fin n, eLpNorm
              (fun x => fderiv ℝ (Φ m) x (EuclideanSpace.single i (1 : ℝ)) - gφ x i)
              (ENNReal.ofReal 2) (volume.restrict K) :=
        hmink.trans (add_le_add le_rfl hco)
      have htr := ENNReal.toReal_mono
        (ENNReal.add_ne_top.2 ⟨hfin1, hsumfin⟩) hcomb
      rw [ENNReal.toReal_add hfin1 hsumfin, ← hd1,
        ENNReal.toReal_sum (fun i _ => hfin2 i)] at htr
      refine htr.trans ?_
      refine add_le_add hd2 ?_
      refine Finset.sum_le_sum fun i _ => ?_
      exact le_of_eq (hdictR 2 (by norm_num) K _ (hcmem m i))
  have hbound : ∀ m, (∫ x in K, |Φ m x| ^ q) ^ (1 / q)
      ≤ C₁ * ρ ^ aa * (Gn + ep m) := by
    intro m
    have h1 := hsmG m
    rw [hIΦ m, hIG m] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (hepb m) hCρ)
  -- (ii) the limit passage on the left, by Fatou along an a.e. convergent subsequence
  have hfatou : (∫ x in K, |φ x| ^ q) ^ (1 / q) ≤ C₁ * ρ ^ aa * Gn := by
    have hA0 : (0 : ℝ) ≤ C₁ * ρ ^ aa * Gn := mul_nonneg hCρ hGnn
    have hbq : ∀ m, (∫ x in K, |Φ m x| ^ q)
        ≤ (C₁ * ρ ^ aa * (Gn + ep m)) ^ q := by
      intro m
      have hX0 : (0 : ℝ) ≤ ∫ x in K, |Φ m x| ^ q :=
        integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
      have h1 : ((∫ x in K, |Φ m x| ^ q) ^ (1 / q)) ^ q
          = ∫ x in K, |Φ m x| ^ q := by
        rw [← Real.rpow_mul hX0, one_div, inv_mul_cancel₀ (ne_of_gt hq0),
          Real.rpow_one]
      rw [← h1]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) (hbound m) hq0.le
    have hbto : Filter.Tendsto (fun m => (C₁ * ρ ^ aa * (Gn + ep m)) ^ q)
        Filter.atTop (nhds ((C₁ * ρ ^ aa * Gn) ^ q)) := by
      have h2 : Filter.Tendsto (fun m => Gn + ep m) Filter.atTop (nhds (Gn + 0)) :=
        Filter.Tendsto.const_add _ hepto
      rw [add_zero] at h2
      exact ((Real.continuousAt_rpow_const _ q (Or.inr hq0.le)).tendsto).comp
        (Filter.Tendsto.const_mul (C₁ * ρ ^ aa) h2)
    have hΦmemK : ∀ m, MemLp (Φ m) (ENNReal.ofReal 2) (volume.restrict K) := fun m =>
      ((hΦsm m).continuous.memLp_of_hasCompactSupport
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (hΦcs m)).restrict _
    have hφmemK : MemLp φ (ENNReal.ofReal 2) (volume.restrict K) :=
      hW.2.1.mono_measure (Measure.restrict_mono hKsub le_rfl)
    have hdiffmem : ∀ m, MemLp (Φ m - φ) (ENNReal.ofReal 2) (volume.restrict K) :=
      fun m => (hΦmemK m).sub hφmemK
    have h2ne : (ENNReal.ofReal 2) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; norm_num
    have hL2e : Filter.Tendsto
        (fun m => eLpNorm (Φ m - φ) (ENNReal.ofReal 2) (volume.restrict K))
        Filter.atTop (nhds 0) := by
      have hr : ∀ m, eLpNorm (Φ m - φ) (ENNReal.ofReal 2) (volume.restrict K)
          = ENNReal.ofReal ((∫ x in K, |Φ m x - φ x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
        intro m
        rw [← ENNReal.ofReal_toReal (hdiffmem m).eLpNorm_lt_top.ne,
          hdictR 2 (by norm_num) K (Φ m - φ) (hdiffmem m)]
        simp only [Pi.sub_apply]
      simp only [hr]
      have h2 : Filter.Tendsto (fun a : ℝ => a ^ (1 / 2 : ℝ)) (nhds 0) (nhds 0) := by
        have h3 := (Real.continuousAt_rpow_const (0 : ℝ) (1 / 2 : ℝ)
          (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 2))).tendsto
        rwa [Real.zero_rpow (by norm_num)] at h3
      have h4 : ENNReal.ofReal (0 : ℝ) = 0 := by simp
      rw [← h4]
      exact (ENNReal.continuous_ofReal.tendsto _).comp (h2.comp hL2)
    obtain ⟨ns, hnsmono, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top
      h2ne ENNReal.ofReal_ne_top (fun m => (hΦmemK m).1) hφmemK.1
      hL2e).exists_seq_tendsto_ae
    have hmeasF : ∀ l, AEMeasurable (fun x => ENNReal.ofReal (|Φ (ns l) x| ^ q))
        (volume.restrict K) := by
      intro l
      refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
      exact ((((hΦsm (ns l)).continuous).abs).rpow_const
        (fun _ => Or.inr hq0.le)).measurable
    have hliminf : ∀ᵐ x ∂(volume.restrict K),
        Filter.liminf (fun l => ENNReal.ofReal (|Φ (ns l) x| ^ q)) Filter.atTop
          = ENNReal.ofReal (|φ x| ^ q) := by
      filter_upwards [hae] with x hx
      have h1 : Filter.Tendsto (fun l => ENNReal.ofReal (|Φ (ns l) x| ^ q))
          Filter.atTop (nhds (ENNReal.ofReal (|φ x| ^ q))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp
          (((Real.continuousAt_rpow_const _ q (Or.inr hq0.le)).tendsto).comp hx.abs)
      exact h1.liminf_eq
    have hfat : (∫⁻ x in K, ENNReal.ofReal (|φ x| ^ q))
        ≤ Filter.liminf (fun l => ∫⁻ x in K, ENNReal.ofReal (|Φ (ns l) x| ^ q))
            Filter.atTop := by
      rw [← lintegral_congr_ae hliminf]
      exact lintegral_liminf_le' hmeasF
    have hterm : ∀ l, (∫⁻ x in K, ENNReal.ofReal (|Φ (ns l) x| ^ q))
        ≤ ENNReal.ofReal ((C₁ * ρ ^ aa * (Gn + ep (ns l))) ^ q) := by
      intro l
      have hcont : Continuous (fun x => |Φ (ns l) x| ^ q) :=
        (((hΦsm (ns l)).continuous).abs).rpow_const (fun _ => Or.inr hq0.le)
      have hcsq : HasCompactSupport (fun x => |Φ (ns l) x| ^ q) := by
        refine (hΦcs (ns l)).comp_left (g := fun t : ℝ => |t| ^ q) ?_
        simp [Real.zero_rpow (ne_of_gt hq0)]
      have hint : IntegrableOn (fun x => |Φ (ns l) x| ^ q) K volume :=
        (hcont.integrable_of_hasCompactSupport hcsq).restrict
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _)]
      exact ENNReal.ofReal_le_ofReal (hbq (ns l))
    have hlimb : Filter.liminf (fun l => ENNReal.ofReal
          ((C₁ * ρ ^ aa * (Gn + ep (ns l))) ^ q)) Filter.atTop
        = ENNReal.ofReal ((C₁ * ρ ^ aa * Gn) ^ q) :=
      Filter.Tendsto.liminf_eq
        ((ENNReal.continuous_ofReal.tendsto _).comp
          (hbto.comp hnsmono.tendsto_atTop))
    have hfinal : (∫⁻ x in K, ENNReal.ofReal (|φ x| ^ q))
        ≤ ENNReal.ofReal ((C₁ * ρ ^ aa * Gn) ^ q) := by
      refine hfat.trans ?_
      rw [← hlimb]
      exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hterm)
    by_cases hint : IntegrableOn (fun x => |φ x| ^ q) K volume
    · have h1 : ENNReal.ofReal (∫ x in K, |φ x| ^ q)
          ≤ ENNReal.ofReal ((C₁ * ρ ^ aa * Gn) ^ q) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _)]
        exact hfinal
      have h2 : (∫ x in K, |φ x| ^ q) ≤ (C₁ * ρ ^ aa * Gn) ^ q := by
        rwa [ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hA0 _)] at h1
      calc (∫ x in K, |φ x| ^ q) ^ (1 / q)
          ≤ ((C₁ * ρ ^ aa * Gn) ^ q) ^ (1 / q) :=
            Real.rpow_le_rpow (integral_nonneg fun x =>
              Real.rpow_nonneg (abs_nonneg _) _) h2 (by positivity)
        _ = C₁ * ρ ^ aa * Gn := by
            rw [← Real.rpow_mul hA0, mul_one_div, div_self (ne_of_gt hq0),
              Real.rpow_one]
    · rw [integral_undef hint,
        Real.zero_rpow (by positivity : (0:ℝ) < 1 / q).ne']
      exact hA0
  rw [hIφ]
  exact hfatou
