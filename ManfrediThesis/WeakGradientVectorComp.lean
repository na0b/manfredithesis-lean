import ManfrediThesis.Preamble
import ManfrediThesis.VectorChainRuleWeakGradientIdentity
import ManfrediThesis.ConvolutionFDerivWeakGradient
import ManfrediThesis.ConvolutionLqContraction
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MollifierLqConvergence
import ManfrediThesis.VectorChainRuleLimitPassage
open MeasureTheory

/-- Chain rule for a `C¹` function of several `W^{1,q}_loc ∩ L^∞_loc`
arguments: if each `G j` lies in `W^{1,q}_loc(Ω)` with weak gradient `DG j`, the
family is locally uniformly bounded, and `F : ℝᵐ → ℝ` is `C¹`, then
`F ∘ G ∈ W^{1,q}_loc(Ω)` with weak gradient `Σ_j (D_j F)(G) • DG j`. -/
theorem WeakGradientVectorComp :
    ∀ (n m : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ q →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (G : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
        (DG : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (F : (Fin m → ℝ) → ℝ),
        IsOpen Ω →
        (∀ j, MemW1pLocOn n q Ω (G j) (DG j)) →
        (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω →
          ∃ L : ℝ, ∀ x ∈ K, ∀ j, |G j x| ≤ L) →
        ContDiff ℝ 1 F →
        MemW1pLocOn n q Ω (fun x => F (fun j => G j x))
          (fun x => ∑ j, (fderiv ℝ F (fun i => G i x) (Pi.single j (1 : ℝ))) • DG j x) := by
  intro n m q _hn hq Ω G DG F hΩ hW hbdd hF
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hFc : Continuous F := hF.continuous
  have hFd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hFdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hsingle : ∀ j : Fin m, ‖(Pi.single j (1 : ℝ) : Fin m → ℝ)‖ ≤ 1 := by
    intro j
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
    by_cases h : k = j <;> simp [h]
  -- a single constant bounding `|F|` and every `|D_j F|` on the ball of radius `Lb`
  have hMM : ∀ Lb : ℝ, ∃ C : ℝ, 0 ≤ C
      ∧ (∀ y : Fin m → ℝ, ‖y‖ ≤ Lb → |F y| ≤ C)
      ∧ (∀ (y : Fin m → ℝ), ‖y‖ ≤ Lb → ∀ j,
          |fderiv ℝ F y (Pi.single j (1 : ℝ))| ≤ C) := by
    intro Lb
    obtain ⟨C0, hC0⟩ := (isCompact_closedBall (0 : Fin m → ℝ) Lb).exists_bound_of_continuousOn
      hFc.continuousOn
    obtain ⟨C1, hC1⟩ := (isCompact_closedBall (0 : Fin m → ℝ) Lb).exists_bound_of_continuousOn
      hFd.continuousOn
    refine ⟨max 0 (max C0 C1), le_max_left _ _, fun y hy => ?_, fun y hy j => ?_⟩
    · have := hC0 y (mem_closedBall_zero_iff.2 hy)
      rw [Real.norm_eq_abs] at this
      exact this.trans ((le_max_left C0 C1).trans (le_max_right _ _))
    · have h1 := hC1 y (mem_closedBall_zero_iff.2 hy)
      have h2 : |fderiv ℝ F y (Pi.single j (1 : ℝ))| ≤ ‖fderiv ℝ F y‖ * 1 := by
        refine le_trans ?_ (mul_le_mul_of_nonneg_left (hsingle j) (norm_nonneg _))
        simpa [Real.norm_eq_abs] using (fderiv ℝ F y).le_opNorm (Pi.single j (1 : ℝ))
      rw [mul_one] at h2
      exact h2.trans (h1.trans ((le_max_right C0 C1).trans (le_max_right _ _)))
  have hproj : ∀ k : Fin n, Continuous (fun y : EuclideanSpace ℝ (Fin n) => y k) :=
    fun k => (continuous_apply k).comp (PiLp.continuous_ofLp 2 _)
  have hcoord : ∀ (w : EuclideanSpace ℝ (Fin n)) (k : Fin n), ‖w k‖ ≤ ‖w‖ := by
    intro w k
    rw [EuclideanSpace.norm_eq, Real.norm_eq_abs,
      show |w k| = Real.sqrt (|w k| ^ 2) by rw [Real.sqrt_sq (abs_nonneg _)]]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (f := fun j => |w j| ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ k))
  have l1norm : ∀ h : EuclideanSpace ℝ (Fin n) → ℝ, AEStronglyMeasurable h volume →
      ∫ x, |h x| = (eLpNorm h 1 volume).toReal := by
    intro h hh
    rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm hh]
    simp [Real.norm_eq_abs]
  have hlin : ∀ (T : (Fin m → ℝ) →L[ℝ] ℝ) (a : Fin m → ℝ),
      T a = ∑ j, T (Pi.single j (1 : ℝ)) * a j := by
    intro T a
    conv_lhs => rw [← Finset.univ_sum_single a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (Pi.single j (a j) : Fin m → ℝ) = a j • (Pi.single j (1 : ℝ) : Fin m → ℝ) by
      funext k; by_cases h : k = j <;> simp [h], map_smul, smul_eq_mul, mul_comm]
  have hsetset : ∀ (A B : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ y, y ∉ A → h y = 0) → A ⊆ B → (∫ y in B, h y) = ∫ y in A, h y := by
    intro A B h hh hAB
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := B)
        (fun y hy => hh y (fun k => hy (hAB k))),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := A) hh]
  have step4b : ∀ (K3 : Set (EuclideanSpace ℝ (Fin n)))
      (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (Gf : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      HasWeakGradientOn n Ω f Gf → LocallyIntegrable (K3.indicator f) volume →
      ∀ (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (d : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ρ → HasCompactSupport ρ →
      tsupport ρ = Metric.closedBall 0 d →
      ∀ x : EuclideanSpace ℝ (Fin n), Metric.closedBall x d ⊆ K3 →
      Metric.closedBall x d ⊆ Ω → ∀ i : Fin n,
      fderiv ℝ (convolution (K3.indicator f) ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
          (EuclideanSpace.single i (1 : ℝ))
        = convolution (K3.indicator (fun z => Gf z i)) ρ
            (ContinuousLinearMap.lsmul ℝ ℝ) volume x :=
    ConvolutionFDerivWeakGradient n Ω hΩm hsetset
  refine ⟨?_, ?_⟩
  · -- the weak-gradient identity
    exact VectorChainRuleWeakGradientIdentity n m q _hn hq Ω G DG F hΩ hW hbdd hF
      hΩm hFc hFd hFdiff hMM hproj hcoord l1norm hlin hsetset step4b
  · -- Step 1: the local `L^q` bounds
    intro K hK hKΩ
    obtain ⟨L, hL⟩ := hbdd K hK hKΩ
    have hLb0 : (0 : ℝ) ≤ max L 0 := le_max_right _ _
    have hVK : ∀ x ∈ K, ‖(fun j => G j x : Fin m → ℝ)‖ ≤ max L 0 := fun x hx =>
      (pi_norm_le_iff_of_nonneg hLb0).2 fun j => by
        rw [Real.norm_eq_abs]
        exact le_trans (hL x hx j) (le_max_left _ _)
    obtain ⟨C, hC0, hCF, hCD⟩ := hMM (max L 0)
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    have hfinK : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
    have hGK : ∀ j, MemLp (G j) (ENNReal.ofReal q) (volume.restrict K) :=
      fun j => ((hW j).2 K hK hKΩ).1
    have hDGK : ∀ j, MemLp (DG j) (ENNReal.ofReal q) (volume.restrict K) :=
      fun j => ((hW j).2 K hK hKΩ).2
    have hVmeas : AEStronglyMeasurable (fun x => (fun j => G j x : Fin m → ℝ))
        (volume.restrict K) := by
      rw [aestronglyMeasurable_iff_aemeasurable]
      exact aemeasurable_pi_iff.2 fun j => (hGK j).1.aemeasurable
    refine ⟨?_, ?_⟩
    · exact MemLp.of_bound (hFc.comp_aestronglyMeasurable hVmeas) C
        (ae_restrict_of_forall_mem hKm fun x hx => by
          rw [Real.norm_eq_abs]; exact hCF _ (hVK x hx))
    · have hsum : (fun x => ∑ j, (fderiv ℝ F (fun i => G i x) (Pi.single j (1 : ℝ))) • DG j x)
          = ∑ j, (fun x => (fderiv ℝ F (fun i => G i x) (Pi.single j (1 : ℝ))) • DG j x) := by
        funext x; simp
      rw [hsum]
      refine memLp_finsetSum' _ fun j _ => ?_
      have hcj : AEStronglyMeasurable
          (fun x => fderiv ℝ F (fun i => G i x) (Pi.single j (1 : ℝ)))
          (volume.restrict K) := by
        have h := ((ContinuousLinearMap.apply ℝ ℝ
          (Pi.single j (1 : ℝ) : Fin m → ℝ)).continuous.comp
            hFd).comp_aestronglyMeasurable hVmeas
        simpa [Function.comp_def] using h
      refine MemLp.mono (g := fun x => C * ‖DG j x‖) ((hDGK j).norm.const_mul C)
        (hcj.smul (hDGK j).1) ?_
      refine ae_restrict_of_forall_mem hKm fun x hx => ?_
      rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hC0 (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hCD _ (hVK x hx) j) (norm_nonneg _)
