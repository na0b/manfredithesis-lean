import ManfrediThesis.Preamble
import ManfrediThesis.WeakSolutionTestClassExtension
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.WeakGradientDifferenceQuotient
import ManfrediThesis.WeakGradientVectorComp
import ManfrediThesis.WeakSecondDerivativeSymmetry
import ManfrediThesis.WeakGradientSmoothApprox
import ManfrediThesis.SmoothCompactSupportMemW1p
import ManfrediThesis.TranslatedTestPairAdmissible
import Mathlib.Geometry.Manifold.PartitionOfUnity
import ManfrediThesis.DifferenceQuotientLimitIdentity
open MeasureTheory

/-- The differentiated equation (3.2): the weak form of the equation obtained by
differentiating (3.1) in the direction `x_k`. -/
theorem DifferentiatedEquationWeak :
    ∀ (n : ℕ) (p ε γ₀ γ₁ : ℝ), 2 ≤ n → 1 < p → 0 < ε → 0 < γ₀ → γ₀ ≤ γ₁ →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        IsOpen Ω →
        EllipticStructureQ12 n p ε γ₀ γ₁ Ω (fun _ _ h => A h) →
        CitedRegularityEpsPos n p ε γ₀ γ₁ Ω A →
        IsWeakSolutionOn n p Ω (fun _ _ h => A h) (fun _ _ _ => 0) u g →
        (∀ i : Fin n, MemW1pLocOn n 2 Ω (fun x => g x i) (Dg i)) →
        ∀ (k : Fin n) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
          (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          MemW1pOn n 2 Ω φ gφ →
          HasCompactSupport φ → tsupport φ ⊆ Ω →
          (∫ x in Ω, ∑ i, ∑ j,
              (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i * Dg k x j * gφ x i)
            = 0 := by
  intro n p ε γ₀ γ₁ hn hp hε hγ₀ hγ Ω A u g Dg hΩ hQ hC1 hsol hDg k φ gφ hφW hφcs hφΩ
  have hn1 : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  -- the empty case
  rcases Set.eq_empty_or_nonempty Ω with hΩempty | hΩnonempty
  · simp [hΩempty]
  -- Step 0: `A` is `C¹` on all of `ℝⁿ`, because `ε > 0`
  have hAC1 : ContDiff ℝ 1 A := by
    obtain ⟨x₀, hx₀⟩ := hΩnonempty
    have h1 := hQ.hdiff x₀ hx₀ 0
    have h2 : {h : EuclideanSpace ℝ (Fin n) | ε + ‖h‖ ^ 2 ≠ 0} = Set.univ := by
      ext h
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      positivity
    rw [h2, contDiffOn_univ] at h1
    exact h1
  -- Step 1: what (C1) supplies
  obtain ⟨hu2, g', hg'c, hgg', Dg', hDg'⟩ := hC1 hε hQ u g hsol
  have hgg'0 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ∈ Ω → g x = g' x :=
    (ae_restrict_iff' hΩm).1 hgg'
  have hproj : ∀ i : Fin n, Continuous fun w : EuclideanSpace ℝ (Fin n) => w i :=
    fun i => (EuclideanSpace.proj i).continuous
  have hEext : ∀ v : EuclideanSpace ℝ (Fin n), (∀ i, v i = 0) → v = 0 := by
    intro v hv
    apply (EuclideanSpace.equiv (Fin n) ℝ).injective
    funext i
    simpa using hv i
  have hcoord : ∀ (w : EuclideanSpace ℝ (Fin n)) (j : Fin n), |w j| ≤ ‖w‖ := by
    intro w j
    rw [EuclideanSpace.norm_eq,
      show |w j| = Real.sqrt (|w j| ^ 2) by rw [Real.sqrt_sq (abs_nonneg _)]]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (f := fun l => |w l| ^ 2) (fun l _ => sq_nonneg _)
        (Finset.mem_univ j))
  -- an a.e. transport of `MemW1pLocOn` along equalities on `Ω`, used twice
  have htransport : ∀ (f1 f2 : EuclideanSpace ℝ (Fin n) → ℝ)
      (G1 G2 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ∈ Ω → f1 x = f2 x) →
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ∈ Ω → G1 x = G2 x) →
      MemW1pLocOn n 2 Ω f1 G1 → MemW1pLocOn n 2 Ω f2 G2 := by
    intro f1 f2 G1 G2 hf hG h1
    obtain ⟨hwg, hLp⟩ := h1
    refine ⟨?_, ?_⟩
    · intro ψ hψsm hψcs hψΩ i
      have e1 : (∫ x in Ω, f2 x * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))
          = ∫ x in Ω, f1 x * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) := by
        refine setIntegral_congr_ae hΩm ?_
        filter_upwards [hf] with x hx hxΩ
        rw [hx hxΩ]
      have e2 : (∫ x in Ω, G2 x i * ψ x) = ∫ x in Ω, G1 x i * ψ x := by
        refine setIntegral_congr_ae hΩm ?_
        filter_upwards [hG] with x hx hxΩ
        rw [hx hxΩ]
      rw [e1, e2]
      exact hwg ψ hψsm hψcs hψΩ i
    · intro K hKcpt hKΩ
      have hfK : f1 =ᵐ[volume.restrict K] f2 := by
        refine (ae_restrict_iff' hKcpt.measurableSet).2 ?_
        filter_upwards [hf] with x hx hxK
        exact hx (hKΩ hxK)
      have hGK : G1 =ᵐ[volume.restrict K] G2 := by
        refine (ae_restrict_iff' hKcpt.measurableSet).2 ?_
        filter_upwards [hG] with x hx hxK
        exact hx (hKΩ hxK)
      exact ⟨(hLp K hKcpt hKΩ).1.ae_eq hfK, (hLp K hKcpt hKΩ).2.ae_eq hGK⟩
  -- the two canonical maps between `Fin n → ℝ` and `EuclideanSpace ℝ (Fin n)`
  obtain ⟨Lin, hLinf, hLin⟩ : ∃ L : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n),
      (⇑L = fun z : Fin n → ℝ => (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin n))) ∧
      ∀ z, L z = WithLp.toLp 2 z :=
    ⟨(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap, rfl, fun _ => rfl⟩
  obtain ⟨Pr, hPrf, hPr⟩ : ∃ P : Fin n → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      (∀ i : Fin n, ⇑(P i) = fun w : EuclideanSpace ℝ (Fin n) => w i) ∧
      ∀ (i : Fin n) (w : EuclideanSpace ℝ (Fin n)), P i w = w i :=
    ⟨fun i => (ContinuousLinearMap.proj i).comp
      (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap, fun _ => rfl, fun _ _ => rfl⟩
  -- (0): the components of `g'` have the same weak gradients as those of `g`
  have hg'W : ∀ j : Fin n, MemW1pLocOn n 2 Ω (fun x => g' x j) (Dg j) := by
    intro j
    obtain ⟨hwg0, hLp0⟩ := hDg j
    refine ⟨?_, ?_⟩
    · intro ψ hψsm hψcs hψΩ i
      have h1 : (∫ x in Ω, g' x j *
            fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))
          = ∫ x in Ω, g x j *
            fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) := by
        refine setIntegral_congr_ae hΩm ?_
        filter_upwards [hgg'0] with x hx hxΩ
        rw [hx hxΩ]
      rw [h1]
      exact hwg0 ψ hψsm hψcs hψΩ i
    · intro K hKcpt hKΩ
      have haeK : (fun x => g x j) =ᵐ[volume.restrict K] (fun x => g' x j) := by
        refine (ae_restrict_iff' hKcpt.measurableSet).2 ?_
        filter_upwards [hgg'0] with x hx hxK
        rw [hx (hKΩ hxK)]
      exact ⟨(hLp0 K hKcpt hKΩ).1.ae_eq haeK, (hLp0 K hKcpt hKΩ).2⟩
  -- local uniform boundedness of the components of `g'`
  have hg'bdd : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω →
      ∃ L : ℝ, ∀ x ∈ K, ∀ j : Fin n, |g' x j| ≤ L := by
    intro K hKcpt hKΩ
    obtain ⟨L, hL⟩ := hKcpt.exists_bound_of_continuousOn (hg'c.mono hKΩ)
    exact ⟨L, fun x hx j => le_trans (hcoord (g' x) j) (hL x hx)⟩
  -- Step 2: the composite `Aⁱ ∘ ∇u` lies in `W^{1,2}_loc` with the chain-rule gradient
  have hstep2 : ∀ i : Fin n, MemW1pLocOn n 2 Ω (fun x => A (g x) i)
      (fun x => ∑ j, (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i • Dg j x) := by
    intro i
    -- the scalar function of `n` real arguments to which the chain rule is applied
    have hFC1 : ContDiff ℝ 1 (fun z : Fin n → ℝ => A (WithLp.toLp 2 z) i) := by
      have h : ContDiff ℝ 1 (fun z : Fin n → ℝ => Pr i (A (Lin z))) :=
        (Pr i).contDiff.comp (hAC1.comp (Lin).contDiff)
      have e : (fun z : Fin n → ℝ => Pr i (A (Lin z)))
          = fun z : Fin n → ℝ => A (WithLp.toLp 2 z) i := by
        funext z; rw [hPr, hLin]
      rwa [e] at h
    have hFd : ∀ (y : Fin n → ℝ) (j : Fin n),
        fderiv ℝ (fun z : Fin n → ℝ => A (WithLp.toLp 2 z) i) y (Pi.single j (1 : ℝ))
          = (fderiv ℝ A (WithLp.toLp 2 y) (EuclideanSpace.single j (1 : ℝ))) i := by
      intro y j
      have hL : HasFDerivAt
          (fun z : Fin n → ℝ => (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin n))) Lin y := by
        have h := Lin.hasFDerivAt (x := y)
        rw [hLinf] at h
        exact h
      have hA' : HasFDerivAt A (fderiv ℝ A (WithLp.toLp 2 y)) (WithLp.toLp 2 y) :=
        (hAC1.differentiable (by norm_num) _).hasFDerivAt
      have hP : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin n) => w i)
          (Pr i) (A (WithLp.toLp 2 y)) := by
        have h := (Pr i).hasFDerivAt (x := A (WithLp.toLp 2 y))
        rw [hPrf i] at h
        exact h
      have hcomp0 := hP.comp y (hA'.comp y hL)
      have hcomp : HasFDerivAt (fun z : Fin n → ℝ => A (WithLp.toLp 2 z) i)
          ((Pr i).comp ((fderiv ℝ A (WithLp.toLp 2 y)).comp Lin)) y := hcomp0
      rw [hcomp.fderiv]
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hPr, hLin]
      rfl
    -- the chain rule, for the continuous representative
    have hVC := WeakGradientVectorComp n n 2 hn1 one_le_two Ω (fun j x => g' x j) Dg
      (fun z : Fin n → ℝ => A (WithLp.toLp 2 z) i) hΩ hg'W hg'bdd hFC1
    have htoLp : ∀ x : EuclideanSpace ℝ (Fin n),
        (WithLp.toLp 2 (fun j => g' x j) : EuclideanSpace ℝ (Fin n)) = g' x := fun _ => rfl
    have h1 : MemW1pLocOn n 2 Ω (fun x => A (g' x) i)
        (fun x => ∑ j, (fderiv ℝ A (g' x) (EuclideanSpace.single j (1 : ℝ))) i • Dg j x) := by
      have e1 : (fun x => (fun z : Fin n → ℝ => A (WithLp.toLp 2 z) i) (fun j => g' x j))
          = fun x => A (g' x) i := rfl
      have e2 : (fun x => ∑ j, (fderiv ℝ (fun z : Fin n → ℝ => A (WithLp.toLp 2 z) i)
            (fun i' => g' x i') (Pi.single j (1 : ℝ))) • Dg j x)
          = fun x => ∑ j,
            (fderiv ℝ A (g' x) (EuclideanSpace.single j (1 : ℝ))) i • Dg j x := by
        funext x
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hFd (fun i' => g' x i') j]
      rw [← e1, ← e2]
      exact hVC
    -- transport back to `g`
    refine htransport _ _ _ _ ?_ ?_ h1
    · filter_upwards [hgg'0] with x hx hxΩ
      rw [hx hxΩ]
    · filter_upwards [hgg'0] with x hx hxΩ
      rw [hx hxΩ]
  -- the composite `Aⁱ ∘ g` is a.e. bounded on every compact subset of `Ω`
  have hΨbdd : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        x ∈ K → ∀ i : Fin n, |A (g x) i| ≤ M := by
    intro K hKcpt hKΩ
    obtain ⟨L, hL⟩ := hKcpt.exists_bound_of_continuousOn (hg'c.mono hKΩ)
    obtain ⟨M, hM⟩ :=
      IsCompact.exists_bound_of_continuousOn
        (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) L)
        hAC1.continuous.continuousOn
    refine ⟨max M 0, le_max_right _ _, ?_⟩
    filter_upwards [hgg'0] with x hx hxK i
    rw [hx (hKΩ hxK)]
    calc |A (g' x) i| ≤ ‖A (g' x)‖ := hcoord _ i
      _ ≤ M := hM _ (by rw [Metric.mem_closedBall, dist_zero_right]; exact hL x hxK)
      _ ≤ max M 0 := le_max_left _ _
  -- shrinking the domain of a set integral when the integrand vanishes outside
  have hsetset : ∀ (S T : Set (EuclideanSpace ℝ (Fin n))) (w : EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ y, y ∉ S → w y = 0) → S ⊆ T → (∫ y in T, w y) = ∫ y in S, w y := by
    intro S T w hw hST
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := T)
        (fun y hy => hw y fun hc => hy (hST hc)),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) hw]
  -- the real-`rpow` / `lintegral` dictionary at exponent 2, and finiteness
  have hcq2 : Continuous (fun t : ℝ => |t| ^ (2:ℝ)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (Real.continuousAt_rpow_const _ _
      (Or.inr (by norm_num : (0:ℝ) ≤ 2))).comp continuous_abs.continuousAt
  have h2z : (ENNReal.ofReal 2) ≠ 0 := by simp
  have h2t : (ENNReal.ofReal 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h2r : (ENNReal.ofReal 2).toReal = 2 := by simp
  -- Cauchy–Schwarz on an arbitrary set, for two `L²` factors
  have hCS : ∀ (S : Set (EuclideanSpace ℝ (Fin n))) (F G : EuclideanSpace ℝ (Fin n) → ℝ),
      MemLp F (ENNReal.ofReal 2) (volume.restrict S) →
      MemLp G (ENNReal.ofReal 2) (volume.restrict S) →
      (∫ y in S, |F y * G y|)
        ≤ Real.sqrt (∫ y in S, |F y| ^ (2:ℝ))
          * Real.sqrt (∫ y in S, |G y| ^ (2:ℝ)) := by
    intro S F G hF hG
    have hdict : ∀ u : EuclideanSpace ℝ (Fin n) → ℝ,
        AEStronglyMeasurable u (volume.restrict S) →
        (∫ y in S, |u y| ^ (2:ℝ)) = (∫⁻ y in S, ‖u y‖ₑ ^ (2:ℝ)).toReal := by
      intro u hu
      rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (abs_nonneg _) _)
        (hcq2.comp_aestronglyMeasurable hu)]
      refine congrArg ENNReal.toReal (lintegral_congr fun y => ?_)
      rw [← ofReal_norm, Real.norm_eq_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    have hfin : ∀ u : EuclideanSpace ℝ (Fin n) → ℝ,
        MemLp u (ENNReal.ofReal 2) (volume.restrict S) →
        (∫⁻ y in S, ‖u y‖ₑ ^ (2:ℝ)) ≠ ⊤ := by
      intro u hu
      have h1 := hu.eLpNorm_lt_top
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2z h2t, h2r] at h1
      intro hc
      rw [hc, ENNReal.top_rpow_of_pos (by norm_num)] at h1
      exact absurd h1 (by simp)
    have hconj : (2:ℝ).HolderConjugate (2:ℝ) :=
      Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
    have hHold := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict S) hconj
      (hF.1.enorm : AEMeasurable _ _) (hG.1.enorm : AEMeasurable _ _)
    simp only [Pi.mul_apply] at hHold
    have hprodtop : ((∫⁻ y in S, ‖F y‖ₑ ^ (2:ℝ)) ^ (1/(2:ℝ))
        * (∫⁻ y in S, ‖G y‖ₑ ^ (2:ℝ)) ^ (1/(2:ℝ))) ≠ ⊤ :=
      ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hfin F hF))
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hfin G hG))
    calc (∫ y in S, |F y * G y|)
        = (∫⁻ y in S, ‖F y‖ₑ * ‖G y‖ₑ).toReal := by
          have hm : AEStronglyMeasurable (fun y => F y * G y) (volume.restrict S) :=
            hF.1.mul hG.1
          have h1 : (∫ y in S, ‖F y * G y‖)
              = (∫⁻ y in S, ‖F y * G y‖ₑ).toReal :=
            integral_norm_eq_lintegral_enorm hm
          simp only [Real.norm_eq_abs] at h1
          rw [h1]
          refine congrArg ENNReal.toReal (lintegral_congr fun y => ?_)
          rw [enorm_mul]
      _ ≤ ((∫⁻ y in S, ‖F y‖ₑ ^ (2:ℝ)) ^ (1/(2:ℝ))
            * (∫⁻ y in S, ‖G y‖ₑ ^ (2:ℝ)) ^ (1/(2:ℝ))).toReal :=
          ENNReal.toReal_mono hprodtop hHold
      _ = Real.sqrt (∫ y in S, |F y| ^ (2:ℝ))
            * Real.sqrt (∫ y in S, |G y| ^ (2:ℝ)) := by
          rw [ENNReal.toReal_mul, hdict F hF.1, hdict G hG.1,
            ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
            Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  -- the product of two `L²` factors is integrable
  have hintL2 : ∀ (S : Set (EuclideanSpace ℝ (Fin n))) (F G : EuclideanSpace ℝ (Fin n) → ℝ),
      MemLp F (ENNReal.ofReal 2) (volume.restrict S) →
      MemLp G (ENNReal.ofReal 2) (volume.restrict S) →
      IntegrableOn (fun y => F y * G y) S volume := by
    intro S F G hF hG
    have hFr : Integrable (fun y => ‖F y‖ ^ (2:ℝ)) (volume.restrict S) := by
      have := hF.integrable_norm_rpow h2z h2t
      rwa [h2r] at this
    have hGr : Integrable (fun y => ‖G y‖ ^ (2:ℝ)) (volume.restrict S) := by
      have := hG.integrable_norm_rpow h2z h2t
      rwa [h2r] at this
    refine Integrable.mono' (hFr.add hGr) (hF.1.mul hG.1) ?_
    filter_upwards with y
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
    have e : ∀ t : ℝ, |t| ^ (2:ℝ) = |t| * |t| := by
      intro t
      rw [show (2:ℝ) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [e, e]
    nlinarith [abs_nonneg (F y), abs_nonneg (G y),
      sq_nonneg (|F y| - |G y|)]
  -- Step 3: a weak gradient vanishes off the support
  have hstep3 : ∀ (ψ₀ : EuclideanSpace ℝ (Fin n) → ℝ)
      (g₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      MemW1pOn n 2 Ω ψ₀ g₀ → HasCompactSupport ψ₀ → tsupport ψ₀ ⊆ Ω →
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        x ∈ Ω → x ∉ tsupport ψ₀ → g₀ x = 0 := by
    intro ψ₀ g₀ hW0 hcs0 hsupp0
    obtain ⟨hwg0, hψLp, hgLp⟩ := hW0
    have hUopen : IsOpen (Ω \ tsupport ψ₀) := hΩ.sdiff (isClosed_tsupport ψ₀)
    have hUΩ : Ω \ tsupport ψ₀ ⊆ Ω := Set.sdiff_subset
    have hcomp : ∀ i : Fin n, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        x ∈ Ω \ tsupport ψ₀ → g₀ x i = 0 := by
      intro i
      refine hUopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero ?_ ?_
      · -- local integrability of the `i`-th component on `Ω \ supp ψ₀`
        refine (locallyIntegrableOn_iff hUopen.isLocallyClosed).2 ?_
        intro K hKU hKcpt
        have hfin : IsFiniteMeasure (volume.restrict K) := by
          refine ⟨?_⟩
          rw [Measure.restrict_apply_univ]
          exact hKcpt.measure_lt_top
        have h1 : MemLp g₀ (ENNReal.ofReal 2) (volume.restrict K) :=
          hgLp.mono_measure (Measure.restrict_mono (hKU.trans hUΩ) le_rfl)
        have h2 : Integrable g₀ (volume.restrict K) :=
          h1.integrable (ENNReal.one_le_ofReal.2 one_le_two)
        refine Integrable.mono' h2.norm
          ((hproj i).comp_aestronglyMeasurable h2.1) ?_
        filter_upwards with x
        rw [Real.norm_eq_abs]
        exact hcoord (g₀ x) i
      · -- the pairing against every test function supported in `Ω \ supp ψ₀` vanishes
        intro χ hχsm hχcs hχU
        have hχΩ : tsupport χ ⊆ Ω := hχU.trans hUΩ
        have hWG := hwg0 χ (by exact_mod_cast hχsm) hχcs hχΩ i
        have hL : (∫ x in Ω, ψ₀ x *
            fderiv ℝ χ x (EuclideanSpace.single i (1 : ℝ))) = 0 := by
          have hz : ∀ x, ψ₀ x * fderiv ℝ χ x (EuclideanSpace.single i (1 : ℝ)) = 0 := by
            intro x
            by_cases hx : x ∈ tsupport χ
            · have h0 : ψ₀ x = 0 :=
                image_eq_zero_of_notMem_tsupport (hχU hx).2
              rw [h0, zero_mul]
            · rw [fderiv_of_notMem_tsupport ℝ hx]; simp
          simp [hz]
        rw [hL] at hWG
        have hR : (∫ x in Ω, g₀ x i * χ x) = 0 := by linarith [hWG]
        have hcommute : (fun x => χ x • g₀ x i) = fun x => g₀ x i * χ x := by
          funext x; rw [smul_eq_mul, mul_comm]
        rw [hcommute, ← hR]
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
        have h0 : χ x = 0 :=
          image_eq_zero_of_notMem_tsupport fun hc => hx (hχΩ hc)
        rw [h0, mul_zero]
    have hall : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ∀ i : Fin n, x ∈ Ω \ tsupport ψ₀ → g₀ x i = 0 := ae_all_iff.2 hcomp
    filter_upwards [hall] with x hx hxΩ hxn
    exact hEext _ fun i => hx i ⟨hxΩ, hxn⟩
  -- Step 4: (1.2) extends to the `W^{1,2}` test class with compact support
  have hstep4 : ∀ (ψ₀ : EuclideanSpace ℝ (Fin n) → ℝ)
      (g₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      MemW1pOn n 2 Ω ψ₀ g₀ → HasCompactSupport ψ₀ → tsupport ψ₀ ⊆ Ω →
      (∫ x in Ω, ∑ i, A (g x) i * g₀ x i) = 0 :=
    WeakSolutionTestClassExtension n p Ω A u g Dg hp hΩ hn1 hΩm hsol hproj hcoord
      hstep2 hsetset hCS hintL2 hstep3
  -- Step 5a: geometry
  obtain ⟨δ, hδ0, hδsub⟩ : ∃ δ : ℝ, 0 < δ ∧
      Metric.cthickening (3 * δ) (tsupport φ) ⊆ Ω := by
    obtain ⟨dd, hdd0, hddsub⟩ := hφcs.exists_cthickening_subset_open hΩ hφΩ
    refine ⟨dd / 3, by positivity, ?_⟩
    rw [show 3 * (dd / 3) = dd by ring]
    exact hddsub
  have hK0m : MeasurableSet (tsupport φ) := hφcs.isClosed.measurableSet
  have hnormsmul : ∀ s : ℝ,
      ‖s • EuclideanSpace.single k (1 : ℝ)‖ = |s| := by
    intro s
    rw [norm_smul, Real.norm_eq_abs]
    simp
  have hKδcpt : IsCompact (Metric.cthickening δ (tsupport φ)) := hφcs.cthickening
  have hKδΩ : Metric.cthickening δ (tsupport φ) ⊆ Ω :=
    (Metric.cthickening_mono (by linarith) _).trans hδsub
  have hshiftK : ∀ (y : EuclideanSpace ℝ (Fin n)) (s : ℝ), y ∈ tsupport φ → |s| ≤ δ →
      y + s • EuclideanSpace.single k (1 : ℝ) ∈ Metric.cthickening δ (tsupport φ) := by
    intro y s hy hs
    refine Metric.mem_cthickening_of_dist_le _ y δ _ hy ?_
    rw [dist_eq_norm]
    simpa [hnormsmul] using hs
  -- translating an a.e. statement
  have htransae : ∀ (P : EuclideanSpace ℝ (Fin n) → Prop) (c : EuclideanSpace ℝ (Fin n)),
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), P x) →
      ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), P (y + c) := by
    intro P c hP
    have h1 : {y : EuclideanSpace ℝ (Fin n) | ¬ P (y + c)}
        = (fun y => y + c) ⁻¹' {x | ¬ P x} := rfl
    have h2 : volume ((fun y : EuclideanSpace ℝ (Fin n) => y + c) ⁻¹' {x | ¬ P x}) = 0 := by
      rw [measure_preimage_add_right volume c]
      exact hP
    exact h2
  -- the continuous representative of the composite
  have hΨ'cont : ∀ i : Fin n, ContinuousOn (fun x => A (g' x) i) Ω := fun i =>
    (hproj i).comp_continuousOn (hAC1.continuous.comp_continuousOn hg'c)
  -- the truncated gradient of `φ`
  have hĝ : ∀ᵐ x ∂(volume.restrict Ω),
      (tsupport φ).indicator gφ x = gφ x := by
    refine (ae_restrict_iff' hΩm).2 ?_
    filter_upwards [hstep3 φ gφ hφW hφcs hφΩ] with x hx hxΩ
    by_cases hxs : x ∈ tsupport φ
    · rw [Set.indicator_of_mem hxs]
    · rw [Set.indicator_of_notMem hxs, hx hxΩ hxs]
  -- Step 6: the translated pair lies in the test class of Step 4.  This is
  -- `TranslatedTestPairAdmissible`, whose docstring records the route (the
  -- measure-preserving translation, and the smooth cut-off `χ` that repairs the
  -- support of the translated test function).
  have hstep6 := TranslatedTestPairAdmissible n Ω hΩ k φ gφ hφW hφcs hφΩ
    (hstep3 φ gφ hφW hφcs hφΩ) δ hδ0 hδsub
  -- measurability on `tsupport φ`, through the continuous representative
  have hgK0 : ∀ᵐ y ∂(volume.restrict (tsupport φ)), g y = g' y := by
    refine (ae_restrict_iff' hK0m).2 ?_
    filter_upwards [hgg'0] with x hx hxK
    exact hx (hφΩ hxK)
  have hgshiftK : ∀ h : ℝ, |h| ≤ δ → ∀ᵐ y ∂(volume.restrict (tsupport φ)),
      g (y + h • EuclideanSpace.single k (1 : ℝ))
        = g' (y + h • EuclideanSpace.single k (1 : ℝ)) := by
    intro h hhδ
    refine (ae_restrict_iff' hK0m).2 ?_
    filter_upwards [htransae (fun x => x ∈ Ω → g x = g' x)
      (h • EuclideanSpace.single k (1 : ℝ)) hgg'0] with y hy hyK
    exact hy (hKδΩ (hshiftK y h hyK hhδ))
  have hAESM1 : ∀ i : Fin n, AEStronglyMeasurable (fun y => A (g y) i)
      (volume.restrict (tsupport φ)) := by
    intro i
    refine AEStronglyMeasurable.congr
      (((hΨ'cont i).mono hφΩ).aestronglyMeasurable hK0m) ?_
    filter_upwards [hgK0] with y hy
    rw [hy]
  have hAESM2 : ∀ h : ℝ, |h| ≤ δ → ∀ i : Fin n, AEStronglyMeasurable
      (fun y => A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i)
      (volume.restrict (tsupport φ)) := by
    intro h hhδ i
    have hc : ContinuousOn
        (fun y => A (g' (y + h • EuclideanSpace.single k (1 : ℝ))) i) (tsupport φ) := by
      have h0 := ContinuousOn.comp (hΨ'cont i)
        (f := fun y : EuclideanSpace ℝ (Fin n) =>
          y + h • EuclideanSpace.single k (1 : ℝ))
        (continuous_id.add continuous_const).continuousOn
        (fun y hy => hKδΩ (hshiftK y h hy hhδ))
      exact h0
    refine AEStronglyMeasurable.congr (hc.aestronglyMeasurable hK0m) ?_
    filter_upwards [hgshiftK h hhδ] with y hy
    rw [hy]
  -- the a.e. bounds
  obtain ⟨M, hM0, hM⟩ := hΨbdd (Metric.cthickening δ (tsupport φ)) hKδcpt hKδΩ
  have hMK0 : ∀ᵐ y ∂(volume.restrict (tsupport φ)), ∀ i : Fin n, |A (g y) i| ≤ M := by
    refine (ae_restrict_iff' hK0m).2 ?_
    filter_upwards [hM] with y hy hyK
    exact hy (Metric.self_subset_cthickening _ hyK)
  have hMshift : ∀ h : ℝ, |h| ≤ δ → ∀ᵐ y ∂(volume.restrict (tsupport φ)),
      ∀ i : Fin n, |A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i| ≤ M := by
    intro h hhδ
    refine (ae_restrict_iff' hK0m).2 ?_
    filter_upwards [htransae
      (fun x => x ∈ Metric.cthickening δ (tsupport φ) → ∀ i : Fin n, |A (g x) i| ≤ M)
      (h • EuclideanSpace.single k (1 : ℝ)) hM] with y hy hyK
    exact hy (hshiftK y h hyK hhδ)
  -- the dominating integrable function
  have hfinK0 : IsFiniteMeasure (volume.restrict (tsupport φ)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hφcs.measure_lt_top
  have hgφL1 : IntegrableOn (fun y => ‖gφ y‖) (tsupport φ) volume := by
    have h1 : MemLp gφ (ENNReal.ofReal 2) (volume.restrict (tsupport φ)) :=
      hφW.2.2.mono_measure (Measure.restrict_mono hφΩ le_rfl)
    exact (h1.integrable (ENNReal.one_le_ofReal.2 one_le_two)).norm
  have hgm : ∀ i : Fin n, AEStronglyMeasurable (fun y => gφ y i)
      (volume.restrict (tsupport φ)) := fun i =>
    (hproj i).comp_aestronglyMeasurable
      (hφW.2.2.1.mono_measure (Measure.restrict_mono hφΩ le_rfl))
  have hintgen : ∀ F : Fin n → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ i, AEStronglyMeasurable (F i) (volume.restrict (tsupport φ))) →
      (∀ᵐ y ∂(volume.restrict (tsupport φ)), ∀ i : Fin n, |F i y| ≤ M) →
      IntegrableOn (fun y => ∑ i, F i y * gφ y i) (tsupport φ) volume := by
    intro F hFm hFb
    have hsum : AEStronglyMeasurable (fun y => ∑ i, F i y * gφ y i)
        (volume.restrict (tsupport φ)) := by
      have h1 : AEStronglyMeasurable (∑ i : Fin n, fun y => F i y * gφ y i)
          (volume.restrict (tsupport φ)) :=
        Finset.aestronglyMeasurable_sum _ fun i _ => (hFm i).mul (hgm i)
      have heq : (∑ i : Fin n, fun y => F i y * gφ y i)
          = fun y => ∑ i, F i y * gφ y i := by
        funext y; rw [Finset.sum_apply]
      rwa [heq] at h1
    refine Integrable.mono' (hgφL1.const_mul ((n : ℝ) * M)) hsum ?_
    filter_upwards [hFb] with y hy
    rw [Real.norm_eq_abs]
    calc |∑ i, F i y * gφ y i| ≤ ∑ i, |F i y * gφ y i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, M * ‖gφ y‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hy i) (hcoord (gφ y) i) (abs_nonneg _) hM0
      _ = (n : ℝ) * M * ‖gφ y‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_assoc]
  -- (7): the exact difference identity
  have h7 : ∀ h : ℝ, 0 < |h| → |h| ≤ δ →
      (∫ y in tsupport φ, ∑ i, ((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i
          - A (g y) i) / h) * gφ y i) = 0 := by
    intro h hh0 hhδ
    have hne : h ≠ 0 := by rwa [← abs_pos]
    obtain ⟨hW6, hcs6, hsupp6⟩ := hstep6 h hh0 hhδ
    have hint1 := hintgen (fun i y => A (g y) i) hAESM1 hMK0
    have hint2 := hintgen
      (fun i y => A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i)
      (hAESM2 h hhδ) (hMshift h hhδ)
    -- the two applications of Step 4
    have hA : (∫ y in tsupport φ, ∑ i, A (g y) i * gφ y i) = 0 := by
      have e1 : (∫ x in Ω, ∑ i, A (g x) i * gφ x i)
          = ∫ x in Ω, ∑ i, A (g x) i * (tsupport φ).indicator gφ x i := by
        refine setIntegral_congr_ae hΩm ?_
        filter_upwards [(ae_restrict_iff' hΩm).1 hĝ] with x hx hxΩ
        rw [hx hxΩ]
      have e2 : (∫ x in Ω, ∑ i, A (g x) i * (tsupport φ).indicator gφ x i)
          = ∫ y in tsupport φ, ∑ i, A (g y) i * (tsupport φ).indicator gφ y i :=
        hsetset _ _ _ (fun y hy => by simp [Set.indicator_of_notMem hy]) hφΩ
      have e3 : (∫ y in tsupport φ, ∑ i, A (g y) i * (tsupport φ).indicator gφ y i)
          = ∫ y in tsupport φ, ∑ i, A (g y) i * gφ y i := by
        refine setIntegral_congr_fun hK0m fun y hy => ?_
        simp [Set.indicator_of_mem hy]
      rw [← e3, ← e2, ← e1]
      exact hstep4 φ gφ hφW hφcs hφΩ
    have hB : (∫ y in tsupport φ, ∑ i,
        A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i * gφ y i) = 0 := by
      have hvanΩ : ∀ x, x ∉ Ω →
          (∑ i, A (g x) i * (tsupport φ).indicator gφ
            (x - h • EuclideanSpace.single k (1 : ℝ)) i) = 0 := by
        intro x hx
        have hns : x - h • EuclideanSpace.single k (1 : ℝ) ∉ tsupport φ := by
          intro hc
          refine hx (hKδΩ ?_)
          simpa using hshiftK _ h hc hhδ
        simp [Set.indicator_of_notMem hns]
      have f2 : (∫ x, ∑ i, A (g x) i * (tsupport φ).indicator gφ
          (x - h • EuclideanSpace.single k (1 : ℝ)) i) = 0 := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvanΩ]
        exact hstep4 _ _ hW6 hcs6 hsupp6
      have hmp := (measurePreserving_add_right volume
          (h • EuclideanSpace.single k (1 : ℝ))).integral_comp
        (MeasurableEquiv.addRight
          (h • EuclideanSpace.single k (1 : ℝ))).measurableEmbedding
        (fun x => ∑ i, A (g x) i * (tsupport φ).indicator gφ
          (x - h • EuclideanSpace.single k (1 : ℝ)) i)
      have f3 : (∫ y, ∑ i, A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i *
            (tsupport φ).indicator gφ y i) = 0 := by
        rw [← f2, ← hmp]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp
      have b1 : (∫ y in tsupport φ, ∑ i,
          A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i *
            (tsupport φ).indicator gφ y i)
          = ∫ y, ∑ i, A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i *
            (tsupport φ).indicator gφ y i :=
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => by simp [Set.indicator_of_notMem hy])
      have b2 : (∫ y in tsupport φ, ∑ i,
          A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i * gφ y i)
          = ∫ y in tsupport φ, ∑ i,
            A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i *
              (tsupport φ).indicator gφ y i := by
        refine setIntegral_congr_fun hK0m fun y hy => ?_
        simp [Set.indicator_of_mem hy]
      rw [b2, b1]
      exact f3
    -- subtract and divide by `h`
    have hpt : ∀ y : EuclideanSpace ℝ (Fin n),
        (∑ i, ((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
            * gφ y i)
          = h⁻¹ * ((∑ i, A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i * gφ y i)
            - ∑ i, A (g y) i * gφ y i) := by
      intro y
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    calc (∫ y in tsupport φ, ∑ i,
          ((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
            * gφ y i)
        = ∫ y in tsupport φ, h⁻¹ *
            ((∑ i, A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i * gφ y i)
              - ∑ i, A (g y) i * gφ y i) := by
          refine setIntegral_congr_fun hK0m fun y _ => hpt y
      _ = h⁻¹ * ((∫ y in tsupport φ, ∑ i,
            A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i * gφ y i)
          - ∫ y in tsupport φ, ∑ i, A (g y) i * gφ y i) := by
          rw [integral_const_mul, integral_sub hint2 hint1]
      _ = 0 := by rw [hA, hB]; ring
  -- Step 7: passing to the limit `h → 0`.  This is
  -- `DifferenceQuotientLimitIdentity`, whose docstring records the route (the
  -- `L²(tsupport φ)` convergence of the difference quotients by
  -- `WeakGradientDifferenceQuotient`, Cauchy-Schwarz against the fixed factor
  -- `(g_φ)_i`, and the vanishing of every approximating term by (7)).
  have h8 := DifferenceQuotientLimitIdentity n Ω hn1 hΩ A g Dg k φ gφ hφW hφcs
    hφΩ hstep2 hsetset hCS hintL2 δ hδ0 hĝ hAESM1 hAESM2 M hMK0 hMshift h7
  -- Step 8: restoring the thesis' index order
  have hsym0 : ∀ q : Fin n × Fin n, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∈ Ω → Dg q.2 x q.1 = Dg q.1 x q.2 := fun q =>
    WeakSecondDerivativeSymmetry n 2 hn1 one_le_two Ω u g Dg hΩ hu2 hDg q.1 q.2
  have hsym : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ q : Fin n × Fin n, x ∈ Ω → Dg q.2 x q.1 = Dg q.1 x q.2 :=
    ae_all_iff.2 hsym0
  have hcong : (∫ x in Ω, ∑ i, ∑ j,
        (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i * Dg k x j * gφ x i)
      = ∫ x in Ω, ∑ i,
        (∑ j, (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i • Dg j x) k
          * gφ x i := by
    refine setIntegral_congr_ae hΩm ?_
    filter_upwards [hsym] with x hx hxΩ
    have hco : ∀ i : Fin n,
        (∑ j, (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i • Dg j x) k
          = ∑ j, (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i * Dg j x k := by
      intro i; simp [Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hco i, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hx (j, k) hxΩ]
  rw [hcong]
  exact h8
