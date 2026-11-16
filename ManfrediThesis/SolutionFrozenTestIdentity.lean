import ManfrediThesis.Preamble
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.FrozenComparisonOn
import ManfrediThesis.WeakSolutionBoundedZeroTest
import ManfrediThesis.WeakSolutionZeroTest
open MeasureTheory

/-- The thesis' (5.4): testing both the equation on `Ω` and the frozen
comparison equation on `B_R(x₀)` against the single test function `w = u - v`
and subtracting bounds the frozen monotone pairing `I₁` by the freezing error
`I₂` plus the right-hand-side term `I₃`.  This is thesis l. 1464-1477; the
displayed identity at l. 1466-1469 carries the `B`-integral, which is what makes
this a two-form statement rather than one application of a zero-test. -/
theorem SolutionFrozenTestIdentity :
    ∀ (n : ℕ) (p : ℝ), 1 ≤ n → 1 < p →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n))
        (B : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
        (u U : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (x₀ : EuclideanSpace ℝ (Fin n)) (R T : ℝ)
        (v V : EuclideanSpace ℝ (Fin n) → ℝ)
        (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        IsOpen Ω → 0 < R → Metric.ball x₀ R ⊆ Ω →
        IsWeakSolutionOn n p Ω A B u g →
        FrozenComparisonOn n p x₀ R (fun h => A x₀ (U x₀) h) u U g v V gv →
        MemLp (fun x => A x (u x) (g x)) (ENNReal.ofReal (p / (p - 1)))
          (volume.restrict (Metric.ball x₀ R)) →
        MemLp (fun x => A x₀ (U x₀) (g x)) (ENNReal.ofReal (p / (p - 1)))
          (volume.restrict (Metric.ball x₀ R)) →
        MemLp (fun x => A x₀ (U x₀) (gv x)) (ENNReal.ofReal (p / (p - 1)))
          (volume.restrict (Metric.ball x₀ R)) →
        MemLp (fun x => g x - gv x) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R)) →
        IntegrableOn (fun x => B x (u x) (g x)) (Metric.ball x₀ R) volume →
        0 ≤ T →
        (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), |u x - v x| ≤ T) →
        (∫ x in Metric.ball x₀ R,
            ∑ i, (A x₀ (U x₀) (g x) - A x₀ (U x₀) (gv x)) i * (g x - gv x) i)
          ≤ |∫ x in Metric.ball x₀ R,
                ∑ i, (A x (u x) (g x) - A x₀ (U x₀) (g x)) i * (g x - gv x) i|
            + |∫ x in Metric.ball x₀ R, B x (u x) (g x) * (u x - v x)| := by
  intro n p hn hp Ω A B u U g x₀ R T v V gv hΩ hR hBsub hsol hfc hALp hA0gLp
    hA0gvLp hdLp hBint hT0 huv
  have hp0 : (0:ℝ) < p := by linarith
  obtain ⟨hsol0, hvW, hzeroW, hUc, hUu, hVc, hVv, hVU⟩ := hfc
  -- the Hölder pairing: integrability of each of the three `A`-pairings
  have hIP : ∀ a b : EuclideanSpace ℝ (Fin n),
      (∑ i, a i * b i) = (innerSL ℝ b) a := by
    intro a b
    show (∑ i, a i * b i) = inner ℝ b a
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hCS : ∀ a b : EuclideanSpace ℝ (Fin n), |∑ i, a i * b i| ≤ ‖a‖ * ‖b‖ := by
    intro a b
    rw [hIP a b, mul_comm ‖a‖ ‖b‖]
    exact abs_real_inner_le_norm b a
  have hconj : Real.HolderConjugate p (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have hHT : ENNReal.HolderTriple (ENNReal.ofReal (p / (p - 1)))
      (ENNReal.ofReal p) 1 :=
    ⟨by rw [inv_one]; exact hconj.symm.inv_add_inv_ennreal⟩
  have hpair : ∀ F H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      MemLp F (ENNReal.ofReal (p / (p - 1)))
          (volume.restrict (Metric.ball x₀ R)) →
      MemLp H (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) →
      IntegrableOn (fun x => ∑ i, F x i * H x i) (Metric.ball x₀ R) volume := by
    intro F H hF hH
    have hprod : Integrable (fun x => ‖F x‖ * ‖H x‖)
        (volume.restrict (Metric.ball x₀ R)) := hF.norm.integrable_mul hH.norm
    have hmeas : AEStronglyMeasurable (fun x => ∑ i, F x i * H x i)
        (volume.restrict (Metric.ball x₀ R)) := by
      have hinner : AEStronglyMeasurable (fun x => (inner ℝ (H x) (F x) : ℝ))
          (volume.restrict (Metric.ball x₀ R)) :=
        (continuous_inner (𝕜 := ℝ)
          (E := EuclideanSpace ℝ (Fin n))).comp_aestronglyMeasurable
          (hH.aestronglyMeasurable.prodMk hF.aestronglyMeasurable)
      exact hinner.congr (Filter.Eventually.of_forall fun x => (hIP (F x) (H x)).symm)
    refine hprod.mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hCS _ _
  -- the four integrable pieces, all written against `g - gv` and `u - v`
  have hPint := hpair (fun x => A x (u x) (g x)) (fun x => g x - gv x) hALp hdLp
  have hZint := hpair (fun x => A x₀ (U x₀) (g x)) (fun x => g x - gv x) hA0gLp hdLp
  have hSint := hpair (fun x => A x₀ (U x₀) (gv x)) (fun x => g x - gv x)
    hA0gvLp hdLp
  have huvm : AEStronglyMeasurable (fun x => u x - v x)
      (volume.restrict (Metric.ball x₀ R)) :=
    hzeroW.1.2.1.aestronglyMeasurable.neg.congr
      (Filter.Eventually.of_forall fun x => by simp)
  have hQint : IntegrableOn (fun x => B x (u x) (g x) * (u x - v x))
      (Metric.ball x₀ R) volume := by
    refine (hBint.norm.const_mul T).mono'
      (hBint.aestronglyMeasurable.mul huvm) ?_
    filter_upwards [huv] with x h
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
  -- Step 1: the equation on Ω, tested against the bounded W^{1,p}_0 pair
  have hvuT : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      |v x - u x| ≤ T := by
    filter_upwards [huv] with x h
    rwa [abs_sub_comm]
  have h1 := WeakSolutionBoundedZeroTest n p hn hp Ω x₀ R A B u g
    (fun x => v x - u x) (fun x => gv x - g x) T hΩ hR hBsub hsol hALp hBint
    hzeroW hT0 hvuT
  -- Step 2: the frozen equation on the ball, tested against the same pair
  have h2 := WeakSolutionZeroTest n p hn hp (Metric.ball x₀ R)
    (fun _ _ h => A x₀ (U x₀) h) v gv (fun x => v x - u x) (fun x => gv x - g x)
    Metric.isOpen_ball hsol0 hA0gvLp hzeroW
  -- rewrite both against `g - gv` and `u - v`
  have hflipP : (∫ x in Metric.ball x₀ R,
        ((∑ i, (A x (u x) (g x)) i * (gv x - g x) i)
          + B x (u x) (g x) * (v x - u x)))
      = -((∫ x in Metric.ball x₀ R, ∑ i, (A x (u x) (g x)) i * (g x - gv x) i)
          + ∫ x in Metric.ball x₀ R, B x (u x) (g x) * (u x - v x)) := by
    rw [← integral_add hPint hQint, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
    have e1 : (∑ i, (A x (u x) (g x)) i * (gv x - g x) i)
        = -∑ i, (A x (u x) (g x)) i * (g x - gv x) i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : (gv x - g x) i = -((g x - gv x) i) := by simp
      rw [e]; ring
    rw [e1]
    ring
  have hflipS : (∫ x in Metric.ball x₀ R,
        ∑ i, (A x₀ (U x₀) (gv x)) i * (gv x - g x) i)
      = -∫ x in Metric.ball x₀ R, ∑ i, (A x₀ (U x₀) (gv x)) i * (g x - gv x) i := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (gv x - g x) i = -((g x - gv x) i) := by simp
    rw [e]; ring
  rw [hflipP] at h1
  rw [hflipS] at h2
  -- the two linear splittings
  have hsplitLHS : (∫ x in Metric.ball x₀ R,
        ∑ i, (A x₀ (U x₀) (g x)) i * (g x - gv x) i)
      = (∫ x in Metric.ball x₀ R,
            ∑ i, (A x₀ (U x₀) (g x) - A x₀ (U x₀) (gv x)) i * (g x - gv x) i)
        + ∫ x in Metric.ball x₀ R,
            ∑ i, (A x₀ (U x₀) (gv x)) i * (g x - gv x) i := by
    rw [← integral_add (hpair (fun x => A x₀ (U x₀) (g x) - A x₀ (U x₀) (gv x))
      (fun x => g x - gv x) (hA0gLp.sub hA0gvLp) hdLp) hSint]
    refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (A x₀ (U x₀) (g x) - A x₀ (U x₀) (gv x)) i
        = (A x₀ (U x₀) (g x)) i - (A x₀ (U x₀) (gv x)) i := by simp
    rw [e]; ring
  have hsplitRHS : (∫ x in Metric.ball x₀ R,
        ∑ i, (A x (u x) (g x) - A x₀ (U x₀) (g x)) i * (g x - gv x) i)
      = (∫ x in Metric.ball x₀ R, ∑ i, (A x (u x) (g x)) i * (g x - gv x) i)
        - ∫ x in Metric.ball x₀ R,
            ∑ i, (A x₀ (U x₀) (g x)) i * (g x - gv x) i := by
    rw [← integral_sub hPint hZint]
    refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (A x (u x) (g x) - A x₀ (U x₀) (g x)) i
        = (A x (u x) (g x)) i - (A x₀ (U x₀) (g x)) i := by simp
    rw [e]; ring
  -- the two identities, read as linear relations between the named integrals
  have hPQ : (∫ x in Metric.ball x₀ R, ∑ i, (A x (u x) (g x)) i * (g x - gv x) i)
      + (∫ x in Metric.ball x₀ R, B x (u x) (g x) * (u x - v x)) = 0 := by
    have := h1
    linarith
  have hS0 : (∫ x in Metric.ball x₀ R,
      ∑ i, (A x₀ (U x₀) (gv x)) i * (g x - gv x) i) = 0 := by
    have := h2
    linarith
  rw [hsplitRHS]
  -- the triangle inequality on the three named reals
  have hfin : (∫ x in Metric.ball x₀ R,
        ∑ i, (A x₀ (U x₀) (g x)) i * (g x - gv x) i)
      ≤ |(∫ x in Metric.ball x₀ R, ∑ i, (A x (u x) (g x)) i * (g x - gv x) i)
            - ∫ x in Metric.ball x₀ R,
              ∑ i, (A x₀ (U x₀) (g x)) i * (g x - gv x) i|
        + |∫ x in Metric.ball x₀ R, B x (u x) (g x) * (u x - v x)| := by
    set P := ∫ x in Metric.ball x₀ R, ∑ i, (A x (u x) (g x)) i * (g x - gv x) i
      with hPdef
    set Z := ∫ x in Metric.ball x₀ R, ∑ i, (A x₀ (U x₀) (g x)) i * (g x - gv x) i
      with hZdef
    set Q := ∫ x in Metric.ball x₀ R, B x (u x) (g x) * (u x - v x) with hQdef
    have hPnegQ : P = -Q := by linarith
    have h1' : |Z| ≤ |P - Z| + |P| := by
      have e : |(P - Z) - P| ≤ |P - Z| + |P| := abs_sub _ _
      rw [show (P - Z) - P = -Z from by ring, abs_neg] at e
      exact e
    have h2' : |P| = |Q| := by rw [hPnegQ, abs_neg]
    calc Z ≤ |Z| := le_abs_self Z
      _ ≤ |P - Z| + |P| := h1'
      _ = |P - Z| + |Q| := by rw [h2']
  linarith [hsplitLHS, hS0, hfin]
