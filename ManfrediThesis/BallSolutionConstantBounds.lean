import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.BallComparisonPrinciple
import ManfrediThesis.WeakGradientLinear
import ManfrediThesis.WeakGradientCompactSupportIntegral
open MeasureTheory

/-- A weak solution on a ball is trapped between the two constants that trap
its continuous extension on the sphere.  The field is only assumed to have a
(Q1)-(Q2) NORMALISATION `A - A 0`, which is the form `FrozenOperatorStructureQ12`
produces; the shift is absorbed here, using that the weak gradient of a
compactly supported `W^{1,p}` function on the ball integrates to zero.  This is
the route by which thesis l. 1137-1139 bounds the comparison map, replacing the
thesis' appeal to the oscillation clause of Lemma 3.1. -/
theorem BallSolutionConstantBounds :
    ∀ (n : ℕ) (p ε γ₀ γ₁ : ℝ), 2 ≤ n → 1 < p → 0 ≤ ε → 0 < γ₀ → γ₀ ≤ γ₁ →
      CitedSobolevPoincareBall n →
      ∀ (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
        (v V : EuclideanSpace ℝ (Fin n) → ℝ)
        (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (m M : ℝ),
        0 < R →
        EllipticStructureQ12 n p ε γ₀ γ₁ Set.univ (fun _ _ h => A h - A 0) →
        IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h)
          (fun _ _ _ => 0) v gv →
        MemW1pOn n p (Metric.ball x₀ R) v gv →
        ContinuousOn V (Metric.closedBall x₀ R) →
        (∀ x ∈ Metric.ball x₀ R, V x = v x) →
        (∀ x ∈ Metric.sphere x₀ R, m ≤ V x ∧ V x ≤ M) →
        ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), m ≤ v x ∧ v x ≤ M := by
  intro n p ε γ₀ γ₁ hn hp hε hγ₀ hγ hSP A x₀ R v V gv m M hR hQ hvsol hvW hVc hVv hbd
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hball : IsOpen (Metric.ball x₀ R) := Metric.isOpen_ball
  have hfin : volume (Metric.ball x₀ R) ≠ ⊤ := measure_ball_lt_top.ne
  -- `v` solves the normalised equation: the constant shift integrates to zero
  have hvsol' : IsWeakSolutionOn n p (Metric.ball x₀ R)
      (fun _ _ h => A h - A 0) (fun _ _ _ => 0) v gv := by
    refine ⟨hvsol.1, ?_⟩
    intro φ gφ hφW hcs hsupp
    obtain ⟨hI, hInt⟩ := hvsol.2 φ gφ hφW hcs hsupp
    have hcoord : ∀ i : Fin n,
        IntegrableOn (fun x => gφ x i) (Metric.ball x₀ R) volume
          ∧ (∫ x in Metric.ball x₀ R, gφ x i) = 0 :=
      fun i => WeakGradientCompactSupportIntegral n p hn1 hp.le x₀ R φ gφ hR hφW hcs hsupp i
    have hshiftI : IntegrableOn (fun x => ∑ i, A 0 i * gφ x i)
        (Metric.ball x₀ R) volume :=
      integrable_finsetSum _ fun i _ => ((hcoord i).1).const_mul _
    have hshift0 : (∫ x in Metric.ball x₀ R, ∑ i, A 0 i * gφ x i) = 0 := by
      rw [integral_finsetSum _ fun i _ => ((hcoord i).1).const_mul _]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_const_mul, (hcoord i).2, mul_zero]
    have hptw : ∀ x : EuclideanSpace ℝ (Fin n),
        ((∑ i, ((fun _ _ h => A h - A 0) x (v x) (gv x)) i * gφ x i)
            + ((fun _ _ _ => (0:ℝ)) x (v x) (gv x)) * φ x)
          = ((∑ i, ((fun _ _ h => A h) x (v x) (gv x)) i * gφ x i)
            + ((fun _ _ _ => (0:ℝ)) x (v x) (gv x)) * φ x)
            - ∑ i, A 0 i * gφ x i := by
      intro x
      have hcomp : ∀ i : Fin n, ((A (gv x) - A 0) i : ℝ) = A (gv x) i - A 0 i := by
        intro i
        simp
      have hs : (∑ i, (A (gv x) - A 0) i * gφ x i)
          = (∑ i, A (gv x) i * gφ x i) - ∑ i, A 0 i * gφ x i := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcomp i]
        ring
      show ((∑ i, (A (gv x) - A 0) i * gφ x i) + 0 * φ x)
        = ((∑ i, A (gv x) i * gφ x i) + 0 * φ x) - ∑ i, A 0 i * gφ x i
      rw [hs]
      ring
    constructor
    · exact (hI.sub hshiftI).congr (Filter.Eventually.of_forall fun x => (hptw x).symm)
    · rw [integral_congr_ae (Filter.Eventually.of_forall hptw),
        integral_sub hI hshiftI, hInt, hshift0, sub_zero]
  -- constants are competitors
  have hWGL := fun c : ℝ => WeakGradientLinear n p hn1 hp.le (Metric.ball x₀ R)
    (fun _ => (0:ℝ)) (fun _ => (0:ℝ))
    (fun _ => (0 : EuclideanSpace ℝ (Fin n))) (fun _ => (0 : EuclideanSpace ℝ (Fin n)))
    0 0 c hball
  have hconstW : ∀ c : ℝ, MemW1pOn n p (Metric.ball x₀ R) (fun _ => c) (fun _ => 0) :=
    fun c => (hWGL c).2.2.2 hfin
  have hconstSol : ∀ c : ℝ, IsWeakSolutionOn n p (Metric.ball x₀ R)
      (fun _ _ h => A h - A 0) (fun _ _ _ => 0) (fun _ => c) (fun _ => 0) := by
    intro c
    refine ⟨(hWGL c).2.2.1, ?_⟩
    intro φ gφ hφW hcs hsupp
    have hz : (fun x : EuclideanSpace ℝ (Fin n) =>
        (∑ i, ((fun _ _ h => A h - A 0) x ((fun _ => c) x)
            ((fun _ => (0 : EuclideanSpace ℝ (Fin n))) x)) i * gφ x i)
          + ((fun _ _ _ => (0:ℝ)) x ((fun _ => c) x)
            ((fun _ => (0 : EuclideanSpace ℝ (Fin n))) x)) * φ x)
        = fun _ => (0:ℝ) := by
      funext x
      show ((∑ i, (A 0 - A 0) i * gφ x i) + 0 * φ x) = 0
      simp
    rw [hz]
    exact ⟨integrable_zero _ _ _, integral_zero _ _⟩
  -- the two comparisons
  have hupper : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), v x ≤ M := by
    refine BallComparisonPrinciple n p ε γ₀ γ₁ hn hp hε hγ₀ hγ hSP
      (fun h => A h - A 0) x₀ R v (fun _ => M) V (fun _ => M) gv (fun _ => 0) hR hQ
      hvsol' (hconstSol M) hvW (hconstW M) hVc hVv continuousOn_const
      (fun x _ => rfl) ?_
    intro x hx
    exact (hbd x hx).2
  have hlower : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), m ≤ v x := by
    refine BallComparisonPrinciple n p ε γ₀ γ₁ hn hp hε hγ₀ hγ hSP
      (fun h => A h - A 0) x₀ R (fun _ => m) v (fun _ => m) V (fun _ => 0) gv hR hQ
      (hconstSol m) hvsol' (hconstW m) hvW continuousOn_const (fun x _ => rfl)
      hVc hVv ?_
    intro x hx
    exact (hbd x hx).1
  filter_upwards [hupper, hlower] with x h1 h2
  exact ⟨h2, h1⟩
