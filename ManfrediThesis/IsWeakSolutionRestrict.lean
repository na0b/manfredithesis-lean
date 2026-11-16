import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.WeakGradientRestrict
import ManfrediThesis.WeakGradientZeroExtend
open MeasureTheory

/-- A weak solution of `div A(x, u, ∇u) = B(x, u, ∇u)` on an open set `Ω`, in the
sense of (1.2), is a weak solution with the same weak gradient on every ball
contained in `Ω`. -/
theorem IsWeakSolutionRestrict :
    ∀ (n : ℕ) (p : ℝ), 1 ≤ n → 1 ≤ p →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (x₀ : EuclideanSpace ℝ (Fin n)) (σ : ℝ)
        (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n))
        (B : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        IsOpen Ω → 0 < σ → Metric.ball x₀ σ ⊆ Ω →
        IsWeakSolutionOn n p Ω A B u g →
        IsWeakSolutionOn n p (Metric.ball x₀ σ) A B u g := by
  intro n p hn hp Ω x₀ σ A B u g hΩ hσ hsub hsol
  obtain ⟨hmem, htest⟩ := hsol
  refine ⟨(WeakGradientRestrict n p hn hp Ω (Metric.ball x₀ σ) u g hΩ
    Metric.isOpen_ball hsub).2.1 hmem, ?_⟩
  intro φ gφ hφ hcs hts
  -- the zero extension of the test pair is admissible for `Ω`
  have hext : MemW1pOn n p Ω φ ((Metric.ball x₀ σ).indicator gφ) :=
    WeakGradientZeroExtend n p hn hp Ω x₀ σ φ gφ hΩ hsub hφ hcs hts
  obtain ⟨hint, hzero⟩ :=
    htest φ ((Metric.ball x₀ σ).indicator gφ) hext hcs (hts.trans hsub)
  -- the two integrands agree on the ball
  have hon : ∀ x ∈ Metric.ball x₀ σ,
      ((∑ i, (A x (u x) (g x)) i * ((Metric.ball x₀ σ).indicator gφ x) i)
          + B x (u x) (g x) * φ x)
        = ((∑ i, (A x (u x) (g x)) i * gφ x i) + B x (u x) (g x) * φ x) := by
    intro x hx
    rw [Set.indicator_of_mem hx]
  -- and the `Ω`-integrand vanishes off the ball
  have hoff : ∀ x ∈ Ω \ Metric.ball x₀ σ,
      ((∑ i, (A x (u x) (g x)) i * ((Metric.ball x₀ σ).indicator gφ x) i)
          + B x (u x) (g x) * φ x) = 0 := by
    intro x hx
    have hφ0 : φ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hc => hx.2 (hts hc))
    rw [Set.indicator_of_notMem hx.2, hφ0]
    simp
  refine ⟨?_, ?_⟩
  · refine IntegrableOn.congr_fun (hint.mono_set hsub) ?_ Metric.isOpen_ball.measurableSet
    intro x hx
    exact hon x hx
  · have h1 :
        (∫ x in Ω, ((∑ i, (A x (u x) (g x)) i * ((Metric.ball x₀ σ).indicator gφ x) i)
            + B x (u x) (g x) * φ x))
          = ∫ x in Metric.ball x₀ σ,
              ((∑ i, (A x (u x) (g x)) i * ((Metric.ball x₀ σ).indicator gφ x) i)
                + B x (u x) (g x) * φ x) :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet hsub hoff
    rw [← setIntegral_congr_fun Metric.isOpen_ball.measurableSet hon, ← h1, hzero]
