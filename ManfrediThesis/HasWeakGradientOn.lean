import ManfrediThesis.Preamble
open MeasureTheory

/-- `HasWeakGradientOn n Ω f g`: the vector field `g` is the distributional
(weak) gradient of `f` on the open set `Ω`, as in §1 of the paper. -/
def HasWeakGradientOn (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=

  ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ Ω → ∀ i : Fin n,
      (∫ x in Ω, f x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        = -∫ x in Ω, g x i * φ x
