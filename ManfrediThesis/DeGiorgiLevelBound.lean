import ManfrediThesis.Preamble
open MeasureTheory

/-- `DeGiorgiLevelBound n γ f g x₀ ℓ ρ₀ ρ₁` is one instance of condition (2.1) of
the paper, for the function `f` with weak gradient `g` on concentric balls. -/
def DeGiorgiLevelBound (n : ℕ) (γ : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (ℓ ρ₀ ρ₁ : ℝ) : Prop :=

  (∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ₁)), max (f x - ℓ) 0 ≤ C) ∧
    (∫ x in Metric.ball x₀ ρ₀ ∩ {y | ℓ < f y}, ‖g x‖ ^ 2)
      ≤ γ / (ρ₁ - ρ₀) ^ 2
        * essSup (fun x => max (f x - ℓ) 0 ^ 2) (volume.restrict (Metric.ball x₀ ρ₁))
        * (volume (Metric.ball x₀ ρ₁ ∩ {y | ℓ < f y})).toReal
