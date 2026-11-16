import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pOn
open MeasureTheory

/-- Cited result (C6): the Sobolev-Poincaré inequality on balls. -/
def CitedSobolevPoincareBall (n : ℕ) : Prop :=

  ∃ C : ℝ, 0 < C ∧
    ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
      ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ)
        (gg : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        MemW1pOn n 1 (Metric.ball x₀ ρ) g gg →
        (∫ x in Metric.ball x₀ ρ,
            |g x - (volume (Metric.ball x₀ ρ)).toReal⁻¹ * ∫ y in Metric.ball x₀ ρ, g y|
              ^ ((n : ℝ) / ((n : ℝ) - 1))) ^ (((n : ℝ) - 1) / (n : ℝ))
          ≤ C * ∫ x in Metric.ball x₀ ρ, ‖gg x‖
