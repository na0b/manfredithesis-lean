import ManfrediThesis.Preamble
open MeasureTheory

/-- The frozen operator `A(h) = ∇_h f⁰(h)` of §4, where `f⁰(h) = fdens x₀ z h`. -/
noncomputable def FrozenGradientOperator (n : ℕ)
    (fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (z : ℝ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=

  fun h => WithLp.toLp 2 fun i =>
    fderiv ℝ (fdens x₀ z) h (EuclideanSpace.single i (1 : ℝ))
