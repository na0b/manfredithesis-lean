import ManfrediThesis.Preamble
import ManfrediThesis.IsQuasiregularOn
open MeasureTheory

/-- `τ` is the distortion matrix of the quasiregular mapping `F`, as defined on
thesis p. 52. -/
def IsDistortionMatrix (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (G : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (τ : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) : Prop :=

  ∀ x ∈ Ω,
    (0 < (Matrix.of fun i j => G i x j).det →
        τ x * ((Matrix.of fun i j => G i x j).transpose * (Matrix.of fun i j => G i x j))
          = ((Matrix.of fun i j => G i x j).det ^ ((2 : ℝ) / n))
            • (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
      (¬ 0 < (Matrix.of fun i j => G i x j).det →
        τ x = (1 : Matrix (Fin n) (Fin n) ℝ))
