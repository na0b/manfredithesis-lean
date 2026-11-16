import ManfrediThesis.Preamble
open MeasureTheory

/-- `MemHolderOn n η Ω u`: `u ∈ C^η(Ω)`. -/
def MemHolderOn (n : ℕ) (η : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=

  ContinuousOn u Ω ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ω, ∀ y ∈ Ω, |u x - u y| ≤ C * dist x y ^ η
