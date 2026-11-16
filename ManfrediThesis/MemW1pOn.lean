import ManfrediThesis.Preamble
import ManfrediThesis.HasWeakGradientOn
open MeasureTheory

/-- `MemW1pOn n p Ω f g`: `f ∈ W^{1,p}(Ω)` with weak gradient `g`. -/
def MemW1pOn (n : ℕ) (p : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=

  HasWeakGradientOn n Ω f g ∧
    MemLp f (ENNReal.ofReal p) (volume.restrict Ω) ∧
    MemLp g (ENNReal.ofReal p) (volume.restrict Ω)
