import ManfrediThesis.Preamble
import ManfrediThesis.HasWeakGradientOn
open MeasureTheory

/-- `MemW1pLocOn n p Ω f g`: `f ∈ W^{1,p}_{loc}(Ω)` with weak gradient `g`. -/
def MemW1pLocOn (n : ℕ) (p : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=

  HasWeakGradientOn n Ω f g ∧
    ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω →
      MemLp f (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp g (ENNReal.ofReal p) (volume.restrict K)
