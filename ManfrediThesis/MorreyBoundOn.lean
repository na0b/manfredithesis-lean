import ManfrediThesis.Preamble
open MeasureTheory

/-- `MorreyBoundOn n q lam Ω u N`: `u ∈ L^{q,lam}(Ω)` with Morrey norm at most
`N`. -/
def MorreyBoundOn (n : ℕ) (q lam : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (N : ℝ) : Prop :=

  MemLp u (ENNReal.ofReal q) (volume.restrict Ω) ∧
    ∀ x ∈ Ω, ∀ ρ : ℝ, 0 < ρ → ρ < Metric.diam Ω →
      (∫ y in Ω ∩ Metric.ball x ρ, |u y| ^ q) ≤ N ^ q * ρ ^ lam
