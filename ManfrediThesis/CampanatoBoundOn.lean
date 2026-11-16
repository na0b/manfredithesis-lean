import ManfrediThesis.Preamble
open MeasureTheory

/-- `CampanatoBoundOn n q lam Ω u N`: `u ∈ 𝓛^{q,lam}(Ω)` with Campanato norm at
most `N`. -/
def CampanatoBoundOn (n : ℕ) (q lam : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (N : ℝ) : Prop :=

  MemLp u (ENNReal.ofReal q) (volume.restrict Ω) ∧
    ∀ x ∈ Ω, ∀ ρ : ℝ, 0 < ρ → ρ < Metric.diam Ω →
      (∫ y in Ω ∩ Metric.ball x ρ,
          |u y - (volume (Ω ∩ Metric.ball x ρ)).toReal⁻¹
            * ∫ w in Ω ∩ Metric.ball x ρ, u w| ^ q)
        ≤ N ^ q * ρ ^ lam
