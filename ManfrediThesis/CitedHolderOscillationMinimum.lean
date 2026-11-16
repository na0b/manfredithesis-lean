import ManfrediThesis.Preamble
import ManfrediThesis.VariationalGrowthF1
import ManfrediThesis.IsLocalMinimumOn
import ManfrediThesis.EssOscOn
open MeasureTheory

/-- Cited result (C4)(a) of the Note for the formalization (De
Giorgi-Ladyzhenskaya-Ural'tseva Hölder estimates; [G, chapter VII,
Theorems 2.1-2.2], [GG2], [LU, chapter 4]): the oscillation estimate for bounded local minima under (F1),
displayed on thesis p. 31.
Stated as its own predicate rather than as a field of a two-field bundle, so
that a defect in the other half of (C4) cannot empty this one's consumers --
the paper itself labels the two halves (a) and (b) at l. 263. -/
def CitedHolderOscillationMinimum (n : ℕ) (p : ℝ) : Prop :=

  ∀ lam Lam a M : ℝ, 0 < lam → lam ≤ Lam → 0 < a → 0 ≤ M →
    ∃ α d : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < d ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (x₀ : EuclideanSpace ℝ (Fin n)) (R ρ : ℝ),
        IsOpen Ω → VariationalGrowthF1 n p ε lam Lam a Ω fdens →
        IsLocalMinimumOn n p Ω fdens u g →
        (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
        Metric.closedBall x₀ R ⊆ Ω → 0 < ρ → ρ ≤ R →
        EssOscOn n (Metric.ball x₀ ρ) u
          ≤ (4 : ℝ) ^ α * max (EssOscOn n (Metric.ball x₀ R) u) (d * R) * (ρ / R) ^ α
