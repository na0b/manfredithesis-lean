import ManfrediThesis.Preamble
import ManfrediThesis.EssOscOn
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.EllipticStructureQ345
import ManfrediThesis.IsWeakSolutionOn
open MeasureTheory

/-- Cited result (C4)(b) of the Note for the formalization (De
Giorgi-Ladyzhenskaya-Ural'tseva Hölder estimates; [G, chapter VII,
Theorems 2.1-2.2], [GG2], [LU, chapter 4]): the oscillation estimate (5.1) for bounded weak solutions of (1.1)
under (Q1)-(Q5).
Stated as its own predicate rather than as a field of a two-field bundle, so
that a defect in the other half of (C4) cannot empty this one's consumers --
the paper itself labels the two halves (a) and (b) at l. 263. -/
def CitedHolderOscillationSolution (n : ℕ) (p : ℝ) : Prop :=

  ∀ μ γ₀ γ₁ γ₂ γ₃ γ₄ M : ℝ, 0 < γ₀ → 0 < γ₁ → 0 < γ₂ →
      0 < γ₃ → 0 < γ₄ → 0 < μ → 0 ≤ M →
    ∃ α d : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < d ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n))
        (B : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (x₀ : EuclideanSpace ℝ (Fin n)) (R ρ : ℝ),
        IsOpen Ω → EllipticStructureQ12 n p ε γ₀ γ₁ Ω A →
        EllipticStructureQ345 n p ε μ γ₂ γ₃ γ₄ Ω A B →
        IsWeakSolutionOn n p Ω A B u g →
        (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
        Metric.closedBall x₀ R ⊆ Ω → 0 < ρ → ρ ≤ R →
        EssOscOn n (Metric.ball x₀ ρ) u
          ≤ (4 : ℝ) ^ α * max (EssOscOn n (Metric.ball x₀ R) u) (d * R) * (ρ / R) ^ α
