import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pZeroOn
import ManfrediThesis.MemHolderOn
import ManfrediThesis.MemW1pLocOn
open MeasureTheory

/-- Cited result (C3): existence and regularity for the Dirichlet problem of
Lemma 3.1 with Hölder boundary data. -/
def CitedDirichletHolder (n : ℕ) (p ε γ₀ γ₁ : ℝ)
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=

  EllipticStructureQ12 n p ε γ₀ γ₁ Set.univ (fun _ _ h => A h) → 0 ≤ ε → A 0 = 0 →
    ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R β : ℝ), 0 < R → 0 ≤ β → β < 1 →
      ∀ fb : EuclideanSpace ℝ (Fin n) → ℝ,
        MemHolderOn n β (Metric.sphere x₀ R) fb →
        ∃ (u U : EuclideanSpace ℝ (Fin n) → ℝ)
          (gu : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          MemW1pLocOn n p (Metric.ball x₀ R) u gu ∧
            IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h) (fun _ _ _ => 0) u gu ∧
            ContDiffOn ℝ 1 u (Metric.ball x₀ R) ∧
            MemHolderOn n β (Metric.closedBall x₀ R) U ∧
            (∀ x ∈ Metric.ball x₀ R, U x = u x) ∧
            (∀ x ∈ Metric.sphere x₀ R, U x = fb x) ∧
            (∀ (b : EuclideanSpace ℝ (Fin n) → ℝ)
               (gb : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
              MemW1pOn n p (Metric.ball x₀ R) b gb →
              ContinuousOn b (Metric.closedBall x₀ R) →
              (∀ x ∈ Metric.sphere x₀ R, b x = fb x) →
              MemW1pZeroOn n p (Metric.ball x₀ R) (fun x => u x - b x) (fun x => gu x - gb x))
