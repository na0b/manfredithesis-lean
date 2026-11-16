import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pZeroOn
open MeasureTheory

/-- Cited result (C2): solvability of the Dirichlet problem for (3.1) with
Sobolev boundary data. -/
def CitedDirichletW1p (n : ℕ) (p ε γ₀ γ₁ : ℝ)
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=

  EllipticStructureQ12 n p ε γ₀ γ₁ Set.univ (fun _ _ h => A h) → 0 ≤ ε → A 0 = 0 →
    ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R →
      ∀ (b : EuclideanSpace ℝ (Fin n) → ℝ) (gb : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        MemW1pOn n p (Metric.ball x₀ R) b gb →
        ∃ (v : EuclideanSpace ℝ (Fin n) → ℝ) (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h) (fun _ _ _ => 0) v gv ∧
            MemW1pZeroOn n p (Metric.ball x₀ R) (fun x => v x - b x) (fun x => gv x - gb x)
