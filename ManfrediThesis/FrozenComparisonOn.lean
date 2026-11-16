import ManfrediThesis.Preamble
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pZeroOn
open MeasureTheory

/-- `v` (with continuous extension `V` and weak gradient `gv`) is the comparison
map for `u` on `B_R(x₀)`: it solves `div A(∇v) = 0` in `B_R(x₀)` and takes the
boundary values of `u` on `∂B_R(x₀)`. -/
def FrozenComparisonOn (n : ℕ) (p : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (u U : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (v V : EuclideanSpace ℝ (Fin n) → ℝ)
    (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=

  IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h) (fun _ _ _ => 0) v gv ∧
    MemW1pOn n p (Metric.ball x₀ R) v gv ∧
    MemW1pZeroOn n p (Metric.ball x₀ R) (fun x => v x - u x) (fun x => gv x - g x) ∧
    ContinuousOn U (Metric.closedBall x₀ R) ∧
    (∀ x ∈ Metric.ball x₀ R, U x = u x) ∧
    ContinuousOn V (Metric.closedBall x₀ R) ∧
    (∀ x ∈ Metric.ball x₀ R, V x = v x) ∧
    (∀ x ∈ Metric.sphere x₀ R, V x = U x)
