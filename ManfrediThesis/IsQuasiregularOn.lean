import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pLocOn
open MeasureTheory

/-- `F` is `K`-quasiregular on `Ω`, with `G i` the weak gradient of the `i`-th
component `F^i`, as in (5.10). -/
def IsQuasiregularOn (n : ℕ) (K : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (G : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=

  (∀ i : Fin n, MemW1pLocOn n (n : ℝ) Ω (fun x => F x i) (G i)) ∧
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ∈ Ω →
      ∀ ξ : EuclideanSpace ℝ (Fin n),
        (∑ i, (∑ j, G i x j * ξ j) ^ 2) ^ ((n : ℝ) / 2)
          ≤ K * (Matrix.of fun i j => G i x j).det * ‖ξ‖ ^ (n : ℝ)
