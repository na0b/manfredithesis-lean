import ManfrediThesis.Preamble
import ManfrediThesis.IsQuasiregularOn
import ManfrediThesis.IsDistortionMatrix
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.IsLocalMinimumOn
open MeasureTheory

/-- Cited result (C7): the basic properties of quasiregular mappings used in
Theorem 7. -/
def CitedQuasiregularBasics (n : ℕ) (K : ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (G : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (τ : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) : Prop :=

  IsQuasiregularOn n K Ω F G → IsDistortionMatrix n Ω G τ →
    (∃ Ft : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        ContinuousOn Ft Ω ∧ ∀ᵐ x ∂(volume.restrict Ω), F x = Ft x) ∧
      ((¬ ∃ c : EuclideanSpace ℝ (Fin n),
            ∀ᵐ x ∂(volume.restrict Ω), F x = c) →
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ∈ Ω →
          0 < (Matrix.of fun i j => G i x j).det) ∧
      (∀ i : Fin n, IsWeakSolutionOn n (n : ℝ) Ω
        (fun x _ h => ((∑ a, ∑ b, τ x a b * h a * h b) ^ ((n : ℝ) / 2 - 1)) •
          (WithLp.toLp 2 (fun r => ∑ s, τ x r s * h s) : EuclideanSpace ℝ (Fin n)))
        (fun _ _ _ => 0) (fun x => F x i) (G i)) ∧
      (∀ i : Fin n, IsLocalMinimumOn n (n : ℝ) Ω
        (fun x _ h => (∑ a, ∑ b, τ x a b * h a * h b) ^ ((n : ℝ) / 2))
        (fun x => F x i) (G i))
