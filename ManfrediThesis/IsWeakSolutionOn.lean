import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MemW1pOn
open MeasureTheory

/-- `u` (with weak gradient `g`) is a weak solution of
`div A(x, u, ∇u) = B(x, u, ∇u)` in `Ω`, as in (1.2). -/
def IsWeakSolutionOn (n : ℕ) (p : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=

  MemW1pLocOn n p Ω u g ∧
    ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ)
      (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      MemW1pOn n p Ω φ gφ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      IntegrableOn
          (fun x => (∑ i, (A x (u x) (g x)) i * gφ x i) + B x (u x) (g x) * φ x)
          Ω volume ∧
        (∫ x in Ω, ((∑ i, (A x (u x) (g x)) i * gφ x i) + B x (u x) (g x) * φ x)) = 0
