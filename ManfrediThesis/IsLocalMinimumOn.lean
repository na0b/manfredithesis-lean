import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MemW1pOn
open MeasureTheory

/-- `u` (with weak gradient `g`) is a local minimum in `Ω` for the functional
`F(v; E) = ∫_E fdens (x, v x, ∇v x) dx`, as in §4. -/
def IsLocalMinimumOn (n : ℕ) (p : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=

  MemW1pLocOn n p Ω u g ∧
    ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ)
      (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      MemW1pOn n p Ω φ gφ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      IntegrableOn (fun x => fdens x (u x) (g x)) (tsupport φ) volume ∧
        IntegrableOn (fun x => fdens x (u x + φ x) (g x + gφ x))
          (tsupport φ) volume ∧
        (∫ x in tsupport φ, fdens x (u x) (g x))
          ≤ ∫ x in tsupport φ, fdens x (u x + φ x) (g x + gφ x)
