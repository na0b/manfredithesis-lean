import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pLocOn
open MeasureTheory

/-- Cited result (C1): regularity of weak solutions of (3.1) when `ε > 0`. -/
def CitedRegularityEpsPos (n : ℕ) (p ε γ₀ γ₁ : ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=

  0 < ε → EllipticStructureQ12 n p ε γ₀ γ₁ Ω (fun _ _ h => A h) →
    ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      IsWeakSolutionOn n p Ω (fun _ _ h => A h) (fun _ _ _ => 0) u g →
      MemW1pLocOn n 2 Ω u g ∧
        ∃ g' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
          ContinuousOn g' Ω ∧
            (∀ᵐ x ∂(volume.restrict Ω), g x = g' x) ∧
            (∃ Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
              ∀ i : Fin n, MemW1pLocOn n 2 Ω (fun x => g' x i) (Dg i))
