import ManfrediThesis.Preamble
open MeasureTheory

/-- Conditions (Q3), (Q4) and (Q5) of the paper for `A` and `B`. -/
structure EllipticStructureQ345 (n : ℕ) (p ε μ γ₂ γ₃ γ₄ : ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ) : Prop where

  measB_x : ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)), Measurable fun x => B x z h
  contB_zh : ∀ x : EuclideanSpace ℝ (Fin n),
    Continuous fun q : ℝ × EuclideanSpace ℝ (Fin n) => B x q.1 q.2
  Q3 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ∈ Ω →
    ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)),
      γ₂ * (ε + ‖h‖ ^ 2) ^ (p / 2) - μ ≤ ∑ i, (A x z h) i * h i
  Q4 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ∈ Ω →
    ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      |(A x z h) i| ≤ γ₃ * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2)
  Q5 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ∈ Ω →
    ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)),
      |B x z h| ≤ γ₄ * (1 + ‖h‖ ^ 2) ^ (p / 2)
