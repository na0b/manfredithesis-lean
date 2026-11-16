import ManfrediThesis.Preamble
open MeasureTheory

/-- Conditions (Q1) and (Q2) of the paper for `A : Ω × ℝ × ℝⁿ → ℝⁿ`. -/
structure EllipticStructureQ12 (n : ℕ) (p ε γ₀ γ₁ : ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n)) : Prop where

  meas_x : ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)), Measurable fun x => A x z h
  cont_zh : ∀ x : EuclideanSpace ℝ (Fin n),
    Continuous fun q : ℝ × EuclideanSpace ℝ (Fin n) => A x q.1 q.2
  hcont : ∀ x ∈ Ω, ∀ z : ℝ, Continuous (A x z)
  hdiff : ∀ x ∈ Ω, ∀ z : ℝ,
    ContDiffOn ℝ 1 (A x z) {h : EuclideanSpace ℝ (Fin n) | ε + ‖h‖ ^ 2 ≠ 0}
  Q1 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ∈ Ω →
    ∀ (z : ℝ) (h ξ : EuclideanSpace ℝ (Fin n)), ε + ‖h‖ ^ 2 ≠ 0 →
      γ₀ * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖ξ‖ ^ 2 ≤ ∑ i, (fderiv ℝ (A x z) h ξ) i * ξ i
  Q2 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ∈ Ω →
    ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)) (i j : Fin n), ε + ‖h‖ ^ 2 ≠ 0 →
      |(fderiv ℝ (A x z) h (EuclideanSpace.single j (1 : ℝ))) i|
        ≤ γ₁ * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1)
