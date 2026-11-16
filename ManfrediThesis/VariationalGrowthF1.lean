import ManfrediThesis.Preamble
open MeasureTheory

/-- Condition (F1) of §4 alone: the two-sided growth condition on the
integrand, together with the Carathéodory property. -/
structure VariationalGrowthF1 (n : ℕ) (p ε lam Lam a : ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ) : Prop where

  meas_x : ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)), Measurable fun x => fdens x z h
  cont_zh : ∀ x : EuclideanSpace ℝ (Fin n),
    Continuous fun q : ℝ × EuclideanSpace ℝ (Fin n) => fdens x q.1 q.2
  F1 : ∀ x ∈ Ω, ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)),
    -a + lam * (ε + ‖h‖ ^ 2) ^ (p / 2) ≤ fdens x z h ∧
      fdens x z h ≤ Lam * (ε + ‖h‖ ^ 2) ^ (p / 2) + a
