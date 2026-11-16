import ManfrediThesis.Preamble
open MeasureTheory

/-- Conditions (F1), (F2) and (F3) of §4 for the integrand `fdens`, together
with the Carathéodory property. -/
structure VariationalStructureF123 (n : ℕ) (p ε lam Lam a ν₀ ν₁ : ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (σ : ℝ → ℝ) : Prop where

  meas_x : ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)), Measurable fun x => fdens x z h
  cont_zh : ∀ x : EuclideanSpace ℝ (Fin n),
    Continuous fun q : ℝ × EuclideanSpace ℝ (Fin n) => fdens x q.1 q.2
  F1 : ∀ x ∈ Ω, ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)),
    -a + lam * (ε + ‖h‖ ^ 2) ^ (p / 2) ≤ fdens x z h ∧
      fdens x z h ≤ Lam * (ε + ‖h‖ ^ 2) ^ (p / 2) + a
  F2_diff : ∀ x ∈ Ω, ∀ z : ℝ, ContDiff ℝ 1 (fdens x z)
  F2_diff2 : ∀ x ∈ Ω, ∀ z : ℝ,
    ContDiffOn ℝ 2 (fdens x z) {h : EuclideanSpace ℝ (Fin n) | ε + ‖h‖ ^ 2 ≠ 0}
  F2 : ∀ x ∈ Ω, ∀ (z : ℝ) (h ζ : EuclideanSpace ℝ (Fin n)), ε + ‖h‖ ^ 2 ≠ 0 →
    ν₀ * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖ζ‖ ^ 2
        ≤ fderiv ℝ (fun h' => fderiv ℝ (fdens x z) h' ζ) h ζ ∧
      fderiv ℝ (fun h' => fderiv ℝ (fdens x z) h' ζ) h ζ
        ≤ ν₁ * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖ζ‖ ^ 2
  σ_bdd : ∃ C : ℝ, ∀ t : ℝ, σ t ≤ C
  σ_cont : Continuous σ
  σ_mono : Monotone σ
  σ_zero : σ 0 = 0
  F3 : ∀ x ∈ Ω, ∀ x' ∈ Ω, ∀ (z z' : ℝ) (h : EuclideanSpace ℝ (Fin n)),
    |fdens x z h - fdens x' z' h|
      ≤ (1 + ‖h‖ ^ 2) ^ (p / 2) * σ (dist x x' + |z - z'|)
