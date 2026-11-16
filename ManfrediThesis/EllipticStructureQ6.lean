import ManfrediThesis.Preamble
open MeasureTheory

/-- Condition (Q6) of the paper: Dini continuity of `A` in `(x, z)`, uniformly
in `h`, with modulus `σ`. -/
structure EllipticStructureQ6 (n : ℕ) (p : ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n))
    (σ : ℝ → ℝ) : Prop where

  σ_bdd : ∃ C : ℝ, ∀ t : ℝ, σ t ≤ C
  σ_cont : Continuous σ
  σ_mono : Monotone σ
  σ_zero : σ 0 = 0
  Q6 : ∀ x ∈ Ω, ∀ x' ∈ Ω, ∀ (z z' : ℝ) (h : EuclideanSpace ℝ (Fin n)),
    ‖A x z h - A x' z' h‖
      ≤ σ (dist x x' + |z - z'|) * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2)
