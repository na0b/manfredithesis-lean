import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pOn
open MeasureTheory

/-- `MemW1pZeroOn n p Ω f g`: `f ∈ W^{1,p}_0(Ω)` with weak gradient `g`. -/
def MemW1pZeroOn (n : ℕ) (p : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=

  MemW1pOn n p Ω f g ∧
    ∃ φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k) ∧ HasCompactSupport (φ k) ∧ tsupport (φ k) ⊆ Ω) ∧
      Filter.Tendsto (fun k => ∫ x in Ω, |f x - φ k x| ^ p) Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun k => ∫ x in Ω,
          (∑ i, |g x i - fderiv ℝ (φ k) x (EuclideanSpace.single i (1 : ℝ))| ^ 2) ^ (p / 2))
        Filter.atTop (nhds 0)
