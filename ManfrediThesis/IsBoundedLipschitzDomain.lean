import ManfrediThesis.Preamble
open MeasureTheory

/-- `IsBoundedLipschitzDomain n Ω`: `Ω` is a bounded Lipschitz domain in `ℝⁿ`.
This is the hypothesis the paper places on `Ω'` in §4 and §5 -- at l. 1130,
l. 1274, l. 1431 and l. 1551, "Let `Ω'` be a Lipschitz domain such that
`closure Ω' ⊂ Ω`" -- and the hypothesis the cited result (C5) carries at
l. 264, "if `Ω'` is a bounded Lipschitz domain".  "Domain" is open and
connected; "Lipschitz" is the local one-sided graph condition on the boundary,
stated here with the graph function defined on all of `ℝⁿ` and required to be
invariant in the normal direction, which avoids coordinates on a hyperplane. -/
def IsBoundedLipschitzDomain (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=

  IsOpen Ω ∧ IsConnected Ω ∧ Bornology.IsBounded Ω ∧
    ∀ x ∈ frontier Ω,
      ∃ (r L : ℝ) (ν : EuclideanSpace ℝ (Fin n))
        (φ : EuclideanSpace ℝ (Fin n) → ℝ),
        0 < r ∧ 0 ≤ L ∧ ‖ν‖ = 1 ∧
          LipschitzWith (Real.toNNReal L) φ ∧
          (∀ (y : EuclideanSpace ℝ (Fin n)) (t : ℝ), φ (y + t • ν) = φ y) ∧
          ∀ y ∈ Metric.ball x r,
            (y ∈ Ω ↔ φ (y - x) < ∑ i, (y - x) i * ν i)
