import ManfrediThesis.Preamble
open MeasureTheory

/-- `EssOscOn n s f`: the essential oscillation of `f` on `s`. -/
noncomputable def EssOscOn (n : ℕ) (s : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=

  essSup f (volume.restrict s) - essInf f (volume.restrict s)
