import ManfrediThesis.Preamble
import ManfrediThesis.MeanReplacementLpGeneral
open MeasureTheory

/-- The mean-replacement inequality: on a set `s` of finite positive measure, the
`L^p` deviation of `f` from its own mean is controlled, with the constant `2^p`,
by the deviation from an arbitrary constant vector `c`. -/
theorem MeanReplacementLp :
    ∀ (n : ℕ) (p : ℝ) (s : Set (EuclideanSpace ℝ (Fin n)))
      (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (c : EuclideanSpace ℝ (Fin n)),
      1 < p → MeasurableSet s → 0 < volume s → volume s ≠ ⊤ →
      MemLp f (ENNReal.ofReal p) (volume.restrict s) →
      (∫ x in s, ‖f x - (volume s).toReal⁻¹ • ∫ y in s, f y‖ ^ p)
        ≤ 2 ^ p * ∫ x in s, ‖f x - c‖ ^ p := by
  intro n p s f c hp _hsm hs0 hsfin hf
  exact MeanReplacementLpGeneral n p s f c hp hs0 hsfin hf
