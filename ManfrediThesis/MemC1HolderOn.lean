import ManfrediThesis.Preamble
open MeasureTheory

/-- `MemC1HolderOn n β Ω Ωcl u g`: `u ∈ C^1(Ω)` with gradient `g`, and `g` is
`β`-Hölder on `Ωcl`.  At `Ωcl = closure Ω` this is the class
`C^{1+β}(closure Ω)` of §4 and §5, whose Hölder seminorm the paper takes on the
closure (l. 278) while its displayed conclusions place the differentiability on
the open set (l. 1352, l. 1574); Lemma 3.1 writes the same split as
`C^1(B_R) ∩ C^β(closure B_R)` (l. 559).  Taking `Ωcl = Ω` recovers the
one-set class definitionally. -/
def MemC1HolderOn (n : ℕ) (β : ℝ) (Ω Ωcl : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=

  (∀ x ∈ Ω, DifferentiableAt ℝ u x ∧
      ∀ i : Fin n, fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)) = g x i) ∧
    ContinuousOn g Ωcl ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ωcl, ∀ y ∈ Ωcl, ‖g x - g y‖ ≤ C * dist x y ^ β
