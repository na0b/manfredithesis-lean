import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.EllipticStructureQ6
import ManfrediThesis.StructureQ12AtEveryPoint
open MeasureTheory

/-- Freezing the field of the equation at a point of the domain, normalised at
the origin, keeps all six clauses of (Q1)-(Q2) on the whole of `ℝⁿ` with the
same constants, and so does the frozen field itself before normalisation.  This is the §5 freezing `A⁰ = A(x₀, U(x₀), ·)` of thesis
l. 1467, together with the paper's own normalisation at l. 542, "since
`div A(0) = 0` we may assume without loss of generality that `A(0) = 0`".

The hypothesis `EllipticStructureQ6` is not decoration and the node is false
without it.  (Q1) and (Q2) are stated for *almost every* `x ∈ Ω`, while a
frozen field is constant in `x`, so its (Q1)/(Q2) clauses are the original ones
evaluated at the *single* point `x₁` -- a null set, about which the
almost-everywhere hypothesis says nothing.  That is pm-0034's gap, and the
upgrade from "almost every `x`" to "every `x`" is exactly
`StructureQ12AtEveryPoint`, which consumes the (Q6) modulus.

This is the equation-side analogue of `FrozenOperatorStructureQ12`, which is
the §4 branch: that node freezes the *gradient operator of a variational
integrand*, `FrozenGradientOperator n fdens x₁ z₁`, and its hypothesis is
`VariationalStructureF123` on `fdens`.  The present node freezes the field `A`
of the equation itself and its hypotheses are `EllipticStructureQ12` and
`EllipticStructureQ6` on `A`.  Neither implies the other: no variational
integrand is available on the equation side, and `EllipticStructureQ6` is not
available on the variational side. -/
theorem FrozenSolutionStructureQ12 :
    ∀ (n : ℕ) (p ε γ₀ γ₁ : ℝ), 2 ≤ n → 1 < p → 0 ≤ ε → 0 < γ₀ → 0 < γ₁ →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n))
        (σ : ℝ → ℝ) (x₁ : EuclideanSpace ℝ (Fin n)) (z₁ : ℝ),
        IsOpen Ω → x₁ ∈ Ω →
        EllipticStructureQ12 n p ε γ₀ γ₁ Ω A →
        EllipticStructureQ6 n p Ω A σ →
        EllipticStructureQ12 n p ε γ₀ γ₁ Set.univ (fun _ _ h => A x₁ z₁ h)
          ∧ EllipticStructureQ12 n p ε γ₀ γ₁ Set.univ
              (fun _ _ h => A x₁ z₁ h - A x₁ z₁ 0) := by
  intro n p ε γ₀ γ₁ hn hp hε hγ₀ hγ₁ Ω A σ x₁ z₁ hΩ hx₁ hQ12 hQ6
  obtain ⟨hq1, hq2⟩ :=
    StructureQ12AtEveryPoint n p ε γ₀ γ₁ hn hp hε hγ₀ hγ₁ Ω A σ hΩ hQ12 hQ6
  have hcont₁ : Continuous (A x₁ z₁) := hQ12.hcont x₁ hx₁ z₁
  have hdiff₁ : ContDiffOn ℝ 1 (A x₁ z₁)
      {h : EuclideanSpace ℝ (Fin n) | ε + ‖h‖ ^ 2 ≠ 0} := hQ12.hdiff x₁ hx₁ z₁
  have hfd : ∀ h : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fun y => A x₁ z₁ y - A x₁ z₁ 0) h = fderiv ℝ (A x₁ z₁) h :=
    fun h => fderiv_sub_const _
  refine ⟨⟨fun z h => measurable_const, fun x => hcont₁.comp continuous_snd,
      fun x _ z => hcont₁, fun x _ z => hdiff₁, ?_, ?_⟩,
    ⟨fun z h => measurable_const,
      fun x => (hcont₁.sub continuous_const).comp continuous_snd,
      fun x _ z => hcont₁.sub continuous_const,
      fun x _ z => hdiff₁.sub contDiffOn_const, ?_, ?_⟩⟩
  · exact Filter.Eventually.of_forall fun x _ z h ξ hne => hq1 x₁ hx₁ z₁ h ξ hne
  · exact Filter.Eventually.of_forall fun x _ z h i j hne => hq2 x₁ hx₁ z₁ h i j hne
  · refine Filter.Eventually.of_forall fun x _ z h ξ hne => ?_
    rw [hfd h]
    exact hq1 x₁ hx₁ z₁ h ξ hne
  · refine Filter.Eventually.of_forall fun x _ z h i j hne => ?_
    rw [hfd h]
    exact hq2 x₁ hx₁ z₁ h i j hne
