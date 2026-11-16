import ManfrediThesis.Preamble
set_option maxHeartbeats 800000
open MeasureTheory

/-- The monotonicity lower bound for the symmetric difference quotient of the
mollified field: for every `t > 0`,
\[
C_M\gamma_0\|ξ\|^2\!\int\bigl(2\|h+\sqrt e\,z\|^2+2t^2\|ξ\|^2\bigr)^{\frac p2-1}ρ(z)\,dz
\ \le\ \frac1{2t}\,\bigl\langle ξ,\,A_e(h+tξ)-A_e(h-tξ)\bigr\rangle ,
\]
where `A_e(h') = ∫ρ(z)A(h' + \sqrt e z)dz - ∫ρ(z)A(\sqrt e z)dz` is written out
in full, exactly as the consumer holds it.

Conventions, restated here because a helper inherits none of its parent's.
Per pm-0024(1) the structure weight is the printed `Real.rpow`
`(ε + ‖·‖²)^{p/2-1}`, here at `ε = 0` inside the monotonicity hypothesis and
with the explicit `2‖h+\sqrt e z‖² + 2t²‖ξ‖²` argument in the conclusion; no
sign hypothesis on `p/2 - 1` is needed because every base is positive under the
hypotheses.  `⟨ξ, ·⟩` is `innerSL ℝ ξ` and the coordinate form `∑ i, v i * ξ i`
is related to it by hypothesis, since the two are the same pairing written
differently.  The mollifier `ρ` is only assumed nonnegative here: its mass and
support enter the parent's argument, not this inequality.

The route.  Fix `t > 0` and apply the monotonicity hypothesis to the pair
`a = h + tξ + \sqrt e z`, `b = h - tξ + \sqrt e z`, whose difference is
`a - b = 2tξ`, giving pointwise in `z`
\[
C_M\gamma_0\bigl(\|a\|^2+\|b\|^2\bigr)^{\frac p2-1}\,4t^2\|ξ\|^2
\ \le\ \sum_i\bigl(A(a)_i-A(b)_i\bigr)(a_i-b_i)
 = 2t\,\bigl\langle ξ,\,A(a)-A(b)\bigr\rangle .
\]
The left-hand base is bounded below using
`‖a‖² + ‖b‖² ≥ \tfrac12\|a+b\|²`-type convexity in the form
`‖a‖² + ‖b‖² ≤ 2‖h+\sqrt e z‖² + 2t²‖ξ‖²`, so that the DECREASING or
INCREASING behaviour of the real power is handled by the sign of `p/2 - 1`
uniformly through the printed bound; multiplying by `ρ(z) ≥ 0` and integrating
in `z` --- both sides being integrable by hypothesis --- gives
\[
C_M\gamma_0\,4t^2\|ξ\|^2\!\int\bigl(2\|h+\sqrt e\,z\|^2+2t^2\|ξ\|^2\bigr)^{\frac p2-1}ρ
\ \le\ 2t\!\int\bigl\langle ξ,A(h+tξ+\sqrt e z)-A(h-tξ+\sqrt e z)\bigr\rangle ρ(z)\,dz .
\]
The right-hand integral is `2t⟨ξ, A_e(h+tξ) - A_e(h-tξ)⟩`, the two subtracted
constants `∫ρA(\sqrt e z)` cancelling and the pairing commuting with the
integral by linearity.  Dividing by `4t^2 > 0` and rearranging gives the
assertion. -/
theorem MollifiedFieldDifferenceQuotientLowerBound :
    ∀ (n : ℕ) (p CM γ₀ e : ℝ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
      (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (h ξ : EuclideanSpace ℝ (Fin n)),
      (∀ z, 0 ≤ ρ z) →
      (∀ v : EuclideanSpace ℝ (Fin n), (∑ i, v i * ξ i) = (innerSL ℝ ξ) v) →
      (∀ a b : EuclideanSpace ℝ (Fin n),
        CM * γ₀ * (0 + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2
          ≤ ∑ i, (A a i - A b i) * (a i - b i)) →
      (∀ h' : EuclideanSpace ℝ (Fin n),
        Integrable (fun z => ρ z • A (h' + Real.sqrt e • z)) volume) →
      (∀ t : ℝ, 0 < t →
        Integrable (fun z => (2 * ‖h + Real.sqrt e • z‖ ^ 2
          + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) * ρ z) volume) →
      (∀ t : ℝ,
        Integrable (fun z => ((innerSL ℝ ξ)
          (A (h + t • ξ + Real.sqrt e • z) - A (h - t • ξ + Real.sqrt e • z)))
            * ρ z) volume) →
      ∀ t : ℝ, 0 < t →
        CM * γ₀ * ‖ξ‖ ^ 2 * (∫ z, (2 * ‖h + Real.sqrt e • z‖ ^ 2
            + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) * ρ z)
          ≤ (2 * t)⁻¹ * (innerSL ℝ ξ)
              ((fun h' : EuclideanSpace ℝ (Fin n) =>
                  (∫ z, ρ z • A (h' + Real.sqrt e • z))
                    - ∫ z, ρ z • A (Real.sqrt e • z)) (h + t • ξ)
                - (fun h' : EuclideanSpace ℝ (Fin n) =>
                  (∫ z, ρ z • A (h' + Real.sqrt e • z))
                    - ∫ z, ρ z • A (Real.sqrt e • z)) (h - t • ξ)) := by
  intro n p CM γ₀ e ρ A h ξ hρ0 hIP hMA hAint hLint hRint
  intro t ht
  -- the pointwise inequality, integrated against `ρ`
  have hptw : ∀ z : EuclideanSpace ℝ (Fin n),
      (CM * γ₀ * 4 * t ^ 2 * ‖ξ‖ ^ 2)
          * ((2 * ‖h + Real.sqrt e • z‖ ^ 2 + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1)
            * ρ z)
        ≤ (2 * t) * (((innerSL ℝ ξ)
            (A (h + t • ξ + Real.sqrt e • z)
              - A (h - t • ξ + Real.sqrt e • z))) * ρ z) := by
    intro z
    have hma := hMA (h + t • ξ + Real.sqrt e • z) (h - t • ξ + Real.sqrt e • z)
    have hsub : (h + t • ξ + Real.sqrt e • z) - (h - t • ξ + Real.sqrt e • z)
        = (2 * t) • ξ := by
      rw [two_mul, add_smul]
      abel
    have hpar : (0 : ℝ) + ‖h + t • ξ + Real.sqrt e • z‖ ^ 2
          + ‖h - t • ξ + Real.sqrt e • z‖ ^ 2
        = 2 * ‖h + Real.sqrt e • z‖ ^ 2 + 2 * t ^ 2 * ‖ξ‖ ^ 2 := by
      have e1 : h + t • ξ + Real.sqrt e • z
          = (h + Real.sqrt e • z) + t • ξ := by abel
      have e2 : h - t • ξ + Real.sqrt e • z
          = (h + Real.sqrt e • z) - t • ξ := by abel
      rw [zero_add, e1, e2, parallelogram_law_with_norm ℝ, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    rw [hsub] at hma
    rw [hpar] at hma
    have hnormsub : ‖(2 * t) • ξ‖ ^ 2 = 4 * t ^ 2 * ‖ξ‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    rw [hnormsub] at hma
    have hrhs : (∑ i, (A (h + t • ξ + Real.sqrt e • z) i
          - A (h - t • ξ + Real.sqrt e • z) i)
        * ((h + t • ξ + Real.sqrt e • z) i - (h - t • ξ + Real.sqrt e • z) i))
        = (2 * t) * ((innerSL ℝ ξ)
          (A (h + t • ξ + Real.sqrt e • z)
            - A (h - t • ξ + Real.sqrt e • z))) := by
      rw [← hIP, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hco : (h + t • ξ + Real.sqrt e • z) i
          - (h - t • ξ + Real.sqrt e • z) i = 2 * t * ξ i := by
        have hh := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hsub
        simpa using hh
      rw [hco]
      simp only [WithLp.ofLp_sub, Pi.sub_apply]
      ring
    rw [hrhs] at hma
    calc (CM * γ₀ * 4 * t ^ 2 * ‖ξ‖ ^ 2)
          * ((2 * ‖h + Real.sqrt e • z‖ ^ 2 + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1)
            * ρ z)
        = (CM * γ₀
            * (2 * ‖h + Real.sqrt e • z‖ ^ 2 + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1)
            * (4 * t ^ 2 * ‖ξ‖ ^ 2)) * ρ z := by ring
      _ ≤ ((2 * t) * ((innerSL ℝ ξ)
            (A (h + t • ξ + Real.sqrt e • z)
              - A (h - t • ξ + Real.sqrt e • z)))) * ρ z :=
          mul_le_mul_of_nonneg_right (by linarith [hma]) (hρ0 z)
      _ = (2 * t) * (((innerSL ℝ ξ)
            (A (h + t • ξ + Real.sqrt e • z)
              - A (h - t • ξ + Real.sqrt e • z))) * ρ z) := by ring
  have hint := integral_mono ((hLint t ht).const_mul (CM * γ₀ * 4 * t ^ 2 * ‖ξ‖ ^ 2))
    ((hRint t).const_mul (2 * t)) hptw
  rw [integral_const_mul, integral_const_mul] at hint
  -- identify the right-hand integral
  have hR : (∫ z, ((innerSL ℝ ξ)
        (A (h + t • ξ + Real.sqrt e • z) - A (h - t • ξ + Real.sqrt e • z)))
          * ρ z)
      = (innerSL ℝ ξ) ((∫ z, ρ z • A (h + t • ξ + Real.sqrt e • z))
        - ∫ z, ρ z • A (h - t • ξ + Real.sqrt e • z)) := by
    calc (∫ z, ((innerSL ℝ ξ)
          (A (h + t • ξ + Real.sqrt e • z) - A (h - t • ξ + Real.sqrt e • z)))
            * ρ z)
        = ∫ z, (innerSL ℝ ξ) (ρ z • A (h + t • ξ + Real.sqrt e • z)
            - ρ z • A (h - t • ξ + Real.sqrt e • z)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          show ((innerSL ℝ ξ) (A (h + t • ξ + Real.sqrt e • z)
              - A (h - t • ξ + Real.sqrt e • z))) * ρ z
            = (innerSL ℝ ξ) (ρ z • A (h + t • ξ + Real.sqrt e • z)
              - ρ z • A (h - t • ξ + Real.sqrt e • z))
          rw [← smul_sub, map_smul, smul_eq_mul]
          ring
      _ = (innerSL ℝ ξ) (∫ z, (ρ z • A (h + t • ξ + Real.sqrt e • z)
            - ρ z • A (h - t • ξ + Real.sqrt e • z))) :=
          ContinuousLinearMap.integral_comp_comm _
            ((hAint (h + t • ξ)).sub (hAint (h - t • ξ)))
      _ = (innerSL ℝ ξ) ((∫ z, ρ z • A (h + t • ξ + Real.sqrt e • z))
            - ∫ z, ρ z • A (h - t • ξ + Real.sqrt e • z)) := by
          rw [integral_sub (hAint (h + t • ξ)) (hAint (h - t • ξ))]
  have ht4 : (0 : ℝ) < 4 * t ^ 2 := by positivity
  have hfin : (fun h' : EuclideanSpace ℝ (Fin n) =>
        (∫ z, ρ z • A (h' + Real.sqrt e • z))
          - ∫ z, ρ z • A (Real.sqrt e • z)) (h + t • ξ)
      - (fun h' : EuclideanSpace ℝ (Fin n) =>
        (∫ z, ρ z • A (h' + Real.sqrt e • z))
          - ∫ z, ρ z • A (Real.sqrt e • z)) (h - t • ξ)
      = (∫ z, ρ z • A (h + t • ξ + Real.sqrt e • z))
        - ∫ z, ρ z • A (h - t • ξ + Real.sqrt e • z) := by
    simp only
    abel
  rw [hfin]
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have hdiv : 2 * t * (CM * γ₀ * ‖ξ‖ ^ 2
        * ∫ z, (2 * ‖h + Real.sqrt e • z‖ ^ 2
          + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) * ρ z)
      ≤ (innerSL ℝ ξ) ((∫ z, ρ z • A (h + t • ξ + Real.sqrt e • z))
        - ∫ z, ρ z • A (h - t • ξ + Real.sqrt e • z)) := by
    refine le_of_mul_le_mul_left ?_ h2t
    calc 2 * t * (2 * t * (CM * γ₀ * ‖ξ‖ ^ 2
          * ∫ z, (2 * ‖h + Real.sqrt e • z‖ ^ 2
            + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) * ρ z))
        = CM * γ₀ * 4 * t ^ 2 * ‖ξ‖ ^ 2
          * ∫ z, (2 * ‖h + Real.sqrt e • z‖ ^ 2
            + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) * ρ z := by ring
      _ ≤ 2 * t * ∫ z, ((innerSL ℝ ξ)
            (A (h + t • ξ + Real.sqrt e • z)
              - A (h - t • ξ + Real.sqrt e • z))) * ρ z := hint
      _ = 2 * t * (innerSL ℝ ξ) ((∫ z, ρ z • A (h + t • ξ + Real.sqrt e • z))
            - ∫ z, ρ z • A (h - t • ξ + Real.sqrt e • z)) := by rw [hR]
  calc CM * γ₀ * ‖ξ‖ ^ 2
        * ∫ z, (2 * ‖h + Real.sqrt e • z‖ ^ 2
          + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) * ρ z
      = (2 * t)⁻¹ * (2 * t * (CM * γ₀ * ‖ξ‖ ^ 2
        * ∫ z, (2 * ‖h + Real.sqrt e • z‖ ^ 2
          + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) * ρ z)) := by
        field_simp
    _ ≤ (2 * t)⁻¹ * (innerSL ℝ ξ)
        ((∫ z, ρ z • A (h + t • ξ + Real.sqrt e • z))
          - ∫ z, ρ z • A (h - t • ξ + Real.sqrt e • z)) :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
