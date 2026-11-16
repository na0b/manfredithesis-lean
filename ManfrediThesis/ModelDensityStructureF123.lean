import ManfrediThesis.Preamble
import ManfrediThesis.VariationalStructureF123
open MeasureTheory

/-- The paper's own model density `f(h) = (ε + |h|²)^(p/2)` of §4 satisfies
conditions (F1), (F2) and (F3) on all of `ℝⁿ`, for every `ε ≥ 0` and every `p`
in the singular range `1 < p < 2`, with `lam = Lam = 1`, any `a ≥ 0`, modulus
`σ ≡ 0`, and the ellipticity constants `ν₀ = p(p-1)`, `ν₁ = p`.  The second
conjunct adds (F4) for that modulus, at every `cσ > 0` and `δ > 0`.

This is an inhabitation witness, and that is its purpose: the Note for the
formalization requires at l. 258 that the cited results "must not be vacuous
(each must be a true statement for the operators to which it is applied)", and
the demand applies a fortiori to the structure bundle the §4 statements are
conditioned on.  Together with `ModelFieldStructureQ12` for the §§1-3 bundle it
is the reason `VariationalStructureF123` can be edited safely: the witness is
re-read whenever a clause is added.

The constants are admissible at the consumers: `0 < lam ≤ Lam` holds as
`1 ≤ 1`, and `0 < ν₀ < ν₁` holds because `0 < p(p-1) < p` exactly when
`0 < p - 1 < 1`, i.e. on `1 < p < 2`.  `a` is left free and merely required
nonnegative, so the witness applies at the consumers' `0 < a`. -/
theorem ModelDensityStructureF123 :
    ∀ (n : ℕ) (p ε a : ℝ), 1 ≤ n → 1 < p → p < 2 → 0 ≤ ε → 0 ≤ a →
      VariationalStructureF123 n p ε 1 1 a (p * (p - 1)) p Set.univ
          (fun _ _ h => (ε + ‖h‖ ^ 2) ^ (p / 2)) (fun _ => 0)
        ∧ ∀ cσ δ : ℝ, 0 < cσ → 0 < δ → ∀ t : ℝ, 0 ≤ t →
            (fun _ : ℝ => (0 : ℝ)) t ≤ cσ * t ^ δ := by
  intro n p ε a hn hp1 hp2 hε ha
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp1
  -- the degeneracy set is open
  have hDopen : IsOpen {y : EuclideanSpace ℝ (Fin n) | ε + ‖y‖ ^ 2 ≠ 0} := by
    have hc : Continuous fun y : EuclideanSpace ℝ (Fin n) => ε + ‖y‖ ^ 2 :=
      continuous_const.add (continuous_norm.pow 2)
    exact isOpen_ne.preimage hc
  -- the weight and its derivative
  have hwd : ∀ h : EuclideanSpace ℝ (Fin n),
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => ε + ‖y‖ ^ 2) (2 • innerSL ℝ h) h :=
    fun h => ((hasStrictFDerivAt_norm_sq h).hasFDerivAt).const_add ε
  -- the first derivative of the density off the degeneracy set
  have hfd : ∀ h : EuclideanSpace ℝ (Fin n), ε + ‖h‖ ^ 2 ≠ 0 →
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => (ε + ‖y‖ ^ 2) ^ (p / 2))
        (((p / 2) * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1)) • (2 • innerSL ℝ h)) h :=
    fun h hh => (hwd h).rpow_const (Or.inl hh)
  have hfderiv : ∀ h : EuclideanSpace ℝ (Fin n), ε + ‖h‖ ^ 2 ≠ 0 →
      ∀ ξ : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => (ε + ‖y‖ ^ 2) ^ (p / 2)) h ξ
        = p * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * (inner ℝ h ξ : ℝ) := by
    intro h hh ξ
    rw [(hfd h hh).fderiv]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
    ring
  -- smoothness off the degeneracy set
  have hCD2 : ∀ h : EuclideanSpace ℝ (Fin n), ε + ‖h‖ ^ 2 ≠ 0 →
      ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => (ε + ‖y‖ ^ 2) ^ (p / 2)) h := by
    intro h hh
    have h1 : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => ε + ‖y‖ ^ 2) h :=
      (contDiff_const.add (contDiff_norm_sq ℝ)).contDiffAt
    exact h1.rpow_const_of_ne hh
  -- a degenerate point forces `ε = 0` and `h = 0`
  have hdeg : ∀ h : EuclideanSpace ℝ (Fin n), ε + ‖h‖ ^ 2 = 0 → ε = 0 ∧ h = 0 := by
    intro h hh
    have h1 : ‖h‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖h‖, norm_nonneg h]
    have h2 : ε = 0 := by linarith [sq_nonneg ‖h‖]
    exact ⟨h2, norm_eq_zero.mp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h1)⟩
  -- `(‖y‖²)^(p/2) = ‖y‖^p`
  have hnp : ∀ y : EuclideanSpace ℝ (Fin n), ((‖y‖ ^ 2 : ℝ)) ^ (p / 2) = ‖y‖ ^ p := by
    intro y
    rw [← Real.rpow_natCast ‖y‖ 2, ← Real.rpow_mul (norm_nonneg y)]
    congr 1
    push_cast
    ring
  -- `t ↦ t^(p-1)` tends to `0` at `0`, composed with the norm
  have htend : Filter.Tendsto (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ (p - 1))
      (nhds (0 : EuclideanSpace ℝ (Fin n))) (nhds 0) := by
    have h1 : Filter.Tendsto (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖)
        (nhds (0 : EuclideanSpace ℝ (Fin n))) (nhds 0) := by
      simpa using (continuous_norm (E := EuclideanSpace ℝ (Fin n))).tendsto 0
    have h2 : Filter.Tendsto (fun s : ℝ => s ^ (p - 1)) (nhds 0) (nhds 0) := by
      have := Real.continuousAt_rpow_const 0 (p - 1) (Or.inr (by linarith))
      simpa [ContinuousAt, Real.zero_rpow (show p - 1 ≠ 0 by linarith)] using this
    exact h2.comp h1
  -- the derivative at a degenerate point is `0`
  have hdegd : ∀ h : EuclideanSpace ℝ (Fin n), ε + ‖h‖ ^ 2 = 0 →
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => (ε + ‖y‖ ^ 2) ^ (p / 2))
        (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) h := by
    intro h hh
    obtain ⟨hε0, hh0⟩ := hdeg h hh
    subst hε0
    subst hh0
    rw [hasFDerivAt_iff_tendsto]
    have hfun : ∀ y : EuclideanSpace ℝ (Fin n),
        ‖y - 0‖⁻¹ * ‖(0 + ‖y‖ ^ 2) ^ (p / 2)
            - (0 + ‖(0 : EuclideanSpace ℝ (Fin n))‖ ^ 2) ^ (p / 2)
            - (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (y - 0)‖ = ‖y‖ ^ (p - 1) := by
      intro y
      have hz : (0 + ‖(0 : EuclideanSpace ℝ (Fin n))‖ ^ 2 : ℝ) ^ (p / 2) = 0 := by
        simp [Real.zero_rpow (show p / 2 ≠ 0 by positivity)]
      rw [hz]
      simp only [sub_zero, zero_apply, zero_add]
      rcases eq_or_ne y 0 with rfl | hy
      · simp [Real.zero_rpow (show p - 1 ≠ 0 by linarith)]
      · have hy0 : (0:ℝ) < ‖y‖ := norm_pos_iff.mpr hy
        rw [hnp y, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _)]
        rw [← Real.rpow_neg_one ‖y‖, ← Real.rpow_add hy0]
        congr 1
        ring
    simp only [hfun]
    exact htend
  -- `‖Df(y)‖ ≤ p ‖y‖^(p-1)` in the degenerate case `ε = 0`
  have hC1 : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin n) => (ε + ‖y‖ ^ 2) ^ (p / 2)) := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun h => ?_, ?_⟩
    · by_cases hh : ε + ‖h‖ ^ 2 = 0
      · exact (hdegd h hh).differentiableAt
      · exact (hfd h hh).differentiableAt
    · rw [continuous_iff_continuousAt]
      intro h
      by_cases hh : ε + ‖h‖ ^ 2 = 0
      · obtain ⟨hε0, hh0⟩ := hdeg h hh
        subst hε0
        subst hh0
        rw [ContinuousAt, (hdegd 0 (by simp)).fderiv]
        have hbound : ∀ y : EuclideanSpace ℝ (Fin n),
            ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => (0 + ‖z‖ ^ 2) ^ (p / 2)) y‖
              ≤ p * ‖y‖ ^ (p - 1) := by
          intro y
          rcases eq_or_ne y 0 with rfl | hy
          · rw [(hdegd 0 (by simp)).fderiv]
            simp [Real.zero_rpow (show p - 1 ≠ 0 by linarith)]
          · have hy0 : (0:ℝ) < ‖y‖ := norm_pos_iff.mpr hy
            have hyne : (0:ℝ) + ‖y‖ ^ 2 ≠ 0 := by positivity
            refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun ξ => ?_)
            rw [hfderiv y hyne ξ, Real.norm_eq_abs, abs_mul, abs_mul]
            have h1 : |(inner ℝ y ξ : ℝ)| ≤ ‖y‖ * ‖ξ‖ := abs_real_inner_le_norm y ξ
            have h2 : |((0:ℝ) + ‖y‖ ^ 2) ^ (p / 2 - 1)| = ‖y‖ ^ (p - 2) := by
              rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _), zero_add,
                ← Real.rpow_natCast ‖y‖ 2, ← Real.rpow_mul (norm_nonneg y)]
              congr 1
              ring
            have h3 : ‖y‖ ^ (p - 2) * ‖y‖ = ‖y‖ ^ (p - 1) := by
              rw [← Real.rpow_add_one hy0.ne']
              congr 1
              ring
            have h4 : (0:ℝ) ≤ ‖y‖ ^ (p - 2) := Real.rpow_nonneg (norm_nonneg y) _
            rw [h2, abs_of_pos hp0]
            calc p * ‖y‖ ^ (p - 2) * |(inner ℝ y ξ : ℝ)|
                ≤ p * ‖y‖ ^ (p - 2) * (‖y‖ * ‖ξ‖) := by
                  refine mul_le_mul_of_nonneg_left h1 (by positivity)
              _ = p * (‖y‖ ^ (p - 2) * ‖y‖) * ‖ξ‖ := by ring
              _ = p * ‖y‖ ^ (p - 1) * ‖ξ‖ := by rw [h3]
        have hlim : Filter.Tendsto (fun y : EuclideanSpace ℝ (Fin n) => p * ‖y‖ ^ (p - 1))
            (nhds (0 : EuclideanSpace ℝ (Fin n))) (nhds 0) := by
          have := htend.const_mul p
          simpa using this
        exact squeeze_zero_norm hbound hlim
      · exact ((hCD2 h hh).fderiv_right (m := 0) (by norm_num)).continuousAt
  -- the second derivative in the direction `ζ`
  have hsecond : ∀ h ζ : EuclideanSpace ℝ (Fin n), ε + ‖h‖ ^ 2 ≠ 0 →
      fderiv ℝ (fun h' : EuclideanSpace ℝ (Fin n) =>
          fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => (ε + ‖y‖ ^ 2) ^ (p / 2)) h' ζ) h ζ
        = p * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖ζ‖ ^ 2
          + p * (p - 2) * (ε + ‖h‖ ^ 2) ^ (p / 2 - 2) * (inner ℝ h ζ : ℝ) ^ 2 := by
    intro h ζ hh
    have heq : (fun h' : EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => (ε + ‖y‖ ^ 2) ^ (p / 2)) h' ζ)
        =ᶠ[nhds h] (fun h' : EuclideanSpace ℝ (Fin n) =>
          p * (ε + ‖h'‖ ^ 2) ^ (p / 2 - 1) * (inner ℝ h' ζ : ℝ)) := by
      filter_upwards [hDopen.mem_nhds hh] with y hy
      exact hfderiv y hy ζ
    rw [heq.fderiv_eq]
    have hu : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => (ε + ‖y‖ ^ 2) ^ (p / 2 - 1))
        (((p / 2 - 1) * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1 - 1)) • (2 • innerSL ℝ h)) h :=
      (hwd h).rpow_const (Or.inl hh)
    have hvfun : (fun y : EuclideanSpace ℝ (Fin n) => (inner ℝ y ζ : ℝ))
        = fun y : EuclideanSpace ℝ (Fin n) => (innerSL ℝ ζ) y := by
      funext y
      rw [innerSL_apply_apply, real_inner_comm]
    have hv : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => (inner ℝ y ζ : ℝ))
        (innerSL ℝ ζ) h := by
      rw [hvfun]
      exact (innerSL ℝ ζ).hasFDerivAt
    have hG : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) =>
        p * (ε + ‖y‖ ^ 2) ^ (p / 2 - 1) * (inner ℝ y ζ : ℝ)) _ h :=
      (hu.const_mul p).mul hv
    rw [hG.fderiv]
    simp only [smul_apply, add_apply, innerSL_apply_apply, smul_eq_mul]
    rw [real_inner_self_eq_norm_sq, real_inner_comm ζ h]
    have hexp : (ε + ‖h‖ ^ 2) ^ (p / 2 - 1 - 1) = (ε + ‖h‖ ^ 2) ^ (p / 2 - 2) := by
      congr 1
      ring
    rw [hexp]
    ring
  -- the scalar form of the two (F2) bounds
  have hscal : ∀ W N I : ℝ, 0 < W → 0 ≤ N → I ^ 2 ≤ W * N →
      p * (p - 1) * W ^ (p / 2 - 1) * N
          ≤ p * W ^ (p / 2 - 1) * N + p * (p - 2) * W ^ (p / 2 - 2) * I ^ 2
        ∧ p * W ^ (p / 2 - 1) * N + p * (p - 2) * W ^ (p / 2 - 2) * I ^ 2
          ≤ p * W ^ (p / 2 - 1) * N := by
    intro W N I hW hN hCS
    have hpos : (0:ℝ) < W ^ (p / 2 - 2) := Real.rpow_pos_of_pos hW _
    have hWt : W ^ (p / 2 - 2) * W = W ^ (p / 2 - 1) := by
      rw [← Real.rpow_add_one hW.ne']
      congr 1
      ring
    constructor
    · rw [← hWt]
      have hhint : (0:ℝ) ≤ p * (2 - p) * (W ^ (p / 2 - 2) * (W * N - I ^ 2)) :=
        mul_nonneg (mul_nonneg hp0.le (by linarith))
          (mul_nonneg hpos.le (by linarith))
      nlinarith [hhint]
    · have hhint : (0:ℝ) ≤ p * (2 - p) * (W ^ (p / 2 - 2) * I ^ 2) :=
        mul_nonneg (mul_nonneg hp0.le (by linarith))
          (mul_nonneg hpos.le (sq_nonneg I))
      nlinarith [hhint]
  -- assemble
  refine ⟨⟨fun _ _ => measurable_const, fun _ => hC1.continuous.comp continuous_snd,
    fun _ _ _ _ => ⟨by linarith [ha], by linarith [ha]⟩, fun _ _ _ => hC1,
    fun _ _ _ => fun y hy => (hCD2 y (by simpa using hy)).contDiffWithinAt, ?_,
    ⟨0, fun _ => le_refl 0⟩, continuous_const, monotone_const, rfl, ?_⟩, ?_⟩
  · -- (F2)
    intro x _ z h ζ hh
    have hW : (0:ℝ) < ε + ‖h‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hh)
    have hCS : (inner ℝ h ζ : ℝ) ^ 2 ≤ (ε + ‖h‖ ^ 2) * ‖ζ‖ ^ 2 := by
      have h1 := real_inner_mul_inner_self_le h ζ
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
      nlinarith [h1, sq_nonneg ‖ζ‖]
    obtain ⟨hlo, hhi⟩ := hscal (ε + ‖h‖ ^ 2) (‖ζ‖ ^ 2) (inner ℝ h ζ : ℝ) hW
      (sq_nonneg _) hCS
    rw [hsecond h ζ hh]
    exact ⟨hlo, hhi⟩
  · -- (F3)
    intro x _ x' _ z z' h
    simp
  · -- (F4)
    intro cσ δ hcσ hδ t ht
    positivity
