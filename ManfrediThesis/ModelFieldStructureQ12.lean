import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
open MeasureTheory Real

/-- The paper's own model field `A(h) = ‖h‖^(p-2) h` of (1.3) satisfies the
tablet's `EllipticStructureQ12` on all of `ℝⁿ` at the degenerate parameter
`ε = 0`, on the singular range `1 < p < 2`, with `γ₀ = p - 1 > 0` and
`γ₁ = 3 - p`, so that `γ₁/γ₀ = (3-p)/(p-1)` depends only on `p`.

This is an inhabitation witness, and that is its purpose: the Note for the
formalization requires at l. 258 that the cited results "must not be vacuous
(each must be a true statement for the operators to which it is applied)", and a
structure bundle that no field satisfies would make every statement assuming it
vacuously true.  A bundle carrying a witness cannot be vacuous, and the witness
is re-checked mechanically whenever the bundle is edited -- in particular it
discharges the two Carathéodory clauses `meas_x` and `cont_zh`, and it is the
reason the restriction of the differentiability clause to `{h : ε + ‖h‖² ≠ 0}`
is a correction rather than a convenience: read on all of `ℝⁿ` the conditions
are satisfied by nothing at all when `ε = 0` and `1 < p < 2`.

`γ₁ = 3 - p` rather than `1` because the tablet's (Q2) is the componentwise
bound `|(DA(h)eⱼ)ᵢ| ≤ γ₁ w`, not the quadratic form. -/
theorem ModelFieldStructureQ12 :
    ∀ (n : ℕ) (p : ℝ), 1 ≤ n → 1 < p → p < 2 →
      EllipticStructureQ12 n p 0 (p - 1) (3 - p) Set.univ
        (fun _ _ h => (‖h‖ ^ 2) ^ ((p - 2) / 2) • h) := by
  intro n p _ hp1 hp2
  -- `Amod` as a local abbreviation for the model field.
  set Amod : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun h => (‖h‖ ^ 2) ^ ((p - 2) / 2) • h with hAmod
  have hAzero : Amod 0 = 0 := by simp [hAmod]
  have hasFDerivAt_Amod : ∀ {h : EuclideanSpace ℝ (Fin n)}, ‖h‖ ^ 2 ≠ 0 →
      HasFDerivAt Amod
        ((‖h‖ ^ 2) ^ ((p - 2) / 2) • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
          + ((((p - 2) / 2) * (‖h‖ ^ 2) ^ ((p - 2) / 2 - 1)) • (2 • innerSL ℝ h)).smulRight h)
        h := by
    intro h hh
    have hq : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) (2 • innerSL ℝ h) h :=
      (hasStrictFDerivAt_norm_sq h).hasFDerivAt
    have hc := hq.rpow_const (p := (p - 2) / 2) (Or.inl hh)
    exact hc.smul (hasFDerivAt_id h)
  have contDiffAt_Amod : ∀ {h : EuclideanSpace ℝ (Fin n)}, ‖h‖ ^ 2 ≠ 0 →
      ContDiffAt ℝ 1 Amod h := by
    intro h hh
    have h1 : ContDiffAt ℝ 1 (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) h :=
      (contDiff_norm_sq ℝ).contDiffAt
    exact (h1.rpow_const_of_ne hh).smul contDiffAt_id
  have fderiv_Amod_apply : ∀ {h : EuclideanSpace ℝ (Fin n)}, ‖h‖ ^ 2 ≠ 0 →
      ∀ ξ : EuclideanSpace ℝ (Fin n),
      fderiv ℝ Amod h ξ
        = (‖h‖ ^ 2) ^ ((p - 2) / 2) • ξ
          + ((p - 2) * (‖h‖ ^ 2) ^ ((p - 2) / 2 - 1) * (inner ℝ h ξ)) • h := by
    intro h hh ξ
    rw [(hasFDerivAt_Amod hh).fderiv]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply, smul_eq_mul]
    congr 2
    ring
  have abs_coord_le : ∀ (h : EuclideanSpace ℝ (Fin n)) (i : Fin n), |h i| ≤ ‖h‖ := by
    intro h i
    have := abs_real_inner_le_norm h (EuclideanSpace.single i (1 : ℝ))
    simpa [EuclideanSpace.inner_single_right, PiLp.norm_single] using this
  have norm_Amod : ∀ y : EuclideanSpace ℝ (Fin n), ‖Amod y‖ = ‖y‖ ^ (p - 1) := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · rw [hAzero]
      simp [Real.zero_rpow (show p - 1 ≠ 0 by linarith)]
    · have hy0 : (0:ℝ) < ‖y‖ := norm_pos_iff.mpr hy
      have h2 : ((‖y‖ ^ 2 : ℝ)) ^ ((p - 2) / 2) = ‖y‖ ^ (p - 2) := by
        rw [← Real.rpow_natCast ‖y‖ 2, ← Real.rpow_mul hy0.le]
        congr 1
        push_cast
        ring
      rw [hAmod]
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by positivity) _), h2,
        ← Real.rpow_add_one hy0.ne' (p - 2)]
      ring_nf
  have continuous_Amod : Continuous Amod := by
    rw [continuous_iff_continuousAt]
    intro h
    rcases eq_or_ne (‖h‖ ^ 2) 0 with hh | hh
    · have hz : h = 0 := by
        have h0 : ‖h‖ = 0 := by
          simpa using (pow_eq_zero_iff (n := 2) (by norm_num)).mp hh
        exact norm_eq_zero.mp h0
      subst hz
      rw [ContinuousAt, hAzero]
      have hbound : ∀ y : EuclideanSpace ℝ (Fin n), ‖Amod y‖ ≤ ‖y‖ ^ (p - 1) :=
        fun y => le_of_eq (norm_Amod y)
      have h1 : Filter.Tendsto (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖)
          (nhds (0 : EuclideanSpace ℝ (Fin n))) (nhds 0) := by
        simpa using (continuous_norm (E := EuclideanSpace ℝ (Fin n))).tendsto 0
      have h2 : Filter.Tendsto (fun s : ℝ => s ^ (p - 1)) (nhds 0) (nhds 0) := by
        have := Real.continuousAt_rpow_const 0 (p - 1) (Or.inr (by linarith))
        simpa [ContinuousAt, Real.zero_rpow (show p - 1 ≠ 0 by linarith)] using this
      exact squeeze_zero_norm hbound (h2.comp h1)
    · exact (contDiffAt_Amod hh).continuousAt
  have Q1_scalar : ∀ W N I : ℝ, 0 < W → 0 ≤ N → I ^ 2 ≤ W * N →
      (p - 1) * W ^ ((p - 2) / 2) * N
        ≤ W ^ ((p - 2) / 2) * N + (p - 2) * W ^ ((p - 2) / 2 - 1) * I ^ 2 := by
    intro W N I hW hN hCS
    have hpos : (0:ℝ) < W ^ ((p - 2) / 2 - 1) := Real.rpow_pos_of_pos hW _
    have hWt : W ^ ((p - 2) / 2 - 1) * W = W ^ ((p - 2) / 2) := by
      rw [Real.rpow_sub hW, Real.rpow_one, div_mul_cancel₀ _ hW.ne']
    rw [← hWt]
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 2 - p by linarith)
        (mul_nonneg hpos.le (sub_nonneg.mpr hCS)), hpos]
  have Q2_scalar : ∀ W d u : ℝ, 0 < W → |d| ≤ 1 → |u| ≤ W →
      |W ^ ((p - 2) / 2) * d + (p - 2) * W ^ ((p - 2) / 2 - 1) * u|
        ≤ (3 - p) * W ^ ((p - 2) / 2) := by
    intro W d u hW hd hu
    have hpos : (0:ℝ) < W ^ ((p - 2) / 2 - 1) := Real.rpow_pos_of_pos hW _
    have hposW : (0:ℝ) < W ^ ((p - 2) / 2) := Real.rpow_pos_of_pos hW _
    have hWt : W ^ ((p - 2) / 2 - 1) * W = W ^ ((p - 2) / 2) := by
      rw [Real.rpow_sub hW, Real.rpow_one, div_mul_cancel₀ _ hW.ne']
    rw [abs_le] at hd hu ⊢
    obtain ⟨hd1, hd2⟩ := hd
    obtain ⟨hu1, hu2⟩ := hu
    constructor
    · nlinarith [mul_nonneg (show (0:ℝ) ≤ 2 - p by linarith)
          (mul_nonneg hpos.le (show (0:ℝ) ≤ W - u by linarith)),
        mul_le_mul_of_nonneg_left hd1 hposW.le, hpos, hposW]
    · nlinarith [mul_nonneg (show (0:ℝ) ≤ 2 - p by linarith)
          (mul_nonneg hpos.le (show (0:ℝ) ≤ u + W by linarith)),
        mul_le_mul_of_nonneg_left hd2 hposW.le, hpos, hposW]
  refine
    { meas_x := fun _ _ => measurable_const
      cont_zh := fun _ => continuous_Amod.comp continuous_snd
      hcont := fun _ _ _ => continuous_Amod
      hdiff := fun _ _ _ y hy => (contDiffAt_Amod (by simpa using hy)).contDiffWithinAt
      Q1 := ?_
      Q2 := ?_ }
  · refine MeasureTheory.ae_of_all _ fun x _ z h ξ hg => ?_
    have hh : ‖h‖ ^ 2 ≠ 0 := by simpa using hg
    have hW : (0:ℝ) < ‖h‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hh)
    have hinner : ∀ v w : EuclideanSpace ℝ (Fin n), ∑ i, v i * w i = inner ℝ v w := by
      intro v w
      rw [PiLp.inner_apply]
      simp [RCLike.inner_apply, mul_comm]
    have hsum : ∑ i, (fderiv ℝ Amod h ξ) i * ξ i
        = (‖h‖ ^ 2) ^ ((p - 2) / 2) * ‖ξ‖ ^ 2
          + (p - 2) * (‖h‖ ^ 2) ^ ((p - 2) / 2 - 1) * (inner ℝ h ξ) ^ 2 := by
      rw [hinner, fderiv_Amod_apply hh, inner_add_left, real_inner_smul_left,
        real_inner_smul_left, real_inner_self_eq_norm_sq]
      ring
    have hCS : (inner ℝ h ξ : ℝ) ^ 2 ≤ ‖h‖ ^ 2 * ‖ξ‖ ^ 2 := by
      have hcs := real_inner_mul_inner_self_le h ξ
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
      nlinarith [hcs]
    rw [zero_add, show p / 2 - 1 = (p - 2) / 2 by ring, hsum]
    exact Q1_scalar _ _ _ hW (by positivity) hCS
  · refine MeasureTheory.ae_of_all _ fun x _ z h i j hg => ?_
    have hh : ‖h‖ ^ 2 ≠ 0 := by simpa using hg
    have hW : (0:ℝ) < ‖h‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hh)
    have hcoord : (fderiv ℝ Amod h (EuclideanSpace.single j (1:ℝ))) i
        = (‖h‖ ^ 2) ^ ((p - 2) / 2) * (if i = j then (1:ℝ) else 0)
          + (p - 2) * (‖h‖ ^ 2) ^ ((p - 2) / 2 - 1) * (h j * h i) := by
      rw [fderiv_Amod_apply hh]
      simp [EuclideanSpace.inner_single_right]
      ring
    have hd : |(if i = j then (1:ℝ) else 0)| ≤ 1 := by split <;> simp
    have hu : |h j * h i| ≤ ‖h‖ ^ 2 := by
      rw [abs_mul]
      calc |h j| * |h i| ≤ ‖h‖ * ‖h‖ :=
            mul_le_mul (abs_coord_le h j) (abs_coord_le h i) (abs_nonneg _) (norm_nonneg _)
        _ = ‖h‖ ^ 2 := by ring
    rw [zero_add, show p / 2 - 1 = (p - 2) / 2 by ring, hcoord]
    exact Q2_scalar _ _ _ hW hd hu
