import ManfrediThesis.Preamble
open MeasureTheory

/-- The structure facts for the frozen integrand `h ↦ (τ h, h)^{n/2}` of §5.
For a symmetric matrix whose quadratic form is two-sidedly comparable to
`‖ξ‖²` with the ratios `K^{-2/n}` and `K^{2(n-1)/n}` of (5.10), the integrand is
`C¹` on all of the space, `C²` away from the origin, and its second derivative
satisfies the two-sided (F2) bounds with `ν₀ = n/K` and
`ν₁ = n(n-1)K^{n-1}`; and its oscillation in the matrix is controlled
linearly by the entrywise oscillation.  The hypothesis `2 ≤ n` is used twice:
once in the lower bound, where it makes `n/2 - 1 ≥ 0`, and once in the upper
bound, where the cross term is nonnegative. -/
theorem FrozenQuadraticFormStructure :
    ∀ (n : ℕ) (K ν₀ ν₁ : ℝ), 2 ≤ n → 1 ≤ K →
      0 < ν₀ → ν₀ ≤ (n : ℝ) / K →
      (n : ℝ) * ((n : ℝ) - 1) * K ^ ((n : ℝ) - 1) ≤ ν₁ →
      ∀ T : Matrix (Fin n) (Fin n) ℝ,
        T.IsSymm →
        (∀ ξ : EuclideanSpace ℝ (Fin n),
          K ^ (-(2 : ℝ) / (n : ℝ)) * ‖ξ‖ ^ 2 ≤ ∑ a, ∑ b, T a b * ξ a * ξ b ∧
            (∑ a, ∑ b, T a b * ξ a * ξ b)
              ≤ K ^ (2 * ((n : ℝ) - 1) / (n : ℝ)) * ‖ξ‖ ^ 2) →
        ContDiff ℝ 1
            (fun h : EuclideanSpace ℝ (Fin n) =>
              (∑ a, ∑ b, T a b * h a * h b) ^ ((n : ℝ) / 2)) ∧
          ContDiffOn ℝ 2
            (fun h : EuclideanSpace ℝ (Fin n) =>
              (∑ a, ∑ b, T a b * h a * h b) ^ ((n : ℝ) / 2))
            {h : EuclideanSpace ℝ (Fin n) | (0 : ℝ) + ‖h‖ ^ 2 ≠ 0} ∧
          (∀ h ζ : EuclideanSpace ℝ (Fin n), (0 : ℝ) + ‖h‖ ^ 2 ≠ 0 →
            ν₀ * ((0 : ℝ) + ‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖ζ‖ ^ 2
                ≤ fderiv ℝ
                    (fun h' : EuclideanSpace ℝ (Fin n) =>
                      fderiv ℝ
                        (fun h'' : EuclideanSpace ℝ (Fin n) =>
                          (∑ a, ∑ b, T a b * h'' a * h'' b) ^ ((n : ℝ) / 2))
                        h' ζ) h ζ ∧
              fderiv ℝ
                  (fun h' : EuclideanSpace ℝ (Fin n) =>
                    fderiv ℝ
                      (fun h'' : EuclideanSpace ℝ (Fin n) =>
                        (∑ a, ∑ b, T a b * h'' a * h'' b) ^ ((n : ℝ) / 2))
                      h' ζ) h ζ
                ≤ ν₁ * ((0 : ℝ) + ‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖ζ‖ ^ 2) ∧
          ∀ (T' : Matrix (Fin n) (Fin n) ℝ) (w : ℝ),
            (∀ ξ : EuclideanSpace ℝ (Fin n),
              0 ≤ ∑ a, ∑ b, T' a b * ξ a * ξ b ∧
                (∑ a, ∑ b, T' a b * ξ a * ξ b)
                  ≤ K ^ (2 * ((n : ℝ) - 1) / (n : ℝ)) * ‖ξ‖ ^ 2) →
            (∀ a b : Fin n, |T a b - T' a b| ≤ w) →
            ∀ h : EuclideanSpace ℝ (Fin n),
              |(∑ a, ∑ b, T a b * h a * h b) ^ ((n : ℝ) / 2)
                  - (∑ a, ∑ b, T' a b * h a * h b) ^ ((n : ℝ) / 2)|
                ≤ (n : ℝ) ^ 2 / 2 * K ^ (((n : ℝ) - 1) * ((n : ℝ) - 2) / (n : ℝ))
                    * w * ‖h‖ ^ (n : ℝ) := by
  intro n K ν₀ ν₁ hn hK hν₀ hν₀n hν₁ T hsymm hbounds
  -- Scalar facts, established before the data are used.
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hKrpow : ∀ e : ℝ, (0 : ℝ) < K ^ e := fun e => Real.rpow_pos_of_pos hK0 e
  have hhalf : (1 : ℝ) ≤ (n : ℝ) / 2 := by linarith
  have hhalf1 : (0 : ℝ) ≤ (n : ℝ) / 2 - 1 := by linarith
  -- The coordinate functionals.
  set P : Fin n → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    fun a => (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) with hPdef
  have hPapp : ∀ (a : Fin n) (v : EuclideanSpace ℝ (Fin n)), P a v = v a := fun a v => rfl
  -- The quadratic form and its basic properties.
  have hqcd : ContDiff ℝ (⊤ : ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin n) => ∑ a, ∑ b, T a b * u a * u b) :=
    ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
      (((P a).contDiff).const_smul (T a b)).mul ((P b).contDiff)
  have hqnn : ∀ u : EuclideanSpace ℝ (Fin n), 0 ≤ ∑ a, ∑ b, T a b * u a * u b := fun u =>
    le_trans (mul_nonneg (le_of_lt (hKrpow _)) (sq_nonneg _)) (hbounds u).1
  have hqpos : ∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 →
      0 < ∑ a, ∑ b, T a b * u a * u b := fun u hu =>
    lt_of_lt_of_le (mul_pos (hKrpow _) (pow_pos (norm_pos_iff.mpr hu) 2)) (hbounds u).1
  -- The bilinear functional attached to `T`, as a continuous linear map.
  set L : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    fun v => ∑ a : Fin n, (∑ b, T a b * v b) • P a with hLdef
  have hLapp : ∀ u v : EuclideanSpace ℝ (Fin n),
      L v u = ∑ a, ∑ b, T a b * u a * v b := by
    intro u v
    rw [hLdef]
    simp only [FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hPapp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hBsymm : ∀ u v : EuclideanSpace ℝ (Fin n),
      (∑ a, ∑ b, T a b * u a * v b) = ∑ a, ∑ b, T a b * v a * u b := by
    intro u v
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hT : T b a = T a b := by simpa using Matrix.IsSymm.apply hsymm a b
    rw [hT]; ring
  -- The derivative of the quadratic form.
  have hqd : ∀ h' : EuclideanSpace ℝ (Fin n),
      HasFDerivAt (fun u : EuclideanSpace ℝ (Fin n) => ∑ a, ∑ b, T a b * u a * u b)
        ((2 : ℝ) • L h') h' := by
    intro h'
    have key : HasFDerivAt
        (fun u : EuclideanSpace ℝ (Fin n) => ∑ a, ∑ b, T a b * u a * u b)
        (∑ a : Fin n, ∑ b : Fin n,
          ((T a b * h' a) • P b + h' b • ((T a b) • P a))) h' :=
      HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun b _ =>
        (((P a).hasFDerivAt (x := h')).const_mul (T a b)).fun_mul
          ((P b).hasFDerivAt (x := h'))
    refine key.congr_fderiv (ContinuousLinearMap.ext fun ζ => ?_)
    simp only [FunLike.coe_sum, Finset.sum_apply, add_apply, smul_eq_mul, hPapp,
      smul_apply, hLapp]
    have e1 : ∑ a : Fin n, ∑ b : Fin n, (T a b * h' a * ζ b + h' b * (T a b * ζ a))
        = (∑ a, ∑ b, T a b * h' a * ζ b) + ∑ a, ∑ b, T a b * ζ a * h' b := by
      simp only [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [e1, hBsymm h' ζ]
    ring
  -- The expansion of the form along a line, and Cauchy--Schwarz from it.
  have hexpand : ∀ (u v : EuclideanSpace ℝ (Fin n)) (t : ℝ),
      (∑ a, ∑ b, T a b * (u + t • v) a * (u + t • v) b)
        = (∑ a, ∑ b, T a b * u a * u b) + 2 * t * (∑ a, ∑ b, T a b * u a * v b)
          + t ^ 2 * (∑ a, ∑ b, T a b * v a * v b) := by
    intro u v t
    have hpt : ∀ a : Fin n, (u + t • v) a = u a + t * v a := fun a => by simp
    simp only [hpt]
    have hexp : ∀ a b : Fin n,
        T a b * (u a + t * v a) * (u b + t * v b)
          = T a b * u a * u b + t * (T a b * u a * v b) + t * (T a b * v a * u b)
            + t ^ 2 * (T a b * v a * v b) := fun a b => by ring
    simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hBsymm v u]
    ring
  have hCS : ∀ u v : EuclideanSpace ℝ (Fin n),
      (∑ a, ∑ b, T a b * u a * v b) ^ 2
        ≤ (∑ a, ∑ b, T a b * u a * u b) * (∑ a, ∑ b, T a b * v a * v b) := by
    intro u v
    rcases eq_or_ne v 0 with rfl | hv
    · simp only [show ∀ a : Fin n, (0 : EuclideanSpace ℝ (Fin n)) a = 0 from
        fun a => by simp, mul_zero, Finset.sum_const_zero]
      simp
    · have hzpos := hqpos v hv
      have key := hqnn (u + (-((∑ a, ∑ b, T a b * u a * v b) /
        (∑ a, ∑ b, T a b * v a * v b))) • v)
      rw [hexpand u v _] at key
      have hkey2 : 0 ≤ (∑ a, ∑ b, T a b * u a * u b)
          - (∑ a, ∑ b, T a b * u a * v b) ^ 2 / (∑ a, ∑ b, T a b * v a * v b) := by
        have e : (∑ a, ∑ b, T a b * u a * u b)
            + 2 * (-((∑ a, ∑ b, T a b * u a * v b) /
              (∑ a, ∑ b, T a b * v a * v b))) * (∑ a, ∑ b, T a b * u a * v b)
            + (-((∑ a, ∑ b, T a b * u a * v b) /
              (∑ a, ∑ b, T a b * v a * v b))) ^ 2 * (∑ a, ∑ b, T a b * v a * v b)
            = (∑ a, ∑ b, T a b * u a * u b)
              - (∑ a, ∑ b, T a b * u a * v b) ^ 2
                / (∑ a, ∑ b, T a b * v a * v b) := by
          field_simp; ring
        rwa [e] at key
      rw [sub_nonneg, div_le_iff₀ hzpos] at hkey2
      linarith
  -- The mean value bound for the real power.
  have hmvt : ∀ p A B : ℝ, 1 ≤ p → 0 ≤ A → 0 ≤ B →
      |A ^ p - B ^ p| ≤ p * (max A B) ^ (p - 1) * |A - B| := by
    intro p A B hp hA hB
    have hconv : Convex ℝ (Set.Icc (0 : ℝ) (max A B)) := convex_Icc _ _
    have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) (max A B),
        HasDerivWithinAt (fun t : ℝ => t ^ p) (p * x ^ (p - 1))
          (Set.Icc (0 : ℝ) (max A B)) x :=
      fun x _ => (Real.hasDerivAt_rpow_const (Or.inr hp)).hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Icc (0 : ℝ) (max A B),
        ‖p * x ^ (p - 1)‖ ≤ p * (max A B) ^ (p - 1) := by
      intro x hx
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hx.1 _))]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hx.1 hx.2 (by linarith)) (by linarith)
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (Set.mem_Icc.2 ⟨hB, le_max_right _ _⟩) (Set.mem_Icc.2 ⟨hA, le_max_left _ _⟩)
    simpa [Real.norm_eq_abs] using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `C^1` on all of the space: the exponent `n/2` is at least `1`.
    exact (hqcd.of_le (by exact_mod_cast le_top)).rpow_const_of_le
      (by push_cast; linarith)
  · -- `C^2` away from the origin, where the form is positive.
    have hqcd2 : ContDiff ℝ 2
        (fun u : EuclideanSpace ℝ (Fin n) => ∑ a, ∑ b, T a b * u a * u b) :=
      ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
        (((P a).contDiff).const_smul (T a b)).mul ((P b).contDiff)
    refine hqcd2.contDiffOn.rpow_const_of_ne fun x hx => ne_of_gt (hqpos x ?_)
    intro hx0
    exact hx (by rw [hx0]; simp)
  · -- (F2): the two-sided bounds on the second derivative.
    intro h ζ hhne
    have hh0 : h ≠ 0 := fun hc => hhne (by rw [hc]; simp)
    have hqhpos : (0 : ℝ) < ∑ a, ∑ b, T a b * h a * h b := hqpos h hh0
    have hsecond : fderiv ℝ (fun h' : EuclideanSpace ℝ (Fin n) =>
          fderiv ℝ (fun h'' : EuclideanSpace ℝ (Fin n) =>
            (∑ a, ∑ b, T a b * h'' a * h'' b) ^ ((n : ℝ) / 2)) h' ζ) h ζ
        = (n : ℝ) * ((n : ℝ) - 2)
            * (∑ a, ∑ b, T a b * h a * h b) ^ ((n : ℝ) / 2 - 2)
            * (∑ a, ∑ b, T a b * h a * ζ b) ^ 2
          + (n : ℝ) * (∑ a, ∑ b, T a b * h a * h b) ^ ((n : ℝ) / 2 - 1)
            * (∑ a, ∑ b, T a b * ζ a * ζ b) := by
      have hnbhd : ∀ᶠ h' in nhds h, (∑ a, ∑ b, T a b * h' a * h' b) ≠ 0 :=
        (hqcd.continuous.continuousAt (x := h)).eventually_ne (ne_of_gt hqhpos)
      have hGeq : (fun h' : EuclideanSpace ℝ (Fin n) =>
          fderiv ℝ (fun h'' : EuclideanSpace ℝ (Fin n) =>
            (∑ a, ∑ b, T a b * h'' a * h'' b) ^ ((n : ℝ) / 2)) h' ζ)
          =ᶠ[nhds h] fun h' => ((n : ℝ)
            * (∑ a, ∑ b, T a b * h' a * h' b) ^ ((n : ℝ) / 2 - 1)) * (L ζ) h' := by
        filter_upwards [hnbhd] with h' hh'
        rw [((hqd h').rpow_const (p := (n : ℝ) / 2) (Or.inl hh')).fderiv]
        simp only [smul_apply, smul_eq_mul, hLapp]
        rw [hBsymm ζ h']
        ring
      rw [Filter.EventuallyEq.fderiv_eq hGeq]
      have hA := ((hqd h).rpow_const (p := (n : ℝ) / 2 - 1)
        (Or.inl (ne_of_gt hqhpos))).const_mul (n : ℝ)
      rw [(hA.fun_mul ((L ζ).hasFDerivAt (x := h))).fderiv]
      simp only [add_apply, smul_apply, smul_eq_mul, hLapp]
      rw [hBsymm ζ h, show ((n : ℝ) / 2 - 1 - 1) = (n : ℝ) / 2 - 2 by ring]
      ring
    rw [hsecond, zero_add]
    set qh : ℝ := ∑ a, ∑ b, T a b * h a * h b with hqhdef
    set qz : ℝ := ∑ a, ∑ b, T a b * ζ a * ζ b with hqzdef
    set S : ℝ := ∑ a, ∑ b, T a b * h a * ζ b with hSdef
    have hqz : (0 : ℝ) ≤ qz := hqnn ζ
    have hpow1 : (0 : ℝ) ≤ qh ^ ((n : ℝ) / 2 - 1) :=
      Real.rpow_nonneg (le_of_lt hqhpos) _
    have hpow2 : (0 : ℝ) ≤ qh ^ ((n : ℝ) / 2 - 2) :=
      Real.rpow_nonneg (le_of_lt hqhpos) _
    have hnormpow : (0 : ℝ) ≤ (‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) :=
      Real.rpow_nonneg (sq_nonneg _) _
    have hW : (0 : ℝ) ≤ (‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖ζ‖ ^ 2 :=
      mul_nonneg hnormpow (sq_nonneg _)
    have hterm1nn : (0 : ℝ)
        ≤ (n : ℝ) * ((n : ℝ) - 2) * qh ^ ((n : ℝ) / 2 - 2) * S ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hn0) (by linarith)) hpow2)
        (sq_nonneg _)
    constructor
    · -- the lower bound: the first term is nonnegative and is dropped
      have hKcomb : K ^ ((2 : ℝ) / (n : ℝ) - 1) * K ^ (-(2 : ℝ) / (n : ℝ)) = 1 / K := by
        rw [← Real.rpow_add hK0,
          show ((2 : ℝ) / (n : ℝ) - 1 + -(2 : ℝ) / (n : ℝ)) = -1 by ring,
          Real.rpow_neg_one]
        exact inv_eq_one_div K
      have hlowpow : K ^ ((2 : ℝ) / (n : ℝ) - 1) * (‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1)
          ≤ qh ^ ((n : ℝ) / 2 - 1) := by
        refine le_trans (le_of_eq ?_)
          (Real.rpow_le_rpow (mul_nonneg (le_of_lt (hKrpow _)) (sq_nonneg _))
            (hbounds h).1 hhalf1)
        rw [Real.mul_rpow (le_of_lt (hKrpow _)) (sq_nonneg _),
          ← Real.rpow_mul (le_of_lt hK0)]
        congr 2
        field_simp
        ring
      have hmul0 : K ^ ((2 : ℝ) / (n : ℝ) - 1) * (‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1)
            * (K ^ (-(2 : ℝ) / (n : ℝ)) * ‖ζ‖ ^ 2)
          ≤ qh ^ ((n : ℝ) / 2 - 1) * qz :=
        mul_le_mul hlowpow (hbounds ζ).1
          (mul_nonneg (le_of_lt (hKrpow _)) (sq_nonneg _)) hpow1
      have hmul : 1 / K * ((‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖ζ‖ ^ 2)
          ≤ qh ^ ((n : ℝ) / 2 - 1) * qz := by
        refine le_trans (le_of_eq ?_) hmul0
        rw [← hKcomb]; ring
      have hstep : ν₀ * ((‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖ζ‖ ^ 2)
          ≤ (n : ℝ) * qh ^ ((n : ℝ) / 2 - 1) * qz := by
        calc ν₀ * ((‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖ζ‖ ^ 2)
            ≤ ((n : ℝ) / K) * ((‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖ζ‖ ^ 2) :=
              mul_le_mul_of_nonneg_right hν₀n hW
          _ = (n : ℝ) * (1 / K * ((‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖ζ‖ ^ 2)) := by ring
          _ ≤ (n : ℝ) * (qh ^ ((n : ℝ) / 2 - 1) * qz) :=
              mul_le_mul_of_nonneg_left hmul (le_of_lt hn0)
          _ = (n : ℝ) * qh ^ ((n : ℝ) / 2 - 1) * qz := by ring
      have hgoal : ν₀ * (‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖ζ‖ ^ 2
          = ν₀ * ((‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖ζ‖ ^ 2) := by ring
      rw [hgoal]
      linarith
    · -- the upper bound: Cauchy--Schwarz, then the two powers of `K` compose
      have hcollapse : qh ^ ((n : ℝ) / 2 - 2) * qh = qh ^ ((n : ℝ) / 2 - 1) := by
        have h1 : qh ^ ((n : ℝ) / 2 - 2) * qh ^ (1 : ℝ)
            = qh ^ ((n : ℝ) / 2 - 2 + 1) := (Real.rpow_add hqhpos _ _).symm
        rw [Real.rpow_one] at h1
        rw [h1, show ((n : ℝ) / 2 - 2 + 1) = (n : ℝ) / 2 - 1 by ring]
      have hterm1 : (n : ℝ) * ((n : ℝ) - 2) * qh ^ ((n : ℝ) / 2 - 2) * S ^ 2
          ≤ (n : ℝ) * ((n : ℝ) - 2) * qh ^ ((n : ℝ) / 2 - 1) * qz := by
        have hc : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 2) * qh ^ ((n : ℝ) / 2 - 2) :=
          mul_nonneg (mul_nonneg (le_of_lt hn0) (by linarith)) hpow2
        calc (n : ℝ) * ((n : ℝ) - 2) * qh ^ ((n : ℝ) / 2 - 2) * S ^ 2
            ≤ (n : ℝ) * ((n : ℝ) - 2) * qh ^ ((n : ℝ) / 2 - 2) * (qh * qz) :=
              mul_le_mul_of_nonneg_left (hCS h ζ) hc
          _ = (n : ℝ) * ((n : ℝ) - 2) * (qh ^ ((n : ℝ) / 2 - 2) * qh) * qz := by ring
          _ = (n : ℝ) * ((n : ℝ) - 2) * qh ^ ((n : ℝ) / 2 - 1) * qz := by rw [hcollapse]
      have huppow : qh ^ ((n : ℝ) / 2 - 1)
          ≤ K ^ (((n : ℝ) - 1) * ((n : ℝ) - 2) / (n : ℝ))
            * (‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) := by
        refine le_trans (Real.rpow_le_rpow (le_of_lt hqhpos) (hbounds h).2 hhalf1)
          (le_of_eq ?_)
        rw [Real.mul_rpow (le_of_lt (hKrpow _)) (sq_nonneg _),
          ← Real.rpow_mul (le_of_lt hK0)]
        congr 2
        field_simp
      have hKsum : K ^ (((n : ℝ) - 1) * ((n : ℝ) - 2) / (n : ℝ))
            * K ^ (2 * ((n : ℝ) - 1) / (n : ℝ))
          = K ^ ((n : ℝ) - 1) := by
        rw [← Real.rpow_add hK0]
        congr 1
        field_simp
        ring
      have hprod : qh ^ ((n : ℝ) / 2 - 1) * qz
          ≤ K ^ ((n : ℝ) - 1) * ((‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖ζ‖ ^ 2) := by
        refine le_trans (mul_le_mul huppow (hbounds ζ).2 hqz
          (mul_nonneg (le_of_lt (hKrpow _)) hnormpow)) (le_of_eq ?_)
        rw [← hKsum]; ring
      have hnn1 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) :=
        mul_nonneg (le_of_lt hn0) (by linarith)
      calc (n : ℝ) * ((n : ℝ) - 2) * qh ^ ((n : ℝ) / 2 - 2) * S ^ 2
              + (n : ℝ) * qh ^ ((n : ℝ) / 2 - 1) * qz
          ≤ (n : ℝ) * ((n : ℝ) - 2) * qh ^ ((n : ℝ) / 2 - 1) * qz
              + (n : ℝ) * qh ^ ((n : ℝ) / 2 - 1) * qz := by linarith
        _ = (n : ℝ) * ((n : ℝ) - 1) * (qh ^ ((n : ℝ) / 2 - 1) * qz) := by ring
        _ ≤ (n : ℝ) * ((n : ℝ) - 1)
              * (K ^ ((n : ℝ) - 1) * ((‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖ζ‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hprod hnn1
        _ = ((n : ℝ) * ((n : ℝ) - 1) * K ^ ((n : ℝ) - 1))
              * ((‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖ζ‖ ^ 2) := by ring
        _ ≤ ν₁ * ((‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖ζ‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hν₁ hW
        _ = ν₁ * (‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖ζ‖ ^ 2 := by ring
  · -- the oscillation bound
    intro T' w hT'bounds hTT' h
    have hidx : Fin n := ⟨0, by omega⟩
    have hw0 : (0 : ℝ) ≤ w := le_trans (abs_nonneg _) (hTT' hidx hidx)
    rcases eq_or_ne h 0 with rfl | hh0
    · simp only [show ∀ a : Fin n, (0 : EuclideanSpace ℝ (Fin n)) a = 0 from
        fun a => by simp, mul_zero, Finset.sum_const_zero, sub_self, abs_zero,
        norm_zero, Real.zero_rpow hnne, mul_zero, le_refl]
    · have hhn : (0 : ℝ) < ‖h‖ := norm_pos_iff.mpr hh0
      -- (i) the forms differ by at most `n * w * ‖h‖²`
      have hCS2 : (∑ a : Fin n, |h a|) ^ 2 ≤ (n : ℝ) * ‖h‖ ^ 2 := by
        have e1 : (∑ a : Fin n, |h a|) ^ 2 = ∑ a : Fin n, ∑ b : Fin n, |h a| * |h b| := by
          rw [sq, Finset.sum_mul_sum]
        have e2 : ∀ a b : Fin n, |h a| * |h b| ≤ (|h a| ^ 2 + |h b| ^ 2) / 2 :=
          fun a b => by nlinarith [sq_nonneg (|h a| - |h b|)]
        have hAA : ∑ a : Fin n, ∑ _b : Fin n, |h a| ^ 2
            = (n : ℝ) * ∑ a, |h a| ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, Finset.mul_sum]
        have hBB : ∑ _a : Fin n, ∑ b : Fin n, |h b| ^ 2
            = (n : ℝ) * ∑ b, |h b| ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ]
        have hsplit : ∑ a : Fin n, ∑ b : Fin n, (|h a| ^ 2 + |h b| ^ 2) / 2
            = (∑ a : Fin n, ∑ b : Fin n, |h a| ^ 2) / 2
              + (∑ a : Fin n, ∑ b : Fin n, |h b| ^ 2) / 2 := by
          simp only [add_div, Finset.sum_add_distrib, Finset.sum_div]
        have hnormsq : ‖h‖ ^ 2 = ∑ a : Fin n, |h a| ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]
          exact Finset.sum_congr rfl fun a _ => by rw [Real.norm_eq_abs]
        rw [e1, hnormsq]
        refine le_trans (Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum fun b _ => e2 a b) ?_
        rw [hsplit, hAA, hBB]
        linarith
      have hdiffbound : |(∑ a, ∑ b, T a b * h a * h b)
            - ∑ a, ∑ b, T' a b * h a * h b| ≤ (n : ℝ) * w * ‖h‖ ^ 2 := by
        have hsub : (∑ a, ∑ b, T a b * h a * h b) - ∑ a, ∑ b, T' a b * h a * h b
            = ∑ a, ∑ b, (T a b - T' a b) * h a * h b := by
          rw [show (∑ a, ∑ b, (T a b - T' a b) * h a * h b)
              = ∑ a : Fin n, ∑ b : Fin n, (T a b * h a * h b - T' a b * h a * h b) from
            Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring]
          simp only [Finset.sum_sub_distrib]
        rw [hsub]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have hinner : ∀ a : Fin n, |∑ b, (T a b - T' a b) * h a * h b|
            ≤ w * |h a| * ∑ b : Fin n, |h b| := by
          intro a
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun b _ => ?_
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hTT' a b) (abs_nonneg _)) (abs_nonneg _)
        refine le_trans (Finset.sum_le_sum fun a _ => hinner a) ?_
        calc (∑ a : Fin n, w * |h a| * ∑ b : Fin n, |h b|)
            = w * (∑ a : Fin n, |h a|) ^ 2 := by
              rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
          _ ≤ w * ((n : ℝ) * ‖h‖ ^ 2) := mul_le_mul_of_nonneg_left hCS2 hw0
          _ = (n : ℝ) * w * ‖h‖ ^ 2 := by ring
      -- (ii) the mean value bound, with the maximum under control
      have hmaxpow : (max (∑ a, ∑ b, T a b * h a * h b)
            (∑ a, ∑ b, T' a b * h a * h b)) ^ ((n : ℝ) / 2 - 1)
          ≤ K ^ (((n : ℝ) - 1) * ((n : ℝ) - 2) / (n : ℝ))
            * (‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) := by
        refine le_trans (Real.rpow_le_rpow
          (le_trans (hqnn h) (le_max_left _ _))
          (max_le (hbounds h).2 (hT'bounds h).2) hhalf1) (le_of_eq ?_)
        rw [Real.mul_rpow (le_of_lt (hKrpow _)) (sq_nonneg _),
          ← Real.rpow_mul (le_of_lt hK0)]
        congr 2
        field_simp
      -- (iii) assemble
      have hnormid : (‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖h‖ ^ 2 = ‖h‖ ^ (n : ℝ) := by
        have h2 : ‖h‖ ^ 2 = ‖h‖ ^ (2 : ℝ) := by rw [Real.rpow_two]
        rw [h2, ← Real.rpow_mul (le_of_lt hhn), ← Real.rpow_add hhn]
        congr 1
        ring
      have hc0 : (0 : ℝ) ≤ (n : ℝ) / 2 * (K ^ (((n : ℝ) - 1) * ((n : ℝ) - 2) / (n : ℝ))
          * (‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1)) :=
        mul_nonneg (by linarith)
          (mul_nonneg (le_of_lt (hKrpow _)) (Real.rpow_nonneg (sq_nonneg _) _))
      calc |(∑ a, ∑ b, T a b * h a * h b) ^ ((n : ℝ) / 2)
              - (∑ a, ∑ b, T' a b * h a * h b) ^ ((n : ℝ) / 2)|
          ≤ (n : ℝ) / 2 * (max (∑ a, ∑ b, T a b * h a * h b)
                (∑ a, ∑ b, T' a b * h a * h b)) ^ ((n : ℝ) / 2 - 1)
              * |(∑ a, ∑ b, T a b * h a * h b)
                - ∑ a, ∑ b, T' a b * h a * h b| :=
            hmvt ((n : ℝ) / 2) _ _ hhalf (hqnn h) (hT'bounds h).1
        _ ≤ (n : ℝ) / 2 * (K ^ (((n : ℝ) - 1) * ((n : ℝ) - 2) / (n : ℝ))
                * (‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1))
              * ((n : ℝ) * w * ‖h‖ ^ 2) := by
            refine mul_le_mul ?_ hdiffbound (abs_nonneg _) hc0
            exact mul_le_mul_of_nonneg_left hmaxpow (by linarith)
        _ = (n : ℝ) ^ 2 / 2 * K ^ (((n : ℝ) - 1) * ((n : ℝ) - 2) / (n : ℝ)) * w
              * ((‖h‖ ^ 2) ^ ((n : ℝ) / 2 - 1) * ‖h‖ ^ 2) := by ring
        _ = (n : ℝ) ^ 2 / 2 * K ^ (((n : ℝ) - 1) * ((n : ℝ) - 2) / (n : ℝ)) * w
              * ‖h‖ ^ (n : ℝ) := by rw [hnormid]
