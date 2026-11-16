import ManfrediThesis.Preamble
open MeasureTheory

/-- The mean-replacement inequality for an arbitrary Banach codomain: on a set
`s ⊆ ℝⁿ` of finite positive measure, the `L^p` deviation of `f` from its own
mean is controlled, with the constant `2^p`, by the deviation from an arbitrary
constant vector `c`.

Conventions, restated here because a helper inherits none of its parent's.
The codomain `E` is any real Banach space; the two cases the consumers need
are `E = ℝ` and `E = EuclideanSpace ℝ (Fin n)`, and the proof uses nothing
beyond completeness, so it is stated once in that generality.  The exponent `p`
is a REAL number with `1 < p`, so `‖·‖ ^ p` is the real power throughout and
the exponent in `2 ^ p` is the same real `p`.  The mean is
`(volume s).toReal⁻¹ • ∫_s f`, written with the scalar action of the real
reciprocal of the measure, exactly as the consumers hold it.  NO
measurability hypothesis on `s` is assumed: the integrals are over `s` with the
restricted measure, and the argument never needs `MeasurableSet s`, which is
what lets a consumer apply it to a set given only through `0 < volume s` and
`volume s ≠ ⊤`.

The route.  Write `V = (volume s).toReal > 0`, `h = f - c`, `m = V⁻¹∫_sf`, and
`I = ∫_s‖h‖^p`.  Two elementary inequalities drive the proof.  First, the
two-term power mean inequality `(X + Y)^p ≤ 2^{p-1}(X^p + Y^p)` for
`X, Y ≥ 0`, which is `NNReal.rpow_add_le_mul_rpow_add_rpow` transported to the
reals.  Second, `‖f - m‖ ≤ ‖f - c‖ + ‖c - m‖` pointwise, so the first
inequality gives
`∫_s‖f - m‖^p ≤ 2^{p-1}\bigl(I + V‖c - m‖^p\bigr)`, the constant term
integrating to `V‖c - m‖^p` over a set of measure `V`.  It remains to bound
`V‖c - m‖^p` by `I`.  Since `m - c = V⁻¹∫_s(f - c) = V⁻¹∫_sh`, the norm
inequality for the Bochner integral gives
`‖m - c‖ ≤ V⁻¹∫_s‖h‖`, and Jensen's inequality in the form
`\bigl(V⁻¹∫_s‖h‖\bigr)^p ≤ V⁻¹∫_s‖h‖^p` --- available because `p > 1` and the
averaging measure `V⁻¹·volume|_s` is a probability measure --- yields
`V‖c - m‖^p ≤ I`.  Combining, `∫_s‖f - m‖^p ≤ 2^{p-1}(I + I) = 2^pI`, which is
the assertion.  Every integrability side condition comes from `f ∈ L^p(s)`
together with `memLp_const` and `MemLp.sub`, the finiteness of the measure
being what makes the constant function integrable. -/
theorem MeanReplacementLpGeneral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] :
    ∀ (n : ℕ) (p : ℝ) (s : Set (EuclideanSpace ℝ (Fin n)))
      (f : EuclideanSpace ℝ (Fin n) → E) (c : E),
      1 < p → 0 < volume s → volume s ≠ ⊤ →
      MemLp f (ENNReal.ofReal p) (volume.restrict s) →
      (∫ x in s, ‖f x - (volume s).toReal⁻¹ • ∫ y in s, f y‖ ^ p)
        ≤ 2 ^ p * ∫ x in s, ‖f x - c‖ ^ p := by
  intro n p s f c hp hs0 hsfin hf
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  have : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hsfin⟩
  set μ := volume.restrict s with hμ
  set V : ℝ := (volume s).toReal with hV
  have hVpos : 0 < V := by
    rw [hV]; exact ENNReal.toReal_pos (ne_of_gt hs0) hsfin
  -- h = f - c
  set h : EuclideanSpace ℝ (Fin n) → E := fun x => f x - c with hh
  have hcmem : MemLp (fun _ : EuclideanSpace ℝ (Fin n) => c) (ENNReal.ofReal p) μ :=
    memLp_const c
  have hhmem : MemLp h (ENNReal.ofReal p) μ := hf.sub hcmem
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hhint : Integrable h μ := hhmem.integrable hp1
  have hfint : Integrable f μ := hf.integrable hp1
  have htoR : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  -- the two-term power-mean inequality, (E1)
  have pow2 : ∀ X Y : ℝ, 0 ≤ X → 0 ≤ Y → (X + Y) ^ p ≤ 2 ^ (p - 1) * (X ^ p + Y ^ p) := by
    intro X Y hX hY
    have h := NNReal.rpow_add_le_mul_rpow_add_rpow X.toNNReal Y.toNNReal hp.le
    have hc : ((X.toNNReal + Y.toNNReal : NNReal) : ℝ) = X + Y := by
      push_cast [Real.coe_toNNReal _ hX, Real.coe_toNNReal _ hY]; ring
    have := (NNReal.coe_le_coe (r₁ := (X.toNNReal + Y.toNNReal) ^ p)
      (r₂ := 2 ^ (p - 1) * (X.toNNReal ^ p + Y.toNNReal ^ p))).2 h
    push_cast [Real.coe_toNNReal _ hX, Real.coe_toNNReal _ hY] at this
    exact this
  set m : E := V⁻¹ • ∫ y in s, f y with hm
  have hmmem : MemLp (fun _ : EuclideanSpace ℝ (Fin n) => m) (ENNReal.ofReal p) μ :=
    memLp_const m
  have hfcmem : MemLp (fun x => f x - c) (ENNReal.ofReal p) μ := hf.sub hcmem
  have hfmmem : MemLp (fun x => f x - m) (ENNReal.ofReal p) μ := hf.sub hmmem
  have hI : Integrable (fun x => ‖f x - c‖ ^ p) μ := by
    have h := hfcmem.integrable_norm_rpow'
    rwa [htoR] at h
  have hJ : Integrable (fun x => ‖f x - m‖ ^ p) μ := by
    have h := hfmmem.integrable_norm_rpow'
    rwa [htoR] at h
  set I : ℝ := ∫ x in s, ‖f x - c‖ ^ p with hIdef
  have hI0 : 0 ≤ I := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p
  -- Step 1: the mean difference as the mean of `f - c`
  have hconst : ∫ _x in s, c = V • c := by
    rw [setIntegral_const, Measure.real_def]
  have hstep1 : m - c = V⁻¹ • ∫ x in s, (f x - c) := by
    rw [integral_sub hfint (integrable_const c), hconst, smul_sub, smul_smul,
      inv_mul_cancel₀ hVpos.ne', one_smul, hm]
  -- Steps 2-3: Cauchy-Schwarz/Hölder on the finite-measure set
  have hq : Real.HolderConjugate p (p / (p - 1)) := by
    refine Real.holderConjugate_iff.2 ⟨hp, ?_⟩
    field_simp
    ring
  have hhol := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hq
    (f := fun x => ‖f x - c‖) (g := fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall fun x => norm_nonneg _)
    (Filter.Eventually.of_forall fun _ => zero_le_one)
    hfcmem.norm (memLp_const 1)
  simp only [mul_one, Real.one_rpow, integral_const, smul_eq_mul] at hhol
  have hmeasV : (volume.restrict s).real Set.univ = V := by
    rw [Measure.real_def, Measure.restrict_apply_univ]
  rw [hmeasV] at hhol
  have hexp : (1:ℝ)/(p/(p-1)) = 1 - 1/p := by field_simp
  rw [hexp] at hhol
  -- Step 4: the mean of `f` is within `(V⁻¹ I)^{1/p}` of `c`
  have hnmc : ‖m - c‖ ≤ V⁻¹ * ∫ x in s, ‖f x - c‖ := by
    rw [hstep1, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hVpos]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
  have hVip : V⁻¹ * (I ^ (1/p) * V ^ (1 - 1/p)) = V ^ (-(1/p)) * I ^ (1/p) := by
    rw [show V⁻¹ = V ^ (-1 : ℝ) from (Real.rpow_neg_one V).symm,
      show V ^ (-1:ℝ) * (I ^ (1/p) * V ^ (1 - 1/p))
          = (V ^ (-1:ℝ) * V ^ (1 - 1/p)) * I ^ (1/p) from by ring,
      ← Real.rpow_add hVpos]
    congr 2
    ring
  have hmc2 : ‖m - c‖ ≤ V ^ (-(1/p)) * I ^ (1/p) := by
    rw [← hVip]
    exact le_trans hnmc (mul_le_mul_of_nonneg_left hhol (by positivity))
  have hkey : ‖m - c‖ ^ p ≤ V⁻¹ * I := by
    have h1 := Real.rpow_le_rpow (norm_nonneg _) hmc2 hp0.le
    rw [Real.mul_rpow (Real.rpow_nonneg hVpos.le _) (Real.rpow_nonneg hI0 _),
      ← Real.rpow_mul hVpos.le, ← Real.rpow_mul hI0,
      show -(1/p) * p = -1 by field_simp, show 1/p * p = 1 by field_simp,
      Real.rpow_neg_one, Real.rpow_one] at h1
    exact h1
  -- Step 5: the triangle inequality in L^p
  have hpt : ∀ x, ‖f x - m‖ ^ p ≤ 2 ^ (p-1) * (‖f x - c‖ ^ p + ‖c - m‖ ^ p) := by
    intro x
    refine le_trans (Real.rpow_le_rpow (norm_nonneg _) ?_ hp0.le)
      (pow2 _ _ (norm_nonneg _) (norm_nonneg _))
    calc ‖f x - m‖ = ‖(f x - c) + (c - m)‖ := by congr 1; abel
      _ ≤ ‖f x - c‖ + ‖c - m‖ := norm_add_le _ _
  have hint2 : Integrable (fun x => 2 ^ (p-1) * (‖f x - c‖ ^ p + ‖c - m‖ ^ p)) μ :=
    (hI.add (integrable_const _)).const_mul _
  have hmono := integral_mono hJ hint2 hpt
  rw [integral_const_mul, integral_add hI (integrable_const _), integral_const, hmeasV,
    smul_eq_mul] at hmono
  have hcm : ‖c - m‖ = ‖m - c‖ := norm_sub_rev _ _
  have hfinal : V * ‖c - m‖ ^ p ≤ I := by
    rw [hcm]
    calc V * ‖m - c‖ ^ p ≤ V * (V⁻¹ * I) :=
          mul_le_mul_of_nonneg_left hkey hVpos.le
      _ = I := by field_simp
  have htwo : (2:ℝ) ^ (p - 1) * 2 = 2 ^ p := by
    rw [← Real.rpow_add_one (by norm_num : (2:ℝ) ≠ 0)]
    congr 1
    ring
  calc (∫ x in s, ‖f x - m‖ ^ p)
      ≤ 2 ^ (p-1) * (I + V * ‖c - m‖ ^ p) := hmono
    _ ≤ 2 ^ (p-1) * (I + I) :=
        mul_le_mul_of_nonneg_left (by linarith [hfinal]) (Real.rpow_nonneg (by norm_num) _)
    _ = 2 ^ p * I := by rw [← htwo]; ring


-- The REPAIRED clause (A) of ComparisonSchemeCampanatoCore: the bundle now
-- carries `MemW1pOn n p (ball x₀ R) v gv`, the `.tex`'s own parenthetical
-- "the gradient of a comparison map v on B_R(x₀)".
