import ManfrediThesis.Preamble
set_option maxHeartbeats 800000
open MeasureTheory

/-- The regularised fields `V_η = (p/2)(|g^k| + η)^{p/2-1}Dg^k` of the
subquadratic signed power: the pointwise supremum of `‖V_{η_j}‖²` along the
regularisation sequence `η_j ↓ 0` has finite integral over `B_T(x₀)`, it
dominates `‖V_0‖²` pointwise, and `Dg^k = 0` almost everywhere on
`{g^k = 0}`.

Conventions, restated here because a helper inherits none of its parent's.
`g` plays the role of `∇u` and `Dg k` of `∇D_ku`; `p < 2`, so the exponent
`p/2 - 1` is NEGATIVE, which is the whole mechanism below and is carried as an
explicit hypothesis; every power of a nonnegative real is the real power, so
`(|g^k| + η)^{p/2-1}` is finite exactly because `η > 0` keeps the base away
from `0`.  The supremum and the integral of the third conclusion are taken in
`ℝ≥0∞`, which is what makes the statement meaningful before finiteness is
known: `⨆ j` is the extended-real supremum of the sequence and `∫⁻` the lower
Lebesgue integral.  The uniform bound `W^{-1}K` is carried as an abstract real,
since only its finiteness is used.

The route.  The map `η ↦ ‖V_η(x)‖²` is MONOTONE DECREASING in `η`, because the
exponent `p/2 - 1` is negative and `|g^k(x)| + η` increases with `η`; since
`η_j = e_0/(j+1)` decreases, the sequence `j ↦ ‖V_{η_j}(x)‖²` is monotone
increasing and its supremum is its limit.  Monotone convergence (Preamble)
therefore turns the uniform bound on each `∫_{B_T}‖V_{η_j}‖²` into the same
bound for the integral of the supremum, which is the first conclusion.  Being
integrable, the supremum is finite almost everywhere.  That forces the second
conclusion: at a point with `g^k(x) = 0` and `Dg^k(x) ≠ 0` one has
`‖V_{η_j}(x)‖² = (p/2)²(η_j)^{p-2}‖Dg^k(x)‖²` with `p - 2 < 0` and
`η_j → 0`, so `(η_j)^{p-2} → +∞` and the supremum is `+∞`; the set of such
points is therefore null.  The third conclusion is the limit case `η = 0` of
the same monotonicity: `|g^k(x)| + η_j → |g^k(x)|` and the powers converge, so
`‖V_0(x)‖²` is the limit of an increasing sequence and hence at most its
supremum.  This is the route the parent's own comment calls reviewer elision
(4), and it replaces the manuscript's positive-part/uniqueness argument. -/
theorem RegularisedGradientSupremumBound :
    ∀ (n : ℕ) (p ε e0 T W2L Kc : ℝ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (x₀ : EuclideanSpace ℝ (Fin n)) (k : Fin n) (ηs : ℕ → ℝ),
      (0:ℝ) < p → p < 2 → p / 2 - 1 < 0 →
      (∀ (η : ℝ), 0 < η → ∀ s : ℝ, 0 < |s| + η) →
      0 < e0 → (∀ j : ℕ, ηs j = e0 / ((j : ℝ) + 1)) →
      (∀ j : ℕ, 0 < ηs j) → (∀ j : ℕ, (ηs j) ^ 2 < ε) →
      Filter.Tendsto ηs Filter.atTop (nhds 0) →
      (∀ (η : ℝ), 0 < η →
        IntegrableOn (fun x => ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
          (Metric.ball x₀ T) volume) →
      (∀ (η : ℝ), 0 < η → η ^ 2 < ε →
        (∫ x in Metric.ball x₀ T,
            ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
          ≤ W2L⁻¹ * Kc) →
      ((∫⁻ x in Metric.ball x₀ T, ⨆ j : ℕ,
            ENNReal.ofReal (‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2))
          ≤ ENNReal.ofReal (W2L⁻¹ * Kc))
      ∧ (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ T)), g x k = 0 → Dg k x = 0)
      ∧ (∀ x : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
            ≤ ⨆ j : ℕ, ENNReal.ofReal
              (‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2)) := by
  intro n p ε e0 T W2L Kc g Dg x₀ k ηs hp0 hp2 hexpn hbase he00 hηsval hηs0 hηsε
    hηt hVsqint hVbnd
  have hVn : ∀ (b : ℝ) (x : EuclideanSpace ℝ (Fin n)), 0 ≤ b →
      ‖(p / 2 * b ^ (p / 2 - 1)) • Dg k x‖ ^ 2
        = (p / 2 * b ^ (p / 2 - 1)) ^ 2 * ‖Dg k x‖ ^ 2 := by
    intro b x hb
    rw [norm_smul, Real.norm_eq_abs, mul_pow,
      abs_of_nonneg (mul_nonneg (by linarith only [hp0]) (Real.rpow_nonneg hb _))]
  have hVm2 : ∀ (η : ℝ), 0 < η → AEMeasurable
      (fun x => ENNReal.ofReal
        (‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2))
      (volume.restrict (Metric.ball x₀ T)) := fun η hη =>
    ((hVsqint η hη).1).aemeasurable.ennreal_ofReal
  have hηsanti : ∀ j j' : ℕ, j ≤ j' → ηs j' ≤ ηs j := by
    intro j j' h
    have h1 : (0:ℝ) < (j:ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) j; linarith only [this]
    have h3 : (0:ℝ) < (j':ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) j'; linarith only [this]
    have h2 : ((j:ℝ) + 1) ≤ ((j':ℝ) + 1) := by
      have : (j:ℝ) ≤ (j':ℝ) := by exact_mod_cast h
      linarith only [this]
    rw [hηsval j, hηsval j', div_le_div_iff₀ h3 h1]
    nlinarith only [h2, he00]
  have hVmono : ∀ (x : EuclideanSpace ℝ (Fin n)) (j j' : ℕ), j ≤ j' →
      ‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2
        ≤ ‖(p / 2 * (|g x k| + ηs j') ^ (p / 2 - 1)) • Dg k x‖ ^ 2 := by
    intro x j j' h
    have hb1 : (0:ℝ) ≤ |g x k| + ηs j :=
      le_of_lt (hbase (ηs j) (hηs0 j) (g x k))
    have hb2 : (0:ℝ) ≤ |g x k| + ηs j' :=
      le_of_lt (hbase (ηs j') (hηs0 j') (g x k))
    rw [hVn _ x hb1, hVn _ x hb2]
    have hle : (|g x k| + ηs j) ^ (p / 2 - 1)
        ≤ (|g x k| + ηs j') ^ (p / 2 - 1) :=
      Real.rpow_le_rpow_of_nonpos (hbase (ηs j') (hηs0 j') (g x k))
        (by linarith only [hηsanti j j' h]) hexpn.le
    have h0 : (0:ℝ) ≤ p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1) :=
      mul_nonneg (by linarith only [hp0]) (Real.rpow_nonneg hb1 _)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ h0
        (mul_le_mul_of_nonneg_left hle (by linarith only [hp0])) 2)
      (sq_nonneg _)
  have hSsum : (∫⁻ x in Metric.ball x₀ T, ⨆ j : ℕ,
        ENNReal.ofReal (‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2))
      ≤ ENNReal.ofReal (W2L⁻¹ * Kc) := by
    rw [lintegral_iSup' (fun j => hVm2 (ηs j) (hηs0 j))
      (Filter.Eventually.of_forall fun x => fun j j' h =>
        ENNReal.ofReal_le_ofReal (hVmono x j j' h))]
    refine iSup_le fun j => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hVsqint (ηs j) (hηs0 j))
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hVbnd (ηs j) (hηs0 j) (hηsε j))
  have hSm : AEMeasurable (fun x => ⨆ j : ℕ,
      ENNReal.ofReal (‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2))
      (volume.restrict (Metric.ball x₀ T)) :=
    AEMeasurable.iSup (fun j => hVm2 (ηs j) (hηs0 j))
  have hSne : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ T)),
      (⨆ j : ℕ, ENNReal.ofReal
        (‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2)) ≠ ⊤ := by
    have h1 : (∫⁻ x in Metric.ball x₀ T, ⨆ j : ℕ, ENNReal.ofReal
        (‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSsum
    filter_upwards [ae_lt_top' hSm h1] with x hx
    exact hx.ne
  -- `(η_j)^{p-2} → +∞`
  have hinvtop : Filter.Tendsto (fun j : ℕ => (ηs j) ^ (p - 2))
      Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun j : ℕ => ((j:ℝ) + 1) / e0)
        Filter.atTop Filter.atTop := by
      refine Filter.Tendsto.atTop_div_const he00 ?_
      exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 : Filter.Tendsto (fun j : ℕ => (((j:ℝ) + 1) / e0) ^ (2 - p))
        Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (by linarith only [hp2])).comp h1
    refine Filter.Tendsto.congr (fun j => ?_) h2
    have hj : ηs j = e0 / ((j:ℝ) + 1) := hηsval j
    have hpos := hηs0 j
    rw [show ((j:ℝ) + 1) / e0 = (ηs j)⁻¹ from by rw [hj, inv_div],
      Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le]
    congr 1
    ring
  -- REVIEWER ELISION (4)
  have hDz : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ T)),
      g x k = 0 → Dg k x = 0 := by
    filter_upwards [hSne] with x hS hg0
    by_contra hne
    have hD0 : (0:ℝ) < ‖Dg k x‖ ^ 2 := by
      have h1 : 0 < ‖Dg k x‖ := norm_pos_iff.2 hne
      positivity
    have hbnd' : ∀ j : ℕ, p ^ 2 / 4 * (ηs j) ^ (p - 2) * ‖Dg k x‖ ^ 2
        ≤ (⨆ j : ℕ, ENNReal.ofReal
            (‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2)).toReal := by
      intro j
      have hval : ‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2
          = p ^ 2 / 4 * (ηs j) ^ (p - 2) * ‖Dg k x‖ ^ 2 := by
        rw [hg0, abs_zero, zero_add,
          hVn _ x (hηs0 j).le]
        have he : ((ηs j) ^ (p / 2 - 1)) ^ 2 = (ηs j) ^ (p - 2) := by
          rw [← Real.rpow_natCast ((ηs j) ^ (p / 2 - 1)) 2,
            ← Real.rpow_mul (hηs0 j).le]
          congr 1
          push_cast
          ring
        calc (p / 2 * (ηs j) ^ (p / 2 - 1)) ^ 2 * ‖Dg k x‖ ^ 2
            = p ^ 2 / 4 * ((ηs j) ^ (p / 2 - 1)) ^ 2 * ‖Dg k x‖ ^ 2 := by ring
          _ = p ^ 2 / 4 * (ηs j) ^ (p - 2) * ‖Dg k x‖ ^ 2 := by rw [he]
      rw [← hval, ← ENNReal.ofReal_le_iff_le_toReal hS]
      exact le_iSup (fun j : ℕ => ENNReal.ofReal
        (‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2)) j
    have hFt : Filter.Tendsto
        (fun j : ℕ => p ^ 2 / 4 * (ηs j) ^ (p - 2) * ‖Dg k x‖ ^ 2)
        Filter.atTop Filter.atTop :=
      (hinvtop.const_mul_atTop (show (0:ℝ) < p ^ 2 / 4 by positivity)).atTop_mul_const
        hD0
    obtain ⟨j, hj⟩ := (hFt.eventually_ge_atTop
      ((⨆ j : ℕ, ENNReal.ofReal
        (‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2)).toReal + 1)).exists
    linarith only [hj, hbnd' j]
  -- the limit integrand is dominated by the supremum, pointwise
  have hVle : ∀ x : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
        ≤ ⨆ j : ℕ, ENNReal.ofReal
          (‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2) := by
    intro x
    rcases eq_or_ne (g x k) 0 with hg0 | hg0
    · have hz : ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 = 0 := by
        rw [hg0, abs_zero, Real.zero_rpow (ne_of_lt hexpn), mul_zero, zero_smul,
          norm_zero]
        ring
      rw [hz, ENNReal.ofReal_zero]
      exact zero_le
    · have hc : ContinuousAt (fun s : ℝ => s ^ (p / 2 - 1)) |g x k| :=
        Real.continuousAt_rpow_const _ _ (Or.inl (abs_ne_zero.2 hg0))
      have h1 : Filter.Tendsto (fun j : ℕ => |g x k| + ηs j) Filter.atTop
          (nhds |g x k|) := by
        have h2 := (tendsto_const_nhds (x := |g x k|)
          (f := (Filter.atTop : Filter ℕ))).add hηt
        simpa using h2
      have h4 : Filter.Tendsto
          (fun j : ℕ => ‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
          Filter.atTop
          (nhds (‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)) :=
        ((((hc.tendsto.comp h1).const_mul (p / 2)).smul_const
          (Dg k x)).norm).pow 2
      have h5 := ENNReal.tendsto_ofReal h4
      have h6 := tendsto_atTop_iSup (f := fun j : ℕ => ENNReal.ofReal
        (‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖ ^ 2))
        (fun j j' h => ENNReal.ofReal_le_ofReal (hVmono x j j' h))
      exact le_of_eq (tendsto_nhds_unique h5 h6)
  exact ⟨hSsum, hDz, hVle⟩
