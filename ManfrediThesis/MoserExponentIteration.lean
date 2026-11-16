import ManfrediThesis.Preamble
set_option maxHeartbeats 1600000
open MeasureTheory

/-- The exponent iteration of Moser's argument: from the reverse-H\"older step
at a single pair of radii to a pointwise bound on the whole inner ball.

Conventions, restated here because a helper inherits none of its parent's.
`v ≥ 0` is the function being iterated on `B_R(x₀)`;
`Y s ρ = (|B_R(x₀)|^{-1}∫_{B_ρ(x₀)}v^{2s})^{1/(2s)}` is the normalised
`L^{2s}` mean on the inner ball, *normalised by the measure of the OUTER ball
`B_R(x₀)`* at every radius, which is the convention that makes the radii cancel
in the iteration; and `Bnd ρ A` abbreviates `v ≤ A` almost everywhere on
`B_ρ(x₀)`.  `χ > 1` is the Sobolev exponent gain, `σ₁ = χ/(2(χ-1))` and
`σ₂ = χ/(2(χ-1)²)` are the two exponent sums, and `E = (2D)^{σ₁}2^{σ₂}` with
`D` the step constant of the reverse-H\"older hypothesis.

Given that hypothesis --- `Y(θχ)r' ≤ (DR/(r-r'))^{1/θ}Y θ r` for every `θ > 1`
and all `R/2 ≤ r' < r ≤ 3R/4` --- and monotonicity of `Y s ·` in the radius,
the conclusion is
`Bnd ρ' (E(R/(ρ-ρ'))^{σ₁}Y 2 ρ)` for all `R/2 ≤ ρ' < ρ ≤ 3R/4`.

The route has two halves.  First the iteration proper: with `θ_j = 2χ^j` and
`r_j = ρ' + 2^{-j}(ρ-ρ')`, the hypothesis at `(θ_j, r_{j+1}, r_j)` chains into
`Y(θ_m)ρ' ≤ exp(Σ_{j<m}θ_j^{-1}log(DR/(r_j-r_{j+1}))) · Y 2 ρ`, and the
exponent sums converge: `Σ_j θ_j^{-1} = σ₁` and `Σ_j jθ_j^{-1} = σ₂` are the
two geometric sums, `r_j - r_{j+1} = 2^{-(j+1)}(ρ-ρ')`, and `D ≥ 1` lets every
partial product be bounded by the infinite one, giving the uniform bound
`Y(θ_m)ρ' ≤ E(R/(ρ-ρ'))^{σ₁}Y 2 ρ` for every `m`.  Second, the Chebyshev half
of the `L^q`-mean characterisation of the essential supremum turns that uniform
bound into the pointwise one: if `A < t` and `|B_{ρ'} ∩ {v > t}| > 0`, then
`Y(s)ρ' ≥ t(|B_{ρ'} ∩ {v>t}|/|B_R|)^{1/(2s)}`, whose right-hand side tends to
`t > A` as `s → ∞` along `θ_m`, contradicting `Y(θ_m)ρ' ≤ A`; so every
superlevel set `{v > t}` with `t > A` is null in `B_{ρ'}`, and taking a
sequence `t ↓ A` gives `v ≤ A` almost everywhere there, i.e. `Bnd ρ' A`. -/
theorem MoserExponentIteration :
    ∀ (n : ℕ) (χ σ₁ σ₂ D E : ℝ), 1 < χ →
      σ₁ = χ / (2 * (χ - 1)) → σ₂ = χ / (2 * (χ - 1) ^ 2) →
      E = (2 * D) ^ σ₁ * 2 ^ σ₂ → 0 < E → 1 ≤ D →
    ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
      (v : EuclideanSpace ℝ (Fin n) → ℝ),
      0 < R → Measurable v → (∀ x, 0 ≤ v x) →
      0 < (volume (Metric.ball x₀ R)).toReal →
    ∀ (Y : ℝ → ℝ → ℝ) (Bnd : ℝ → ℝ → Prop),
      (∀ s ρ : ℝ, Y s ρ = ((volume (Metric.ball x₀ R)).toReal⁻¹
          * ∫ x in Metric.ball x₀ ρ, v x ^ (2 * s)) ^ (1 / (2 * s))) →
      Bnd = (fun ρ A => ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ)), v x ≤ A) →
      (∀ s ρ : ℝ, 1 < s → 0 < ρ → ρ < R →
        IntegrableOn (fun x => v x ^ (2 * s)) (Metric.ball x₀ ρ) volume) →
      (∀ s ρ : ℝ, 0 < s → 0 ≤ Y s ρ) →
      (∀ θ r' r : ℝ, 1 < θ → R / 2 ≤ r' → r' < r → r ≤ 3 * R / 4 →
        Y (θ * χ) r' ≤ (D * R / (r - r')) ^ (1 / θ) * Y θ r) →
      (∀ s a b : ℝ, 1 < s → 0 < a → a ≤ b → b < R → Y s a ≤ Y s b) →
    ∀ ρ' ρ : ℝ, R / 2 ≤ ρ' → ρ' < ρ → ρ ≤ 3 * R / 4 →
      Bnd ρ' (E * (R / (ρ - ρ')) ^ σ₁ * Y 2 ρ) := by
  intro n χ σ₁ σ₂ D E hχ1 hσ₁def hσ₂def hEdef hE0 hD1 x₀ R v hR hvmeas hvnn
    hmR0 Y Bnd hYeq hBnddef hintpow hYnn h1 hYmono
  have hcheb : ∀ (ρ'' A : ℝ) (sq : ℕ → ℝ), 0 < ρ'' → ρ'' < R → 0 ≤ A →
      (∀ m, 1 < sq m) → Filter.Tendsto sq Filter.atTop Filter.atTop →
      (∀ m : ℕ, Y (sq m) ρ'' ≤ A) → Bnd ρ'' A := by

    intro ρ'' A sq hρ'' hρ''R hA hsq1 hsqto hYb
    have hnull : ∀ t : ℝ, A < t →
        volume (Metric.ball x₀ ρ'' ∩ {x | t < v x}) = 0 := by
      intro t hAt
      have ht0 : 0 < t := lt_of_le_of_lt hA hAt
      have hZmeas : MeasurableSet (Metric.ball x₀ ρ'' ∩ {x | t < v x}) :=
        measurableSet_ball.inter (measurableSet_lt measurable_const hvmeas)
      have hZsub : Metric.ball x₀ ρ'' ∩ {x | t < v x} ⊆ Metric.ball x₀ ρ'' :=
        Set.inter_subset_left
      have hZtop : volume (Metric.ball x₀ ρ'' ∩ {x | t < v x}) ≠ ⊤ :=
        ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hZsub)
      by_contra hZ0
      have hZpos : 0 < (volume (Metric.ball x₀ ρ'' ∩ {x | t < v x})).toReal :=
        ENNReal.toReal_pos hZ0 hZtop
      have hlow : ∀ m : ℕ, t * ((volume (Metric.ball x₀ R)).toReal⁻¹
          * (volume (Metric.ball x₀ ρ'' ∩ {x | t < v x})).toReal) ^ (1 / (2 * sq m))
          ≤ Y (sq m) ρ'' := by
        intro m
        have hs0 : (0 : ℝ) < sq m := lt_trans one_pos (hsq1 m)
        have hint := hintpow (sq m) ρ'' (hsq1 m) hρ'' hρ''R
        have hZle := setIntegral_ge_of_const_le_real (μ := volume)
          (s := Metric.ball x₀ ρ'' ∩ {x | t < v x})
          (f := fun x => v x ^ (2 * sq m)) (c := t ^ (2 * sq m))
          hZmeas hZtop
          (fun x hx => Real.rpow_le_rpow ht0.le (le_of_lt hx.2) (by linarith))
          (hint.mono_set hZsub)
        rw [MeasureTheory.measureReal_def] at hZle
        have hc2 : (∫ x in Metric.ball x₀ ρ'' ∩ {x | t < v x}, v x ^ (2 * sq m))
            ≤ ∫ x in Metric.ball x₀ ρ'', v x ^ (2 * sq m) :=
          setIntegral_mono_set hint
            (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hvnn x) _)
            (LE.le.eventuallyLE hZsub)
        have hstep1 : t ^ (2 * sq m)
            * (volume (Metric.ball x₀ ρ'' ∩ {x | t < v x})).toReal
            ≤ ∫ x in Metric.ball x₀ ρ'', v x ^ (2 * sq m) := hZle.trans hc2
        rw [hYeq (sq m) ρ'']
        have hbase : (0 : ℝ) ≤ (volume (Metric.ball x₀ R)).toReal⁻¹
            * (t ^ (2 * sq m)
              * (volume (Metric.ball x₀ ρ'' ∩ {x | t < v x})).toReal) := by positivity
        have hmono := Real.rpow_le_rpow hbase
          (mul_le_mul_of_nonneg_left hstep1 (by positivity :
            (0 : ℝ) ≤ (volume (Metric.ball x₀ R)).toReal⁻¹))
          (by positivity : (0 : ℝ) ≤ 1 / (2 * sq m))
        refine le_trans (le_of_eq ?_) hmono
        rw [show (volume (Metric.ball x₀ R)).toReal⁻¹
            * (t ^ (2 * sq m)
              * (volume (Metric.ball x₀ ρ'' ∩ {x | t < v x})).toReal)
            = t ^ (2 * sq m) * ((volume (Metric.ball x₀ R)).toReal⁻¹
              * (volume (Metric.ball x₀ ρ'' ∩ {x | t < v x})).toReal) from by ring,
          Real.mul_rpow (Real.rpow_nonneg ht0.le _) (by positivity),
          ← Real.rpow_mul ht0.le,
          show (2 * sq m) * (1 / (2 * sq m)) = 1 from by field_simp, Real.rpow_one]
      have hc0 : (0 : ℝ) < (volume (Metric.ball x₀ R)).toReal⁻¹
          * (volume (Metric.ball x₀ ρ'' ∩ {x | t < v x})).toReal := by positivity
      have hz : Filter.Tendsto (fun m : ℕ => 1 / (2 * sq m)) Filter.atTop (nhds 0) := by
        have h1 : Filter.Tendsto (fun m : ℕ => 2 * sq m) Filter.atTop Filter.atTop :=
          Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) hsqto
        exact Filter.Tendsto.congr (fun m => (one_div (2 * sq m)).symm)
          h1.inv_tendsto_atTop
      have hto1 : Filter.Tendsto (fun m : ℕ => ((volume (Metric.ball x₀ R)).toReal⁻¹
          * (volume (Metric.ball x₀ ρ'' ∩ {x | t < v x})).toReal) ^ (1 / (2 * sq m)))
          Filter.atTop (nhds 1) := by
        have hcont := (Real.continuousAt_const_rpow (ne_of_gt hc0)).tendsto.comp hz
        simpa [Function.comp_def, Real.rpow_zero] using hcont
      have hlim : t ≤ A := by
        have h1 := Filter.Tendsto.const_mul t hto1
        rw [mul_one] at h1
        exact le_of_tendsto h1
          (Filter.Eventually.of_forall fun m => (hlow m).trans (hYb m))
      linarith
    have hkey : volume (Metric.ball x₀ ρ'' ∩ {x | A < v x}) = 0 := by
      have hcover : Metric.ball x₀ ρ'' ∩ {x | A < v x}
          = ⋃ k : ℕ, Metric.ball x₀ ρ'' ∩ {x | A + 1 / ((k : ℝ) + 1) < v x} := by
        ext y
        constructor
        · intro hy
          have hy2 : A < v y := hy.2
          obtain ⟨k, hk⟩ := exists_nat_gt (1 / (v y - A))
          refine Set.mem_iUnion.2 ⟨k, hy.1, ?_⟩
          have hpos : 0 < v y - A := by linarith
          have hk1 : (1 : ℝ) / ((k : ℝ) + 1) < v y - A := by
            rw [div_lt_iff₀ (by positivity)]
            rw [div_lt_iff₀ hpos] at hk
            nlinarith
          show A + 1 / ((k : ℝ) + 1) < v y
          linarith
        · intro hy
          obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hy
          have h2 : A + 1 / ((k : ℝ) + 1) < v y := hk.2
          have h3 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
          exact ⟨hk.1, by show A < v y; linarith⟩
      rw [hcover]
      refine measure_iUnion_null fun k => ?_
      refine hnull (A + 1 / ((k : ℝ) + 1)) ?_
      have h3 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    rw [hBnddef]
    show ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ'')), v x ≤ A
    rw [Filter.eventually_iff, mem_ae_iff,
      show {x : EuclideanSpace ℝ (Fin n) | v x ≤ A}ᶜ = {x | A < v x} from by
        ext y; simp [not_le],
      Measure.restrict_apply' measurableSet_ball]
    refine measure_mono_null ?_ hkey
    intro y hy
    exact ⟨hy.2, hy.1⟩
  -- (2): the exponent iteration
  have h2 : ∀ ρ' ρ : ℝ, R / 2 ≤ ρ' → ρ' < ρ → ρ ≤ 3 * R / 4 →
      Bnd ρ' (E * (R / (ρ - ρ')) ^ σ₁ * Y 2 ρ) := by

    intro ρ' ρ hρ'lo hρ'ρ hρhi
    have hρ'0 : 0 < ρ' := by linarith
    have hdρ : 0 < ρ - ρ' := by linarith
    have hρR : ρ < R := by linarith
    have hRdρ : (0 : ℝ) < R / (ρ - ρ') := div_pos hR hdρ
    -- the exponents `θ j = 2 χ^j`
    obtain ⟨θ, hθdef⟩ : ∃ θ : ℕ → ℝ, θ = fun j : ℕ => 2 * χ ^ j := ⟨_, rfl⟩
    have hθeq : ∀ j : ℕ, θ j = 2 * χ ^ j := fun j => by rw [hθdef]
    have hχpow : ∀ j : ℕ, (1 : ℝ) ≤ χ ^ j := fun j => one_le_pow₀ (by linarith)
    have hθ1 : ∀ j, 1 < θ j := by intro j; rw [hθeq j]; linarith [hχpow j]
    have hθ0 : ∀ j, 0 < θ j := fun j => lt_trans one_pos (hθ1 j)
    have hθsucc : ∀ j : ℕ, θ (j + 1) = θ j * χ := by
      intro j; rw [hθeq, hθeq, pow_succ]; ring
    have hθto : Filter.Tendsto θ Filter.atTop Filter.atTop := by
      rw [hθdef]
      exact Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
        (tendsto_pow_atTop_atTop_of_one_lt hχ1)
    -- the radii `r j` decreasing to `ρ'`
    obtain ⟨rj, hrjdef⟩ : ∃ rj : ℕ → ℝ,
        rj = fun j : ℕ => ρ' + (1 / 2 : ℝ) ^ j * (ρ - ρ') := ⟨_, rfl⟩
    have hrjeq : ∀ j : ℕ, rj j = ρ' + (1 / 2 : ℝ) ^ j * (ρ - ρ') := fun j => by rw [hrjdef]
    have hrj0 : rj 0 = ρ := by rw [hrjeq 0]; norm_num
    have hrjlo : ∀ j, ρ' ≤ rj j := by
      intro j
      rw [hrjeq j]
      have h1 : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
      nlinarith
    have hrjhi : ∀ j, rj j ≤ ρ := by
      intro j
      rw [hrjeq j]
      have h1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have hrjdiff : ∀ j : ℕ, rj j - rj (j + 1) = (1 / 2 : ℝ) ^ (j + 1) * (ρ - ρ') := by
      intro j; rw [hrjeq j, hrjeq (j + 1), pow_succ]; ring
    have hrjlt : ∀ j : ℕ, rj (j + 1) < rj j := by
      intro j
      have h := hrjdiff j
      have h1 : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) * (ρ - ρ') := by positivity
      linarith
    -- the base constant of the iteration
    obtain ⟨K0, hK0def⟩ : ∃ K0 : ℝ, K0 = 2 * D * (R / (ρ - ρ')) := ⟨_, rfl⟩
    have hK0ge : (4 : ℝ) ≤ R / (ρ - ρ') := by
      rw [le_div_iff₀ hdρ]; linarith
    have hK01 : 1 ≤ K0 := by rw [hK0def]; nlinarith
    have hK00 : 0 < K0 := by linarith
    -- one step of (1)
    have hstep : ∀ j : ℕ, Y (θ (j + 1)) (rj (j + 1))
        ≤ ((2 : ℝ) ^ j * K0) ^ (1 / θ j) * Y (θ j) (rj j) := by
      intro j
      have h := h1 (θ j) (rj (j + 1)) (rj j) (hθ1 j)
        (le_trans hρ'lo (hrjlo (j + 1))) (hrjlt j) (le_trans (hrjhi j) hρhi)
      rw [← hθsucc j] at h
      refine h.trans (le_of_eq ?_)
      congr 2
      rw [hrjdiff j, hK0def]
      have hne : ((1 : ℝ) / 2) ^ (j + 1) ≠ 0 := by positivity
      have hdne : (ρ - ρ') ≠ 0 := ne_of_gt hdρ
      rw [div_pow, one_pow]
      field_simp
      ring
    -- the product, in exponential form
    have hiter : ∀ m : ℕ, Y (θ m) (rj m)
        ≤ Real.exp (∑ j ∈ Finset.range m, (1 / θ j)
            * ((j : ℝ) * Real.log 2 + Real.log K0)) * Y 2 ρ := by
      intro m
      induction m with
      | zero =>
          rw [hrj0, show θ 0 = 2 from by rw [hθeq 0]; norm_num]
          simp
      | succ m ih =>
          have hexpK : ((2 : ℝ) ^ m * K0) ^ (1 / θ m)
              = Real.exp ((1 / θ m) * ((m : ℝ) * Real.log 2 + Real.log K0)) := by
            rw [Real.rpow_def_of_pos (by positivity)]
            congr 1
            rw [Real.log_mul (by positivity) (ne_of_gt hK00), Real.log_pow]
            ring
          refine (hstep m).trans ?_
          refine (mul_le_mul_of_nonneg_left ih
            (Real.rpow_nonneg (by positivity) _)).trans (le_of_eq ?_)
          rw [hexpK, Finset.sum_range_succ, Real.exp_add]
          ring
    -- the two series bounds
    have hiχ : (0 : ℝ) ≤ 1 / χ := by positivity
    have hiχ1 : (1 : ℝ) / χ < 1 := by rw [div_lt_one (by linarith)]; linarith
    have hg1 : HasSum (fun j : ℕ => (1 / χ : ℝ) ^ j) (1 - 1 / χ)⁻¹ :=
      hasSum_geometric_of_lt_one hiχ hiχ1
    have hg2 : HasSum (fun j : ℕ => (j : ℝ) * (1 / χ : ℝ) ^ j)
        ((1 / χ) / (1 - 1 / χ) ^ 2) :=
      hasSum_coe_mul_geometric_of_norm_lt_one (by
        rw [Real.norm_eq_abs, abs_of_nonneg hiχ]; exact hiχ1)
    have hχne : (χ : ℝ) ≠ 0 := by linarith
    have hs1 : ∀ m : ℕ, (∑ j ∈ Finset.range m, 1 / θ j) ≤ σ₁ := by
      intro m
      have hrw1 : ∀ j : ℕ, 1 / θ j = (1 / 2 : ℝ) * (1 / χ : ℝ) ^ j := by
        intro j
        rw [hθeq j, div_pow, one_pow]
        field_simp
      rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range m) => hrw1 j), ← Finset.mul_sum]
      have hps := hg1.summable.sum_le_tsum (Finset.range m)
        (fun j (_ : j ∉ Finset.range m) =>
          le_of_lt (by positivity : (0 : ℝ) < (1 / χ : ℝ) ^ j))
      rw [hg1.tsum_eq] at hps
      have hσ : σ₁ = (1 / 2 : ℝ) * (1 - 1 / χ)⁻¹ := by
        rw [hσ₁def]
        field_simp
      rw [hσ]
      exact mul_le_mul_of_nonneg_left hps (by norm_num)
    have hs2 : ∀ m : ℕ, (∑ j ∈ Finset.range m, (j : ℝ) / θ j) ≤ σ₂ := by
      intro m
      have hrw2 : ∀ j : ℕ, (j : ℝ) / θ j
          = (1 / 2 : ℝ) * ((j : ℝ) * (1 / χ : ℝ) ^ j) := by
        intro j
        rw [hθeq j, div_pow, one_pow]
        field_simp
      rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range m) => hrw2 j), ← Finset.mul_sum]
      have hps := hg2.summable.sum_le_tsum (Finset.range m)
        (fun j (_ : j ∉ Finset.range m) =>
          mul_nonneg (Nat.cast_nonneg j)
            (le_of_lt (by positivity : (0 : ℝ) < (1 / χ : ℝ) ^ j)))
      rw [hg2.tsum_eq] at hps
      have hσ : σ₂ = (1 / 2 : ℝ) * ((1 / χ) / (1 - 1 / χ) ^ 2) := by
        rw [hσ₂def]
        field_simp
      rw [hσ]
      exact mul_le_mul_of_nonneg_left hps (by norm_num)
    have hsumb : ∀ m : ℕ, (∑ j ∈ Finset.range m, (1 / θ j)
          * ((j : ℝ) * Real.log 2 + Real.log K0))
        ≤ σ₂ * Real.log 2 + σ₁ * Real.log K0 := by
      intro m
      have hrw : ∀ j : ℕ, (1 / θ j) * ((j : ℝ) * Real.log 2 + Real.log K0)
          = Real.log 2 * ((j : ℝ) / θ j) + Real.log K0 * (1 / θ j) := by
        intro j
        ring
      rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range m) => hrw j),
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hlK : (0 : ℝ) ≤ Real.log K0 := Real.log_nonneg hK01
      have ha := mul_le_mul_of_nonneg_left (hs2 m) hl2.le
      have hb := mul_le_mul_of_nonneg_left (hs1 m) hlK
      linarith
    -- the constant identity
    have hid : Real.exp (σ₂ * Real.log 2 + σ₁ * Real.log K0)
        = E * (R / (ρ - ρ')) ^ σ₁ := by
      have e1 : (2 : ℝ) ^ σ₂ = Real.exp (σ₂ * Real.log 2) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
      have e2 : K0 ^ σ₁ = Real.exp (σ₁ * Real.log K0) := by
        rw [Real.rpow_def_of_pos hK00]; congr 1; ring
      have e3 : K0 ^ σ₁ = (2 * D) ^ σ₁ * (R / (ρ - ρ')) ^ σ₁ := by
        rw [hK0def, Real.mul_rpow (by linarith) hRdρ.le]
      rw [Real.exp_add, ← e1, ← e2, e3, hEdef]
      ring
    -- all the means at `ρ'` are bounded by the same quantity
    have hYb : ∀ m : ℕ, Y (θ m) ρ' ≤ E * (R / (ρ - ρ')) ^ σ₁ * Y 2 ρ := by
      intro m
      refine (hYmono (θ m) ρ' (rj m) (hθ1 m) hρ'0 (hrjlo m)
        (lt_of_le_of_lt (hrjhi m) hρR)).trans ((hiter m).trans ?_)
      refine mul_le_mul_of_nonneg_right ?_ (hYnn 2 ρ (by norm_num))
      rw [← hid]
      exact Real.exp_le_exp.2 (hsumb m)
    refine hcheb ρ' _ θ hρ'0 (by linarith) ?_ hθ1 hθto hYb
    exact mul_nonneg (mul_nonneg hE0.le (Real.rpow_nonneg hRdρ.le _))
      (hYnn 2 ρ (by norm_num))
  exact h2
