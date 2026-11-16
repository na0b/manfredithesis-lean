import ManfrediThesis.Preamble
import ManfrediThesis.RegularisedGradientSupremumBound
import ManfrediThesis.MemW1pOn
import ManfrediThesis.HasWeakGradientOn
set_option maxHeartbeats 1600000
open MeasureTheory

/-- Conclusion (1) of the subquadratic signed-power estimate: for every inner
radius `0 < T < R` the function `v = |g^k|^{p/2-1} g^k` lies in `W^{1,2}(B_T)`
with weak gradient `V = (p/2)|g^k|^{p/2-1} Dg^k`.

Conventions, restated here because a helper inherits none of its parent's: the
exponent range is `1 < p < 2`, so `p/2 - 1 < 0` and the powers are
`Real.rpow`, which gives `0^{p/2-1} = 0`; `w = ε + ‖g‖²` is the weight of the
structure conditions and `w^{p/2-1}` is written exactly as (Q1)/(Q2) print it;
`λ = μ/2` where `μ` bounds every component of `g` almost everywhere on `B_R`;
`π_η(s) = (|s|+η)^{p-2}s` and `G_η(s) = ∫_0^s (p/2)(|t|+η)^{p/2-1}dt` are the
thesis' `η`-regularisations, with `ψ_η = π_η(g^k)` and `v_η = G_η(g^k)`;
`V_η = (p/2)(|g^k|+η)^{p/2-1} Dg^k`; `supp` is the closed support; and
`η_j = e_0/(j+1)` is the regularisation sequence of (D.6a), with `0 < e_0` and
`η_j² < ε`.

The route is (D5).  `MemLp v 2` is free: `|v| = |g^k|^{p/2} ≤ μ^{p/2}` almost
everywhere, and `B_T` has finite measure, so a bounded almost everywhere
measurable function lies in `L²`.  `MemLp V 2` comes from the hypothesis (3.17)
at the level `ℓ = 0`, both signs, with the cut-off `ζ_{T,T'}` for some
`T < T' < R` -- so `ζ = 1` on `closedBall x₀ T` -- and the almost everywhere
lower bound `w^{p/2-1} ≥ ((1+4n)λ²)^{p/2-1} > 0` coming from `w ≤ (1+4n)λ²`;
no Fatou is needed, (3.17) already being the `η → 0` statement.  The two sets
`{ψ > 0}` and `{ψ < 0}` exhaust `{g^k ≠ 0}` because `π_η` is odd and strictly
increasing, and on `{g^k = 0}` the field `V` vanishes POINTWISE, since
`0^{p/2-1} = 0` for the negative exponent; that observation is what removes any
appeal to `Dg^k = 0` almost everywhere on `{g^k = 0}` from this half.

The weak-gradient identity is the only remaining work, and it is dominated
convergence in the identity for `(v_η, V_η)` as `η = η_j ↓ 0`, for each fixed
test function `φ`.  Two inputs: (a) `v_η → v` pointwise, obtained from the
closed form of `G_η` -- on `[0,s]` with `s > 0` one has `|t| = t`, so the
integrand is `(p/2)(t+η)^{p/2-1}` with antiderivative `(t+η)^{p/2}` and
`G_η(s) = (s+η)^{p/2} - η^{p/2}`, symmetrically for `s < 0`, and `G_η(0) = 0`;
the limit is then continuity of `η ↦ (|s|+η)^{p/2}` at `η = 0` together with
`η^{p/2} → 0`.  And (b) the domination `‖V_η‖ ≤ ‖V‖` almost everywhere, which
off `{g^k = 0}` is `(|t|+η)^{p/2-1} ≤ |t|^{p/2-1}` for the negative exponent,
and which on `{g^k = 0}` is false pointwise -- there `V = 0` while
`V_η = (p/2)η^{p/2-1} Dg^k` -- so that is exactly where `Dg^k = 0` almost
everywhere on `{g^k = 0}` is needed.  The dominating function on the
`v_η ∂_i φ` side is `(2λ+1)^{p/2}|∂_i φ|`. -/
theorem SignedPowerMemW12OnInnerBall :
    ∀ (n : ℕ) (p : ℝ), 1 < p → p < 2 →
      ∀ (Lc C₂ ε μ lam : ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ) (k : Fin n),
        0 < ε → 0 < μ → lam = μ / 2 → 0 < lam → 0 ≤ C₂ →
        (∀ i : Fin n, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), |g x i| ≤ μ) →
        (∀ ρ₀ ρ₁ : ℝ, 0 < ρ₀ → ρ₀ < ρ₁ →
          ∃ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
            ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧
            tsupport ζ ⊆ Metric.ball x₀ ρ₁ ∧
            (∀ x, 0 ≤ ζ x) ∧ (∀ x, ζ x ≤ 1) ∧
            (∀ x ∈ Metric.closedBall x₀ ρ₀, ζ x = 1) ∧
            (∀ x, ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2
                ≤ Lc / (ρ₁ - ρ₀) ^ 2)) →
        (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
          ε + ‖g x‖ ^ 2 ≤ (1 + 4 * (n : ℝ)) * lam ^ 2) →
        (∀ x : EuclideanSpace ℝ (Fin n), ε ≤ ε + ‖g x‖ ^ 2) →
        (∀ i : Fin n, AEStronglyMeasurable (fun x => g x i)
          (volume.restrict (Metric.ball x₀ R))) →
        AEStronglyMeasurable (Dg k) (volume.restrict (Metric.ball x₀ R)) →
      ∀ pie Gee : ℝ → ℝ → ℝ,
        Gee = (fun η s => ∫ t in (0:ℝ)..s, p / 2 * (|t| + η) ^ (p / 2 - 1)) →
        (∀ (η : ℝ), 0 < η → ∀ s : ℝ, 0 < |s| + η) →
        (∀ (η : ℝ), 0 < η → ContDiff ℝ 1 (Gee η)) →
        (∀ (η : ℝ), 0 < η →
          ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
            |pie η (g x k)| ≤ μ ^ (p - 1)) →
        (∀ (η : ℝ), 0 < η → ∀ T : ℝ, 0 < T → T < R →
          MemW1pOn n 2 (Metric.ball x₀ T) (fun x => Gee η (g x k))
            (fun x => (p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x)) →
      ∀ (e0 : ℝ) (ηs : ℕ → ℝ), 0 < e0 → e0 ≤ 1 →
        (∀ j : ℕ, ηs j = e0 / ((j : ℝ) + 1)) →
        (∀ j : ℕ, 0 < ηs j) → (∀ j : ℕ, (ηs j) ^ 2 < ε) →
        Filter.Tendsto ηs Filter.atTop (nhds 0) →
        (∀ (η : ℝ), 0 < η → η ^ 2 < ε →
          ∀ (ℓ : ℝ) (ζ : EuclideanSpace ℝ (Fin n) → ℝ),
            ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
            tsupport ζ ⊆ Metric.ball x₀ R →
            IntegrableOn (fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
                  * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
                (Metric.ball x₀ R) volume
              ∧ ((∫ x in Metric.ball x₀ R ∩ {y | ℓ < pie η (g y k)},
                    (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
                      * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
                  ≤ C₂ * (∫ x in Metric.ball x₀ R,
                      max (pie η (g x k) - ℓ) 0 ^ 2
                        * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)))
              ∧ ((∫ x in Metric.ball x₀ R ∩ {y | pie η (g y k) < ℓ},
                    (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
                      * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
                  ≤ C₂ * (∫ x in Metric.ball x₀ R,
                      max (ℓ - pie η (g x k)) 0 ^ 2
                        * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)))) →
      ∀ T : ℝ, 0 < T → T < R →
        MemW1pOn n 2 (Metric.ball x₀ T)
          (fun x => |g x k| ^ (p / 2 - 1) * g x k)
          (fun x => (p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x) := by
  intro n p hp hp2 Lc C₂ ε μ lam g Dg x₀ R k hε hμ hlamdef hlam0 hC₂0 hbd hcut
    hwup hwlow hgmRi hDgmR pie Gee hGeedef hbase hGeeC1 hpiebd hveeW e0 ηs he00
    he0le1 hηsval hηs0 hηsε hηt hD5 T hT0 hTR
  have hp0 : (0:ℝ) < p := by linarith
  have hexpn : p / 2 - 1 < 0 := by linarith
  -- (D5.1) the cut-off `ζ_{T,T'}` and the lower bound on the weight
  obtain ⟨T', hT'def⟩ : ∃ t : ℝ, t = (T + R) / 2 := ⟨_, rfl⟩
  have hTT' : T < T' := by rw [hT'def]; linarith only [hTR]
  have hT'R : T' < R := by rw [hT'def]; linarith only [hTR]
  obtain ⟨ζ, hζsm, hζcs, hζts, hζnn, hζle1, hζone, hζgrad⟩ := hcut T T' hT0 hTT'
  have hζtsR : tsupport ζ ⊆ Metric.ball x₀ R :=
    hζts.trans (Metric.ball_subset_ball hT'R.le)
  have hsubT : Metric.ball x₀ T ⊆ Metric.ball x₀ R :=
    Metric.ball_subset_ball hTR.le
  obtain ⟨W2L, hW2Ldef⟩ : ∃ t : ℝ,
    t = ((1 + 4 * (n:ℝ)) * lam ^ 2) ^ (p / 2 - 1) := ⟨_, rfl⟩
  have hW2L0 : 0 < W2L := by
    rw [hW2Ldef]; exact Real.rpow_pos_of_pos (by positivity) _
  have hwlowW : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      W2L ≤ (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) := by
    filter_upwards [hwup] with x hx
    rw [hW2Ldef]
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hε (hwlow x)) hx hexpn.le
  -- (D5.2) `‖V_η‖²` is integrable on `B_T`, from (D.2)
  have hVsqint : ∀ (η : ℝ), 0 < η →
      IntegrableOn (fun x => ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
        (Metric.ball x₀ T) volume := by
    intro η hη
    have hmem := (hveeW η hη T hT0 hTR).2.2
    have h1 : Integrable (fun x =>
        ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖
          ^ (ENNReal.ofReal 2).toReal)
        (volume.restrict (Metric.ball x₀ T)) :=
      hmem.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp] at h1
    refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
    show ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ (2:ℝ)
        = ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2
    rw [← Real.rpow_natCast
      ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ 2]
    norm_num
  -- (D5.3) THE UNIFORM BOUND.  `hD5` at the level `ℓ₀ = -μ^{p-1} - 1`, which
  -- every value of `ψ_η` exceeds almost everywhere, so the superlevel set is
  -- all of `B_R` and no splitting of `B_R` by the sign of `g^k` is needed.
  obtain ⟨ℓ₀, hℓ₀def⟩ : ∃ t : ℝ, t = -(μ ^ (p - 1)) - 1 := ⟨_, rfl⟩
  have hμp0 : (0:ℝ) < μ ^ (p - 1) := Real.rpow_pos_of_pos hμ _
  obtain ⟨Kc, hKcdef⟩ : ∃ t : ℝ, t = C₂ * ((μ ^ (p - 1) + |ℓ₀|) ^ 2
    * (Lc / (T' - T) ^ 2)) * (volume (Metric.ball x₀ R)).toReal := ⟨_, rfl⟩
  have hfinR : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hbnd : ∀ (η : ℝ), 0 < η → η ^ 2 < ε →
      (∫ x in Metric.ball x₀ R, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
          * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
        ≤ Kc := by
    intro η hη hηε
    have hset : volume.restrict (Metric.ball x₀ R ∩ {y | ℓ₀ < pie η (g y k)})
        = volume.restrict (Metric.ball x₀ R) := by
      refine Measure.restrict_congr_set (Filter.eventuallyEq_set.2 ?_)
      have h1 : ∀ᵐ x ∂volume, x ∈ Metric.ball x₀ R →
          |pie η (g x k)| ≤ μ ^ (p - 1) :=
        (ae_restrict_iff' measurableSet_ball).1 (hpiebd η hη)
      filter_upwards [h1] with x hx
      constructor
      · rintro ⟨hxΩ, -⟩
        exact hxΩ
      · intro hxΩ
        refine ⟨hxΩ, ?_⟩
        show ℓ₀ < pie η (g x k)
        have h2 := neg_le_of_abs_le (hx hxΩ)
        rw [hℓ₀def]
        linarith only [h2]
    have heq : (∫ x in Metric.ball x₀ R ∩ {y | ℓ₀ < pie η (g y k)},
          (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
        = ∫ x in Metric.ball x₀ R, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2 := by
      rw [hset]
    have hrhs : (∫ x in Metric.ball x₀ R,
          max (pie η (g x k) - ℓ₀) 0 ^ 2
            * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2))
        ≤ (μ ^ (p - 1) + |ℓ₀|) ^ 2 * (Lc / (T' - T) ^ 2)
          * (volume (Metric.ball x₀ R)).toReal := by
      have hptw : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
          max (pie η (g x k) - ℓ₀) 0 ^ 2
              * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
            ≤ (μ ^ (p - 1) + |ℓ₀|) ^ 2 * (Lc / (T' - T) ^ 2) := by
        filter_upwards [hpiebd η hη] with x hx
        have h1 : max (pie η (g x k) - ℓ₀) 0 ≤ μ ^ (p - 1) + |ℓ₀| := by
          refine max_le ?_ (by positivity)
          have h2 := le_abs_self (pie η (g x k))
          have h3 := neg_abs_le ℓ₀
          linarith only [h2, h3, hx]
        have h4 : (0:ℝ) ≤ max (pie η (g x k) - ℓ₀) 0 := le_max_right _ _
        have h5 : max (pie η (g x k) - ℓ₀) 0 ^ 2 ≤ (μ ^ (p - 1) + |ℓ₀|) ^ 2 :=
          pow_le_pow_left₀ h4 h1 2
        exact mul_le_mul h5 (hζgrad x)
          (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (μ := volume.restrict (Metric.ball x₀ R))
        (f := fun x => max (pie η (g x k) - ℓ₀) 0 ^ 2
          * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2))
        (g := fun _ => (μ ^ (p - 1) + |ℓ₀|) ^ 2 * (Lc / (T' - T) ^ 2))
        (Filter.Eventually.of_forall fun x =>
          mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _))
        (integrable_const _) hptw
      refine le_trans hmono (le_of_eq ?_)
      rw [setIntegral_const, smul_eq_mul, measureReal_def]
      ring
    calc (∫ x in Metric.ball x₀ R, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
        = ∫ x in Metric.ball x₀ R ∩ {y | ℓ₀ < pie η (g y k)},
            (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
              * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2
              * ζ x ^ 2 := heq.symm
      _ ≤ C₂ * (∫ x in Metric.ball x₀ R,
            max (pie η (g x k) - ℓ₀) 0 ^ 2
              * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)) :=
          (hD5 η hη hηε ℓ₀ ζ hζsm hζcs hζtsR).2.1
      _ ≤ Kc := by
          rw [hKcdef, mul_assoc]
          exact mul_le_mul_of_nonneg_left hrhs hC₂0
  -- (D5.4) hence a bound on `‖V_η‖²` over `B_T` that does not depend on `η`
  have hVbnd : ∀ (η : ℝ), 0 < η → η ^ 2 < ε →
      (∫ x in Metric.ball x₀ T,
          ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
        ≤ W2L⁻¹ * Kc := by
    intro η hη hηε
    have hintR := (hD5 η hη hηε ℓ₀ ζ hζsm hζcs hζtsR).1
    have hstep1 : W2L * (∫ x in Metric.ball x₀ T,
          ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
        ≤ ∫ x in Metric.ball x₀ T, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2 := by
      rw [← integral_const_mul]
      refine integral_mono_ae ((hVsqint η hη).const_mul W2L)
        (hintR.mono_set hsubT) ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsubT hwlowW,
        ae_restrict_mem measurableSet_ball] with x hx hxT
      have hζ1 : ζ x = 1 := hζone x (Metric.ball_subset_closedBall hxT)
      rw [hζ1]
      have h1 : (0:ℝ) ≤ ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 :=
        sq_nonneg _
      nlinarith only [hx, h1]
    have hstep2 : (∫ x in Metric.ball x₀ T, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
          * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
        ≤ ∫ x in Metric.ball x₀ R, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2 := by
      refine setIntegral_mono_set hintR ?_
        (Filter.Eventually.of_forall fun x hx => hsubT hx)
      exact Filter.Eventually.of_forall fun x =>
        mul_nonneg (mul_nonneg (Real.rpow_nonneg
          (le_trans hε.le (hwlow x)) _) (sq_nonneg _)) (sq_nonneg _)
    have hchain : W2L * (∫ x in Metric.ball x₀ T,
        ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2) ≤ Kc :=
      le_trans (le_trans hstep1 hstep2) (hbnd η hη hηε)
    rw [← le_div_iff₀' hW2L0] at hchain
    calc (∫ x in Metric.ball x₀ T,
          ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
        ≤ Kc / W2L := hchain
      _ = W2L⁻¹ * Kc := by field_simp
  -- (D5.5) ONE monotone limit, which delivers both `‖V‖ ∈ L²(B_T)` and the
  -- `.tex`'s claim that `Dg^k = 0` almost everywhere on `{g^k = 0}`.  The
  -- family `‖V_η‖²` INCREASES as `η` decreases, so its supremum along `η_j`
  -- is handled by monotone convergence; the uniform bound (D5.4) makes that
  -- supremum finite almost everywhere, and at a point with `g^k = 0` and
  -- `Dg^k ≠ 0` the supremum is `+∞`, because `(η_j)^{p-2} → +∞` for the
  -- negative exponent `p - 2`.  That is reviewer elision (4), obtained here
  -- without the `.tex`'s positive-part/uniqueness argument.
  obtain ⟨hSsum, hDz, hVle⟩ :=
    RegularisedGradientSupremumBound n p ε e0 T W2L Kc g Dg x₀ k ηs hp0 hp2 hexpn
      hbase he00 hηsval hηs0 hηsε hηt hVsqint hVbnd
  -- (D5.6) `MemLp` of the two fields
  have hfinT : IsFiniteMeasure (volume.restrict (Metric.ball x₀ T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hgkT : AEStronglyMeasurable (fun x => g x k)
      (volume.restrict (Metric.ball x₀ T)) :=
    (hgmRi k).mono_measure (Measure.restrict_mono hsubT le_rfl)
  have hDgT : AEStronglyMeasurable (Dg k) (volume.restrict (Metric.ball x₀ T)) :=
    hDgmR.mono_measure (Measure.restrict_mono hsubT le_rfl)
  have hVmeas : AEStronglyMeasurable
      (fun x => (p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x)
      (volume.restrict (Metric.ball x₀ T)) :=
    (((((continuous_abs.comp_aestronglyMeasurable hgkT).aemeasurable).pow_const
      (p / 2 - 1)).const_mul (p / 2)).aestronglyMeasurable).smul hDgT
  have hVsq0 : IntegrableOn
      (fun x => ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
      (Metric.ball x₀ T) volume := by
    refine ⟨hVmeas.norm.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    exact lt_of_le_of_lt
      (le_trans (lintegral_mono fun x => hVle x) hSsum) ENNReal.ofReal_lt_top
  have hrp2 : ∀ a : ℝ, a ^ (2:ℝ) = a ^ 2 := by
    intro a
    rw [show (2:ℝ) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  have hVmem : MemLp (fun x => (p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x)
      (ENNReal.ofReal 2) (volume.restrict (Metric.ball x₀ T)) := by
    refine (integrable_norm_rpow_iff hVmeas (by simp) (by simp)).1 ?_
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp]
    exact hVsq0.congr (Filter.Eventually.of_forall fun x => (hrp2 _).symm)
  have hvmeas : AEStronglyMeasurable (fun x => |g x k| ^ (p / 2 - 1) * g x k)
      (volume.restrict (Metric.ball x₀ T)) :=
    ((((continuous_abs.comp_aestronglyMeasurable hgkT).aemeasurable).pow_const
      (p / 2 - 1)).mul hgkT.aemeasurable).aestronglyMeasurable
  have habsv : ∀ t : ℝ, |(|t| ^ (p / 2 - 1) * t)| ≤ |t| ^ (p / 2) := by
    intro t
    rcases eq_or_ne t 0 with h0 | h0
    · subst h0
      rw [mul_zero, abs_zero]
      exact Real.rpow_nonneg le_rfl _
    · have hta : 0 < |t| := abs_pos.2 h0
      have he : |t| ^ (p / 2) = |t| ^ (p / 2 - 1) * |t| := by
        rw [← Real.rpow_add_one (ne_of_gt hta) (p / 2 - 1)]
        congr 1
        ring
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _), he]
  have hvmem : MemLp (fun x => |g x k| ^ (p / 2 - 1) * g x k)
      (ENNReal.ofReal 2) (volume.restrict (Metric.ball x₀ T)) := by
    refine MemLp.of_bound hvmeas (μ ^ (p / 2)) ?_
    have hbdT : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ T)), |g x k| ≤ μ :=
      ae_restrict_of_ae_restrict_of_subset hsubT (hbd k)
    filter_upwards [hbdT] with x hx
    rw [Real.norm_eq_abs]
    exact le_trans (habsv (g x k))
      (Real.rpow_le_rpow (abs_nonneg _) hx (by linarith only [hp0]))
  -- (D5.7) the closed form of `G_η`, one branch per sign
  have hGeepos : ∀ (η : ℝ), 0 < η → ∀ s : ℝ, 0 ≤ s →
      Gee η s = (s + η) ^ (p / 2) - η ^ (p / 2) := by
    intro η hη s hs
    have hmem : ∀ t ∈ Set.uIcc (0:ℝ) s, 0 ≤ t := by
      intro t ht
      rw [Set.uIcc_of_le hs] at ht
      exact ht.1
    have hcong : (∫ t in (0:ℝ)..s, p / 2 * (|t| + η) ^ (p / 2 - 1))
        = ∫ t in (0:ℝ)..s, p / 2 * (t + η) ^ (p / 2 - 1) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [abs_of_nonneg (hmem t ht)]
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) s,
        HasDerivAt (fun y : ℝ => (y + η) ^ (p / 2))
          (p / 2 * (t + η) ^ (p / 2 - 1)) t := by
      intro t ht
      have hne : t + η ≠ 0 := by
        have := hmem t ht
        linarith only [this, hη]
      have h1 : HasDerivAt (fun y : ℝ => y + η) 1 t := (hasDerivAt_id t).add_const η
      have h2 := h1.rpow_const (p := p / 2) (Or.inl hne)
      simpa using h2
    have hint : IntervalIntegrable
        (fun t : ℝ => p / 2 * (t + η) ^ (p / 2 - 1)) volume 0 s := by
      refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.mul (ContinuousOn.rpow_const ?_ ?_)
      · exact (continuous_id.add continuous_const).continuousOn
      · intro t ht
        exact Or.inl (by have := hmem t ht; linarith only [this, hη])
    have hval : Gee η s = ∫ t in (0:ℝ)..s, p / 2 * (|t| + η) ^ (p / 2 - 1) := by
      simp only [hGeedef]
    rw [hval, hcong, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
      zero_add]
  have hGeeneg : ∀ (η : ℝ), 0 < η → ∀ s : ℝ, s ≤ 0 →
      Gee η s = -((-s + η) ^ (p / 2) - η ^ (p / 2)) := by
    intro η hη s hs
    have hmem : ∀ t ∈ Set.uIcc (0:ℝ) s, t ≤ 0 := by
      intro t ht
      rw [Set.uIcc_of_ge hs] at ht
      exact ht.2
    have hcong : (∫ t in (0:ℝ)..s, p / 2 * (|t| + η) ^ (p / 2 - 1))
        = ∫ t in (0:ℝ)..s, p / 2 * (-t + η) ^ (p / 2 - 1) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [abs_of_nonpos (hmem t ht)]
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) s,
        HasDerivAt (fun y : ℝ => -((-y + η) ^ (p / 2)))
          (p / 2 * (-t + η) ^ (p / 2 - 1)) t := by
      intro t ht
      have hne : -t + η ≠ 0 := by
        have := hmem t ht
        linarith only [this, hη]
      have h1 : HasDerivAt (fun y : ℝ => -y + η) (-1) t :=
        ((hasDerivAt_id t).neg).add_const η
      have h2 := h1.rpow_const (p := p / 2) (Or.inl hne)
      have h3 := h2.neg
      have h4 : p / 2 * (-t + η) ^ (p / 2 - 1)
          = -(-1 * (p / 2) * (-t + η) ^ (p / 2 - 1)) := by ring
      rw [h4]
      exact h3
    have hint : IntervalIntegrable
        (fun t : ℝ => p / 2 * (-t + η) ^ (p / 2 - 1)) volume 0 s := by
      refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.mul (ContinuousOn.rpow_const ?_ ?_)
      · exact ((continuous_id.neg).add continuous_const).continuousOn
      · intro t ht
        exact Or.inl (by have := hmem t ht; linarith only [this, hη])
    have hval : Gee η s = ∫ t in (0:ℝ)..s, p / 2 * (|t| + η) ^ (p / 2 - 1) := by
      simp only [hGeedef]
    rw [hval, hcong, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
      neg_zero, zero_add]
    ring
  -- (D5.8) the pointwise limits `v_η → v` and `V_η → V`
  have hp2pos : (0:ℝ) < p / 2 := by linarith only [hp0]
  have hηsle1 : ∀ j : ℕ, ηs j ≤ 1 := by
    intro j
    have h1 : (1:ℝ) ≤ (j:ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) j; linarith only [this]
    have h2 : e0 ≤ 1 := he0le1
    rw [hηsval j]
    exact le_trans (div_le_self he00.le h1) h2
  have hηpow0 : Filter.Tendsto (fun j : ℕ => (ηs j) ^ (p / 2))
      Filter.atTop (nhds 0) := by
    have hc : ContinuousAt (fun s : ℝ => s ^ (p / 2)) 0 :=
      Real.continuousAt_rpow_const _ _ (Or.inr hp2pos.le)
    have h1 := hc.tendsto.comp hηt
    rw [Real.zero_rpow (ne_of_gt hp2pos)] at h1
    exact h1
  have hvvalp : ∀ t : ℝ, 0 ≤ t → |t| ^ (p / 2 - 1) * t = t ^ (p / 2) := by
    intro t ht
    rcases eq_or_lt_of_le ht with h0 | h0
    · rw [← h0, mul_zero, Real.zero_rpow (ne_of_gt hp2pos)]
    · rw [abs_of_pos h0, ← Real.rpow_add_one (ne_of_gt h0) (p / 2 - 1)]
      congr 1
      ring
  have hvvaln : ∀ t : ℝ, t ≤ 0 → |t| ^ (p / 2 - 1) * t = -((-t) ^ (p / 2)) := by
    intro t ht
    rcases eq_or_lt_of_le ht with h0 | h0
    · rw [h0, mul_zero, neg_zero, Real.zero_rpow (ne_of_gt hp2pos), neg_zero]
    · have hne : (-t) ≠ 0 := ne_of_gt (by linarith only [h0])
      have he : (-t) ^ (p / 2) = (-t) ^ (p / 2 - 1) * (-t) := by
        rw [← Real.rpow_add_one hne (p / 2 - 1)]
        congr 1
        ring
      rw [abs_of_neg h0, he]
      ring
  have hGeelim : ∀ t : ℝ, Filter.Tendsto (fun j : ℕ => Gee (ηs j) t)
      Filter.atTop (nhds (|t| ^ (p / 2 - 1) * t)) := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · have hc : ContinuousAt (fun s : ℝ => s ^ (p / 2)) t :=
        Real.continuousAt_rpow_const _ _ (Or.inr hp2pos.le)
      have h1 : Filter.Tendsto (fun j : ℕ => t + ηs j) Filter.atTop (nhds t) := by
        have h2 := (tendsto_const_nhds (x := t)
          (f := (Filter.atTop : Filter ℕ))).add hηt
        simpa using h2
      have h3 := (hc.tendsto.comp h1).sub hηpow0
      rw [sub_zero, ← hvvalp t ht] at h3
      refine Filter.Tendsto.congr (fun j => ?_) h3
      exact (hGeepos (ηs j) (hηs0 j) t ht).symm
    · have ht' : t ≤ 0 := le_of_lt ht
      have hc : ContinuousAt (fun s : ℝ => s ^ (p / 2)) (-t) :=
        Real.continuousAt_rpow_const _ _ (Or.inr hp2pos.le)
      have h1 : Filter.Tendsto (fun j : ℕ => -t + ηs j) Filter.atTop
          (nhds (-t)) := by
        have h2 := (tendsto_const_nhds (x := -t)
          (f := (Filter.atTop : Filter ℕ))).add hηt
        simpa using h2
      have h3 := ((hc.tendsto.comp h1).sub hηpow0).neg
      rw [sub_zero, ← hvvaln t ht'] at h3
      refine Filter.Tendsto.congr (fun j => ?_) h3
      exact (hGeeneg (ηs j) (hηs0 j) t ht').symm
  have hGeeabs : ∀ (η : ℝ), 0 < η → ∀ s : ℝ, |Gee η s| ≤ (|s| + η) ^ (p / 2) := by
    intro η hη s
    rcases le_or_gt 0 s with hs | hs
    · have hmono : η ^ (p / 2) ≤ (s + η) ^ (p / 2) :=
        Real.rpow_le_rpow hη.le (by linarith only [hs]) hp2pos.le
      rw [hGeepos η hη s hs, abs_of_nonneg (by linarith only [hmono]),
        abs_of_nonneg hs]
      have h0 : (0:ℝ) ≤ η ^ (p / 2) := Real.rpow_nonneg hη.le _
      linarith only [h0]
    · have hs' : s ≤ 0 := le_of_lt hs
      have hmono : η ^ (p / 2) ≤ (-s + η) ^ (p / 2) :=
        Real.rpow_le_rpow hη.le (by linarith only [hs']) hp2pos.le
      rw [hGeeneg η hη s hs', abs_neg,
        abs_of_nonneg (by linarith only [hmono]), abs_of_neg hs]
      have h0 : (0:ℝ) ≤ η ^ (p / 2) := Real.rpow_nonneg hη.le _
      linarith only [h0]
  have hcoordle : ∀ (y : EuclideanSpace ℝ (Fin n)) (i : Fin n), |y i| ≤ ‖y‖ := by
    intro y i
    have hns : ∑ m, (y m) ^ 2 = ‖y‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq y).symm
    have h1 : (y i) ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [← hns]
      exact Finset.single_le_sum (f := fun m => (y m) ^ 2)
        (fun m _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg _)] at h2
  have hVdom : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ T)), ∀ j : ℕ,
      ‖(p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x‖
        ≤ ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ := by
    filter_upwards [hDz] with x hx j
    rcases eq_or_ne (g x k) 0 with hg0 | hg0
    · rw [hx hg0, smul_zero, smul_zero]
    · have hta : 0 < |g x k| := abs_pos.2 hg0
      have hle : (|g x k| + ηs j) ^ (p / 2 - 1) ≤ |g x k| ^ (p / 2 - 1) :=
        Real.rpow_le_rpow_of_nonpos hta
          (by linarith only [(hηs0 j).le]) hexpn.le
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by linarith only [hp0])
          (Real.rpow_nonneg (by linarith only [hta, (hηs0 j).le]) _)),
        abs_of_nonneg (mul_nonneg (by linarith only [hp0])
          (Real.rpow_nonneg hta.le _))]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hle (by linarith only [hp0])) (norm_nonneg _)
  have hVlim : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ T)), ∀ i : Fin n,
      Filter.Tendsto
        (fun j : ℕ => ((p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x) i)
        Filter.atTop
        (nhds (((p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x) i)) := by
    filter_upwards [hDz] with x hx i
    rcases eq_or_ne (g x k) 0 with hg0 | hg0
    · rw [hx hg0]
      simp only [smul_zero]
      exact tendsto_const_nhds
    · have hc : ContinuousAt (fun s : ℝ => s ^ (p / 2 - 1)) |g x k| :=
        Real.continuousAt_rpow_const _ _ (Or.inl (abs_ne_zero.2 hg0))
      have h1 : Filter.Tendsto (fun j : ℕ => |g x k| + ηs j) Filter.atTop
          (nhds |g x k|) := by
        have h2 := (tendsto_const_nhds (x := |g x k|)
          (f := (Filter.atTop : Filter ℕ))).add hηt
        simpa using h2
      have hsm : ∀ c : ℝ, (c • Dg k x) i = c * Dg k x i := fun c => by simp
      simp only [hsm]
      exact ((hc.tendsto.comp h1).const_mul (p / 2)).mul_const (Dg k x i)
  -- (D5.9) dominated convergence in the identity of (D.2), test function by
  -- test function.  The two dominating functions are the `.tex`'s:
  -- `(2lam+1)^{p/2}|D_iφ|` on the left and `‖V‖|φ|` on the right, the latter
  -- legitimate exactly because of reviewer elision (4) above.
  refine ⟨?_, hvmem, hVmem⟩
  intro φ hφsm hφcs hφts i
  obtain ⟨Lφ, hLφ0, hLφ⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ x, |φ x| ≤ L := by
    obtain ⟨L, hL⟩ := hφcs.exists_bound_of_continuousOn hφsm.continuous.continuousOn
    refine ⟨max L 0, le_max_right _ _, fun x => ?_⟩
    by_cases hx : x ∈ tsupport φ
    · exact le_trans (by simpa using hL x hx) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
      exact le_max_right _ _
  obtain ⟨LDφ, hLDφ0, hLDφ⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ x,
      |fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ))| ≤ L := by
    have hcont : Continuous
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ))) :=
      (hφsm.continuous_fderiv (by simp)).clm_apply continuous_const
    obtain ⟨L, hL⟩ := hφcs.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max L 0, le_max_right _ _, fun x => ?_⟩
    by_cases hx : x ∈ tsupport φ
    · exact le_trans (by simpa using hL x hx) (le_max_left _ _)
    · rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
  have hGm : ∀ j : ℕ, AEStronglyMeasurable
      (fun x => Gee (ηs j) (g x k)
        * fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ)))
      (volume.restrict (Metric.ball x₀ T)) := by
    intro j
    exact (((hGeeC1 (ηs j) (hηs0 j)).continuous).comp_aestronglyMeasurable
      hgkT).mul (((hφsm.continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable)
  have hLlim : Filter.Tendsto (fun j : ℕ => ∫ x in Metric.ball x₀ T,
        Gee (ηs j) (g x k) * fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ)))
      Filter.atTop
      (nhds (∫ x in Metric.ball x₀ T,
        |g x k| ^ (p / 2 - 1) * g x k
          * fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ)))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ => (μ + 1) ^ (p / 2) * LDφ) hGm (integrable_const _) ?_ ?_
    · intro j
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsubT (hbd k)] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |Gee (ηs j) (g x k)| ≤ (μ + 1) ^ (p / 2) := by
        refine le_trans (hGeeabs (ηs j) (hηs0 j) (g x k)) ?_
        refine Real.rpow_le_rpow ?_ ?_ hp2pos.le
        · linarith only [abs_nonneg (g x k), (hηs0 j).le]
        · linarith only [hx, hηsle1 j]
      exact mul_le_mul h1 (hLDφ x) (abs_nonneg _)
        (Real.rpow_nonneg (by linarith only [hμ]) _)
    · filter_upwards with x
      exact (hGeelim (g x k)).mul_const _
  have hVint1 : Integrable (fun x => (p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x)
      (volume.restrict (Metric.ball x₀ T)) :=
    memLp_one_iff_integrable.1 (hVmem.mono_exponent (by
      rw [show (1:ENNReal) = ENNReal.ofReal 1 from by simp]
      exact ENNReal.ofReal_le_ofReal (by norm_num)))
  have hRlim : Filter.Tendsto (fun j : ℕ => ∫ x in Metric.ball x₀ T,
        ((p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x) i * φ x)
      Filter.atTop
      (nhds (∫ x in Metric.ball x₀ T,
        ((p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x) i * φ x)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ * Lφ) ?_
      (hVint1.norm.mul_const Lφ) ?_ ?_
    · intro j
      have h1 := (hveeW (ηs j) (hηs0 j) T hT0 hTR).2.2.1
      exact (((EuclideanSpace.proj (𝕜 := ℝ) i).continuous).comp_aestronglyMeasurable
        h1).mul (hφsm.continuous.aestronglyMeasurable)
    · intro j
      filter_upwards [hVdom] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (le_trans (hcoordle _ i) (hx j)) (hLφ x)
        (abs_nonneg _) (norm_nonneg _)
    · filter_upwards [hVlim] with x hx
      exact (hx i).mul_const _
  have hid : ∀ j : ℕ, (∫ x in Metric.ball x₀ T,
        Gee (ηs j) (g x k) * fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ)))
      = -∫ x in Metric.ball x₀ T,
        ((p / 2 * (|g x k| + ηs j) ^ (p / 2 - 1)) • Dg k x) i * φ x := fun j =>
    (hveeW (ηs j) (hηs0 j) T hT0 hTR).1 φ hφsm hφcs hφts i
  exact tendsto_nhds_unique hLlim
    (Filter.Tendsto.congr (fun j => (hid j).symm) hRlim.neg)
