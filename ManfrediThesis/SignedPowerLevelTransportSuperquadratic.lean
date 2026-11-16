import ManfrediThesis.Preamble
set_option maxHeartbeats 800000
open MeasureTheory

/-- The common core of the two sides of the level transport for `p ≥ 2`: a
weighted Caccioppoli bound on `B_R(x₀) ∩ S` for the energy of `Dg^k` is
transported into the un-weighted bound
\[
∫_{B_{ρ₀}∩S}\bigl\|(\tfrac p2|g^k|^{\frac p2-1})Dg^k\bigr\|^2
  \ \le\ \max\{1,C_a\}\frac{(λ^{p/2})^2}{(σρ)^2}\bigl|B_ρ∩S\bigr| .
\]

Conventions, restated here because a helper inherits none of its parent's.
`supp ζ` means `tsupport ζ`, the CLOSED support, and `|∇ζ|²` abbreviates
`∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i 1))²`; `g` plays the role of `∇u`
and `Dg k` of `∇D_ku`; `λ = μ/2` is the level parameter and `ρ - ρ₀ = σρ` the
width of the annulus.  Every power of a nonnegative real is the real power,
written exactly as the structure conditions print the weight
`(ε + ‖g‖²)^{p/2-1}`, per pm-0024(1).  The constant is carried in its current
form, `C_a = \tfrac94p^2c₄(1 + 4n)^{\frac p2-1}L` with `L` the absolute
constant of \noderef{StandardRadialCutoff}; no `Λ` appears, since the inline
cut-off this node once built has been replaced by that node.  `W_2` is the
uniform UPPER bound for the weight on `B_R(x₀)`, which is the direction
`p ≥ 2` gives --- the subquadratic twin uses a lower bound instead.

The statement is deliberately abstract in the pair `(S, d)`: `S` is a level set
and `d` the corresponding truncation, and the two consumers --- the `+` side
and the `−` side --- differ only in which pair they supply.  The four
hypotheses on `(S, d)` are the Caccioppoli bound with constant `c₄`, the
nonnegativity of `d`, its uniform bound `d ≤ 3λ` almost everywhere on
`B_R(x₀)`, and its vanishing off `S`.

The route.  Since `ζ = 1` on `\overline{B_{ρ₀}(x₀)}` and the integrand is
nonnegative, the left-hand side is at most the same integral over
`B_R(x₀) ∩ S` with `ζ²` inserted; rewriting the norm pointwise as
`\tfrac{p^2}4|g^k|^{p-2}\|Dg^k\|^2` and bounding `|g^k|^{p-2}` by the weight
`(ε + ‖g‖²)^{p/2-1}` --- which is where `p ≥ 2` enters --- turns it into the
weighted energy the Caccioppoli hypothesis controls.  That hypothesis bounds it
by `c₄∫_{B_R}(ε + ‖g‖²)^{p/2-1}d^2|∇ζ|^2`, and on that integral `d` vanishes
off `S` while `∇ζ` vanishes off `supp ζ ⊆ B_ρ`, so the domain cuts down to
`B_ρ ∩ S`; there the weight is at most `W_2`, `d^2 ≤ 9λ^2` and
`|∇ζ|^2 ≤ L/(σρ)^2`, giving `c₄W_2·9λ^2·L(σρ)^{-2}|B_ρ∩S|`.  Collecting the
constants with `W_2 = (1 + 4n)^{\frac p2-1}λ^{p-2}` and the two power
identities `λ^{p-2}λ^2 = λ^{p} = (λ^{p/2})^2` gives exactly
`C_a(λ^{p/2})^2(σρ)^{-2}|B_ρ∩S|`, and `C_a ≤ \max\{1,C_a\}` finishes.  The
degenerate case in which the left-hand integrand is not integrable is handled
separately: there the integral is `0` by convention and the right-hand side is
nonnegative. -/
theorem SignedPowerLevelTransportSuperquadratic :
    ∀ (n : ℕ) (p L c₄ Ca ε lam ρ σ ρ₀ W2 R : ℝ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (k : Fin n) (ζ : EuclideanSpace ℝ (Fin n) → ℝ)
      (x₀ : EuclideanSpace ℝ (Fin n)),
      0 < c₄ → 0 < ε → 0 < lam → 0 < L → 0 < ρ → 0 < σ →
      Ca = 9 * p ^ 2 / 4 * c₄ * (1 + 4 * (n:ℝ)) ^ (p / 2 - 1) * L →
      (∀ x : EuclideanSpace ℝ (Fin n), ε ≤ ε + ‖g x‖ ^ 2) →
      (∀ x : EuclideanSpace ℝ (Fin n),
        ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2
          = p ^ 2 / 4 * |g x k| ^ (p - 2) * ‖Dg k x‖ ^ 2) →
      (∀ x : EuclideanSpace ℝ (Fin n),
        |g x k| ^ (p - 2) ≤ (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)) →
      ρ ≤ R → ρ₀ < ρ → ρ - ρ₀ = σ * ρ →
      tsupport ζ ⊆ Metric.ball x₀ ρ →
      (∀ x ∈ Metric.closedBall x₀ ρ₀, ζ x = 1) →
      (∀ x, ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2
        ≤ L / (ρ - ρ₀) ^ 2) →
      (∀ x, x ∉ tsupport ζ →
        ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 = 0) →
      0 < W2 →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
        (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) ≤ W2) →
      (∀ S : Set (EuclideanSpace ℝ (Fin n)),
        IntegrableOn (fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2
          * ζ x ^ 2) S volume) →
      W2 = (1 + 4 * (n:ℝ)) ^ (p / 2 - 1) * lam ^ (p - 2) →
      (lam ^ (p / 2)) ^ 2 = lam ^ p →
      lam ^ (p - 2) * lam ^ 2 = lam ^ p →
      (0:ℝ) < (σ * ρ) ^ 2 →
      Ca ≤ max 1 Ca →
      (∀ S : Set (EuclideanSpace ℝ (Fin n)),
        (0:ℝ) ≤ max 1 Ca * (lam ^ (p / 2)) ^ 2 / (σ * ρ) ^ 2
          * (volume (Metric.ball x₀ ρ ∩ S)).toReal) →
      ∀ (S : Set (EuclideanSpace ℝ (Fin n)))
        (d : EuclideanSpace ℝ (Fin n) → ℝ),
        (∫ x in Metric.ball x₀ R ∩ S,
            (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
          ≤ c₄ * ∫ x in Metric.ball x₀ R, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * d x ^ 2
            * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 →
        (∀ x, 0 ≤ d x) →
        (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), d x ≤ 3 * lam) →
        (∀ x, x ∉ S → d x = 0) →
        (∫ x in Metric.ball x₀ ρ₀ ∩ S,
            ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
          ≤ max 1 Ca * (lam ^ (p / 2)) ^ 2 / (σ * ρ) ^ 2
            * (volume (Metric.ball x₀ ρ ∩ S)).toReal := by
  intro n p L c₄ Ca ε lam ρ σ ρ₀ W2 R g Dg k ζ x₀ hc₄0 hε hlam0 hL0 hρ hσ hCadef
    hwlow hVnorm hwge hρR hρ₀ρ hdρ hζts hζone hζgrad hDz0 hW20 hwpow hintB hW2val
    hlampow hlamsplit hsq0 hCale hcommon
  intro S d hcac hd0 hdbd hdoff
  obtain ⟨Kc, hKcdef⟩ : ∃ t : ℝ,
    t = W2 * (3 * lam) ^ 2 * (L / (σ * ρ) ^ 2) := ⟨_, rfl⟩
  have hKc0 : (0:ℝ) ≤ Kc := by
    rw [hKcdef]
    exact mul_nonneg (mul_nonneg hW20.le (sq_nonneg _)) (by positivity)
  -- the right-hand integral
  have hB : (∫ x in Metric.ball x₀ R, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * d x ^ 2
        * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
      ≤ Kc * (volume (Metric.ball x₀ ρ ∩ S)).toReal := by
    by_cases hint : IntegrableOn (fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * d x ^ 2
        * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
        (Metric.ball x₀ R) volume
    · obtain ⟨T, hTm, hTsub, hTvol⟩ : ∃ T : Set (EuclideanSpace ℝ (Fin n)),
          MeasurableSet T ∧ Metric.ball x₀ ρ ∩ S ⊆ T ∧
          volume T = volume (Metric.ball x₀ ρ ∩ S) :=
        ⟨toMeasurable volume _, measurableSet_toMeasurable _ _,
          subset_toMeasurable _ _, measure_toMeasurable _⟩
      have hindT : IntegrableOn (fun x => Kc * T.indicator (fun _ => (1:ℝ)) x)
          (Metric.ball x₀ R) volume := by
        refine Integrable.const_mul ?_ Kc
        have hfin : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
        refine Integrable.mono' (g := fun _ => (1:ℝ)) (integrable_const _)
          ((measurable_const.indicator hTm).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun x => ?_)
        by_cases hb : x ∈ T
        · rw [Set.indicator_of_mem hb]; simp
        · rw [Set.indicator_of_notMem hb]; simp
      have hptw : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
          (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * d x ^ 2
              * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2
            ≤ Kc * T.indicator (fun _ => (1:ℝ)) x := by
        filter_upwards [hwpow, hdbd] with x hw hdx
        have hDnn : (0:ℝ) ≤ ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 :=
          Finset.sum_nonneg fun i _ => sq_nonneg _
        have hIT0 : (0:ℝ) ≤ Kc * T.indicator (fun _ => (1:ℝ)) x :=
          mul_nonneg hKc0 (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
        by_cases hb : x ∈ Metric.ball x₀ ρ
        · by_cases hs : x ∈ S
          · rw [Set.indicator_of_mem (hTsub ⟨hb, hs⟩), mul_one, hKcdef]
            have hD : ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2
                ≤ L / (σ * ρ) ^ 2 := by
              have hgr := hζgrad x
              rwa [hdρ] at hgr
            have hd2 : d x ^ 2 ≤ (3 * lam) ^ 2 := pow_le_pow_left₀ (hd0 x) hdx 2
            exact mul_le_mul (mul_le_mul hw hd2 (sq_nonneg _) hW20.le) hD
              hDnn (mul_nonneg hW20.le (sq_nonneg _))
          · rw [hdoff x hs, show (0:ℝ) ^ 2 = 0 from by ring, mul_zero, zero_mul]
            exact hIT0
        · have hxt : x ∉ tsupport ζ := fun hc => hb (hζts hc)
          rw [hDz0 x hxt, mul_zero]
          exact hIT0
      refine le_trans (setIntegral_mono_ae_restrict hint hindT hptw) ?_
      rw [integral_const_mul, setIntegral_indicator hTm, setIntegral_const,
        MeasureTheory.measureReal_def, smul_eq_mul, mul_one]
      refine mul_le_mul_of_nonneg_left ?_ hKc0
      refine ENNReal.toReal_mono ?_ ?_
      · exact (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
          measure_ball_lt_top).ne
      · rw [← hTvol]
        exact measure_mono Set.inter_subset_right
    · rw [integral_undef hint]
      exact mul_nonneg hKc0 ENNReal.toReal_nonneg
  -- the left-hand side
  by_cases hVint : IntegrableOn
      (fun x => ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
      (Metric.ball x₀ ρ₀ ∩ S) volume
  · have hsub0 : Metric.ball x₀ ρ₀ ∩ S ⊆ Metric.ball x₀ R ∩ S := fun y hy =>
      ⟨Metric.ball_subset_ball (le_trans hρ₀ρ.le hρR) hy.1, hy.2⟩
    have hmem0 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ₀ ∩ S)),
        x ∈ Metric.ball x₀ ρ₀ :=
      (ae_restrict_mem Metric.isOpen_ball.measurableSet).filter_mono
        (ae_mono (Measure.restrict_mono Set.inter_subset_left le_rfl))
    have hstep1 : (∫ x in Metric.ball x₀ ρ₀ ∩ S,
          ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
        ≤ ∫ x in Metric.ball x₀ ρ₀ ∩ S, p ^ 2 / 4 *
            ((ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2) := by
      refine integral_mono_ae hVint ((hintB _).const_mul _) ?_
      filter_upwards [hmem0] with x hx
      rw [hVnorm x, hζone x (Metric.ball_subset_closedBall hx)]
      have hfac : (0:ℝ) ≤ p ^ 2 / 4 * ‖Dg k x‖ ^ 2 := by positivity
      calc p ^ 2 / 4 * |g x k| ^ (p - 2) * ‖Dg k x‖ ^ 2
          = p ^ 2 / 4 * ‖Dg k x‖ ^ 2 * |g x k| ^ (p - 2) := by ring
        _ ≤ p ^ 2 / 4 * ‖Dg k x‖ ^ 2 * (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) :=
            mul_le_mul_of_nonneg_left (hwge x) hfac
        _ = p ^ 2 / 4 * ((ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * 1 ^ 2) := by
            ring
    have hstep2 : (∫ x in Metric.ball x₀ ρ₀ ∩ S, p ^ 2 / 4 *
          ((ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2))
        ≤ ∫ x in Metric.ball x₀ R ∩ S, p ^ 2 / 4 *
            ((ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2) := by
      refine setIntegral_mono_set ((hintB _).const_mul _)
        (Filter.Eventually.of_forall fun x => ?_)
        (Filter.Eventually.of_forall fun x hx => hsub0 hx)
      have h1 : (0:ℝ) ≤ (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) :=
        Real.rpow_nonneg (le_trans hε.le (hwlow x)) _
      have : (0:ℝ) ≤ (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2 :=
        mul_nonneg (mul_nonneg h1 (sq_nonneg _)) (sq_nonneg _)
      positivity
    have hconst : p ^ 2 / 4 * (c₄ * Kc) = Ca * lam ^ p / (σ * ρ) ^ 2 := by
      rw [hKcdef, hW2val, hCadef, ← hlamsplit]
      field_simp
      ring
    calc (∫ x in Metric.ball x₀ ρ₀ ∩ S,
          ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
        ≤ ∫ x in Metric.ball x₀ R ∩ S, p ^ 2 / 4 *
            ((ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2) :=
          le_trans hstep1 hstep2
      _ = p ^ 2 / 4 * ∫ x in Metric.ball x₀ R ∩ S,
            (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2 :=
          integral_const_mul _ _
      _ ≤ p ^ 2 / 4 * (c₄ * ∫ x in Metric.ball x₀ R,
            (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * d x ^ 2
              * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2) :=
          mul_le_mul_of_nonneg_left hcac (by positivity)
      _ ≤ p ^ 2 / 4 * (c₄ * (Kc * (volume (Metric.ball x₀ ρ ∩ S)).toReal)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hB hc₄0.le) (by positivity)
      _ = (p ^ 2 / 4 * (c₄ * Kc)) * (volume (Metric.ball x₀ ρ ∩ S)).toReal := by
          ring
      _ = (Ca * lam ^ p / (σ * ρ) ^ 2) * (volume (Metric.ball x₀ ρ ∩ S)).toReal := by
          rw [hconst]
      _ ≤ (max 1 Ca * (lam ^ (p / 2)) ^ 2 / (σ * ρ) ^ 2)
            * (volume (Metric.ball x₀ ρ ∩ S)).toReal := by
          refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
          rw [hlampow, div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCale (Real.rpow_nonneg hlam0.le p))
            (le_of_lt (inv_pos.2 hsq0))
  · rw [integral_undef hVint]
    exact hcommon S
