import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.MemW1pOn
set_option maxHeartbeats 1600000
open MeasureTheory

/-- The dual norms of the mollification error tend to zero: with
`e_m = 1/(m+1)` and `p' = p/(p-1)`,
`δ_m = \bigl(∫_{B_R(x₀)}‖A(g) - A_{e_m}(g)‖^{p'}\bigr)^{1/p'}\longrightarrow0`.

Conventions, restated here because a helper inherits none of its parent's.
`ρ` is the mollifying kernel: nonnegative, of unit mass, supported in the
closed unit ball, and such that `ρ·f` and `ρ•F` are integrable for continuous
scalar and vector fields; `supp ρ` means the CLOSED support, which is where the
bound `‖z‖ ≤ 1` is assumed.  For `e > 0` the mollified field is
`A_e(h) = ∫ρ(z)A(h + √e z)dz − ∫ρ(z)A(√e z)dz`, written exactly as the
hypothesis prints it; per pm-0020 this mollification, and not the perturbation
`A(h) + e^{p/2-1}h`, is the approximating family.  Every power of a nonnegative
real is the real power, so the growth bound `‖A h‖ ≤ Γ(1 + ‖h‖²)^{(p-1)/2}` and
the exponent `p'` are as printed.  `δ` is carried as a plain sequence `ℕ → ℝ`
with its defining equation as a hypothesis.

The route is Step 4 of the parent's manuscript argument.  Pointwise in `x`,
`A_{e_m}(g(x)) → A(g(x))` as `m → ∞`: writing the two integrals out,
`A_{e_m}(h) - A(h) = ∫ρ(z)\bigl(A(h + \sqrt{e_m}z) - A(h)\bigr)dz
  - ∫ρ(z)\bigl(A(\sqrt{e_m}z) - A(0)\bigr)dz`,
using `∫ρ = 1` and `A(0) = 0`; on `supp ρ` one has `‖z‖ ≤ 1`, so both
arguments converge to `h` and to `0` uniformly in `z` as `\sqrt{e_m} → 0`, and
`A` is continuous, so each integrand tends to `0` and is dominated by a
constant multiple of `ρ`, whence both integrals vanish in the limit.  Then the
integrands `‖A(g) - A_{e_m}(g)‖^{p'}` tend to `0` pointwise and are dominated,
uniformly in `m`, by the `m`-free majorant `(2Γ)^{p'}(1 + ‖g‖²)^{p/2}`, which
is integrable on `B_R(x₀)` because `g ∈ L^p(B_R(x₀))`: that is the growth
bound applied to `A` and to each `A_{e_m}` separately, the triangle inequality,
and `(1 + ‖g‖²)^{p/2} ≤ 2^{p/2}(1 + ‖g‖^p)`.  Dominated convergence (Preamble)
then gives `∫‖A(g) - A_{e_m}(g)‖^{p'} → 0`, and raising to the continuous power
`1/p' = (p-1)/p`, which vanishes at `0`, gives `δ_m → 0`. -/
theorem MollifiedFieldDualNormTendstoZero :
    ∀ (n : ℕ) (p : ℝ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ z, 0 ≤ ρ z) → (∫ z, ρ z) = 1 →
      (∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Continuous f →
        Integrable (fun z => ρ z * f z) volume) →
      (∀ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), Continuous F →
        Integrable (fun z => ρ z • F z) volume) →
      (∀ z ∈ tsupport ρ, ‖z‖ ≤ 1) →
      ∀ (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        A 0 = 0 → Continuous A →
      ∀ (Ae : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        (∀ e h, Ae e h = (∫ z, ρ z • A (h + Real.sqrt e • z))
            - ∫ z, ρ z • A (Real.sqrt e • z)) →
      ∀ (r' : ℝ),
        (∀ e : ℝ, 0 < e → e ≤ 1 →
          ∃ γ₀' γ₁' : ℝ, 0 < γ₀' ∧ γ₁' ≤ r' * γ₀' ∧
            EllipticStructureQ12 n p e γ₀' γ₁' Set.univ (fun _ _ h => Ae e h)) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (Γ : ℝ)
        (δ : ℕ → ℝ),
        MemW1pOn n p (Metric.ball x₀ R) u g →
        0 < Γ →
        (∀ h : EuclideanSpace ℝ (Fin n),
          ‖A h‖ ≤ Γ * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2)) →
        (∀ e : ℝ, 0 < e → e ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin n),
          ‖Ae e h‖ ≤ Γ * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2)) →
        (0:ℝ) < (p - 1) / 2 →
        (∀ m : ℕ, (0 : ℝ) < 1 / ((m : ℝ) + 1)) →
        (∀ m : ℕ, (1 : ℝ) / ((m : ℝ) + 1) ≤ 1) →
        (0:ℝ) < p →
        δ = (fun m : ℕ =>
          (∫ x in Metric.ball x₀ R,
            ‖A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x)‖ ^ (p / (p - 1)))
              ^ ((p - 1) / p)) →
        Filter.Tendsto δ Filter.atTop (nhds 0) := by
  intro n p ρ hρ0 hρint hρfint hρFint hsuppz A hA0 hAcont Ae hAeeq r' hAeQ x₀ R u
    g Γ δ hu hΓ0 hΓA hΓAe hq'0 hem0 hem1 hp0 hδdef
  have hp10 : (0:ℝ) < p - 1 := by linarith
  have hp'0 : (0:ℝ) < p / (p - 1) := by positivity
  have hemto : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1))
      Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsqto : Filter.Tendsto (fun m : ℕ => Real.sqrt (1 / ((m : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto (0:ℝ)).comp hemto
    rw [Real.sqrt_zero] at h
    exact h.congr fun m => rfl
  have hsq1 : ∀ m : ℕ, Real.sqrt (1 / ((m : ℝ) + 1)) ≤ 1 := by
    intro m
    have h := Real.sqrt_le_sqrt (hem1 m)
    rwa [Real.sqrt_one] at h
  have hsq0 : ∀ m : ℕ, 0 ≤ Real.sqrt (1 / ((m : ℝ) + 1)) := fun m => Real.sqrt_nonneg _
  -- the mollified fields converge pointwise to `A`
  have hAeconv : ∀ h : EuclideanSpace ℝ (Fin n),
      Filter.Tendsto (fun m : ℕ => Ae (1 / ((m : ℝ) + 1)) h)
        Filter.atTop (nhds (A h)) := by
    intro h
    have hshift : ∀ (c : EuclideanSpace ℝ (Fin n)),
        Filter.Tendsto
          (fun m : ℕ => ∫ z, ρ z • A (c + Real.sqrt (1 / ((m : ℝ) + 1)) • z))
          Filter.atTop (nhds (A c)) := by
      intro c
      have hbd0 : (0:ℝ) ≤ Γ * (1 + (‖c‖ + 1) ^ 2) ^ ((p - 1) / 2) := by positivity
      have hlim : Filter.Tendsto
          (fun m : ℕ => ∫ z, ρ z • A (c + Real.sqrt (1 / ((m : ℝ) + 1)) • z))
          Filter.atTop (nhds (∫ z, ρ z • A c)) := by
        refine tendsto_integral_of_dominated_convergence
          (fun z => ρ z * (Γ * (1 + (‖c‖ + 1) ^ 2) ^ ((p - 1) / 2))) ?_ ?_ ?_ ?_
        · intro m
          exact (hρFint _ (hAcont.comp
            (continuous_const.add (continuous_const_smul _)))).aestronglyMeasurable
        · exact hρfint _ continuous_const
        · intro m
          refine Filter.Eventually.of_forall fun z => ?_
          show ‖ρ z • A (c + Real.sqrt (1 / ((m : ℝ) + 1)) • z)‖ ≤ _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ0 z)]
          by_cases hz : z ∈ tsupport ρ
          · refine mul_le_mul_of_nonneg_left ?_ (hρ0 z)
            have hzn := hsuppz z hz
            have h1 : ‖(Real.sqrt (1 / ((m : ℝ) + 1)) • z :
                EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hsq0 m)]
              nlinarith [norm_nonneg z, hsq0 m, hsq1 m]
            have h2 : ‖c + Real.sqrt (1 / ((m : ℝ) + 1)) • z‖ ≤ ‖c‖ + 1 :=
              le_trans (norm_add_le _ _) (by linarith)
            refine le_trans (hΓA _) (mul_le_mul_of_nonneg_left ?_ hΓ0.le)
            refine Real.rpow_le_rpow (by positivity) ?_ hq'0.le
            nlinarith [norm_nonneg (c + Real.sqrt (1 / ((m : ℝ) + 1)) • z),
              norm_nonneg c]
          · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, zero_mul]
        · refine Filter.Eventually.of_forall fun z => ?_
          have h1 : Filter.Tendsto
              (fun m : ℕ => c + Real.sqrt (1 / ((m : ℝ) + 1)) • z)
              Filter.atTop (nhds c) := by
            have h2 : Filter.Tendsto
                (fun m : ℕ => Real.sqrt (1 / ((m : ℝ) + 1)) • z)
                Filter.atTop (nhds ((0:ℝ) • z)) := hsqto.smul_const z
            rw [zero_smul] at h2
            simpa using Filter.Tendsto.const_add c h2
          exact ((hAcont.tendsto c).comp h1).const_smul (ρ z)
      have hval : (∫ z, ρ z • A c) = A c := by
        rw [integral_smul_const, hρint, one_smul]
      rwa [hval] at hlim
    have hz0 : Filter.Tendsto
        (fun m : ℕ => ∫ z, ρ z • A (Real.sqrt (1 / ((m : ℝ) + 1)) • z))
        Filter.atTop (nhds 0) := by
      have h := hshift 0
      rw [hA0] at h
      refine h.congr fun m => ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show ρ z • A (0 + Real.sqrt (1 / ((m : ℝ) + 1)) • z)
        = ρ z • A (Real.sqrt (1 / ((m : ℝ) + 1)) • z)
      rw [zero_add]
    have hmain := (hshift h).sub hz0
    rw [sub_zero] at hmain
    refine hmain.congr fun m => ?_
    exact (hAeeq _ _).symm
  -- the integrand tends to zero pointwise and is dominated
  have hpow : ∀ t : ℝ, 0 ≤ t →
      (Γ * (1 + t) ^ ((p - 1) / 2) + Γ * (1 + t) ^ ((p - 1) / 2))
          ^ (p / (p - 1))
        = (2 * Γ) ^ (p / (p - 1)) * (1 + t) ^ (p / 2) := by
    intro t ht
    rw [show Γ * (1 + t) ^ ((p - 1) / 2) + Γ * (1 + t) ^ ((p - 1) / 2)
        = (2 * Γ) * (1 + t) ^ ((p - 1) / 2) by ring,
      Real.mul_rpow (by positivity) (Real.rpow_nonneg (by linarith) _),
      ← Real.rpow_mul (by linarith)]
    congr 2
    field_simp
  have hdom : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin n)),
      ‖A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x)‖ ^ (p / (p - 1))
        ≤ (2 * Γ) ^ (p / (p - 1)) * (1 + ‖g x‖ ^ 2) ^ (p / 2) := by
    intro m x
    have h1 : ‖A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x)‖
        ≤ Γ * (1 + ‖g x‖ ^ 2) ^ ((p - 1) / 2)
          + Γ * (1 + ‖g x‖ ^ 2) ^ ((p - 1) / 2) :=
      le_trans (norm_sub_le _ _)
        (add_le_add (hΓA _) (hΓAe _ (hem0 m) (hem1 m) _))
    refine le_trans (Real.rpow_le_rpow (norm_nonneg _) h1 hp'0.le) ?_
    exact le_of_eq (hpow _ (sq_nonneg ‖g x‖))
  -- the majorant is integrable on the ball
  have hgas : AEStronglyMeasurable g (volume.restrict (Metric.ball x₀ R)) :=
    hu.2.2.aestronglyMeasurable
  have hAecont : ∀ m : ℕ, Continuous (Ae (1 / ((m : ℝ) + 1))) := by
    intro m
    obtain ⟨γ₀', γ₁', -, -, hQe⟩ := hAeQ _ (hem0 m) (hem1 m)
    exact hQe.hcont 0 (Set.mem_univ 0) 0
  have hFmeas : ∀ m : ℕ, AEStronglyMeasurable
      (fun x => ‖A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x)‖ ^ (p / (p - 1)))
      (volume.restrict (Metric.ball x₀ R)) := by
    intro m
    have hc : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        ‖A y - Ae (1 / ((m : ℝ) + 1)) y‖ ^ (p / (p - 1))) :=
      ((hAcont.sub (hAecont m)).norm).rpow_const (fun y => Or.inr hp'0.le)
    exact hc.comp_aestronglyMeasurable hgas
  have hfinm : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  have hpne : (ENNReal.ofReal p) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hp0]
  have hptop : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hgp : Integrable (fun x => ‖g x‖ ^ p)
      (volume.restrict (Metric.ball x₀ R)) := by
    have h := hu.2.2.integrable_norm_rpow hpne hptop
    rwa [ENNReal.toReal_ofReal hp0.le] at h
  have h2p : (0:ℝ) < (2:ℝ) ^ (p / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hpowbd : ∀ t : ℝ, 0 ≤ t →
      (1 + t ^ 2) ^ (p / 2) ≤ (2:ℝ) ^ (p / 2) * (1 + t ^ p) := by
    intro t ht
    have hpow2 : ((t ^ 2 : ℝ)) ^ (p / 2) = t ^ p := by
      have ht2 : (t ^ 2 : ℝ) = t ^ (2:ℝ) := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      rw [ht2, ← Real.rpow_mul ht]
      congr 1
      ring
    have htp : (0:ℝ) ≤ t ^ p := Real.rpow_nonneg ht _
    rcases le_total t 1 with h | h
    · have h1 : (1 + t ^ 2 : ℝ) ≤ 2 := by nlinarith
      have h2 : (1 + t ^ 2 : ℝ) ^ (p / 2) ≤ (2:ℝ) ^ (p / 2) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
      have h3 : (0:ℝ) ≤ (2:ℝ) ^ (p / 2) * t ^ p := mul_nonneg h2p.le htp
      linarith [h2, h3]
    · have h1 : (1 + t ^ 2 : ℝ) ≤ 2 * t ^ 2 := by nlinarith
      have h2 : (1 + t ^ 2 : ℝ) ^ (p / 2) ≤ (2 * t ^ 2) ^ (p / 2) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
      rw [Real.mul_rpow (by norm_num) (by positivity), hpow2] at h2
      linarith [h2, h2p]
  have hmaj : Integrable (fun x => (2 * Γ) ^ (p / (p - 1))
      * (1 + ‖g x‖ ^ 2) ^ (p / 2)) (volume.restrict (Metric.ball x₀ R)) := by
    have hbig : Integrable (fun x => (2 * Γ) ^ (p / (p - 1))
        * ((2:ℝ) ^ (p / 2) * (1 + ‖g x‖ ^ p)))
        (volume.restrict (Metric.ball x₀ R)) :=
      (((integrable_const (1:ℝ)).add hgp).const_mul _).const_mul _
    refine hbig.mono' ?_ ?_
    · have hc : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
          (2 * Γ) ^ (p / (p - 1)) * (1 + ‖y‖ ^ 2) ^ (p / 2)) :=
        continuous_const.mul (((continuous_const.add
          (continuous_norm.pow 2))).rpow_const (fun y => Or.inr (by positivity)))
      exact hc.comp_aestronglyMeasurable hgas
    · refine Filter.Eventually.of_forall fun x => ?_
      have hc0 : (0:ℝ) ≤ (2 * Γ) ^ (p / (p - 1)) :=
        Real.rpow_nonneg (by positivity) _
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg hc0 (Real.rpow_nonneg (by positivity) _))]
      exact mul_le_mul_of_nonneg_left (hpowbd _ (norm_nonneg _)) hc0
  -- dominated convergence on the ball
  have hbnd : ∀ m : ℕ, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      ‖‖A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x)‖ ^ (p / (p - 1))‖
        ≤ (2 * Γ) ^ (p / (p - 1)) * (1 + ‖g x‖ ^ 2) ^ (p / 2) := by
    intro m
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hdom m x
  have hlim : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      Filter.Tendsto
        (fun m : ℕ => ‖A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x)‖ ^ (p / (p - 1)))
        Filter.atTop (nhds 0) := by
    refine Filter.Eventually.of_forall fun x => ?_
    have h1 : Filter.Tendsto
        (fun m : ℕ => ‖A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x)‖)
        Filter.atTop (nhds 0) := by
      have h2 := (hAeconv (g x)).const_sub (A (g x))
      rw [sub_self] at h2
      have h3 := (continuous_norm.tendsto
        (0 : EuclideanSpace ℝ (Fin n))).comp h2
      rw [norm_zero] at h3
      exact h3.congr fun m => rfl
    have h4 : Filter.Tendsto (fun t : ℝ => t ^ (p / (p - 1)))
        (nhds 0) (nhds ((0:ℝ) ^ (p / (p - 1)))) :=
      (Real.continuousAt_rpow_const (0:ℝ) _ (Or.inr hp'0.le)).tendsto
    rw [Real.zero_rpow (ne_of_gt hp'0)] at h4
    exact (h4.comp h1).congr fun m => rfl
  have hdct : Filter.Tendsto (fun m : ℕ => ∫ x in Metric.ball x₀ R,
      ‖A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x)‖ ^ (p / (p - 1)))
      Filter.atTop (nhds 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (fun x => (2 * Γ) ^ (p / (p - 1)) * (1 + ‖g x‖ ^ 2) ^ (p / 2))
      hFmeas hmaj hbnd hlim
    simpa using h
  have hqq : (0:ℝ) < (p - 1) / p := div_pos hp10 hp0
  have hcc : Filter.Tendsto (fun t : ℝ => t ^ ((p - 1) / p))
      (nhds 0) (nhds ((0:ℝ) ^ ((p - 1) / p))) :=
    (Real.continuousAt_rpow_const (0:ℝ) _ (Or.inr hqq.le)).tendsto
  rw [Real.zero_rpow (ne_of_gt hqq)] at hcc
  rw [hδdef]
  exact (hcc.comp hdct).congr fun m => rfl
