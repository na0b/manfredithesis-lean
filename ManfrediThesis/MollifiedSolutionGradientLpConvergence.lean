import ManfrediThesis.Preamble
import ManfrediThesis.MollifiedFieldDualNormTendstoZero
import ManfrediThesis.MollifiedGradientDistanceTendstoZero
import ManfrediThesis.MollifiedSolutionUniformEnergyBound
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pZeroOn
import ManfrediThesis.WeakSolutionZeroTest
set_option maxHeartbeats 1400000
open MeasureTheory

/-- Steps 4--8 of the degenerate limit transfer: the gradients of the
approximating solutions converge to `g` in `L^p(B_R(x₀))`.

`A` is the degenerate field, normalised by `A 0 = 0`; `Ae e` is its mollification
`Ae e h = ∫ ρ(z) A(h + √e z) dz - ∫ ρ(z) A(√e z) dz` against a nonnegative
probability density `ρ` supported in the closed unit ball; `u` is a weak
solution for `A` on `B_R(x₀)` with gradient `g`; and `U m`, `G m` are a weak
solution for `Ae(1/(m+1))` on `B_R(x₀)` and its gradient, with
`U m - u ∈ W^{1,p}_0(B_R(x₀))` carrying the gradient `G m - g`.  The two
quantitative inputs are the growth bound with constant `Γ`, valid for `A` and
uniformly for every `Ae e` with `0 < e ≤ 1`, and the monotonicity bound with
constant `c₃ > 0`,
`c₃(e + ‖a‖² + ‖b‖²)^{p/2-1}‖a-b‖² ≤ ⟨Ae e a - Ae e b, a - b⟩`, also uniform in
`e`.  The conclusion is
`∫_{B_R}‖G m - g‖^p → 0`.

The route is the `.tex`'s Steps 4--8.  The two energy identities (E) come from
approximating `U m - u` through `MemW1pZeroOn`'s smooth sequence and
`SmoothCompactSupportMemW1p`, testing both `hsol` and `hUsol m` against it with
`WeakSolutionZeroTest`.  The uniform bound (5a) on
`Y_e = ∫_{B_R}(e + ‖G m‖² + ‖g‖²)^{p/2-1}‖G m - g‖²` follows from the
monotonicity constant `c₃` on the left and the growth constant `Γ` on the
right.  The difference estimate (6) bounds `∫_{B_R}‖Ae e h - A h‖` on the
relevant range by a quantity `δ_e` built from the mollification formula and the
support bound `‖z‖ ≤ 1` on `tsupport ρ`, and `δ_e → 0` by dominated
convergence.  Step 8 then splits into the two Hölder cases `1 < p ≤ 2` and
`p ≥ 2` to pass from `Y_e → 0` to `∫_{B_R}‖G m - g‖^p → 0`.

Only the facts listed in the statement are used; in particular no structure
bundle for `A` itself is needed beyond `A 0 = 0`, continuity of `A`, the growth
constant `Γ` and the monotonicity constant `c₃`, and the clause (1) bundle for
the mollified family enters only through the `EllipticStructureQ12` component
of `hAeQ`.  Per pm-0020 the approximating family here is the mollified one, not
`A(h) + e^{p/2-1}h`; per pm-0048 the normalisation `A 0 = 0` is a hypothesis,
not something re-derived. -/
theorem MollifiedSolutionGradientLpConvergence :
    ∀ (n : ℕ) (p r' : ℝ), 2 ≤ n → 1 < p →
      ∀ ρ : EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ z, 0 ≤ ρ z) →
        (∫ z, ρ z) = 1 →
        (∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Continuous f →
          Integrable (fun z => ρ z * f z) volume) →
        (∀ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), Continuous F →
          Integrable (fun z => ρ z • F z) volume) →
        (∀ z ∈ tsupport ρ, ‖z‖ ≤ 1) →
      ∀ A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        A 0 = 0 → Continuous A →
      ∀ Ae : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        (∀ e h, Ae e h = (∫ z, ρ z • A (h + Real.sqrt e • z))
            - ∫ z, ρ z • A (Real.sqrt e • z)) →
        (∀ e, Ae e 0 = 0) →
        (∀ e : ℝ, 0 < e → e ≤ 1 →
          ∃ γ₀' γ₁' : ℝ, 0 < γ₀' ∧ γ₁' ≤ r' * γ₀' ∧
            EllipticStructureQ12 n p e γ₀' γ₁' Set.univ (fun _ _ h => Ae e h)) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < R →
        MemW1pOn n p (Metric.ball x₀ R) u g →
        IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h)
          (fun _ _ _ => 0) u g →
      ∀ Γ : ℝ, 0 < Γ →
        (∀ h : EuclideanSpace ℝ (Fin n),
          ‖A h‖ ≤ Γ * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2)) →
        (∀ e : ℝ, 0 < e → e ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin n),
          ‖Ae e h‖ ≤ Γ * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2)) →
      ∀ c₃ : ℝ, 0 < c₃ →
        (∀ e : ℝ, 0 < e → e ≤ 1 → ∀ a b : EuclideanSpace ℝ (Fin n),
          c₃ * (e + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2
            ≤ ∑ i, (Ae e a i - Ae e b i) * (a i - b i)) →
      ∀ (U : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
        (G : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        (∀ m : ℕ, IsWeakSolutionOn n p (Metric.ball x₀ R)
            (fun _ _ h => Ae (1 / ((m : ℝ) + 1)) h) (fun _ _ _ => 0) (U m) (G m)) →
        (∀ m : ℕ, MemW1pZeroOn n p (Metric.ball x₀ R)
            (fun x => U m x - u x) (fun x => G m x - g x)) →
        Filter.Tendsto
          (fun m : ℕ => ∫ x in Metric.ball x₀ R, ‖G m x - g x‖ ^ p)
          Filter.atTop (nhds 0) := by
  intro n p r' hn hp ρ hρ0 hρint hρfint hρFint hsuppz A hA0 hAcont Ae hAeeq hAe0
    hAeQ x₀ R u g hR hu hsol Γ hΓ0 hΓA hΓAe c₃ hc₃0 hM U G hUsol hUzero
  have hq'0 : (0:ℝ) < (p - 1) / 2 := by linarith
  have hsq2 : ∀ x y : EuclideanSpace ℝ (Fin n),
      ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    intro x y
    have h1 := norm_add_le x y
    nlinarith [h1, norm_nonneg x, norm_nonneg y, norm_nonneg (x + y),
      sq_nonneg (‖x‖ - ‖y‖)]
  have hIP : ∀ v w : EuclideanSpace ℝ (Fin n), (∑ i, v i * w i) = (innerSL ℝ w) v := by
    intro v w
    show (∑ i, v i * w i) = inner ℝ w v
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hem0 : ∀ m : ℕ, (0 : ℝ) < 1 / ((m : ℝ) + 1) := by
    intro m
    have : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    positivity
  have hem1 : ∀ m : ℕ, (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 := by
    intro m
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hp0 : (0:ℝ) < p := by linarith
  have hp10 : (0:ℝ) < p - 1 := by linarith
  have hpne : (ENNReal.ofReal p) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hp0]
  have hptop : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ → ℝ, X = fun m : ℕ =>
    (∫ x in Metric.ball x₀ R, ‖G m x - g x‖ ^ p) ^ (1 / p) := ⟨_, rfl⟩
  obtain ⟨Iq, hIqdef⟩ : ∃ Iq : ℕ → ℝ, Iq = fun m : ℕ =>
    ∫ x in Metric.ball x₀ R,
      (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
        * ‖G m x - g x‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℕ → ℝ, δ = fun m : ℕ =>
    (∫ x in Metric.ball x₀ R,
      ‖A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x)‖ ^ (p / (p - 1))) ^ ((p - 1) / p) :=
    ⟨_, rfl⟩
  have hXp : ∀ m : ℕ,
      (∫ x in Metric.ball x₀ R, ‖G m x - g x‖ ^ p) = X m ^ p := by
    intro m
    have hnn : (0:ℝ) ≤ ∫ x in Metric.ball x₀ R, ‖G m x - g x‖ ^ p :=
      integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
    rw [hXdef]
    show _ = ((∫ x in Metric.ball x₀ R, ‖G m x - g x‖ ^ p) ^ (1 / p)) ^ p
    rw [← Real.rpow_mul hnn, one_div, inv_mul_cancel₀ (ne_of_gt hp0), Real.rpow_one]
  -- the conjugate exponent, and the `L^{p'} × L^p` toolkit used by Steps 4-6
  have hfinm : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  have hp'0 : (0:ℝ) < p / (p - 1) := by positivity
  have hconj : Real.HolderConjugate p (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have hconj' : Real.HolderConjugate (p / (p - 1)) p := hconj.symm
  have hHT : ENNReal.HolderTriple (ENNReal.ofReal (p / (p - 1)))
      (ENNReal.ofReal p) 1 := ⟨by rw [inv_one]; exact hconj'.inv_add_inv_ennreal⟩
  have hCS : ∀ a b : EuclideanSpace ℝ (Fin n),
      |∑ i, a i * b i| ≤ ‖a‖ * ‖b‖ := by
    intro a b
    rw [hIP a b, mul_comm ‖a‖ ‖b‖]
    exact abs_real_inner_le_norm b a
  have hpair : ∀ F H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      MemLp F (ENNReal.ofReal (p / (p - 1))) (volume.restrict (Metric.ball x₀ R)) →
      MemLp H (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) →
      IntegrableOn (fun x => ∑ i, F x i * H x i) (Metric.ball x₀ R) volume
        ∧ |∫ x in Metric.ball x₀ R, ∑ i, F x i * H x i|
          ≤ (∫ x in Metric.ball x₀ R, ‖F x‖ ^ (p / (p - 1))) ^ ((p - 1) / p)
            * (∫ x in Metric.ball x₀ R, ‖H x‖ ^ p) ^ (1 / p) := by
    intro F H hF hH
    have hprod : Integrable (fun x => ‖F x‖ * ‖H x‖)
        (volume.restrict (Metric.ball x₀ R)) := hF.norm.integrable_mul hH.norm
    have hmeas : AEStronglyMeasurable (fun x => ∑ i, F x i * H x i)
        (volume.restrict (Metric.ball x₀ R)) := by
      have hinner : AEStronglyMeasurable
          (fun x => (inner ℝ (H x) (F x) : ℝ))
          (volume.restrict (Metric.ball x₀ R)) :=
        (continuous_inner (𝕜 := ℝ)
          (E := EuclideanSpace ℝ (Fin n))).comp_aestronglyMeasurable
          (hH.aestronglyMeasurable.prodMk hF.aestronglyMeasurable)
      exact hinner.congr (Filter.Eventually.of_forall fun x => (hIP (F x) (H x)).symm)
    have hint : IntegrableOn (fun x => ∑ i, F x i * H x i)
        (Metric.ball x₀ R) volume := by
      refine hprod.mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs]
      exact hCS _ _
    refine ⟨hint, ?_⟩
    have h1 : |∫ x in Metric.ball x₀ R, ∑ i, F x i * H x i|
        ≤ ∫ x in Metric.ball x₀ R, ‖F x‖ * ‖H x‖ := by
      refine le_trans abs_integral_le_integral_abs ?_
      exact integral_mono hint.abs hprod (fun x => hCS _ _)
    refine le_trans h1 ?_
    have h2 := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume.restrict (Metric.ball x₀ R)) hconj'
      (Filter.Eventually.of_forall fun x => norm_nonneg (F x))
      (Filter.Eventually.of_forall fun x => norm_nonneg (H x)) hF.norm hH.norm
    rwa [show 1 / (p / (p - 1)) = (p - 1) / p by field_simp] at h2
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
  have hgas : AEStronglyMeasurable g (volume.restrict (Metric.ball x₀ R)) :=
    hu.2.2.aestronglyMeasurable
  have hGLp : ∀ m : ℕ, MemLp (G m) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) := by
    intro m
    have h := ((hUzero m).1.2.2).add hu.2.2
    exact MemLp.ae_eq (Filter.Eventually.of_forall fun x => by simp) h
  have hAecont : ∀ m : ℕ, Continuous (Ae (1 / ((m : ℝ) + 1))) := by
    intro m
    obtain ⟨γ₀', γ₁', -, -, hQe⟩ := hAeQ _ (hem0 m) (hem1 m)
    exact hQe.hcont 0 (Set.mem_univ 0) 0
  have hLpof : ∀ (F w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      AEStronglyMeasurable F (volume.restrict (Metric.ball x₀ R)) →
      MemLp w (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) →
      (∀ x, ‖F x‖ ≤ Γ * (1 + ‖w x‖ ^ 2) ^ ((p - 1) / 2)) →
      MemLp F (ENNReal.ofReal (p / (p - 1)))
        (volume.restrict (Metric.ball x₀ R)) := by
    intro F w hFm hw hbd
    refine (integrable_norm_rpow_iff hFm ?_ ENNReal.ofReal_ne_top).1 ?_
    · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    rw [ENNReal.toReal_ofReal hp'0.le]
    have hwp : Integrable (fun x => ‖w x‖ ^ p)
        (volume.restrict (Metric.ball x₀ R)) := by
      have h := hw.integrable_norm_rpow hpne hptop
      rwa [ENNReal.toReal_ofReal hp0.le] at h
    have hbig : Integrable (fun x => Γ ^ (p / (p - 1))
        * ((2:ℝ) ^ (p / 2) * (1 + ‖w x‖ ^ p)))
        (volume.restrict (Metric.ball x₀ R)) :=
      (((integrable_const (1:ℝ)).add hwp).const_mul _).const_mul _
    have hmF : AEStronglyMeasurable (fun x => ‖F x‖ ^ (p / (p - 1)))
        (volume.restrict (Metric.ball x₀ R)) :=
      (continuous_id.rpow_const
        (fun t => Or.inr hp'0.le)).comp_aestronglyMeasurable hFm.norm
    refine hbig.mono' hmF (Filter.Eventually.of_forall fun x => ?_)
    have hΓ0' : (0:ℝ) ≤ Γ := hΓ0.le
    have hbase : (0:ℝ) ≤ (1 + ‖w x‖ ^ 2) ^ ((p - 1) / 2) :=
      Real.rpow_nonneg (by positivity) _
    have hstep1 : ‖F x‖ ^ (p / (p - 1))
        ≤ (Γ * (1 + ‖w x‖ ^ 2) ^ ((p - 1) / 2)) ^ (p / (p - 1)) :=
      Real.rpow_le_rpow (norm_nonneg _) (hbd x) hp'0.le
    have hstep2 : (Γ * (1 + ‖w x‖ ^ 2) ^ ((p - 1) / 2)) ^ (p / (p - 1))
        = Γ ^ (p / (p - 1)) * (1 + ‖w x‖ ^ 2) ^ (p / 2) := by
      rw [Real.mul_rpow hΓ0' hbase, ← Real.rpow_mul (by positivity),
        show (p - 1) / 2 * (p / (p - 1)) = p / 2 by field_simp]
    have hstep3 : (1 + ‖w x‖ ^ 2) ^ (p / 2)
        ≤ (2:ℝ) ^ (p / 2) * (1 + ‖w x‖ ^ p) := hpowbd _ (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc ‖F x‖ ^ (p / (p - 1))
        ≤ Γ ^ (p / (p - 1)) * (1 + ‖w x‖ ^ 2) ^ (p / 2) := by
          rw [← hstep2]; exact hstep1
      _ ≤ Γ ^ (p / (p - 1)) * ((2:ℝ) ^ (p / 2) * (1 + ‖w x‖ ^ p)) :=
          mul_le_mul_of_nonneg_left hstep3 (Real.rpow_nonneg hΓ0' _)
  have hΓpw : ∀ y w : EuclideanSpace ℝ (Fin n),
      ‖y‖ ≤ Γ * (1 + ‖w‖ ^ 2) ^ ((p - 1) / 2) →
      ‖y‖ ^ (p / (p - 1))
        ≤ Γ ^ (p / (p - 1)) * ((2:ℝ) ^ (p / 2) * (1 + ‖w‖ ^ p)) := by
    intro y w hbd
    have hbase : (0:ℝ) ≤ (1 + ‖w‖ ^ 2) ^ ((p - 1) / 2) :=
      Real.rpow_nonneg (by positivity) _
    have hstep1 : ‖y‖ ^ (p / (p - 1))
        ≤ (Γ * (1 + ‖w‖ ^ 2) ^ ((p - 1) / 2)) ^ (p / (p - 1)) :=
      Real.rpow_le_rpow (norm_nonneg _) hbd hp'0.le
    have hstep2 : (Γ * (1 + ‖w‖ ^ 2) ^ ((p - 1) / 2)) ^ (p / (p - 1))
        = Γ ^ (p / (p - 1)) * (1 + ‖w‖ ^ 2) ^ (p / 2) := by
      rw [Real.mul_rpow hΓ0.le hbase, ← Real.rpow_mul (by positivity),
        show (p - 1) / 2 * (p / (p - 1)) = p / 2 by field_simp]
    calc ‖y‖ ^ (p / (p - 1))
        ≤ Γ ^ (p / (p - 1)) * (1 + ‖w‖ ^ 2) ^ (p / 2) := by
          rw [← hstep2]; exact hstep1
      _ ≤ Γ ^ (p / (p - 1)) * ((2:ℝ) ^ (p / 2) * (1 + ‖w‖ ^ p)) :=
          mul_le_mul_of_nonneg_left (hpowbd _ (norm_nonneg _))
            (Real.rpow_nonneg hΓ0.le _)
  have hAeLp : ∀ m : ℕ, MemLp (fun x => Ae (1 / ((m : ℝ) + 1)) (G m x))
      (ENNReal.ofReal (p / (p - 1))) (volume.restrict (Metric.ball x₀ R)) := by
    intro m
    refine hLpof _ (G m)
      ((hAecont m).comp_aestronglyMeasurable (hGLp m).aestronglyMeasurable)
      (hGLp m) ?_
    exact fun x => hΓAe _ (hem0 m) (hem1 m) _
  have hALp : MemLp (fun x => A (g x)) (ENNReal.ofReal (p / (p - 1)))
      (volume.restrict (Metric.ball x₀ R)) :=
    hLpof _ g (hAcont.comp_aestronglyMeasurable hgas) hu.2.2 (fun x => hΓA _)
  have hXnn : ∀ m : ℕ, 0 ≤ X m := by
    intro m
    rw [hXdef]
    exact Real.rpow_nonneg
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _
  have hδnn : ∀ m : ℕ, 0 ≤ δ m := by
    intro m
    rw [hδdef]
    exact Real.rpow_nonneg
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _
  have hWp : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin n)),
      (0:ℝ) < 1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2 := by
    intro m x
    have h := hem0 m
    nlinarith [sq_nonneg ‖G m x‖, sq_nonneg ‖g x‖]
  have hDint : ∀ m : ℕ, IntegrableOn (fun x => ‖G m x - g x‖ ^ p)
      (Metric.ball x₀ R) volume := by
    intro m
    have h := (hUzero m).1.2.2.integrable_norm_rpow hpne hptop
    rwa [ENNReal.toReal_ofReal hp0.le] at h
  have hid2 : ∀ t s : ℝ, 0 ≤ t → (t ^ 2 : ℝ) ^ (s / 2) = t ^ s := by
    intro t s ht
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h]
      rcases eq_or_ne s 0 with hs | hs
      · simp [hs]
      · rw [show ((0:ℝ) ^ 2) = 0 by norm_num,
          Real.zero_rpow (div_ne_zero hs two_ne_zero), Real.zero_rpow hs]
    · have ht2 : (t ^ 2 : ℝ) = t ^ (2:ℝ) := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      rw [ht2, ← Real.rpow_mul h.le]
      congr 1
      ring
  have hid : ∀ t : ℝ, 0 ≤ t → ((t ^ 2) ^ (p / 2 - 1)) * t ^ 2 = t ^ p := by
    intro t ht
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h]
      simp [Real.zero_rpow (ne_of_gt hp0)]
    · have h1 : ((t ^ 2 : ℝ)) ^ (p / 2 - 1) = t ^ (p - 2) := by
        rw [show p / 2 - 1 = (p - 2) / 2 by ring]
        exact hid2 t (p - 2) ht
      have h2 : (t ^ 2 : ℝ) = t ^ (2:ℝ) := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      rw [h1, h2, ← Real.rpow_add h]
      congr 1
      ring
  have hWrpow : ∀ (m : ℕ) (s : ℝ), AEStronglyMeasurable
      (fun x => (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ s)
      (volume.restrict (Metric.ball x₀ R)) := by
    intro m s
    have hWm : AEStronglyMeasurable
        (fun x => 1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2)
        (volume.restrict (Metric.ball x₀ R)) :=
      ((aestronglyMeasurable_const.add
        ((hGLp m).aestronglyMeasurable.norm.pow 2)).add
        (hgas.norm.pow 2))
    have hexp : AEStronglyMeasurable
        (fun x => Real.exp (Real.log
          (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) * s))
        (volume.restrict (Metric.ball x₀ R)) :=
      (Real.measurable_exp.comp_aemeasurable
        ((Real.measurable_log.comp_aemeasurable
          hWm.aemeasurable).mul_const s)).aestronglyMeasurable
    refine hexp.congr (Filter.Eventually.of_forall fun x => ?_)
    exact (Real.rpow_def_of_pos (hWp m x) s).symm
  -- Step 4 (`.tex` l.653-705): the two energy identities (E).  `u_e - u` is not
  -- compactly supported, so `hUzero m` supplies smooth compactly supported
  -- `φ_k` with `(φ_k, ∇φ_k) → (u_e - u, g_e - g)` in `L^p(B_R)`; each pair is
  -- admissible by `SmoothCompactSupportMemW1p`, so `hUsol m` and `hsol` give
  -- the two identities against `∇φ_k`; `hΓAe`/`hΓA` put `A_e(g_e)` and `A(g)`
  -- in `L^{p'}(B_R)` and Hölder passes to the limit.
  have hE : ∀ m : ℕ,
      (∫ x in Metric.ball x₀ R,
          ∑ i, (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (G m x - g x) i) = 0
        ∧ (∫ x in Metric.ball x₀ R,
          ∑ i, (A (g x)) i * (G m x - g x) i) = 0 := by
    intro m
    have hn1 : 1 ≤ n := le_trans (by norm_num) hn
    refine ⟨?_, ?_⟩
    · exact WeakSolutionZeroTest n p hn1 hp (Metric.ball x₀ R)
        (fun _ _ h => Ae (1 / ((m : ℝ) + 1)) h) (U m) (G m)
        (fun x => U m x - u x) (fun x => G m x - g x)
        Metric.isOpen_ball (hUsol m) (hAeLp m) (hUzero m)
    · exact WeakSolutionZeroTest n p hn1 hp (Metric.ball x₀ R)
        (fun _ _ h => A h) u g
        (fun x => U m x - u x) (fun x => G m x - g x)
        Metric.isOpen_ball hsol hALp (hUzero m)
  -- Step 5 (`.tex` l.706-753): `Y_e = ∫|g_e|^p` is bounded uniformly in `e`,
  -- hence so is `∫ (e + |g_e|^2 + |g|^2)^{p/2}`.  From the first identity of
  -- (E), `hM` (the uniform monotonicity bound) on the left and `hΓAe` with
  -- Hölder on the right, giving `S ≤ a₀ + b₁ S^θ` with `θ = (p-1)/p < 1`.
  obtain ⟨E₁, hE₁0, h5bi, h5b⟩ : ∃ E₁ : ℝ, 0 ≤ E₁ ∧
      (∀ m : ℕ, IntegrableOn (fun x =>
        (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2))
        (Metric.ball x₀ R) volume) ∧
      (∀ m : ℕ, (∫ x in Metric.ball x₀ R,
        (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2)) ≤ E₁) :=
    MollifiedSolutionUniformEnergyBound n p A Ae x₀ R u g Γ c₃ G hAe0 hR hΓ0 hu
      hΓAe hc₃0 hM hem0 hem1 hp0 hp10 hpne hptop hp'0 hpair hGLp hΓpw hAeLp hWp
      hid2 hid hWrpow hE
  -- Step 6 (`.tex` l.754-775): subtracting the two identities of (E) and
  -- applying `hM` on the left, Hölder on the right.
  have h6 : ∀ m : ℕ, IntegrableOn (fun x =>
        (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
          * ‖G m x - g x‖ ^ 2) (Metric.ball x₀ R) volume
      ∧ c₃ * Iq m ≤ δ m * X m := by
    intro m
    have hAegLp : MemLp (fun x => Ae (1 / ((m : ℝ) + 1)) (g x))
        (ENNReal.ofReal (p / (p - 1))) (volume.restrict (Metric.ball x₀ R)) :=
      hLpof _ g ((hAecont m).comp_aestronglyMeasurable hgas) hu.2.2
        (fun x => hΓAe _ (hem0 m) (hem1 m) _)
    have hDLp : MemLp (fun x => G m x - g x) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ R)) := (hUzero m).1.2.2
    have hP1 := hpair (fun x => Ae (1 / ((m : ℝ) + 1)) (G m x))
      (fun x => G m x - g x) (hAeLp m) hDLp
    have hP2 := hpair (fun x => Ae (1 / ((m : ℝ) + 1)) (g x))
      (fun x => G m x - g x) hAegLp hDLp
    have hP3 := hpair (fun x => A (g x)) (fun x => G m x - g x) hALp hDLp
    have hFdiffLp : MemLp (fun x => Ae (1 / ((m : ℝ) + 1)) (G m x)
        - Ae (1 / ((m : ℝ) + 1)) (g x)) (ENNReal.ofReal (p / (p - 1)))
        (volume.restrict (Metric.ball x₀ R)) := (hAeLp m).sub hAegLp
    have hGdiffLp : MemLp (fun x => A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x))
        (ENNReal.ofReal (p / (p - 1)))
        (volume.restrict (Metric.ball x₀ R)) := hALp.sub hAegLp
    have hP5 := hpair (fun x => Ae (1 / ((m : ℝ) + 1)) (G m x)
      - Ae (1 / ((m : ℝ) + 1)) (g x)) (fun x => G m x - g x) hFdiffLp hDLp
    have hP4 := hpair (fun x => A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x))
      (fun x => G m x - g x) hGdiffLp hDLp
    -- subtracting the two identities of (E)
    have hsub1 : (∫ x in Metric.ball x₀ R, ∑ i,
          (Ae (1 / ((m : ℝ) + 1)) (G m x) - Ae (1 / ((m : ℝ) + 1)) (g x)) i
            * (G m x - g x) i)
        = (∫ x in Metric.ball x₀ R, ∑ i,
            (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (G m x - g x) i)
          - ∫ x in Metric.ball x₀ R, ∑ i,
            (Ae (1 / ((m : ℝ) + 1)) (g x)) i * (G m x - g x) i := by
      rw [← integral_sub hP1.1 hP2.1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (∑ i, (Ae (1 / ((m : ℝ) + 1)) (G m x)
            - Ae (1 / ((m : ℝ) + 1)) (g x)) i * (G m x - g x) i)
        = (∑ i, (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (G m x - g x) i)
          - ∑ i, (Ae (1 / ((m : ℝ) + 1)) (g x)) i * (G m x - g x) i
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      show (Ae (1 / ((m : ℝ) + 1)) (G m x) i - Ae (1 / ((m : ℝ) + 1)) (g x) i)
          * (G m x - g x) i
        = (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (G m x - g x) i
          - (Ae (1 / ((m : ℝ) + 1)) (g x)) i * (G m x - g x) i
      ring
    have hsub2 : (∫ x in Metric.ball x₀ R, ∑ i,
          (A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x)) i * (G m x - g x) i)
        = (∫ x in Metric.ball x₀ R, ∑ i, (A (g x)) i * (G m x - g x) i)
          - ∫ x in Metric.ball x₀ R, ∑ i,
            (Ae (1 / ((m : ℝ) + 1)) (g x)) i * (G m x - g x) i := by
      rw [← integral_sub hP3.1 hP2.1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (∑ i, (A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x)) i * (G m x - g x) i)
        = (∑ i, (A (g x)) i * (G m x - g x) i)
          - ∑ i, (Ae (1 / ((m : ℝ) + 1)) (g x)) i * (G m x - g x) i
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      show (A (g x) i - Ae (1 / ((m : ℝ) + 1)) (g x) i) * (G m x - g x) i
        = (A (g x)) i * (G m x - g x) i
          - (Ae (1 / ((m : ℝ) + 1)) (g x)) i * (G m x - g x) i
      ring
    have hdiffid : (∫ x in Metric.ball x₀ R, ∑ i,
          (Ae (1 / ((m : ℝ) + 1)) (G m x) - Ae (1 / ((m : ℝ) + 1)) (g x)) i
            * (G m x - g x) i)
        = ∫ x in Metric.ball x₀ R, ∑ i,
            (A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x)) i * (G m x - g x) i := by
      rw [hsub1, hsub2, (hE m).1, (hE m).2]
    -- the monotonicity bound, pointwise and integrated
    have hInn : ∀ x : EuclideanSpace ℝ (Fin n),
        (0:ℝ) ≤ (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
          * ‖G m x - g x‖ ^ 2 :=
      fun x => mul_nonneg (Real.rpow_nonneg (hWp m x).le _) (sq_nonneg _)
    have hmeasI : AEStronglyMeasurable (fun x =>
        (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
          * ‖G m x - g x‖ ^ 2) (volume.restrict (Metric.ball x₀ R)) :=
      (hWrpow m (p / 2 - 1)).mul (hDLp.aestronglyMeasurable.norm.pow 2)
    have hptw : ∀ x : EuclideanSpace ℝ (Fin n),
        c₃ * ((1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖G m x - g x‖ ^ 2)
          ≤ ∑ i, (Ae (1 / ((m : ℝ) + 1)) (G m x)
              - Ae (1 / ((m : ℝ) + 1)) (g x)) i * (G m x - g x) i := by
      intro x
      have h := hM (1 / ((m : ℝ) + 1)) (hem0 m) (hem1 m) (G m x) (g x)
      calc c₃ * ((1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
              * ‖G m x - g x‖ ^ 2)
          = c₃ * (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
              * ‖G m x - g x‖ ^ 2 := by ring
        _ ≤ _ := h
    have hIint : IntegrableOn (fun x =>
        (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
          * ‖G m x - g x‖ ^ 2) (Metric.ball x₀ R) volume := by
      refine Integrable.mono' (hP5.1.const_mul c₃⁻¹) hmeasI
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hInn x)]
      have h := hptw x
      have hc : c₃⁻¹ * (c₃ * ((1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2)
            ^ (p / 2 - 1) * ‖G m x - g x‖ ^ 2))
          = (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖G m x - g x‖ ^ 2 := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc₃0), one_mul]
      calc (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖G m x - g x‖ ^ 2
          = c₃⁻¹ * (c₃ * ((1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2)
              ^ (p / 2 - 1) * ‖G m x - g x‖ ^ 2)) := hc.symm
        _ ≤ c₃⁻¹ * (∑ i, (Ae (1 / ((m : ℝ) + 1)) (G m x)
              - Ae (1 / ((m : ℝ) + 1)) (g x)) i * (G m x - g x) i) :=
            mul_le_mul_of_nonneg_left h (inv_pos.2 hc₃0).le
    refine ⟨hIint, ?_⟩
    have hmono : c₃ * Iq m ≤ ∫ x in Metric.ball x₀ R, ∑ i,
        (Ae (1 / ((m : ℝ) + 1)) (G m x)
          - Ae (1 / ((m : ℝ) + 1)) (g x)) i * (G m x - g x) i := by
      rw [hIqdef]
      show c₃ * (∫ x in Metric.ball x₀ R,
          (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖G m x - g x‖ ^ 2) ≤ _
      rw [← integral_const_mul]
      exact integral_mono (hIint.const_mul c₃) hP5.1 hptw
    calc c₃ * Iq m
        ≤ ∫ x in Metric.ball x₀ R, ∑ i,
          (Ae (1 / ((m : ℝ) + 1)) (G m x)
            - Ae (1 / ((m : ℝ) + 1)) (g x)) i * (G m x - g x) i := hmono
      _ = ∫ x in Metric.ball x₀ R, ∑ i,
          (A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x)) i * (G m x - g x) i := hdiffid
      _ ≤ |∫ x in Metric.ball x₀ R, ∑ i,
          (A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x)) i * (G m x - g x) i| :=
          le_abs_self _
      _ ≤ (∫ x in Metric.ball x₀ R,
            ‖A (g x) - Ae (1 / ((m : ℝ) + 1)) (g x)‖ ^ (p / (p - 1)))
              ^ ((p - 1) / p)
          * (∫ x in Metric.ball x₀ R, ‖G m x - g x‖ ^ p) ^ (1 / p) := hP4.2
      _ = δ m * X m := by rw [hδdef, hXdef]
  -- Step 7 (`.tex` l.776-795): `δ_e → 0`.  `A_e(h) → A(h)` pointwise as
  -- `e ↓ 0` by continuity of `A` (`hAcont`) and `∫ρ = 1`, and `hΓA`/`hΓAe`
  -- give the `e`-free majorant `(2Γ)^{p'}(1+|g|^2)^{p/2} ∈ L^1(B_R)`.
  have h7 : Filter.Tendsto δ Filter.atTop (nhds 0) :=
    MollifiedFieldDualNormTendstoZero n p ρ hρ0 hρint hρfint hρFint hsuppz A hA0
      hAcont Ae hAeeq r' hAeQ x₀ R u g Γ δ hu hΓ0 hΓA hΓAe hq'0 hem0 hem1 hp0
      hδdef
  -- Step 8 (`.tex` l.796-833): `X_e ≤ Ψ(δ_e)`.  For `p ≥ 2`,
  -- `(e+|a|^2+|b|^2)^{p/2-1} ≥ 2^{1-p/2}|a-b|^{p-2}` gives `I_e ≥ 2^{1-p/2}X_e^p`
  -- and `(6)` gives `X_e ≤ (2^{p/2-1}δ_e/c₃)^{1/(p-1)}`.  For `1 < p < 2`,
  -- Hölder at `2/p` and `2/(2-p)` against `Θ = (e+|g_e|^2+|g|^2)^{p/2-1} > 0`
  -- with `(5b)` gives `X_e ≤ (δ_e/c₃) E₁^{(2-p)/p}`.
  have h8 : Filter.Tendsto X Filter.atTop (nhds 0) :=
    MollifiedGradientDistanceTendstoZero n p x₀ R g G c₃ E₁ X Iq δ hc₃0 hp0 hp10
      hE₁0 hsq2 hem0 hIqdef hXp hXnn hδnn hWp hDint hid2 hid h5bi h5b h6 h7
  -- Step 9's input: `∫|g_e - g|^p = X_e^p → 0`.
  have hctp : Filter.Tendsto (fun t : ℝ => t ^ p) (nhds 0) (nhds 0) := by
    have h : Filter.Tendsto (fun t : ℝ => t ^ p) (nhds 0) (nhds ((0:ℝ) ^ p)) :=
      (Real.continuousAt_rpow_const (0:ℝ) p (Or.inr hp0.le)).tendsto
    rw [Real.zero_rpow (ne_of_gt hp0)] at h
    exact h
  exact (hctp.comp h8).congr fun m => (hXp m).symm
