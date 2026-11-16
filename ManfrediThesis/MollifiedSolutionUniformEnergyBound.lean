import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pOn
set_option maxHeartbeats 1600000
open MeasureTheory

/-- The uniform energy bound of the degenerate limit transfer: the weighted
energies `∫_{B_R(x₀)} (e_m + ‖G_m‖² + ‖g‖²)^{p/2}`, with `e_m = 1/(m+1)`, are
integrable on the ball and bounded by a single constant `E₁` independent of `m`.

Conventions, restated here because a helper inherits none of its parent's.
`Ae e` is the mollified field at parameter `e`, normalised by `Ae e 0 = 0`;
`u` is a weak solution for the degenerate field with gradient `g` on
`B_R(x₀)`, and `G m` is the gradient of the approximating solution at the
parameter `e_m = 1/(m+1)`.  Every power of a positive real is the real power,
written exactly as the growth and monotonicity conditions print it --- in
particular the weight `(e + ‖a‖² + ‖b‖²)^{p/2-1}` of the monotonicity
hypothesis and the integrand `(e_m + ‖G_m‖² + ‖g‖²)^{p/2}` here --- and
`p' = p/(p-1)` is the conjugate exponent.  Per pm-0020 the approximating family
is the mollified one, never `A(h) + e^{p/2-1}h`.

The hypotheses are the quantitative inputs the parent has already assembled:
the growth bound for `Ae` with constant `Γ`, the monotonicity bound with
constant `c₃`, the duality pairing with its Hölder estimate, the `L^p`
membership of each `G m`, the `L^{p'}` membership of each `Ae(e_m)(G m)`, the
pointwise positivity of the weight, two elementary power identities, the
measurability of every real power of the weight, and the two orthogonality
identities (E) coming from the two weak formulations tested against `U m - u`.

The route is Step 2 of the parent's manuscript argument.  (2a) Put
`Y_m = ∫_{B_R}‖G_m‖^p`.  The first identity of (E) reads
`∫ Σ_i Ae(e_m)(G_m)_i (G_m - g)_i = 0`; subtracting the same integral with `g`
in place of `G_m` --- which the second identity of (E) sets to `0` as well ---
and applying the monotonicity bound on the left and the Hölder estimate of the
pairing hypothesis on the right gives
`c₃Y_m ≤ a₀ + b₁Y_m^{(p-1)/p}`,
where `a₀` and `b₁` are built from `Γ`, `c₃`, `|B_R|` and `∫‖g‖^p` alone, the
growth bound converting `‖Ae(e_m)(G_m)‖^{p'}` into
`Γ^{p'}2^{p/2}(1+‖G_m‖^p)` pointwise.  Because the exponent `(p-1)/p` is
`< 1`, that inequality bounds `Y_m` by a constant `E` independent of `m`: for
any larger value the right-hand side is smaller than the left.  (2b) Pointwise
`e_m + ‖G_m‖² + ‖g‖² ≤ 3\max\{1, ‖G_m‖², ‖g‖²\}` because `e_m ≤ 1`, so raising
to the power `p/2` --- monotone on `[0,∞)` --- and integrating gives
`∫(e_m + ‖G_m‖² + ‖g‖²)^{p/2} ≤ 3^{p/2}\bigl(|B_R| + E + ∫‖g‖^p\bigr) =: E₁`,
a bound independent of `m`; integrability on the ball follows from the same
majorant together with the measurability hypothesis for the real powers of the
weight. -/
theorem MollifiedSolutionUniformEnergyBound :
    ∀ (n : ℕ) (p : ℝ)
      (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (Ae : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
      (u : EuclideanSpace ℝ (Fin n) → ℝ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (Γ c₃ : ℝ)
      (G : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      (∀ e, Ae e 0 = 0) → 0 < R → 0 < Γ →
      MemW1pOn n p (Metric.ball x₀ R) u g →
      (∀ e : ℝ, 0 < e → e ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin n),
        ‖Ae e h‖ ≤ Γ * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2)) →
      0 < c₃ →
      (∀ e : ℝ, 0 < e → e ≤ 1 → ∀ a b : EuclideanSpace ℝ (Fin n),
        c₃ * (e + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2
          ≤ ∑ i, (Ae e a i - Ae e b i) * (a i - b i)) →
      (∀ m : ℕ, (0 : ℝ) < 1 / ((m : ℝ) + 1)) →
      (∀ m : ℕ, (1 : ℝ) / ((m : ℝ) + 1) ≤ 1) →
      (0:ℝ) < p → (0:ℝ) < p - 1 →
      (ENNReal.ofReal p) ≠ 0 → (ENNReal.ofReal p) ≠ ⊤ →
      (0:ℝ) < p / (p - 1) →
      (∀ F H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        MemLp F (ENNReal.ofReal (p / (p - 1)))
          (volume.restrict (Metric.ball x₀ R)) →
        MemLp H (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) →
        IntegrableOn (fun x => ∑ i, F x i * H x i) (Metric.ball x₀ R) volume
          ∧ |∫ x in Metric.ball x₀ R, ∑ i, F x i * H x i|
            ≤ (∫ x in Metric.ball x₀ R, ‖F x‖ ^ (p / (p - 1))) ^ ((p - 1) / p)
              * (∫ x in Metric.ball x₀ R, ‖H x‖ ^ p) ^ (1 / p)) →
      (∀ m : ℕ, MemLp (G m) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ R))) →
      (∀ y w : EuclideanSpace ℝ (Fin n),
        ‖y‖ ≤ Γ * (1 + ‖w‖ ^ 2) ^ ((p - 1) / 2) →
        ‖y‖ ^ (p / (p - 1))
          ≤ Γ ^ (p / (p - 1)) * ((2:ℝ) ^ (p / 2) * (1 + ‖w‖ ^ p))) →
      (∀ m : ℕ, MemLp (fun x => Ae (1 / ((m : ℝ) + 1)) (G m x))
        (ENNReal.ofReal (p / (p - 1))) (volume.restrict (Metric.ball x₀ R))) →
      (∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin n)),
        (0:ℝ) < 1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) →
      (∀ t s : ℝ, 0 ≤ t → (t ^ 2 : ℝ) ^ (s / 2) = t ^ s) →
      (∀ t : ℝ, 0 ≤ t → ((t ^ 2) ^ (p / 2 - 1)) * t ^ 2 = t ^ p) →
      (∀ (m : ℕ) (s : ℝ), AEStronglyMeasurable
        (fun x => (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ s)
        (volume.restrict (Metric.ball x₀ R))) →
      (∀ m : ℕ,
        (∫ x in Metric.ball x₀ R,
            ∑ i, (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (G m x - g x) i) = 0
          ∧ (∫ x in Metric.ball x₀ R,
            ∑ i, (A (g x)) i * (G m x - g x) i) = 0) →
      ∃ E₁ : ℝ, 0 ≤ E₁ ∧
      (∀ m : ℕ, IntegrableOn (fun x =>
      (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2))
      (Metric.ball x₀ R) volume) ∧
      (∀ m : ℕ, (∫ x in Metric.ball x₀ R,
      (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2)) ≤ E₁) := by
  intro n p A Ae x₀ R u g Γ c₃ G hAe0 hR hΓ0 hu hΓAe hc₃0 hM hem0 hem1 hp0 hp10
    hpne hptop hp'0 hpair hGLp hΓpw hAeLp hWp hid2 hid hWrpow hE
  have hfinm : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  -- the data of the bound
  have hvolfin : (volume (Metric.ball x₀ R)) ≠ ⊤ := measure_ball_lt_top.ne
  have hvol0 : (0:ℝ) < (volume (Metric.ball x₀ R)).toReal := by
    refine ENNReal.toReal_pos (ne_of_gt ?_) hvolfin
    exact Metric.measure_ball_pos volume x₀ hR
  have hKint : IntegrableOn (fun x => ‖g x‖ ^ p) (Metric.ball x₀ R) volume := by
    have h := hu.2.2.integrable_norm_rpow hpne hptop
    rwa [ENNReal.toReal_ofReal hp0.le] at h
  have hK0 : (0:ℝ) ≤ ∫ x in Metric.ball x₀ R, ‖g x‖ ^ p :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hYint : ∀ m : ℕ, IntegrableOn (fun x => ‖G m x‖ ^ p)
      (Metric.ball x₀ R) volume := by
    intro m
    have h := (hGLp m).integrable_norm_rpow hpne hptop
    rwa [ENNReal.toReal_ofReal hp0.le] at h
  have hY0 : ∀ m : ℕ, (0:ℝ) ≤ ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p :=
    fun m => integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hAenorm : ∀ m : ℕ, IntegrableOn (fun x =>
      ‖Ae (1 / ((m : ℝ) + 1)) (G m x)‖ ^ (p / (p - 1)))
      (Metric.ball x₀ R) volume := by
    intro m
    have h := (hAeLp m).integrable_norm_rpow
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)
      ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hp'0.le] at h
  obtain ⟨κp, hκ0, hκ1, hκ2⟩ : ∃ κp : ℝ, 0 < κp ∧ κp ≤ 1
      ∧ κp ≤ (2:ℝ) ^ (p / 2 - 1) := by
    refine ⟨min 1 ((2:ℝ) ^ (p / 2 - 1)),
      lt_min one_pos (Real.rpow_pos_of_pos (by norm_num) _),
      min_le_left _ _, min_le_right _ _⟩
  -- (5.1) the pointwise lower bound on the energy density
  have hptw5 : ∀ (e : ℝ), 0 < e → e ≤ 1 →
      ∀ h : EuclideanSpace ℝ (Fin n),
        κp * (‖h‖ ^ p - e ^ (p / 2))
          ≤ (e + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖ ^ 2 := by
    intro e he0 he1 h
    have hb0 : (0:ℝ) < e + ‖h‖ ^ 2 := by nlinarith [sq_nonneg ‖h‖]
    have hnn : (0:ℝ) ≤ (e + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖ ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hb0.le _) (sq_nonneg _)
    rcases le_total e (‖h‖ ^ 2) with hcase | hcase
    · have hh0 : (0:ℝ) < ‖h‖ ^ 2 := lt_of_lt_of_le he0 hcase
      have hhn : (0:ℝ) < ‖h‖ := by
        rcases eq_or_lt_of_le (norm_nonneg h) with h1 | h1
        · exact absurd (by rw [← h1]; norm_num : ‖h‖ ^ 2 = 0) (ne_of_gt hh0)
        · exact h1
      have hkey : κp * ‖h‖ ^ p ≤ (e + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖ ^ 2 := by
        rcases le_or_gt 0 (p / 2 - 1) with hq | hq
        · have h1 : (‖h‖ ^ 2) ^ (p / 2 - 1) ≤ (e + ‖h‖ ^ 2) ^ (p / 2 - 1) :=
            Real.rpow_le_rpow (sq_nonneg _) (by linarith) hq
          have h2 : κp * ‖h‖ ^ p ≤ (‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖ ^ 2 := by
            rw [hid ‖h‖ (norm_nonneg h)]
            nlinarith [Real.rpow_nonneg (norm_nonneg h) p, hκ1]
          exact le_trans h2 (mul_le_mul_of_nonneg_right h1 (sq_nonneg _))
        · have hle2 : e + ‖h‖ ^ 2 ≤ 2 * ‖h‖ ^ 2 := by linarith
          have h1 : ((2:ℝ) * ‖h‖ ^ 2) ^ (p / 2 - 1)
              ≤ (e + ‖h‖ ^ 2) ^ (p / 2 - 1) :=
            Real.rpow_le_rpow_of_nonpos hb0 hle2 hq.le
          have h3 : ((2:ℝ) * ‖h‖ ^ 2) ^ (p / 2 - 1)
              = (2:ℝ) ^ (p / 2 - 1) * (‖h‖ ^ 2) ^ (p / 2 - 1) :=
            Real.mul_rpow (by norm_num) (sq_nonneg _)
          have h4 : κp * ‖h‖ ^ p
              ≤ ((2:ℝ) * ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖ ^ 2 := by
            rw [h3, mul_assoc, hid ‖h‖ (norm_nonneg h)]
            exact mul_le_mul_of_nonneg_right hκ2
              (Real.rpow_nonneg (norm_nonneg h) p)
          exact le_trans h4 (mul_le_mul_of_nonneg_right h1 (sq_nonneg _))
      have hep : (0:ℝ) ≤ e ^ (p / 2) := Real.rpow_nonneg he0.le _
      nlinarith [hkey, hep, hκ0]
    · have hsmall : ‖h‖ ^ p ≤ e ^ (p / 2) := by
        rw [← hid2 ‖h‖ p (norm_nonneg h)]
        exact Real.rpow_le_rpow (sq_nonneg _) hcase (by positivity)
      nlinarith [hnn, hκ0, hsmall]
  -- (5.2) the monotonicity bound at `b = 0`
  have hM0 : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin n)),
      c₃ * (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2) ^ (p / 2 - 1) * ‖G m x‖ ^ 2
        ≤ ∑ i, (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (G m x) i := by
    intro m x
    have h := hM (1 / ((m : ℝ) + 1)) (hem0 m) (hem1 m) (G m x) 0
    rw [hAe0] at h
    have hz1 : ‖(0 : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 0 := by simp
    have hz2 : (G m x) - (0 : EuclideanSpace ℝ (Fin n)) = G m x := sub_zero _
    rw [hz1, add_zero, hz2] at h
    refine le_trans h (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    show (Ae (1 / ((m : ℝ) + 1)) (G m x) i - (0 : EuclideanSpace ℝ (Fin n)) i)
        * (G m x i - (0 : EuclideanSpace ℝ (Fin n)) i)
      = (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (G m x) i
    simp
  set vol := (volume (Metric.ball x₀ R)).toReal with hvoldef
  set Kg := ∫ x in Metric.ball x₀ R, ‖g x‖ ^ p with hKdef
  -- (5.3) the integrated lower bound
  have hlow5 : ∀ m : ℕ,
      c₃ * κp * ((∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p)
          - vol * (1 / ((m : ℝ) + 1)) ^ (p / 2))
        ≤ ∫ x in Metric.ball x₀ R, ∑ i,
          (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (G m x) i := by
    intro m
    have hP := hpair (fun x => Ae (1 / ((m : ℝ) + 1)) (G m x)) (G m)
      (hAeLp m) (hGLp m)
    have hptw : ∀ x : EuclideanSpace ℝ (Fin n),
        c₃ * κp * (‖G m x‖ ^ p - (1 / ((m : ℝ) + 1)) ^ (p / 2))
          ≤ ∑ i, (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (G m x) i := by
      intro x
      have h1 := hptw5 (1 / ((m : ℝ) + 1)) (hem0 m) (hem1 m) (G m x)
      have h2 := hM0 m x
      nlinarith [h1, h2, hc₃0]
    have hlhs : IntegrableOn (fun x => c₃ * κp
        * (‖G m x‖ ^ p - (1 / ((m : ℝ) + 1)) ^ (p / 2)))
        (Metric.ball x₀ R) volume :=
      ((hYint m).sub (integrable_const _)).const_mul _
    have hmo := integral_mono hlhs hP.1 hptw
    rwa [integral_const_mul, integral_sub (hYint m) (integrable_const _),
      setIntegral_const, MeasureTheory.measureReal_def, smul_eq_mul,
      ← hvoldef] at hmo
  -- (5.4) the energy equals the pairing against `g`
  have hE4 : ∀ m : ℕ, (∫ x in Metric.ball x₀ R, ∑ i,
        (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (G m x) i)
      = ∫ x in Metric.ball x₀ R, ∑ i,
        (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (g x) i := by
    intro m
    have hP1 := hpair (fun x => Ae (1 / ((m : ℝ) + 1)) (G m x)) (G m)
      (hAeLp m) (hGLp m)
    have hP2 := hpair (fun x => Ae (1 / ((m : ℝ) + 1)) (G m x)) g
      (hAeLp m) hu.2.2
    have hsplit : (∫ x in Metric.ball x₀ R, ∑ i,
          (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (G m x - g x) i)
        = (∫ x in Metric.ball x₀ R, ∑ i,
            (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (G m x) i)
          - ∫ x in Metric.ball x₀ R, ∑ i,
            (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (g x) i := by
      rw [← integral_sub hP1.1 hP2.1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (∑ i, (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (G m x - g x) i)
        = (∑ i, (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (G m x) i)
          - ∑ i, (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (g x) i
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      show (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (G m x i - g x i)
        = (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (G m x) i
          - (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (g x) i
      ring
    have h := (hE m).1
    rw [hsplit] at h
    linarith [h]
  -- (5.6)-(5.7) the Hölder bound on the right-hand side
  have hb5 : ∀ m : ℕ, (∫ x in Metric.ball x₀ R, ∑ i,
        (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (g x) i)
      ≤ ((Γ ^ (p / (p - 1)) * (2:ℝ) ^ (p / 2)) ^ ((p - 1) / p)
          * Kg ^ (1 / p))
        * (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p) ^ ((p - 1) / p) := by
    intro m
    have hP := hpair (fun x => Ae (1 / ((m : ℝ) + 1)) (G m x)) g
      (hAeLp m) hu.2.2
    have hcst : (0:ℝ) ≤ Γ ^ (p / (p - 1)) * (2:ℝ) ^ (p / 2) := by positivity
    have hb : (∫ x in Metric.ball x₀ R,
          ‖Ae (1 / ((m : ℝ) + 1)) (G m x)‖ ^ (p / (p - 1)))
        ≤ Γ ^ (p / (p - 1)) * (2:ℝ) ^ (p / 2)
          * (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p) := by
      have hbnd : IntegrableOn (fun x => Γ ^ (p / (p - 1)) * (2:ℝ) ^ (p / 2)
          * (1 + ‖G m x‖ ^ p)) (Metric.ball x₀ R) volume := by
        refine Integrable.const_mul ?_ _
        exact (integrable_const (1:ℝ)).add (hYint m)
      have hmo := integral_mono (hAenorm m) hbnd
        (fun x => by
          have h := hΓpw (Ae (1 / ((m : ℝ) + 1)) (G m x)) (G m x)
            (hΓAe _ (hem0 m) (hem1 m) _)
          calc ‖Ae (1 / ((m : ℝ) + 1)) (G m x)‖ ^ (p / (p - 1))
              ≤ Γ ^ (p / (p - 1)) * ((2:ℝ) ^ (p / 2) * (1 + ‖G m x‖ ^ p)) := h
            _ = Γ ^ (p / (p - 1)) * (2:ℝ) ^ (p / 2) * (1 + ‖G m x‖ ^ p) := by
                ring)
      rwa [integral_const_mul, integral_add (integrable_const _) (hYint m),
        setIntegral_const, MeasureTheory.measureReal_def, smul_eq_mul,
        mul_one, ← hvoldef] at hmo
    have hS0 : (0:ℝ) ≤ vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p := by
      have := hY0 m
      linarith [hvol0]
    have hstep : (∫ x in Metric.ball x₀ R,
          ‖Ae (1 / ((m : ℝ) + 1)) (G m x)‖ ^ (p / (p - 1))) ^ ((p - 1) / p)
        ≤ (Γ ^ (p / (p - 1)) * (2:ℝ) ^ (p / 2)) ^ ((p - 1) / p)
          * (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p) ^ ((p - 1) / p) := by
      rw [← Real.mul_rpow hcst hS0]
      refine Real.rpow_le_rpow (integral_nonneg fun x =>
        Real.rpow_nonneg (norm_nonneg _) _) hb (by positivity)
    have hKnn : (0:ℝ) ≤ Kg ^ (1 / p) := Real.rpow_nonneg hK0 _
    calc (∫ x in Metric.ball x₀ R, ∑ i,
          (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (g x) i)
        ≤ |∫ x in Metric.ball x₀ R, ∑ i,
          (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (g x) i| := le_abs_self _
      _ ≤ (∫ x in Metric.ball x₀ R,
            ‖Ae (1 / ((m : ℝ) + 1)) (G m x)‖ ^ (p / (p - 1))) ^ ((p - 1) / p)
          * Kg ^ (1 / p) := hP.2
      _ ≤ ((Γ ^ (p / (p - 1)) * (2:ℝ) ^ (p / 2)) ^ ((p - 1) / p)
            * (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p) ^ ((p - 1) / p))
          * Kg ^ (1 / p) := mul_le_mul_of_nonneg_right hstep hKnn
      _ = _ := by ring
  -- (5.8)-(5.9) the bootstrap `S ≤ a₀ + b₁ S^θ`
  have hθ0 : (0:ℝ) < (p - 1) / p := div_pos hp10 hp0
  have h1θ : (0:ℝ) < 1 - (p - 1) / p := by
    have : (p - 1) / p < 1 := by rw [div_lt_one hp0]; linarith
    linarith
  have hck : (0:ℝ) < c₃ * κp := mul_pos hc₃0 hκ0
  obtain ⟨b₀, hb₀0, hb₀⟩ : ∃ b₀ : ℝ, 0 ≤ b₀ ∧ ∀ m : ℕ,
      (∫ x in Metric.ball x₀ R, ∑ i,
        (Ae (1 / ((m : ℝ) + 1)) (G m x)) i * (g x) i)
        ≤ b₀ * (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p)
          ^ ((p - 1) / p) := by
    refine ⟨(Γ ^ (p / (p - 1)) * (2:ℝ) ^ (p / 2)) ^ ((p - 1) / p)
      * Kg ^ (1 / p),
      mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg hK0 _), hb5⟩
  have hmaster : ∀ m : ℕ,
      vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p
        ≤ 2 * vol + (b₀ / (c₃ * κp))
          * (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p) ^ ((p - 1) / p) := by
    intro m
    have h1 := hlow5 m
    rw [hE4 m] at h1
    have h2 := le_trans h1 (hb₀ m)
    have he1 : (1 / ((m : ℝ) + 1)) ^ (p / 2) ≤ 1 :=
      Real.rpow_le_one (le_of_lt (hem0 m)) (hem1 m) (by positivity)
    have he0 : (0:ℝ) ≤ (1 / ((m : ℝ) + 1)) ^ (p / 2) :=
      Real.rpow_nonneg (le_of_lt (hem0 m)) _
    have h3 : c₃ * κp * ((∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p) - vol)
        ≤ b₀ * (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p)
          ^ ((p - 1) / p) := by
      refine le_trans ?_ h2
      have hvv : vol * (1 / ((m : ℝ) + 1)) ^ (p / 2) ≤ vol := by
        nlinarith [hvol0, he1, he0]
      nlinarith [hvv, hck]
    have h4 : (∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p) - vol
        ≤ (b₀ / (c₃ * κp))
          * (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p) ^ ((p - 1) / p) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hck]
      nlinarith [h3]
    linarith [h4]
  obtain ⟨E, hE0, hEb⟩ : ∃ E : ℝ, 0 ≤ E ∧ ∀ m : ℕ,
      vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p ≤ E := by
    have hb₁0 : (0:ℝ) ≤ b₀ / (c₃ * κp) := div_nonneg hb₀0 hck.le
    refine ⟨max (4 * vol) ((2 * (b₀ / (c₃ * κp))) ^ (1 / (1 - (p - 1) / p))),
      le_trans (by linarith [hvol0]) (le_max_left _ _), ?_⟩
    intro m
    rcases le_or_gt (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p) (4 * vol)
      with h | h
    · exact le_trans h (le_max_left _ _)
    · have hSpos : (0:ℝ) < vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p := by
        linarith [hvol0]
      have hSθ : (0:ℝ) < (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p)
          ^ ((p - 1) / p) := Real.rpow_pos_of_pos hSpos _
      have h1 : (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p) / 2
          ≤ (b₀ / (c₃ * κp))
            * (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p)
              ^ ((p - 1) / p) := by
        linarith [hmaster m]
      have h3 : (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p)
          = (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p)
              ^ (1 - (p - 1) / p)
            * (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p)
              ^ ((p - 1) / p) := by
        rw [← Real.rpow_add hSpos, sub_add_cancel, Real.rpow_one]
      have h7 : ((vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p)
            ^ (1 - (p - 1) / p) / 2)
          * (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p) ^ ((p - 1) / p)
        ≤ (b₀ / (c₃ * κp))
          * (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p)
            ^ ((p - 1) / p) := by
        have heq : ((vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p)
              ^ (1 - (p - 1) / p) / 2)
            * (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p) ^ ((p - 1) / p)
          = (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p) / 2 := by
          rw [div_mul_eq_mul_div, ← h3]
        rw [heq]
        exact h1
      have h8 : (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p)
          ^ (1 - (p - 1) / p) / 2 ≤ b₀ / (c₃ * κp) :=
        le_of_mul_le_mul_right h7 hSθ
      have h9 : (vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p)
          ^ (1 - (p - 1) / p) ≤ 2 * (b₀ / (c₃ * κp)) := by linarith [h8]
      have h10 : ((vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p)
          ^ (1 - (p - 1) / p)) ^ (1 / (1 - (p - 1) / p))
          = vol + ∫ x in Metric.ball x₀ R, ‖G m x‖ ^ p := by
        rw [← Real.rpow_mul hSpos.le, mul_one_div, div_self (ne_of_gt h1θ),
          Real.rpow_one]
      refine le_trans (le_of_eq h10.symm) (le_trans ?_ (le_max_right _ _))
      exact Real.rpow_le_rpow (Real.rpow_nonneg hSpos.le _) h9
        (div_pos one_pos h1θ).le
  -- (5b): the weight with the `g` term, at the power `p/2`
  have hsub3 : ∀ s t w : ℝ, 0 ≤ s → 0 ≤ t → 0 ≤ w →
      (s + t + w) ^ (p / 2) ≤ (3:ℝ) ^ (p / 2)
        * (s ^ (p / 2) + t ^ (p / 2) + w ^ (p / 2)) := by
    intro s t w hs ht hw
    have hp20 : (0:ℝ) < p / 2 := by linarith
    have hs' : s ≤ max s (max t w) := le_max_left _ _
    have ht' : t ≤ max s (max t w) :=
      le_trans (le_max_left t w) (le_max_right _ _)
    have hw' : w ≤ max s (max t w) :=
      le_trans (le_max_right t w) (le_max_right _ _)
    have hM0 : (0:ℝ) ≤ max s (max t w) := le_trans hs hs'
    have hstep : (s + t + w) ^ (p / 2)
        ≤ ((3:ℝ) * max s (max t w)) ^ (p / 2) :=
      Real.rpow_le_rpow (by linarith) (by linarith) hp20.le
    rw [Real.mul_rpow (by norm_num) hM0] at hstep
    refine le_trans hstep (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hsp : (0:ℝ) ≤ s ^ (p / 2) := Real.rpow_nonneg hs _
    have htp : (0:ℝ) ≤ t ^ (p / 2) := Real.rpow_nonneg ht _
    have hwp : (0:ℝ) ≤ w ^ (p / 2) := Real.rpow_nonneg hw _
    rcases max_cases s (max t w) with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; linarith
    · rcases max_cases t w with ⟨h2, -⟩ | ⟨h2, -⟩
      · rw [h1, h2]; linarith
      · rw [h1, h2]; linarith
  have hdom5 : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin n)),
      (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2)
        ≤ (3:ℝ) ^ (p / 2) * ((1 / ((m : ℝ) + 1)) ^ (p / 2)
          + ‖G m x‖ ^ p + ‖g x‖ ^ p) := by
    intro m x
    have h := hsub3 (1 / ((m : ℝ) + 1)) (‖G m x‖ ^ 2) (‖g x‖ ^ 2)
      (le_of_lt (hem0 m)) (sq_nonneg _) (sq_nonneg _)
    rwa [hid2 ‖G m x‖ p (norm_nonneg _), hid2 ‖g x‖ p (norm_nonneg _)] at h
  have hI1 : ∀ m : ℕ, IntegrableOn (fun x => (1 / ((m : ℝ) + 1)) ^ (p / 2)
      + ‖G m x‖ ^ p) (Metric.ball x₀ R) volume :=
    fun m => (integrable_const _).add (hYint m)
  have hbnd5 : ∀ m : ℕ, IntegrableOn (fun x => (3:ℝ) ^ (p / 2)
      * (((1 / ((m : ℝ) + 1)) ^ (p / 2) + ‖G m x‖ ^ p) + ‖g x‖ ^ p))
      (Metric.ball x₀ R) volume :=
    fun m => Integrable.const_mul ((hI1 m).add hKint) _
  have hint5 : ∀ m : ℕ, IntegrableOn (fun x =>
      (1 / ((m : ℝ) + 1) + ‖G m x‖ ^ 2 + ‖g x‖ ^ 2) ^ (p / 2))
      (Metric.ball x₀ R) volume := by
    intro m
    refine Integrable.mono' (hbnd5 m) (hWrpow m (p / 2))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hWp m x).le _)]
    exact hdom5 m x
  refine ⟨(3:ℝ) ^ (p / 2) * (E + Kg),
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith [hE0, hK0]),
    hint5, ?_⟩
  intro m
  have hmo := integral_mono (hint5 m) (hbnd5 m) (fun x => hdom5 m x)
  rw [integral_const_mul, integral_add (hI1 m) hKint,
    integral_add (integrable_const _) (hYint m), setIntegral_const,
    MeasureTheory.measureReal_def, smul_eq_mul, ← hvoldef, ← hKdef] at hmo
  have he1 : (1 / ((m : ℝ) + 1)) ^ (p / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt (hem0 m)) (hem1 m) (by positivity)
  have he0 : (0:ℝ) ≤ (1 / ((m : ℝ) + 1)) ^ (p / 2) :=
    Real.rpow_nonneg (le_of_lt (hem0 m)) _
  have hvv : vol * (1 / ((m : ℝ) + 1)) ^ (p / 2) ≤ vol := by
    nlinarith [hvol0, he1, he0]
  have h3p : (0:ℝ) < (3:ℝ) ^ (p / 2) := Real.rpow_pos_of_pos (by norm_num) _
  refine le_trans hmo ?_
  refine mul_le_mul_of_nonneg_left ?_ h3p.le
  linarith [hvv, hEb m]
