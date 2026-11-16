import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.CaccioppoliPowerWeight
import ManfrediThesis.MoserLocalBoundedness
import ManfrediThesis.DegenerateLimitTransfer
import ManfrediThesis.GradientSupEstimateEpsPos
import ManfrediThesis.SobolevExponentTwoBall
import ManfrediThesis.CitedDirichletW1p
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.WeakGradientVectorComp
import ManfrediThesis.WeakGradientRestrict
import ManfrediThesis.WeakGradientZeroExtend
open MeasureTheory

/-- Theorem 1: the sup bound for `(ε + |∇u|²)^{p/2}` by its mean on a larger
ball, with a constant depending only on `p`, `γ₁/γ₀` and `n`. -/
theorem GradientSupEstimate :
    ∀ (n : ℕ) (p r : ℝ), 2 ≤ n → 1 < p → 0 < r →
      CitedSobolevPoincareBall n →
      (∀ (ε' γ₀' γ₁' : ℝ)
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → CitedDirichletW1p n p ε' γ₀' γ₁' A') →
      (∀ (ε' γ₀' γ₁' : ℝ) (Ω' : Set (EuclideanSpace ℝ (Fin n)))
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → IsOpen Ω' → CitedRegularityEpsPos n p ε' γ₀' γ₁' Ω' A') →
      ∃ C : ℝ, 0 < C ∧
        ∀ (ε γ₀ γ₁ : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
          (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ),
          0 ≤ ε → 0 < γ₀ → γ₁ ≤ r * γ₀ → IsOpen Ω → 0 < R → A 0 = 0 →
          EllipticStructureQ12 n p ε γ₀ γ₁ Ω (fun _ _ h => A h) →
          IsWeakSolutionOn n p Ω (fun _ _ h => A h) (fun _ _ _ => 0) u g →
          Metric.closedBall x₀ R ⊆ Ω →
          ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))),
            (ε + ‖g x‖ ^ 2) ^ (p / 2)
              ≤ C / R ^ (n : ℝ) * ∫ y in Metric.ball x₀ R, (ε + ‖g y‖ ^ 2) ^ (p / 2) := by
  intro n p r hn hp hr hSP hC2 hC1
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hp0 : (0:ℝ) < p := by linarith
  -- the Step 1 argument, in the form both Step 1 and B4 use it
  have hposgamma : ∀ (ε' γ₀' γ₁' : ℝ) (S : Set (EuclideanSpace ℝ (Fin n)))
      (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      0 ≤ ε' → MeasurableSet S → 0 < volume S →
      EllipticStructureQ12 n p ε' γ₀' γ₁' S (fun _ _ h => A' h) → γ₀' ≤ γ₁' := by
    intro ε' γ₀' γ₁' S A' hε' hSm hSpos hQ'
    obtain ⟨i0⟩ : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
    obtain ⟨e1, he1def⟩ : ∃ e1 : EuclideanSpace ℝ (Fin n),
      e1 = EuclideanSpace.single i0 (1 : ℝ) := ⟨_, rfl⟩
    have hen : ‖e1‖ = 1 := by rw [he1def]; simp
    have hen2 : ‖e1‖ ^ 2 = 1 := by rw [hen]; norm_num
    have hguard : ε' + ‖e1‖ ^ 2 ≠ 0 := by
      rw [hen2]
      exact ne_of_gt (by linarith)
    have hneb : Filter.NeBot (ae (volume.restrict S)) := by
      refine ae_neBot.2 ?_
      simp only [ne_eq, Measure.restrict_eq_zero]
      exact hSpos.ne'
    obtain ⟨x, ⟨hx1, hx2⟩, hxS⟩ :=
      ((ae_restrict_of_ae (hQ'.Q1.and hQ'.Q2)).and (ae_restrict_mem hSm)).exists
    have hQ1 := hx1 hxS 0 e1 e1 hguard
    have hQ2 := hx2 hxS 0 e1 i0 i0 hguard
    have hsum : (∑ i, (fderiv ℝ (fun h => A' h) e1 e1) i * e1 i)
        = (fderiv ℝ (fun h => A' h) e1 e1) i0 := by
      rw [he1def]
      simp
    rw [hsum, hen2, mul_one] at hQ1
    rw [← he1def, hen2] at hQ2
    have hpow : (0:ℝ) < (ε' + 1) ^ (p / 2 - 1) :=
      Real.rpow_pos_of_pos (by linarith) _
    have hle : (fderiv ℝ (fun h => A' h) e1 e1) i0 ≤ γ₁' * (ε' + 1) ^ (p / 2 - 1) :=
      le_trans (le_abs_self _) hQ2
    exact le_of_mul_le_mul_right (by linarith) hpow
  -- the six clauses of `EllipticStructureQ12` are inherited by subsets
  have hrestr : ∀ (ε' γ₀' γ₁' : ℝ) (S : Set (EuclideanSpace ℝ (Fin n)))
      (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      EllipticStructureQ12 n p ε' γ₀' γ₁' Set.univ (fun _ _ h => A' h) →
      EllipticStructureQ12 n p ε' γ₀' γ₁' S (fun _ _ h => A' h) := by
    intro ε' γ₀' γ₁' S A' h
    exact
      { meas_x := h.meas_x
        cont_zh := h.cont_zh
        hcont := fun y _ z => h.hcont y (Set.mem_univ y) z
        hdiff := fun y _ z => h.hdiff y (Set.mem_univ y) z
        Q1 := h.Q1.mono fun y hy _ => hy (Set.mem_univ y)
        Q2 := h.Q2.mono fun y hy _ => hy (Set.mem_univ y) }
  have hunivpos : 0 < volume (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
    isOpen_univ.measure_pos volume ⟨0, trivial⟩
  -- Step 0 (`.tex` l.112-138): the constants, chosen before all the data.
  obtain ⟨r', hr'0, hDLT⟩ := DegenerateLimitTransfer n p r hn hp hr
  obtain ⟨rb, hrb0, hrbr, hrbr'⟩ : ∃ s : ℝ, 0 < s ∧ r ≤ s ∧ r' ≤ s :=
    ⟨max r r', lt_of_lt_of_le hr (le_max_left _ _), le_max_left _ _, le_max_right _ _⟩
  obtain ⟨C₁, hC₁0, hClaimA⟩ :=
    GradientSupEstimateEpsPos n p rb hn hp hrb0 hSP hC1
  obtain ⟨κ, hκ0, hκ1, hκ2⟩ : ∃ κ : ℝ, 0 < κ ∧ 1 ≤ κ ∧ (2:ℝ) ^ (p / 2) ≤ κ :=
    ⟨max 1 ((2:ℝ) ^ (p / 2)), lt_of_lt_of_le one_pos (le_max_left _ _),
      le_max_left _ _, le_max_right _ _⟩
  refine ⟨C₁ * κ ^ 2 * (2:ℝ) ^ (p / 2), by positivity, ?_⟩
  intro ε γ₀ γ₁ Ω A u g x₀ R hε hγ₀ hγ₁r hΩ hR hA0 hQ hsol hball
  have hballsub : Metric.ball x₀ R ⊆ Ω :=
    subset_trans Metric.ball_subset_closedBall hball
  have hΩpos : 0 < volume Ω :=
    lt_of_lt_of_le (Metric.measure_ball_pos volume x₀ hR) (measure_mono hballsub)
  have hneb : Filter.NeBot (ae (volume.restrict Ω)) := by
    refine ae_neBot.2 ?_
    simp only [ne_eq, Measure.restrict_eq_zero]
    exact hΩpos.ne'
  -- Step 1 (`.tex` l.139-164): `γ₀ ≤ γ₁`, so `γ₁ > 0`.
  have hγ₁0 : 0 < γ₁ :=
    lt_of_lt_of_le hγ₀ (hposgamma ε γ₀ γ₁ Ω A hε hΩ.measurableSet hΩpos hQ)
  have hγ₁rb : γ₁ ≤ rb * γ₀ :=
    le_trans hγ₁r (mul_le_mul_of_nonneg_right hrbr hγ₀.le)
  have hCle : C₁ ≤ C₁ * κ ^ 2 * (2:ℝ) ^ (p / 2) := by
    have h2 : (1:ℝ) ≤ (2:ℝ) ^ (p / 2) := by
      have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1)
        (by norm_num : (1:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ p / 2)
      rwa [Real.one_rpow] at h
    have hκsq : (1:ℝ) ≤ κ ^ 2 := by nlinarith [hκ1]
    calc C₁ = C₁ * 1 * 1 := by ring
      _ ≤ C₁ * κ ^ 2 * (2:ℝ) ^ (p / 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hκsq hC₁0.le) h2 (by norm_num)
            (by positivity)
  rcases eq_or_lt_of_le hε with hε0 | hεpos
  · -- Step 3 (`.tex` l.457-740): the case `ε = 0`.
    subst hε0
    -- B1 (`.tex` l.459-487): the structure conditions move from `Ω` to `ℝⁿ`.
    -- The field is `(x, z, h) ↦ A h`, so of the six clauses of
    -- `EllipticStructureQ12` the two Carathéodory ones mention no domain and
    -- carry over verbatim; `hcont` and `hdiff` are `∀ x ∈ Ω` of an assertion
    -- free of `x` and `z`, and `Ω` is nonempty; `Q1` and `Q2` are `∀ᵐ x ∈ Ω` of
    -- such an assertion and `volume Ω > 0` (`hΩpos`), so a single good point
    -- promotes them.  In scope: `hQ`, `hΩ`, `hΩpos`, `hballsub`, `hR`, `hneb`.
    have hB1 : EllipticStructureQ12 n p 0 γ₀ γ₁ Set.univ (fun _ _ h => A h) := by
      obtain ⟨x, ⟨hx1, hx2⟩, hxΩ⟩ :=
        ((ae_restrict_of_ae (hQ.Q1.and hQ.Q2)).and
          (ae_restrict_mem hΩ.measurableSet)).exists
      have hx' : x₀ ∈ Ω := hballsub (Metric.mem_ball_self hR)
      exact
        { meas_x := hQ.meas_x
          cont_zh := hQ.cont_zh
          hcont := fun y _ z => hQ.hcont x₀ hx' z
          hdiff := fun y _ z => hQ.hdiff x₀ hx' z
          Q1 := Filter.Eventually.of_forall fun y _ => hx1 hxΩ
          Q2 := Filter.Eventually.of_forall fun y _ => hx2 hxΩ }
    -- B2' (`.tex` l.556-570): `u ∈ W^{1,p}(B_R)` with weak gradient `g`, by
    -- clause (4) of `WeakGradientRestrict` at `q = p`, `Ω' = ball x₀ R`, using
    -- `closure (ball x₀ R) = closedBall x₀ R` (`R > 0`), its compactness,
    -- `hball : closedBall x₀ R ⊆ Ω` and `hsol.1 : MemW1pLocOn n p Ω u g`.
    have hB2' : MemW1pOn n p (Metric.ball x₀ R) u g := by
      have hn1 : 1 ≤ n := le_trans (by norm_num) hn
      have hcl : closure (Metric.ball x₀ R) = Metric.closedBall x₀ R :=
        closure_ball x₀ (ne_of_gt hR)
      refine (WeakGradientRestrict n p hn1 hp.le Ω (Metric.ball x₀ R) u g hΩ
        Metric.isOpen_ball hballsub).2.2.2 hsol.1 ?_ ?_
      · rw [hcl]
        exact isCompact_closedBall x₀ R
      · rw [hcl]
        exact hball
    -- B2 (`.tex` l.488-537): `u` is a weak solution in `B_R`.  The membership
    -- clause is clause (2) of `WeakGradientRestrict`; for the test clause,
    -- `WeakGradientZeroExtend` turns a test pair `(φ, gφ)` on `B_R` into the
    -- admissible pair `(φ, 1_{B_R} gφ)` on `Ω`, and the `Ω`-integrand vanishes
    -- off `tsupport φ ⊆ B_R`, so both the integrability and the vanishing of
    -- the integral transfer to the ball.
    have hB2 : IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h)
        (fun _ _ _ => 0) u g := by
      have hn1 : 1 ≤ n := le_trans (by norm_num) hn
      refine ⟨(WeakGradientRestrict n p hn1 hp.le Ω (Metric.ball x₀ R) u g hΩ
        Metric.isOpen_ball hballsub).2.1 hsol.1, ?_⟩
      intro φ gφ hφ hcs hts
      have hts' : tsupport φ ⊆ Ω := subset_trans hts hballsub
      have hext := WeakGradientZeroExtend n p hn1 hp.le Ω x₀ R φ gφ hΩ hballsub
        hφ hcs hts
      obtain ⟨hintΩ, hzeroΩ⟩ :=
        hsol.2 φ ((Metric.ball x₀ R).indicator gφ) hext hcs hts'
      have hFzero : ∀ y : EuclideanSpace ℝ (Fin n), y ∉ Metric.ball x₀ R →
          (∑ i, (A (g y)) i * ((Metric.ball x₀ R).indicator gφ y) i)
            + (0:ℝ) * φ y = 0 := by
        intro y hy
        rw [Set.indicator_of_notMem hy]
        simp
      have hagree : ∀ y ∈ Metric.ball x₀ R,
          (∑ i, (A (g y)) i * ((Metric.ball x₀ R).indicator gφ y) i) + (0:ℝ) * φ y
            = (∑ i, (A (g y)) i * gφ y i) + (0:ℝ) * φ y := by
        intro y hy
        rw [Set.indicator_of_mem hy]
      have hintball : IntegrableOn (fun y =>
          (∑ i, (A (g y)) i * ((Metric.ball x₀ R).indicator gφ y) i) + (0:ℝ) * φ y)
          (Metric.ball x₀ R) volume := hintΩ.mono_set hballsub
      have haeeq : (fun y => (∑ i, (A (g y)) i
            * ((Metric.ball x₀ R).indicator gφ y) i) + (0:ℝ) * φ y)
          =ᵐ[volume.restrict (Metric.ball x₀ R)]
          fun y => (∑ i, (A (g y)) i * gφ y i) + (0:ℝ) * φ y :=
        (ae_restrict_iff' measurableSet_ball).2
          (Filter.Eventually.of_forall hagree)
      refine ⟨hintball.congr haeeq, ?_⟩
      have h1 : (∫ y in Metric.ball x₀ R,
            ((∑ i, (A (g y)) i * gφ y i) + (0:ℝ) * φ y))
          = ∫ y in Metric.ball x₀ R,
            ((∑ i, (A (g y)) i * ((Metric.ball x₀ R).indicator gφ y) i)
              + (0:ℝ) * φ y) :=
        (setIntegral_congr_fun measurableSet_ball hagree).symm
      have h2 : (∫ y in Metric.ball x₀ R,
            ((∑ i, (A (g y)) i * ((Metric.ball x₀ R).indicator gφ y) i)
              + (0:ℝ) * φ y))
          = ∫ y in Ω, ((∑ i, (A (g y)) i
              * ((Metric.ball x₀ R).indicator gφ y) i) + (0:ℝ) * φ y) := by
        rw [← integral_indicator measurableSet_ball,
          ← integral_indicator hΩ.measurableSet]
        congr 1
        funext y
        by_cases hy : y ∈ Metric.ball x₀ R
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hballsub hy)]
        · rw [Set.indicator_of_notMem hy]
          by_cases hy2 : y ∈ Ω
          · rw [Set.indicator_of_mem hy2, hFzero y hy]
          · rw [Set.indicator_of_notMem hy2]
      rw [h1, h2]
      exact hzeroΩ
    -- B3 (`.tex` l.538-570): the approximating sequence.
    obtain ⟨em, Ae, U, G, hem0, hemto, hAeQ, hUsol, hUzero, hLp, haeconv⟩ :=
      hDLT γ₀ γ₁ hγ₀ hγ₁r A hA0 hB1 hC2 x₀ R u g hR hB2' hB2
    -- B4 (`.tex` l.571-594): Claim A at `ε := em m`, the field `Ae m`, the
    -- solution `(U m, G m)` on `ball x₀ R`, centre `x₀`, radius `ρ < R`.  Its
    -- `γ₀^{(m)}, γ₁^{(m)}` come from `hAeQ m`; `γ₁^{(m)} > 0` by the Step 1
    -- argument run again for `Ae m` on `ball x₀ R`, legitimate because the six
    -- clauses of `EllipticStructureQ12` are inherited by subsets.
    have hB4 : ∀ ρ : ℝ, 0 < ρ → ρ < R → ∀ m : ℕ,
        ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (ρ / 2))),
          (em m + ‖G m x‖ ^ 2) ^ (p / 2)
            ≤ C₁ / ρ ^ (n : ℝ)
              * ∫ z in Metric.ball x₀ ρ, (em m + ‖G m z‖ ^ 2) ^ (p / 2) := by
      intro ρ hρ0 hρR m
      obtain ⟨-, γ₀m, γ₁m, hγ₀m, hγ₁m, hQm⟩ := hAeQ m
      have hγ₁m0 : 0 < γ₁m :=
        lt_of_lt_of_le hγ₀m (hposgamma (em m) γ₀m γ₁m Set.univ (Ae m)
          (hem0 m).le MeasurableSet.univ hunivpos hQm)
      have hγ₁mrb : γ₁m ≤ rb * γ₀m :=
        le_trans hγ₁m (mul_le_mul_of_nonneg_right hrbr' hγ₀m.le)
      exact hClaimA (em m) γ₀m γ₁m (Metric.ball x₀ R) (Ae m) (U m) (G m) x₀ ρ
        (hem0 m) hγ₀m hγ₁m0 hγ₁mrb Metric.isOpen_ball hρ0
        (hrestr (em m) γ₀m γ₁m (Metric.ball x₀ R) (Ae m) hQm) (hUsol m)
        (Metric.closedBall_subset_ball hρR)
    -- B5 (`.tex` l.595-691): the limit in `m` at a fixed `ρ ∈ (0, R)`.  The
    -- right-hand side of B4 is bounded by `κ e_m^{p/2}|B_R| + κ² 2^{p/2}(∫_{B_R}
    -- |g|^p + ∫_{B_R}|g_m - g|^p)` using `(a+b)^{p/2} ≤ κ(a^{p/2}+b^{p/2})` twice
    -- and `|g_m|² ≤ 2|g|² + 2|g_m-g|²`; the first and last terms vanish as
    -- `m → ∞` by `hemto` and `hLp`, and the left-hand side converges pointwise
    -- a.e. by `haeconv`.  Integrability of `|g_m - g|^p` on `B_R` comes from
    -- `hUzero m`, NOT from `hLp` (the integral of a non-integrable function is
    -- `0`).  In scope: `hB4`, `hem0`, `hemto`, `hLp`, `haeconv`, `hUzero`,
    -- `hsol`, `hball`, `hκ1`, `hκ2`.
    have hB5 : ∀ ρ : ℝ, 0 < ρ → ρ < R →
        ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (ρ / 2))),
          ((0:ℝ) + ‖g x‖ ^ 2) ^ (p / 2)
            ≤ C₁ * κ ^ 2 * (2:ℝ) ^ (p / 2) / ρ ^ (n : ℝ)
              * ∫ z in Metric.ball x₀ R, ((0:ℝ) + ‖g z‖ ^ 2) ^ (p / 2) := by
      intro ρ hρ0 hρR
      have hp20 : (0:ℝ) < p / 2 := by linarith
      have h2p : (0:ℝ) < (2:ℝ) ^ (p / 2) := Real.rpow_pos_of_pos (by norm_num) _
      have hρn : (0:ℝ) < ρ ^ (n : ℝ) := Real.rpow_pos_of_pos hρ0 _
      -- `(a + b)^{p/2} ≤ κ (a^{p/2} + b^{p/2})`, one case, since `2^{p/2} ≤ κ`
      have hsub : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
          (a + b) ^ (p / 2) ≤ κ * (a ^ (p / 2) + b ^ (p / 2)) := by
        intro a b ha hb
        have hM0 : (0:ℝ) ≤ max a b := le_trans ha (le_max_left _ _)
        have h1 : a + b ≤ 2 * max a b := by
          have h3 := le_max_left a b
          have h4 := le_max_right a b
          linarith
        have h2 : (a + b) ^ (p / 2) ≤ ((2:ℝ) * max a b) ^ (p / 2) :=
          Real.rpow_le_rpow (by linarith) h1 hp20.le
        rw [Real.mul_rpow (by norm_num) hM0] at h2
        have h3 : (max a b) ^ (p / 2) ≤ a ^ (p / 2) + b ^ (p / 2) := by
          rcases le_total a b with h | h
          · rw [max_eq_right h]
            have := Real.rpow_nonneg ha (p / 2)
            linarith
          · rw [max_eq_left h]
            have := Real.rpow_nonneg hb (p / 2)
            linarith
        calc (a + b) ^ (p / 2) ≤ (2:ℝ) ^ (p / 2) * (max a b) ^ (p / 2) := h2
          _ ≤ κ * (a ^ (p / 2) + b ^ (p / 2)) :=
              mul_le_mul hκ2 h3 (Real.rpow_nonneg hM0 _) hκ0.le
      have hid2 : ∀ t : ℝ, 0 ≤ t → (t ^ 2 : ℝ) ^ (p / 2) = t ^ p := by
        intro t ht
        rcases eq_or_lt_of_le ht with h | h
        · rw [← h]
          rw [show ((0:ℝ) ^ 2) = 0 by norm_num,
            Real.zero_rpow (ne_of_gt hp20), Real.zero_rpow (ne_of_gt hp0)]
        · have ht2 : (t ^ 2 : ℝ) = t ^ (2:ℝ) := by
            rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
          rw [ht2, ← Real.rpow_mul h.le]
          congr 1
          ring
      -- the pointwise bound of B5
      have hptw : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin n)),
          (em m + ‖G m x‖ ^ 2) ^ (p / 2)
            ≤ κ * (em m) ^ (p / 2)
              + κ ^ 2 * (2:ℝ) ^ (p / 2) * (‖g x‖ ^ p + ‖G m x - g x‖ ^ p) := by
        intro m x
        have hgm : ‖G m x‖ ^ 2 ≤ 2 * ‖g x‖ ^ 2 + 2 * ‖G m x - g x‖ ^ 2 := by
          have h1 : ‖G m x‖ ≤ ‖g x‖ + ‖G m x - g x‖ := by
            calc ‖G m x‖ = ‖g x + (G m x - g x)‖ := by congr 1; abel
              _ ≤ ‖g x‖ + ‖G m x - g x‖ := norm_add_le _ _
          nlinarith [h1, norm_nonneg (g x), norm_nonneg (G m x - g x),
            norm_nonneg (G m x), sq_nonneg (‖g x‖ - ‖G m x - g x‖)]
        have hstep1 : (em m + ‖G m x‖ ^ 2) ^ (p / 2)
            ≤ (em m + (2 * ‖g x‖ ^ 2 + 2 * ‖G m x - g x‖ ^ 2)) ^ (p / 2) := by
          refine Real.rpow_le_rpow ?_ (by linarith) hp20.le
          nlinarith [(hem0 m).le, sq_nonneg ‖G m x‖]
        have hstep2 : (em m + (2 * ‖g x‖ ^ 2 + 2 * ‖G m x - g x‖ ^ 2)) ^ (p / 2)
            ≤ κ * ((em m) ^ (p / 2)
              + (2 * ‖g x‖ ^ 2 + 2 * ‖G m x - g x‖ ^ 2) ^ (p / 2)) :=
          hsub _ _ (hem0 m).le (by positivity)
        have hstep3 : (2 * ‖g x‖ ^ 2 + 2 * ‖G m x - g x‖ ^ 2) ^ (p / 2)
            ≤ (2:ℝ) ^ (p / 2) * (κ * (‖g x‖ ^ p + ‖G m x - g x‖ ^ p)) := by
          have he : (2 * ‖g x‖ ^ 2 + 2 * ‖G m x - g x‖ ^ 2)
              = 2 * (‖g x‖ ^ 2 + ‖G m x - g x‖ ^ 2) := by ring
          rw [he, Real.mul_rpow (by norm_num) (by positivity)]
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt h2p)
          have h := hsub (‖g x‖ ^ 2) (‖G m x - g x‖ ^ 2) (sq_nonneg _) (sq_nonneg _)
          rwa [hid2 _ (norm_nonneg (g x)), hid2 _ (norm_nonneg (G m x - g x))] at h
        have hκnn : (0:ℝ) ≤ κ := hκ0.le
        nlinarith [hstep1, hstep2, hstep3, hκnn, h2p,
          Real.rpow_nonneg (hem0 m).le (p / 2),
          Real.rpow_nonneg (norm_nonneg (g x)) p,
          Real.rpow_nonneg (norm_nonneg (G m x - g x)) p]
      -- integrability on the big ball
      have hpne : (ENNReal.ofReal p) ≠ 0 := by
        simp [ENNReal.ofReal_eq_zero, not_le, hp0]
      have hptop : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hgLpK : MemLp g (ENNReal.ofReal p)
          (volume.restrict (Metric.closedBall x₀ R)) :=
        (hsol.1.2 (Metric.closedBall x₀ R) (isCompact_closedBall x₀ R) hball).2
      have hgLp : MemLp g (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R)) :=
        hgLpK.mono_measure (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
      have hgp : IntegrableOn (fun z => ‖g z‖ ^ p) (Metric.ball x₀ R) volume := by
        have h := hgLp.integrable_norm_rpow hpne hptop
        rwa [ENNReal.toReal_ofReal hp0.le] at h
      have hdLp : ∀ m : ℕ, MemLp (fun z => G m z - g z) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R)) := fun m => (hUzero m).1.2.2
      have hdp : ∀ m : ℕ, IntegrableOn (fun z => ‖G m z - g z‖ ^ p)
          (Metric.ball x₀ R) volume := by
        intro m
        have h := (hdLp m).integrable_norm_rpow hpne hptop
        rwa [ENNReal.toReal_ofReal hp0.le] at h
      have hGLp : ∀ m : ℕ, MemLp (G m) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R)) := by
        intro m
        have h := (hdLp m).add hgLp
        exact MemLp.ae_eq (Filter.Eventually.of_forall fun z => by simp) h
      have hfinm : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) := by
        refine ⟨?_⟩
        rw [Measure.restrict_apply_univ]
        exact measure_ball_lt_top
      have hRHSint : ∀ m : ℕ, IntegrableOn (fun z =>
          κ * (em m) ^ (p / 2)
            + κ ^ 2 * (2:ℝ) ^ (p / 2) * (‖g z‖ ^ p + ‖G m z - g z‖ ^ p))
          (Metric.ball x₀ R) volume := by
        intro m
        have hI1 : IntegrableOn
            (fun _ : EuclideanSpace ℝ (Fin n) => κ * (em m) ^ (p / 2))
            (Metric.ball x₀ R) volume := integrable_const _
        have hI3 : IntegrableOn (fun z => κ ^ 2 * (2:ℝ) ^ (p / 2)
            * (‖g z‖ ^ p + ‖G m z - g z‖ ^ p)) (Metric.ball x₀ R) volume :=
          (hgp.add (hdp m)).const_mul _
        exact hI1.add hI3
      have hLHSint : ∀ m : ℕ, IntegrableOn
          (fun z => (em m + ‖G m z‖ ^ 2) ^ (p / 2)) (Metric.ball x₀ R) volume := by
        intro m
        have hmeas : AEStronglyMeasurable
            (fun z => (em m + ‖G m z‖ ^ 2) ^ (p / 2))
            (volume.restrict (Metric.ball x₀ R)) := by
          have hc : Continuous (fun t : ℝ => (em m + t) ^ (p / 2)) :=
            (continuous_const.add continuous_id).rpow_const fun t => Or.inr hp20.le
          exact hc.comp_aestronglyMeasurable
            ((hGLp m).aestronglyMeasurable.norm.pow 2)
        refine Integrable.mono' (hRHSint m) hmeas
          (Filter.Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg
            (add_nonneg (hem0 m).le (sq_nonneg _)) _)]
        exact hptw m z
      -- the integral bound
      have hbig : ∀ m : ℕ, (∫ z in Metric.ball x₀ ρ, (em m + ‖G m z‖ ^ 2) ^ (p / 2))
          ≤ κ * (em m) ^ (p / 2) * (volume (Metric.ball x₀ R)).toReal
            + κ ^ 2 * (2:ℝ) ^ (p / 2)
              * ((∫ z in Metric.ball x₀ R, ‖g z‖ ^ p)
                + ∫ z in Metric.ball x₀ R, ‖G m z - g z‖ ^ p) := by
        intro m
        have hsubset : Metric.ball x₀ ρ ⊆ Metric.ball x₀ R :=
          Metric.ball_subset_ball hρR.le
        have h1 : (∫ z in Metric.ball x₀ ρ, (em m + ‖G m z‖ ^ 2) ^ (p / 2))
            ≤ ∫ z in Metric.ball x₀ R, (em m + ‖G m z‖ ^ 2) ^ (p / 2) := by
          refine setIntegral_mono_set (hLHSint m)
            (Filter.Eventually.of_forall fun z =>
              Real.rpow_nonneg (add_nonneg (hem0 m).le (sq_nonneg _)) _)
            (LE.le.eventuallyLE hsubset)
        refine le_trans h1 ?_
        have h2 := integral_mono (hLHSint m) (hRHSint m) (fun z => hptw m z)
        refine le_trans h2 (le_of_eq ?_)
        have hI1 : IntegrableOn
            (fun _ : EuclideanSpace ℝ (Fin n) => κ * (em m) ^ (p / 2))
            (Metric.ball x₀ R) volume := integrable_const _
        have hI2 : IntegrableOn (fun z => ‖g z‖ ^ p + ‖G m z - g z‖ ^ p)
            (Metric.ball x₀ R) volume := hgp.add (hdp m)
        have hI3 : IntegrableOn (fun z => κ ^ 2 * (2:ℝ) ^ (p / 2)
            * (‖g z‖ ^ p + ‖G m z - g z‖ ^ p)) (Metric.ball x₀ R) volume :=
          hI2.const_mul _
        have e1 : (∫ _z in Metric.ball x₀ R, κ * (em m) ^ (p / 2))
            = κ * (em m) ^ (p / 2) * (volume (Metric.ball x₀ R)).toReal := by
          rw [setIntegral_const, MeasureTheory.measureReal_def, smul_eq_mul]
          ring
        have e2 : (∫ z in Metric.ball x₀ R, κ ^ 2 * (2:ℝ) ^ (p / 2)
              * (‖g z‖ ^ p + ‖G m z - g z‖ ^ p))
            = κ ^ 2 * (2:ℝ) ^ (p / 2)
              * ((∫ z in Metric.ball x₀ R, ‖g z‖ ^ p)
                + ∫ z in Metric.ball x₀ R, ‖G m z - g z‖ ^ p) := by
          rw [integral_const_mul, integral_add hgp (hdp m)]
        rw [integral_add hI1 hI3, e1, e2]
      -- the limit in `m`
      have hemp : Filter.Tendsto (fun m : ℕ => (em m) ^ (p / 2))
          Filter.atTop (nhds 0) := by
        have hc : Filter.Tendsto (fun t : ℝ => t ^ (p / 2))
            (nhds 0) (nhds ((0:ℝ) ^ (p / 2))) :=
          (Real.continuousAt_rpow_const (0:ℝ) _ (Or.inr hp20.le)).tendsto
        rw [Real.zero_rpow (ne_of_gt hp20)] at hc
        exact (hc.comp hemto).congr fun m => rfl
      have hto : Filter.Tendsto (fun m : ℕ => C₁ / ρ ^ (n : ℝ)
          * (κ * (em m) ^ (p / 2) * (volume (Metric.ball x₀ R)).toReal
            + κ ^ 2 * (2:ℝ) ^ (p / 2)
              * ((∫ z in Metric.ball x₀ R, ‖g z‖ ^ p)
                + ∫ z in Metric.ball x₀ R, ‖G m z - g z‖ ^ p)))
          Filter.atTop
          (nhds (C₁ * κ ^ 2 * (2:ℝ) ^ (p / 2) / ρ ^ (n : ℝ)
            * ∫ z in Metric.ball x₀ R, ((0:ℝ) + ‖g z‖ ^ 2) ^ (p / 2))) := by
        have h1 : Filter.Tendsto (fun m : ℕ =>
            κ * (em m) ^ (p / 2) * (volume (Metric.ball x₀ R)).toReal
              + κ ^ 2 * (2:ℝ) ^ (p / 2)
                * ((∫ z in Metric.ball x₀ R, ‖g z‖ ^ p)
                  + ∫ z in Metric.ball x₀ R, ‖G m z - g z‖ ^ p))
            Filter.atTop
            (nhds (κ * 0 * (volume (Metric.ball x₀ R)).toReal
              + κ ^ 2 * (2:ℝ) ^ (p / 2)
                * ((∫ z in Metric.ball x₀ R, ‖g z‖ ^ p) + 0))) :=
          ((hemp.const_mul κ).mul_const _).add
            (((tendsto_const_nhds.add hLp)).const_mul _)
        have h2 := h1.const_mul (C₁ / ρ ^ (n : ℝ))
        have heq : (∫ z in Metric.ball x₀ R, ((0:ℝ) + ‖g z‖ ^ 2) ^ (p / 2))
            = ∫ z in Metric.ball x₀ R, ‖g z‖ ^ p := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          show ((0:ℝ) + ‖g z‖ ^ 2) ^ (p / 2) = ‖g z‖ ^ p
          rw [zero_add, hid2 _ (norm_nonneg (g z))]
        have hval : C₁ / ρ ^ (n : ℝ)
            * (κ * 0 * (volume (Metric.ball x₀ R)).toReal
              + κ ^ 2 * (2:ℝ) ^ (p / 2)
                * ((∫ z in Metric.ball x₀ R, ‖g z‖ ^ p) + 0))
            = C₁ * κ ^ 2 * (2:ℝ) ^ (p / 2) / ρ ^ (n : ℝ)
              * ∫ z in Metric.ball x₀ R, ‖g z‖ ^ p := by ring
        rw [heq, ← hval]
        exact h2
      -- collect the exceptional sets and pass to the limit
      have hB4all : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ∀ m : ℕ, x ∈ Metric.ball x₀ (ρ / 2) →
            (em m + ‖G m x‖ ^ 2) ^ (p / 2)
              ≤ C₁ / ρ ^ (n : ℝ)
                * ∫ z in Metric.ball x₀ ρ, (em m + ‖G m z‖ ^ 2) ^ (p / 2) := by
        rw [ae_all_iff]
        intro m
        rw [← ae_restrict_iff' measurableSet_ball]
        exact hB4 ρ hρ0 hρR m
      have hconvall : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          x ∈ Metric.ball x₀ R →
            Filter.Tendsto (fun m => G m x) Filter.atTop (nhds (g x)) :=
        (ae_restrict_iff' measurableSet_ball).1 haeconv
      filter_upwards [ae_restrict_of_ae hB4all, ae_restrict_of_ae hconvall,
        ae_restrict_mem measurableSet_ball] with x hx hconv hxmem
      have hxR : x ∈ Metric.ball x₀ R :=
        Metric.ball_subset_ball (by linarith) hxmem
      have hlhs : Filter.Tendsto (fun m : ℕ => (em m + ‖G m x‖ ^ 2) ^ (p / 2))
          Filter.atTop (nhds (((0:ℝ) + ‖g x‖ ^ 2) ^ (p / 2))) := by
        have hb : Filter.Tendsto (fun m : ℕ => em m + ‖G m x‖ ^ 2)
            Filter.atTop (nhds ((0:ℝ) + ‖g x‖ ^ 2)) :=
          hemto.add ((hconv hxR).norm.pow 2)
        have hc : ContinuousAt (fun t : ℝ => t ^ (p / 2)) ((0:ℝ) + ‖g x‖ ^ 2) :=
          Real.continuousAt_rpow_const _ _ (Or.inr hp20.le)
        exact (hc.tendsto.comp hb).congr fun m => rfl
      refine le_of_tendsto_of_tendsto hlhs hto
        (Filter.Eventually.of_forall fun m => ?_)
      refine le_trans (hx m hxmem) ?_
      exact mul_le_mul_of_nonneg_left (hbig m) (div_nonneg hC₁0.le hρn.le)
    -- B6 (`.tex` l.692-717): the limit in `ρ`.
    obtain ⟨rj, hrj0, hrjR, hrjto⟩ : ∃ f : ℕ → ℝ, (∀ j, 0 < f j) ∧ (∀ j, f j < R)
        ∧ Filter.Tendsto f Filter.atTop (nhds R) := by
      refine ⟨fun j => R * (1 - (1/2:ℝ) ^ (j + 1)), ?_, ?_, ?_⟩
      · intro j
        have h1 : (1/2:ℝ) ^ (j + 1) < 1 := by
          refine pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
        nlinarith [hR, h1]
      · intro j
        have h1 : (0:ℝ) < (1/2:ℝ) ^ (j + 1) := by positivity
        nlinarith [hR, h1]
      · have h1 : Filter.Tendsto (fun j : ℕ => (1/2:ℝ) ^ (j + 1))
            Filter.atTop (nhds 0) := by
          have h2 : Filter.Tendsto (fun j : ℕ => (1/2:ℝ) ^ j)
              Filter.atTop (nhds 0) :=
            tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
          exact h2.comp (Filter.tendsto_add_atTop_nat 1)
        have h3 : Filter.Tendsto (fun j : ℕ => R * (1 - (1/2:ℝ) ^ (j + 1)))
            Filter.atTop (nhds (R * (1 - 0))) :=
          Filter.Tendsto.const_mul R (Filter.Tendsto.sub tendsto_const_nhds h1)
        simpa using h3
    have hall : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ∀ j : ℕ, x ∈ Metric.ball x₀ (rj j / 2) →
          ((0:ℝ) + ‖g x‖ ^ 2) ^ (p / 2)
            ≤ C₁ * κ ^ 2 * (2:ℝ) ^ (p / 2) / (rj j) ^ (n : ℝ)
              * ∫ z in Metric.ball x₀ R, ((0:ℝ) + ‖g z‖ ^ 2) ^ (p / 2) := by
      rw [ae_all_iff]
      intro j
      rw [← ae_restrict_iff' measurableSet_ball]
      exact hB5 (rj j) (hrj0 j) (hrjR j)
    have hRn : (0:ℝ) < R ^ (n : ℝ) := Real.rpow_pos_of_pos hR _
    have hFto : Filter.Tendsto
        (fun j : ℕ => C₁ * κ ^ 2 * (2:ℝ) ^ (p / 2) / (rj j) ^ (n : ℝ)
          * ∫ z in Metric.ball x₀ R, ((0:ℝ) + ‖g z‖ ^ 2) ^ (p / 2))
        Filter.atTop
        (nhds (C₁ * κ ^ 2 * (2:ℝ) ^ (p / 2) / R ^ (n : ℝ)
          * ∫ z in Metric.ball x₀ R, ((0:ℝ) + ‖g z‖ ^ 2) ^ (p / 2))) := by
      have hc : ContinuousAt (fun t : ℝ => t ^ (n : ℝ)) R :=
        Real.continuousAt_rpow_const R (n : ℝ) (Or.inl (ne_of_gt hR))
      have hrpow : Filter.Tendsto (fun j : ℕ => (rj j) ^ (n : ℝ))
          Filter.atTop (nhds (R ^ (n : ℝ))) :=
        (hc.tendsto.comp hrjto).congr fun j => rfl
      exact ((tendsto_const_nhds.div hrpow (ne_of_gt hRn)).mul tendsto_const_nhds)
    filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_ball]
      with x hx hxmem
    refine ge_of_tendsto hFto ?_
    have hlt : dist x x₀ < R / 2 := Metric.mem_ball.1 hxmem
    have h2 : Filter.Tendsto (fun j : ℕ => rj j / 2) Filter.atTop (nhds (R / 2)) :=
      hrjto.div_const 2
    filter_upwards [h2.eventually (lt_mem_nhds hlt)] with j hj
    exact hx j (Metric.mem_ball.2 hj)
  · -- Step 2 (`.tex` l.442-456): the case `ε > 0`, directly from Claim A.
    have h := hClaimA ε γ₀ γ₁ Ω A u g x₀ R hεpos hγ₀ hγ₁0 hγ₁rb hΩ hR hQ hsol hball
    have hint0 : (0:ℝ) ≤ ∫ z in Metric.ball x₀ R, (ε + ‖g z‖ ^ 2) ^ (p / 2) :=
      integral_nonneg fun z => Real.rpow_nonneg (by positivity) _
    have hRn : (0:ℝ) < R ^ (n : ℝ) := Real.rpow_pos_of_pos hR _
    filter_upwards [h] with x hx
    refine le_trans hx ?_
    have h1 : C₁ / R ^ (n : ℝ)
        ≤ C₁ * κ ^ 2 * (2:ℝ) ^ (p / 2) / R ^ (n : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hCle (inv_nonneg.2 hRn.le)
    exact mul_le_mul_of_nonneg_right h1 hint0
