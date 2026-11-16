import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MemW1pZeroOn
import ManfrediThesis.MemHolderOn
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.FrozenComparisonOn
import ManfrediThesis.CitedDirichletHolder
import ManfrediThesis.CitedDirichletW1p
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.GradientSupEstimate
import ManfrediThesis.WeakGradientZeroExtend
import ManfrediThesis.WeakGradientLinear
open MeasureTheory

/-- The comparison map of (4.1) and the decay (4.11) of its gradient, for a
frozen operator `A₀` whose normalisation `A₀ - A₀ 0` satisfies (Q1)-(Q2).  The
map takes the boundary values of the Hölder datum `u` on `∂B_R(x₀)`, solves the
frozen equation for `A₀` itself, and its gradient obeys the `n`-decay with a
constant depending only on `n`, `p` and `γ₁/γ₀`.  This is the whole of the
passage that Theorems 3 and 5 share between their structure conditions and the
abstract comparison scheme. -/
theorem FrozenComparisonDecay :
    ∀ (n : ℕ) (p r : ℝ), 2 ≤ n → 1 < p → 0 < r →
      CitedSobolevPoincareBall n →
      (∀ (ε' γ₀' γ₁' : ℝ)
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → CitedDirichletW1p n p ε' γ₀' γ₁' A') →
      (∀ (ε' γ₀' γ₁' : ℝ) (Ω₀ : Set (EuclideanSpace ℝ (Fin n)))
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → IsOpen Ω₀ → CitedRegularityEpsPos n p ε' γ₀' γ₁' Ω₀ A') →
      (∀ (ε' γ₀' γ₁' : ℝ)
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → CitedDirichletHolder n p ε' γ₀' γ₁' A') →
      ∃ c₀ : ℝ, 0 < c₀ ∧
        ∀ (ε α γ₀ γ₁ : ℝ)
          (A₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 ≤ ε → ε ≤ 1 → 0 < α → α ≤ 1 → 0 < γ₀ → 0 < γ₁ → γ₁ ≤ r * γ₀ →
          0 < R →
          EllipticStructureQ12 n p ε γ₀ γ₁ Set.univ
            (fun _ _ h => A₀ h - A₀ 0) →
          MemW1pOn n p (Metric.ball x₀ R) u g →
          MemHolderOn n α (Metric.closedBall x₀ R) u →
          ∃ (v V : EuclideanSpace ℝ (Fin n) → ℝ)
            (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
            FrozenComparisonOn n p x₀ R A₀ u u g v V gv ∧
              ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
                (∫ x in Metric.ball x₀ ρ, (ε + ‖gv x‖ ^ 2) ^ (p / 2))
                  ≤ c₀ * (ρ / R) ^ (n : ℝ)
                    * ∫ x in Metric.ball x₀ R, (ε + ‖gv x‖ ^ 2) ^ (p / 2) := by
  intro n p r hn hp hr hSP hC2 hC1 hC3
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hp1 : (1:ℝ) ≤ p := hp.le
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hntriv : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, hnpos⟩ (1 : ℝ), ?_⟩⟩
    intro hcon
    have h := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w ⟨0, hnpos⟩) hcon
    simp at h
  -- Step 1: the constant `c₀`, chosen before all the data.
  obtain ⟨C₁, hC₁0, hGSE⟩ := GradientSupEstimate n p r hn hp hr hSP hC2 hC1
  obtain ⟨ω, hω⟩ : ∃ t : ℝ,
      t = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := ⟨_, rfl⟩
  have hω0 : 0 < ω := by
    rw [hω]
    refine ENNReal.toReal_pos ?_ measure_ball_lt_top.ne
    exact (Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self one_pos⟩).ne'
  have hballvol : ∀ (y : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 ≤ t →
      volume.real (Metric.ball y t) = ω * t ^ n := by
    intro y t ht
    rw [Measure.real_def, Measure.addHaar_ball volume y ht, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity),
      show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n by simp, hω]
    ring
  refine ⟨max (ω * 2 ^ n * C₁) (4 ^ n), lt_of_lt_of_le (by positivity) (le_max_right _ _), ?_⟩
  intro ε α γ₀ γ₁ A₀ x₀ R u g hε hε1 hα hα1 hγ₀ hγ₁ hγr hR hQ hu hHol
  -- Step 2: the normalised field.
  obtain ⟨At, hAt⟩ : ∃ f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      f = fun h => A₀ h - A₀ 0 := ⟨_, rfl⟩
  have hAt0 : At 0 = 0 := by rw [hAt]; simp
  have hQuniv : EllipticStructureQ12 n p ε γ₀ γ₁ Set.univ (fun _ _ h => At h) := by
    rw [hAt]; exact hQ
  have hQball : EllipticStructureQ12 n p ε γ₀ γ₁ (Metric.ball x₀ R) (fun _ _ h => At h) := by
    refine ⟨hQuniv.meas_x, hQuniv.cont_zh, ?_, ?_, ?_, ?_⟩
    · exact fun x _ z => hQuniv.hcont x (Set.mem_univ x) z
    · exact fun x _ z => hQuniv.hdiff x (Set.mem_univ x) z
    · filter_upwards [hQuniv.Q1] with x hx _ z h ξ hw
      exact hx (Set.mem_univ x) z h ξ hw
    · filter_upwards [hQuniv.Q2] with x hx _ z h i j hw
      exact hx (Set.mem_univ x) z h i j hw
  have hballmeas : MeasurableSet (Metric.ball x₀ R) := measurableSet_ball
  have hballlt : volume (Metric.ball x₀ R) < ⊤ := measure_ball_lt_top
  have hfin : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hballlt⟩
  -- Step 3, (1): the mean of a compactly supported test gradient vanishes.
  have hmean : ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ)
      (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      MemW1pOn n p (Metric.ball x₀ R) φ gφ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball x₀ R →
      ∀ i : Fin n, (∫ x in Metric.ball x₀ R, gφ x i) = 0 := by
    intro φ gφ hφ hφcs hφts i
    have hext := WeakGradientZeroExtend n p hn1 hp1 Set.univ x₀ R φ gφ isOpen_univ
      (Set.subset_univ _) hφ hφcs hφts
    set bump : ContDiffBump x₀ := ⟨R + 1, R + 2, by linarith, by linarith⟩ with hbump
    have hψone : ∀ x ∈ Metric.ball x₀ (R + 1), bump x = 1 := fun x hx =>
      bump.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    have hψfd : ∀ x ∈ Metric.ball x₀ (R + 1), fderiv ℝ (fun y => bump y) x = 0 := by
      intro x hx
      have hev : (fun y => bump y) =ᶠ[nhds x] (fun _ => (1:ℝ)) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy using hψone y hy
      rw [hev.fderiv_eq]
      simp
    have hid := hext.1 (fun y => bump y) bump.contDiff bump.hasCompactSupport
      (Set.subset_univ _) i
    have hlhs : (∫ x in Set.univ,
        φ x * fderiv ℝ (fun y => bump y) x (EuclideanSpace.single i (1:ℝ))) = 0 := by
      have hz : ∀ x : EuclideanSpace ℝ (Fin n),
          φ x * fderiv ℝ (fun y => bump y) x (EuclideanSpace.single i (1:ℝ)) = 0 := by
        intro x
        by_cases hx : x ∈ Metric.ball x₀ (R + 1)
        · rw [hψfd x hx]
          simp
        · have hx2 : x ∉ Metric.ball x₀ R := by
            intro hc
            exact hx (Metric.ball_subset_ball (by linarith) hc)
          rw [image_eq_zero_of_notMem_tsupport (fun hc => hx2 (hφts hc))]
          ring
      simp only [hz]
      simp
    have hrhs : (∫ x in Set.univ,
        (Metric.ball x₀ R).indicator gφ x i * bump x) = ∫ x in Metric.ball x₀ R, gφ x i := by
      rw [setIntegral_univ]
      have he : (fun x => (Metric.ball x₀ R).indicator gφ x i * bump x)
          = Set.indicator (Metric.ball x₀ R) (fun x => gφ x i) := by
        funext x
        by_cases hx : x ∈ Metric.ball x₀ R
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
            hψone x (Metric.ball_subset_ball (by linarith) hx)]
          ring
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
          simp
      rw [he, integral_indicator hballmeas]
    rw [hlhs, hrhs] at hid
    linarith
  -- Step 3: the two equations have the same weak solutions.
  have hcomp : ∀ (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (i : Fin n),
      MemLp gφ (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) →
      IntegrableOn (fun x => A₀ 0 i * gφ x i) (Metric.ball x₀ R) volume := by
    intro gφ i hgφ
    have h1 : Integrable gφ (volume.restrict (Metric.ball x₀ R)) := by
      have h2 : MemLp gφ 1 (volume.restrict (Metric.ball x₀ R)) := by
        refine hgφ.mono_exponent ?_
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hp1
      exact (memLp_one_iff_integrable).mp h2
    have h3 : Integrable (fun x => gφ x i) (volume.restrict (Metric.ball x₀ R)) := by
      refine Integrable.mono' h1.norm ?_ ?_
      · exact ((EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable
          h1.aestronglyMeasurable)
      · filter_upwards with x
        exact PiLp.norm_apply_le (gφ x) i
    exact h3.const_mul _
  have hconv : ∀ (v : EuclideanSpace ℝ (Fin n) → ℝ)
      (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => At h) (fun _ _ _ => 0) v gv →
      IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A₀ h) (fun _ _ _ => 0) v gv := by
    intro v gv hvs
    refine ⟨hvs.1, ?_⟩
    intro φ gφ hφ hφcs hφts
    obtain ⟨hFint, hFzero⟩ := hvs.2 φ gφ hφ hφcs hφts
    have hcint : ∀ i : Fin n,
        IntegrableOn (fun x => A₀ 0 i * gφ x i) (Metric.ball x₀ R) volume :=
      fun i => hcomp gφ i hφ.2.2
    have hcsum : IntegrableOn (fun x => ∑ i, A₀ 0 i * gφ x i) (Metric.ball x₀ R) volume :=
      integrable_finsetSum _ (fun i _ => hcint i)
    have hczero : (∫ x in Metric.ball x₀ R, ∑ i, A₀ 0 i * gφ x i) = 0 := by
      rw [integral_finsetSum _ (fun i _ => hcint i)]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [integral_const_mul, hmean φ gφ hφ hφcs hφts i, mul_zero]
    have hsplit : ∀ x : EuclideanSpace ℝ (Fin n),
        (∑ i, A₀ (gv x) i * gφ x i) + 0 * φ x
          = ((∑ i, At (gv x) i * gφ x i) + 0 * φ x) + (∑ i, A₀ 0 i * gφ x i) := by
      intro x
      have hterm : ∀ i : Fin n,
          A₀ (gv x) i * gφ x i = At (gv x) i * gφ x i + A₀ 0 i * gφ x i := by
        intro i
        rw [hAt]
        simp only [PiLp.sub_apply]
        ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
      ring
    refine ⟨?_, ?_⟩
    · exact (hFint.add hcsum).congr_fun (fun x _ => (hsplit x).symm) hballmeas
    · rw [setIntegral_congr_fun hballmeas (fun x _ => hsplit x),
        integral_add hFint hcsum, hFzero, hczero, add_zero]
  -- Step 4: the comparison map, from the cited Dirichlet result (C3).
  have hubdry : MemHolderOn n (α / 2) (Metric.sphere x₀ R) u := by
    obtain ⟨hcont, Cα, hCα0, hCα⟩ := hHol
    refine ⟨hcont.mono Metric.sphere_subset_closedBall, Cα * (2 * R) ^ (α / 2), ?_, ?_⟩
    · positivity
    · intro x hx y hy
      have hxc : x ∈ Metric.closedBall x₀ R := Metric.sphere_subset_closedBall hx
      have hyc : y ∈ Metric.closedBall x₀ R := Metric.sphere_subset_closedBall hy
      have hdxy : dist x y ≤ 2 * R := by
        have h1 : dist x x₀ ≤ R := Metric.mem_closedBall.mp hxc
        have h2 : dist x₀ y ≤ R := by
          rw [dist_comm]
          exact Metric.mem_closedBall.mp hyc
        have := dist_triangle x x₀ y
        linarith
      have hb := hCα x hxc y hyc
      rcases eq_or_lt_of_le (dist_nonneg (x := x) (y := y)) with hd0 | hd0
      · have hxy : x = y := by
          have := hd0.symm
          exact dist_eq_zero.mp this
        rw [hxy, sub_self, abs_zero, dist_self, Real.zero_rpow (by positivity), mul_zero]
      · have hsplit : dist x y ^ α = dist x y ^ (α / 2) * dist x y ^ (α / 2) := by
          rw [← Real.rpow_add hd0]
          congr 1
          ring
        have hmono : dist x y ^ (α / 2) ≤ (2 * R) ^ (α / 2) :=
          Real.rpow_le_rpow dist_nonneg hdxy (by positivity)
        have hpos : (0:ℝ) ≤ dist x y ^ (α / 2) := Real.rpow_nonneg dist_nonneg _
        calc |u x - u y| ≤ Cα * dist x y ^ α := hb
          _ = Cα * dist x y ^ (α / 2) * dist x y ^ (α / 2) := by rw [hsplit]; ring
          _ ≤ Cα * (2 * R) ^ (α / 2) * dist x y ^ (α / 2) := by
              refine mul_le_mul_of_nonneg_right ?_ hpos
              exact mul_le_mul_of_nonneg_left hmono hCα0
  obtain ⟨v, V, gv, hvloc, hvsolAt, hvC1, hVH, hVv, hVu, hvzero⟩ :=
    hC3 ε γ₀ γ₁ At hγ₀ hγ₁ hQuniv hε hAt0 x₀ R (α / 2) hR (by linarith) (by linarith) u hubdry
  have hzeroclause := hvzero u g hu hHol.1 (fun x _ => rfl)
  have hv3 : MemW1pOn n p (Metric.ball x₀ R) v gv := by
    have hWL := (WeakGradientLinear n p hn1 hp1 (Metric.ball x₀ R)
      (fun x => v x - u x) u (fun x => gv x - g x) g 1 1 0 Metric.isOpen_ball).2.1
      hzeroclause.1 hu
    have e1 : (fun x => (1:ℝ) * (v x - u x) + (1:ℝ) * u x) = v := by
      funext x; ring
    have e2 : (fun x => (1:ℝ) • (gv x - g x) + (1:ℝ) • g x) = gv := by
      funext x
      simp
    rw [e1, e2] at hWL
    exact hWL
  refine ⟨v, V, gv, ⟨hconv v gv hvsolAt, hv3, hzeroclause, hHol.1, fun x _ => rfl,
    hVH.1, hVv, hVu⟩, ?_⟩
  -- Step 5: the decay (4.11).
  have hnneg : ∀ x : EuclideanSpace ℝ (Fin n), (0:ℝ) ≤ (ε + ‖gv x‖ ^ 2) ^ (p / 2) :=
    fun x => Real.rpow_nonneg (by positivity) _
  have hgvLp : MemLp gv (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) := hv3.2.2
  have hcont : Continuous fun t : ℝ => (ε + t ^ 2) ^ (p / 2) := by
    have h1 : Continuous fun s : ℝ => s ^ (p / 2) :=
      continuous_iff_continuousAt.mpr fun s =>
        Real.continuousAt_rpow_const s (p / 2) (Or.inr (by positivity))
    exact h1.comp (by continuity)
  have hmeas : AEStronglyMeasurable (fun x => (ε + ‖gv x‖ ^ 2) ^ (p / 2))
      (volume.restrict (Metric.ball x₀ R)) :=
    hcont.comp_aestronglyMeasurable hgvLp.aestronglyMeasurable.norm
  have hgvp : IntegrableOn (fun x => ‖gv x‖ ^ p) (Metric.ball x₀ R) volume := by
    have h := hgvLp.integrable_norm_rpow
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp0) (by simp)
    rwa [ENNReal.toReal_ofReal hp0.le] at h
  have hdom : IntegrableOn (fun x => (ε + ‖gv x‖ ^ 2) ^ (p / 2))
      (Metric.ball x₀ R) volume := by
    refine Integrable.mono' (g := fun x => 2 ^ (p / 2) * (1 + ‖gv x‖ ^ p)) ?_ hmeas ?_
    · exact ((integrable_const (1:ℝ)).add hgvp).const_mul _
    · filter_upwards with x
      have ht : (0:ℝ) ≤ ‖gv x‖ := norm_nonneg _
      have htp : (0:ℝ) ≤ ‖gv x‖ ^ p := Real.rpow_nonneg ht _
      rw [Real.norm_eq_abs, abs_of_nonneg (hnneg x)]
      by_cases hcase : ‖gv x‖ ≤ 1
      · have h1 : ε + ‖gv x‖ ^ 2 ≤ 2 := by nlinarith
        have h2 : (ε + ‖gv x‖ ^ 2) ^ (p / 2) ≤ (2:ℝ) ^ (p / 2) :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
        nlinarith [Real.rpow_nonneg (show (0:ℝ) ≤ 2 by norm_num) (p / 2)]
      · rw [not_le] at hcase
        have h1 : ε + ‖gv x‖ ^ 2 ≤ 2 * ‖gv x‖ ^ 2 := by nlinarith
        have h2 : (ε + ‖gv x‖ ^ 2) ^ (p / 2) ≤ (2 * ‖gv x‖ ^ 2) ^ (p / 2) :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
        have h3 : (2 * ‖gv x‖ ^ 2) ^ (p / 2) = 2 ^ (p / 2) * ‖gv x‖ ^ p := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
          congr 1
          rw [← Real.rpow_natCast ‖gv x‖ 2, ← Real.rpow_mul ht]
          congr 1
          push_cast
          ring
        rw [h3] at h2
        nlinarith [Real.rpow_nonneg (show (0:ℝ) ≤ 2 by norm_num) (p / 2)]
  have hIR : (0:ℝ) ≤ ∫ x in Metric.ball x₀ R, (ε + ‖gv x‖ ^ 2) ^ (p / 2) :=
    setIntegral_nonneg hballmeas (fun x _ => hnneg x)
  have hcbsub : Metric.closedBall x₀ (R / 2) ⊆ Metric.ball x₀ R := by
    intro y hy
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (by linarith))
  have hgse := hGSE ε γ₀ γ₁ (Metric.ball x₀ R) At v gv x₀ (R / 2) hε hγ₀ hγr
    Metric.isOpen_ball (by linarith) hAt0 hQball hvsolAt hcbsub
  intro ρ hρ hρR
  have hIhalf : (∫ x in Metric.ball x₀ (R / 2), (ε + ‖gv x‖ ^ 2) ^ (p / 2))
      ≤ ∫ x in Metric.ball x₀ R, (ε + ‖gv x‖ ^ 2) ^ (p / 2) := by
    refine setIntegral_mono_set hdom (Filter.Eventually.of_forall (fun x => hnneg x)) ?_
    exact Filter.Eventually.of_forall (Metric.ball_subset_ball (by linarith))
  have hρRpow : (0:ℝ) ≤ (ρ / R) ^ (n : ℝ) := Real.rpow_nonneg (by positivity) _
  have hcast : (ρ / R) ^ (n : ℝ) = (ρ / R) ^ n := Real.rpow_natCast _ n
  rcases le_or_gt ρ (R / 4) with hcase | hcase
  · -- the inner case: integrate the sup bound
    have hsub : Metric.ball x₀ ρ ⊆ Metric.ball x₀ (R / 2 / 2) :=
      Metric.ball_subset_ball (by linarith)
    have hae : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ)),
        (ε + ‖gv x‖ ^ 2) ^ (p / 2)
          ≤ C₁ / (R / 2) ^ (n : ℝ)
            * ∫ y in Metric.ball x₀ (R / 2), (ε + ‖gv y‖ ^ 2) ^ (p / 2) :=
      ae_restrict_of_ae_restrict_of_subset hsub hgse
    have hfinρ : IsFiniteMeasure (volume.restrict (Metric.ball x₀ ρ)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have hmono : (∫ x in Metric.ball x₀ ρ, (ε + ‖gv x‖ ^ 2) ^ (p / 2))
        ≤ ∫ _x in Metric.ball x₀ ρ, C₁ / (R / 2) ^ (n : ℝ)
            * ∫ y in Metric.ball x₀ (R / 2), (ε + ‖gv y‖ ^ 2) ^ (p / 2) := by
      refine integral_mono_ae (hdom.mono_set (Metric.ball_subset_ball (by linarith)))
        (integrable_const _) hae
    rw [setIntegral_const, hballvol x₀ ρ hρ.le, smul_eq_mul] at hmono
    have hRn : (R / 2) ^ (n : ℝ) = R ^ n / 2 ^ n := by
      rw [Real.rpow_natCast, div_pow]
    rw [hRn] at hmono
    have hRnpos : (0:ℝ) < R ^ n := by positivity
    have hkey : ω * ρ ^ n * (C₁ / (R ^ n / 2 ^ n)
        * ∫ y in Metric.ball x₀ (R / 2), (ε + ‖gv y‖ ^ 2) ^ (p / 2))
        ≤ max (ω * 2 ^ n * C₁) (4 ^ n) * (ρ / R) ^ n
          * ∫ x in Metric.ball x₀ R, (ε + ‖gv x‖ ^ 2) ^ (p / 2) := by
      have h1 : ω * ρ ^ n * (C₁ / (R ^ n / 2 ^ n)
          * ∫ y in Metric.ball x₀ (R / 2), (ε + ‖gv y‖ ^ 2) ^ (p / 2))
          = (ω * 2 ^ n * C₁) * (ρ / R) ^ n
            * ∫ y in Metric.ball x₀ (R / 2), (ε + ‖gv y‖ ^ 2) ^ (p / 2) := by
        rw [div_pow]
        field_simp
      rw [h1]
      have h2 : (0:ℝ) ≤ ω * 2 ^ n * C₁ * (ρ / R) ^ n := by positivity
      have h3 : ω * 2 ^ n * C₁ ≤ max (ω * 2 ^ n * C₁) (4 ^ n) := le_max_left _ _
      have h4 : (0:ℝ) ≤ (ρ / R) ^ n := by positivity
      calc ω * 2 ^ n * C₁ * (ρ / R) ^ n
            * ∫ y in Metric.ball x₀ (R / 2), (ε + ‖gv y‖ ^ 2) ^ (p / 2)
          ≤ ω * 2 ^ n * C₁ * (ρ / R) ^ n
            * ∫ x in Metric.ball x₀ R, (ε + ‖gv x‖ ^ 2) ^ (p / 2) :=
            mul_le_mul_of_nonneg_left hIhalf h2
        _ ≤ max (ω * 2 ^ n * C₁) (4 ^ n) * (ρ / R) ^ n
            * ∫ x in Metric.ball x₀ R, (ε + ‖gv x‖ ^ 2) ^ (p / 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 h4) hIR
    rw [hcast]
    exact le_trans hmono hkey
  · -- the outer case: monotonicity alone
    have hsub : Metric.ball x₀ ρ ⊆ Metric.ball x₀ R := Metric.ball_subset_ball hρR
    have h1 : (∫ x in Metric.ball x₀ ρ, (ε + ‖gv x‖ ^ 2) ^ (p / 2))
        ≤ ∫ x in Metric.ball x₀ R, (ε + ‖gv x‖ ^ 2) ^ (p / 2) := by
      refine setIntegral_mono_set hdom (Filter.Eventually.of_forall (fun x => hnneg x)) ?_
      exact Filter.Eventually.of_forall hsub
    have h2 : (1:ℝ) ≤ 4 ^ n * (ρ / R) ^ n := by
      have h3 : (1:ℝ) ≤ 4 * (ρ / R) := by
        rw [← mul_div_assoc, le_div_iff₀ hR]
        linarith
      calc (1:ℝ) = 1 ^ n := by norm_num
        _ ≤ (4 * (ρ / R)) ^ n := pow_le_pow_left₀ (by norm_num) h3 n
        _ = 4 ^ n * (ρ / R) ^ n := by rw [mul_pow]
    have h4 : (4:ℝ) ^ n ≤ max (ω * 2 ^ n * C₁) (4 ^ n) := le_max_right _ _
    have hq : (0:ℝ) ≤ (ρ / R) ^ n := by positivity
    rw [hcast]
    calc (∫ x in Metric.ball x₀ ρ, (ε + ‖gv x‖ ^ 2) ^ (p / 2))
        ≤ ∫ x in Metric.ball x₀ R, (ε + ‖gv x‖ ^ 2) ^ (p / 2) := h1
      _ ≤ 4 ^ n * (ρ / R) ^ n * ∫ x in Metric.ball x₀ R, (ε + ‖gv x‖ ^ 2) ^ (p / 2) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr h2) hIR]
      _ ≤ max (ω * 2 ^ n * C₁) (4 ^ n) * (ρ / R) ^ n
            * ∫ x in Metric.ball x₀ R, (ε + ‖gv x‖ ^ 2) ^ (p / 2) := by
          have h5 : (4:ℝ) ^ n * (ρ / R) ^ n
              ≤ max (ω * 2 ^ n * C₁) (4 ^ n) * (ρ / R) ^ n :=
            mul_le_mul_of_nonneg_right h4 hq
          nlinarith [hIR]
