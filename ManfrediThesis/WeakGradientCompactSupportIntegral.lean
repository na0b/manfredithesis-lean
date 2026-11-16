import ManfrediThesis.Preamble
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.WeakGradientZeroExtend
import ManfrediThesis.StandardRadialCutoff
open MeasureTheory

/-- Each component of the weak gradient of a `W^{1,q}` function with compact
support inside a ball is integrable on that ball and has integral zero. -/
theorem WeakGradientCompactSupportIntegral :
    ∀ (n : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ q →
      ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
        (φ : EuclideanSpace ℝ (Fin n) → ℝ)
        (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < R →
        MemW1pOn n q (Metric.ball x₀ R) φ gφ →
        HasCompactSupport φ → tsupport φ ⊆ Metric.ball x₀ R →
        ∀ i : Fin n,
          IntegrableOn (fun x => gφ x i) (Metric.ball x₀ R) volume ∧
            (∫ x in Metric.ball x₀ R, gφ x i) = 0 := by
  intro n q hn hq x₀ R φ gφ hR hφ hcs hts i
  -- the coordinate bound `|v i| ≤ ‖v‖`
  have hcoord : ∀ (v : EuclideanSpace ℝ (Fin n)) (k : Fin n), |v k| ≤ ‖v‖ := by
    intro v k
    have h1 : (v k) ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (f := fun m => (v m) ^ 2)
        (fun m _ => sq_nonneg _) (Finset.mem_univ k)
    nlinarith [abs_nonneg (v k), norm_nonneg v, sq_abs (v k)]
  -- integrability of the `i`-th component on the ball
  have hfin : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  have hq1 : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq
  have hintv : Integrable gφ (volume.restrict (Metric.ball x₀ R)) :=
    MemLp.integrable hq1 hφ.2.2
  have hmeas : AEStronglyMeasurable (fun x => gφ x i)
      (volume.restrict (Metric.ball x₀ R)) :=
    (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hφ.2.2.1
  have hint : IntegrableOn (fun x => gφ x i) (Metric.ball x₀ R) volume := by
    refine Integrable.mono hintv hmeas ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hcoord (gφ x) i
  refine ⟨hint, ?_⟩
  -- the extension of the test pair by zero is a `W^{1,q}` pair on all of `ℝⁿ`
  have hext : MemW1pOn n q Set.univ φ ((Metric.ball x₀ R).indicator gφ) :=
    WeakGradientZeroExtend n q hn hq Set.univ x₀ R φ gφ isOpen_univ
      (Set.subset_univ _) hφ hcs hts
  -- a cut-off equal to `1` on a ball containing `B_R(x₀)`
  obtain ⟨L, hL, hcut⟩ := StandardRadialCutoff n hn
  obtain ⟨M, hMdef⟩ : ∃ s : ℝ, s = ‖x₀‖ + R + 1 := ⟨_, rfl⟩
  have hM0 : 0 < M := by
    rw [hMdef]; have := norm_nonneg x₀; linarith
  have hballsub : Metric.ball x₀ R ⊆ Metric.ball 0 M := by
    intro y hy
    rw [Metric.mem_ball] at hy
    rw [Metric.mem_ball]
    have ht : dist y 0 ≤ dist y x₀ + dist x₀ 0 := dist_triangle _ _ _
    have h1 : dist x₀ (0 : EuclideanSpace ℝ (Fin n)) = ‖x₀‖ := dist_zero_right x₀
    rw [h1] at ht
    rw [hMdef]
    linarith
  obtain ⟨ζ, hζsm, hζcs, -, -, -, hζone, -⟩ :=
    hcut 0 M (M + 1) hM0 (by linarith)
  have hwg := hext.1 ζ hζsm hζcs (Set.subset_univ _) i
  -- the left-hand side of the weak-gradient identity vanishes pointwise
  have hlhs : (∫ x in Set.univ,
      φ x * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) = 0 := by
    have hz : ∀ x : EuclideanSpace ℝ (Fin n),
        φ x * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)) = 0 := by
      intro x
      by_cases hx : x ∈ tsupport φ
      · have hxb : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) M :=
          hballsub (hts hx)
        have hev : ζ =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
          filter_upwards [Metric.isOpen_ball.mem_nhds hxb] with y hy
          exact hζone y (Metric.ball_subset_closedBall hy)
        rw [hev.fderiv_eq]
        simp
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    simp only [hz, integral_zero]
  -- and the right-hand side is the integral we want
  have hptw : ∀ x : EuclideanSpace ℝ (Fin n),
      ((Metric.ball x₀ R).indicator gφ x) i * ζ x
        = (Metric.ball x₀ R).indicator (fun y => gφ y i) x := by
    intro x
    by_cases hx : x ∈ Metric.ball x₀ R
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (s := Metric.ball x₀ R) hx,
        hζone x (Metric.ball_subset_closedBall (hballsub hx)), mul_one]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (s := Metric.ball x₀ R) hx]
      simp
  have hrhs : (∫ x in Set.univ, ((Metric.ball x₀ R).indicator gφ x) i * ζ x)
      = ∫ x in Metric.ball x₀ R, gφ x i := by
    rw [setIntegral_univ, integral_congr_ae (Filter.Eventually.of_forall hptw)]
    exact integral_indicator measurableSet_ball
  rw [hlhs, hrhs] at hwg
  linarith
