import ManfrediThesis.Preamble
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.MemW1pOn
open MeasureTheory

/-- Zero extension of a compactly supported Sobolev function: if `φ` lies in
`W^{1,q}` of a ball with weak gradient `gφ` and has compact support inside that
ball, then `φ` lies in `W^{1,q}` of every open set containing the ball, with
weak gradient the ZERO EXTENSION of `gφ` (which carries no information off the
ball). -/
theorem WeakGradientZeroExtend :
    ∀ (n : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ q →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (x₀ : EuclideanSpace ℝ (Fin n)) (r : ℝ)
        (φ : EuclideanSpace ℝ (Fin n) → ℝ)
        (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        IsOpen Ω → Metric.ball x₀ r ⊆ Ω →
        MemW1pOn n q (Metric.ball x₀ r) φ gφ →
        HasCompactSupport φ → tsupport φ ⊆ Metric.ball x₀ r →
        MemW1pOn n q Ω φ ((Metric.ball x₀ r).indicator gφ) := by
  intro n q hn hq Ω x₀ r φ gφ hΩ hBΩ hw hcsφ htsφ
  obtain ⟨hwg, hφLp, hgLp⟩ := hw
  set B : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball x₀ r with hB
  have hBo : IsOpen B := Metric.isOpen_ball
  have hBfin : volume B ≠ ⊤ := by
    simpa [hB] using (Metric.isBounded_ball (x := x₀) (r := r)).measure_lt_top.ne
  have h1q : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]; exact ENNReal.ofReal_le_ofReal hq
  have hφzero : ∀ x ∉ tsupport φ, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  -- `gφ` is integrable on `B`, coordinatewise.
  have hBfinM : IsFiniteMeasure (volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hBfin⟩
  have hgI : ∀ a : Fin n, IntegrableOn (fun x => gφ x a) B volume := by
    intro a
    refine memLp_one_iff_integrable.1 ((hgLp.mono_exponent h1q).mono ?_ ?_)
    · exact (EuclideanSpace.proj a).continuous.comp_aestronglyMeasurable
        (hgLp.mono_exponent h1q).aestronglyMeasurable
    · filter_upwards with x using PiLp.norm_apply_le _ a
  -- `gφ` vanishes a.e. on `B \ tsupport φ`, because `φ` vanishes on that open set.
  have hgvan : ∀ a : Fin n, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∈ B \ tsupport φ → gφ x a = 0 := by
    intro a
    have hU : IsOpen (B \ tsupport φ) := hBo.sdiff (isClosed_tsupport φ)
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hgI a).mono_set Set.sdiff_subset).locallyIntegrableOn ?_
    intro ξ hξ hcsξ htsξ
    have htsξB : tsupport ξ ⊆ B := htsξ.trans Set.sdiff_subset
    have hzero : ∀ x, ξ x • gφ x a = 0 → True := fun _ _ => trivial
    -- the weak-gradient identity at the test function `ξ`
    have hid := hwg ξ hξ hcsξ htsξB a
    -- its left side vanishes pointwise
    have hlhs : ∀ x, φ x * fderiv ℝ ξ x (EuclideanSpace.single a (1:ℝ)) = 0 := by
      intro x
      by_cases hx : x ∈ tsupport ξ
      · have : x ∉ tsupport φ := (htsξ hx).2
        simp [hφzero x this]
      · have h0 : fderiv ℝ ξ x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hh => hx (tsupport_fderiv_subset ℝ hh))
        simp [h0]
    rw [show (∫ x in B, φ x * fderiv ℝ ξ x (EuclideanSpace.single a (1:ℝ))) = 0 by
      simp [hlhs]] at hid
    -- so the right side is zero, and it is the integral we need
    have hconv : (∫ x, ξ x • gφ x a) = ∫ x in B, gφ x a * ξ x := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := B) (f := fun x => ξ x • gφ x a) ?_]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp [smul_eq_mul, mul_comm]
      · intro x hx
        have : ξ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (htsξB hh))
        simp [this]
    rw [hconv]
    linarith [hid]
  have hBms : MeasurableSet B := hBo.measurableSet
  -- The two `L^q` clauses, by zero-extension from `B`.
  have hφLpΩ : MemLp φ (ENNReal.ofReal q) (volume.restrict Ω) := by
    have h1 : MemLp (B.indicator φ) (ENNReal.ofReal q) volume :=
      (memLp_indicator_iff_restrict hBms).2 hφLp
    have h2 : B.indicator φ = φ := by
      funext x
      by_cases hx : x ∈ B
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx, hφzero x (fun hh => hx (htsφ hh))]
    rw [h2] at h1
    exact h1.mono_measure Measure.restrict_le_self
  have hgLpΩ : MemLp (B.indicator gφ) (ENNReal.ofReal q) (volume.restrict Ω) :=
    ((memLp_indicator_iff_restrict hBms).2 hgLp).mono_measure Measure.restrict_le_self
  refine ⟨?_, hφLpΩ, hgLpΩ⟩
  -- The weak-gradient clause.
  rcases le_or_gt r 0 with hr | hr
  · -- Degenerate: the ball is empty, so `φ = 0` everywhere.
    have hBe : B = (∅ : Set (EuclideanSpace ℝ (Fin n))) := by
      rw [hB]
      exact Metric.ball_eq_empty.2 hr
    have hφ0 : ∀ x, φ x = 0 := by
      intro x
      refine hφzero x ?_
      intro hh
      rw [hBe] at htsφ
      exact htsφ hh
    intro ζ hζ hcsζ htsζ i
    have h1 : (∫ x in Ω, φ x * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) = 0 := by
      simp [hφ0]
    have h2 : (∫ x in Ω, (B.indicator gφ) x i * ζ x) = 0 := by
      simp [hBe]
    rw [h1, h2]; simp
  · -- The main case: build the cut-off.
    obtain ⟨r₁, hr₁mem, hKsub⟩ :=
      exists_pos_lt_subset_ball hr (isClosed_tsupport φ) htsφ
    have hr₁pos : 0 < r₁ := hr₁mem.1
    have hr₁lt : r₁ < r := hr₁mem.2
    set bump : ContDiffBump x₀ := ⟨r₁, (r₁ + r) / 2, hr₁pos, by linarith⟩ with hbump
    have hbrOut : bump.rOut = (r₁ + r) / 2 := rfl
    have hχcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => bump x) := bump.contDiff
    have hχcs : HasCompactSupport (fun x => bump x) := bump.hasCompactSupport
    have hχts : tsupport (fun x => bump x) ⊆ B := by
      rw [bump.tsupport_eq, hB]
      intro y hy
      simp only [Metric.mem_closedBall] at hy
      exact Metric.mem_ball.2 (lt_of_le_of_lt hy (by rw [hbrOut]; linarith))
    have hχone : ∀ x ∈ Metric.ball x₀ r₁, bump x = 1 := fun x hx =>
      bump.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    have hχfd : ∀ x ∈ Metric.ball x₀ r₁, fderiv ℝ (fun y => bump y) x = 0 := by
      intro x hx
      have hev : (fun y => bump y) =ᶠ[nhds x] (fun _ => (1:ℝ)) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy using hχone y hy
      rw [hev.fderiv_eq]; simp
    intro ζ hζ hcsζ htsζ i
    -- `bump * ζ` is an admissible test pair for `B`.
    have htcd : ContDiff ℝ (⊤ : ℕ∞) (fun y => bump y * ζ y) := hχcd.mul hζ
    have htcs : HasCompactSupport (fun y => bump y * ζ y) := hχcs.mul_right
    have htts : tsupport (fun y => bump y * ζ y) ⊆ B :=
      (tsupport_mul_subset_left).trans hχts
    have hid := hwg _ htcd htcs htts i
    -- The integrand on the left is `φ * D_i ζ`, pointwise.
    have hlhsPt : ∀ x, φ x * fderiv ℝ (fun y => bump y * ζ y) x
          (EuclideanSpace.single i (1:ℝ))
        = φ x * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ)) := by
      intro x
      have hpr : HasFDerivAt (fun y => bump y * ζ y)
          (bump x • fderiv ℝ ζ x + ζ x • fderiv ℝ (fun y => bump y) x) x :=
        ((hχcd.differentiable (by simp)).differentiableAt.hasFDerivAt).mul
          ((hζ.differentiable (by simp)).differentiableAt.hasFDerivAt)
      rw [hpr.fderiv]
      by_cases hx : x ∈ Metric.ball x₀ r₁
      · simp [hχone x hx, hχfd x hx]
      · have : φ x = 0 := hφzero x (fun hh => hx (hKsub hh))
        simp [this]
    -- Transfer both sides from `B` to `Ω`.
    have hLB : (∫ x in B, φ x * fderiv ℝ (fun y => bump y * ζ y) x
          (EuclideanSpace.single i (1:ℝ)))
        = ∫ x in Ω, φ x * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ)) := by
      rw [show (∫ x in B, φ x * fderiv ℝ (fun y => bump y * ζ y) x
            (EuclideanSpace.single i (1:ℝ)))
          = ∫ x in B, φ x * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ)) from
        integral_congr_ae (Filter.Eventually.of_forall hlhsPt)]
      refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet hBΩ ?_).symm
      intro x hx
      have : φ x = 0 := hφzero x (fun hh => hx.2 (htsφ hh))
      simp [this]
    have hRB : (∫ x in B, gφ x i * (bump x * ζ x))
        = ∫ x in Ω, (B.indicator gφ) x i * ζ x := by
      have hstep : (∫ x in B, gφ x i * (bump x * ζ x)) = ∫ x in B, gφ x i * ζ x := by
        refine integral_congr_ae ((MeasureTheory.ae_restrict_iff' hBms).2 ?_)
        filter_upwards [hgvan i] with x hx hxB
        by_cases hb : x ∈ Metric.ball x₀ r₁
        · simp [hχone x hb]
        · have hz : gφ x i = 0 := hx ⟨hxB, fun hh => hb (hKsub hh)⟩
          simp [hz]
      have hstep2 : (∫ x in B, gφ x i * ζ x)
          = ∫ x in B, (B.indicator gφ) x i * ζ x := by
        refine integral_congr_ae ((MeasureTheory.ae_restrict_iff' hBms).2 ?_)
        filter_upwards with x hxB
        simp [Set.indicator_of_mem hxB]
      have hstep3 : (∫ x in Ω, (B.indicator gφ) x i * ζ x)
          = ∫ x in B, (B.indicator gφ) x i * ζ x := by
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet hBΩ ?_
        intro x hx
        simp [Set.indicator_of_notMem hx.2]
      rw [hstep, hstep2, hstep3]
    rw [hLB, hRB] at hid
    exact hid
