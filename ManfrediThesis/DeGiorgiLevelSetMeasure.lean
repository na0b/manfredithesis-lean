import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pOn
import ManfrediThesis.WeakGradientPositivePart
import ManfrediThesis.CitedSobolevPoincareBall
open MeasureTheory

/-- Lemma 2.2 (De Giorgi): an isoperimetric-type estimate for the level sets of
a `W^{1,1}` function on a ball. -/
theorem DeGiorgiLevelSetMeasure :
    ∀ n : ℕ, 2 ≤ n → CitedSobolevPoincareBall n →
      ∃ β : ℝ, 0 < β ∧
        ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
          (f : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (k l : ℝ),
          0 < R → MemW1pOn n 1 (Metric.ball x₀ R) f g → k ≤ l →
          0 < (volume (Metric.ball x₀ R \ {y | k < f y})).toReal →
          (l - k) * (volume (Metric.ball x₀ R ∩ {y | l < f y})).toReal ^ (1 - 1 / (n : ℝ))
            ≤ β * R ^ (n : ℝ) / (volume (Metric.ball x₀ R \ {y | k < f y})).toReal
              * ∫ x in (Metric.ball x₀ R ∩ {y | k < f y}) \ {y | l < f y}, ‖g x‖ := by
  intro n hn hSPB
  obtain ⟨C, hC0, hSP⟩ := hSPB
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hn1 : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hntriv : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, hnpos⟩ (1 : ℝ), ?_⟩⟩
    intro hc
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hnpos⟩) hc
    simp at h
  have hsubco : ∀ (u v : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      (u - v) i = u i - v i := fun _ _ _ => rfl
  have hproj : ∀ i : Fin n, Continuous fun w : EuclideanSpace ℝ (Fin n) => w i :=
    fun i => (EuclideanSpace.proj i).continuous
  have hcoord : ∀ (w : EuclideanSpace ℝ (Fin n)) (i : Fin n), |w i| ≤ ‖w‖ := by
    intro w i
    rw [EuclideanSpace.norm_eq,
      show |w i| = Real.sqrt (|w i| ^ 2) by rw [Real.sqrt_sq (abs_nonneg _)]]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (f := fun j => |w j| ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i))
  -- the exponent `q = n/(n-1)`
  have hq : (1 : ℝ) < (n : ℝ) / ((n : ℝ) - 1) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hq0 : (0 : ℝ) < (n : ℝ) / ((n : ℝ) - 1) := lt_trans one_pos hq
  have hiq : 1 / ((n : ℝ) / ((n : ℝ) - 1)) = 1 - 1 / (n : ℝ) := by
    rw [one_div_div]
    field_simp
  have hiqnn : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
    have h1 : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnR0]; linarith
    linarith
  -- `ω_n` and the constant
  refine ⟨2 * C * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal, ?_, ?_⟩
  · have hω : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
      refine ENNReal.toReal_pos ?_ measure_ball_lt_top.ne
      exact (Metric.isOpen_ball.measure_pos volume
        ⟨0, Metric.mem_ball_self one_pos⟩).ne'
    positivity
  intro x₀ R f g k l hR hW hkl hZpos
  -- the ball and the four sets
  have hBtop : volume (Metric.ball x₀ R) ≠ ⊤ := measure_ball_lt_top.ne
  have hBpos : 0 < volume (Metric.ball x₀ R) :=
    Metric.isOpen_ball.measure_pos volume ⟨x₀, Metric.mem_ball_self hR⟩
  have hmono : ∀ S : Set (EuclideanSpace ℝ (Fin n)), S ⊆ Metric.ball x₀ R →
      volume S ≠ ⊤ := fun S hS =>
    (lt_of_le_of_lt (measure_mono hS) measure_ball_lt_top).ne
  have hZsub : Metric.ball x₀ R \ {y | k < f y} ⊆ Metric.ball x₀ R := Set.sdiff_subset
  have hAlsub : Metric.ball x₀ R ∩ {y | l < f y} ⊆ Metric.ball x₀ R := Set.inter_subset_left
  have hEsub : (Metric.ball x₀ R ∩ {y | k < f y}) \ {y | l < f y}
      ⊆ Metric.ball x₀ R := Set.sdiff_subset.trans Set.inter_subset_left
  -- the ball volume
  have hball : (volume (Metric.ball x₀ R)).toReal
      = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal * R ^ n := by
    rw [Measure.addHaar_ball volume x₀ hR.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity),
      show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n by simp]
    ring
  -- the integral on the right is nonnegative
  have hInn : 0 ≤ ∫ x in (Metric.ball x₀ R ∩ {y | k < f y}) \ {y | l < f y}, ‖g x‖ :=
    integral_nonneg fun x => norm_nonneg _
  -- the degenerate case `l = k`
  rcases eq_or_lt_of_le hkl with hlk | hlk
  · subst hlk
    simp only [sub_self, zero_mul]
    positivity
  -- Step 1: the truncation `w = (f-k)⁺ - (f-l)⁺`, and the linearity of the
  -- weak-gradient relation in the pair, done inline as the `.tex` does it
  have hsub : ∀ (u₁ u₂ : EuclideanSpace ℝ (Fin n) → ℝ)
      (G₁ G₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      MemW1pOn n 1 (Metric.ball x₀ R) u₁ G₁ → MemW1pOn n 1 (Metric.ball x₀ R) u₂ G₂ →
      MemW1pOn n 1 (Metric.ball x₀ R) (fun x => u₁ x - u₂ x)
        (fun x => G₁ x - G₂ x) := by
    intro u₁ u₂ G₁ G₂ h1 h2
    obtain ⟨hwg1, hu1, hG1⟩ := h1
    obtain ⟨hwg2, hu2, hG2⟩ := h2
    have hone : (ENNReal.ofReal 1) = 1 := by simp
    have hint : ∀ (D : EuclideanSpace ℝ (Fin n) → ℝ),
        MemLp D (ENNReal.ofReal 1) (volume.restrict (Metric.ball x₀ R)) →
        ∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous χ → HasCompactSupport χ →
        IntegrableOn (fun x => D x * χ x) (Metric.ball x₀ R) volume := by
      intro D hD χ hχc hχcs
      obtain ⟨Cχ, hCχ⟩ := hχcs.exists_bound_of_continuous hχc
      have hDint : Integrable D (volume.restrict (Metric.ball x₀ R)) := by
        rw [hone] at hD
        exact memLp_one_iff_integrable.1 hD
      refine Integrable.mono' (hDint.norm.const_mul Cχ)
        (hDint.1.mul hχc.aestronglyMeasurable) ?_
      filter_upwards with x
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hCχ x) (norm_nonneg _)
    have hcoint : ∀ (D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (i : Fin n),
        MemLp D (ENNReal.ofReal 1) (volume.restrict (Metric.ball x₀ R)) →
        MemLp (fun x => D x i) (ENNReal.ofReal 1)
          (volume.restrict (Metric.ball x₀ R)) := by
      intro D i hD
      refine hD.mono ((hproj i).comp_aestronglyMeasurable hD.1) ?_
      exact Filter.Eventually.of_forall fun x => hcoord _ i
    refine ⟨?_, hu1.sub hu2, hG1.sub hG2⟩
    intro ψ hψsm hψcs hψΩ i
    have hDψc : Continuous (fun x => fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) :=
      (hψsm.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hDψcs : HasCompactSupport
        (fun x => fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) :=
      (hψcs.fderiv ℝ).comp_left
        (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
          L (EuclideanSpace.single i (1 : ℝ))) (by simp)
    have e1 : (∫ x in Metric.ball x₀ R, (u₁ x - u₂ x) *
          fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))
        = (∫ x in Metric.ball x₀ R, u₁ x *
            fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))
          - ∫ x in Metric.ball x₀ R, u₂ x *
            fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) := by
      rw [← integral_sub (hint u₁ hu1 _ hDψc hDψcs) (hint u₂ hu2 _ hDψc hDψcs)]
      refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
      ring
    have e2 : (∫ x in Metric.ball x₀ R, (G₁ x - G₂ x) i * ψ x)
        = (∫ x in Metric.ball x₀ R, G₁ x i * ψ x)
          - ∫ x in Metric.ball x₀ R, G₂ x i * ψ x := by
      rw [← integral_sub (hint _ (hcoint G₁ i hG1) _ hψsm.continuous hψcs)
        (hint _ (hcoint G₂ i hG2) _ hψsm.continuous hψcs)]
      refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
      rw [hsubco (G₁ x) (G₂ x) i]
      ring
    rw [e1, e2, hwg1 ψ hψsm hψcs hψΩ i, hwg2 ψ hψsm hψcs hψΩ i]
    ring
  have hWk := WeakGradientPositivePart n 1 k hn1 le_rfl (Metric.ball x₀ R) f g
    Metric.isOpen_ball hBtop hW
  have hWl := WeakGradientPositivePart n 1 l hn1 le_rfl (Metric.ball x₀ R) f g
    Metric.isOpen_ball hBtop hW
  have hWw : MemW1pOn n 1 (Metric.ball x₀ R)
      (fun x => max (f x - k) 0 - max (f x - l) 0)
      (fun x => (if k < f x then g x else 0) - (if l < f x then g x else 0)) :=
    hsub _ _ _ _ hWk hWl
  -- the pointwise properties of `w`
  have hw0 : ∀ x : EuclideanSpace ℝ (Fin n), ¬ (k < f x) →
      max (f x - k) 0 - max (f x - l) 0 = 0 := by
    intro x hx
    have h1 : f x - k ≤ 0 := by linarith [not_lt.1 hx]
    have h2 : f x - l ≤ 0 := by linarith [not_lt.1 hx]
    rw [max_eq_right h1, max_eq_right h2, sub_zero]
  have hwtop : ∀ x : EuclideanSpace ℝ (Fin n), l < f x →
      max (f x - k) 0 - max (f x - l) 0 = l - k := by
    intro x hx
    have h1 : (0:ℝ) ≤ f x - k := by linarith
    have h2 : (0:ℝ) ≤ f x - l := by linarith
    rw [max_eq_left h1, max_eq_left h2]
    ring
  have hwnn : ∀ x : EuclideanSpace ℝ (Fin n),
      0 ≤ max (f x - k) 0 - max (f x - l) 0 := by
    intro x
    have : max (f x - l) 0 ≤ max (f x - k) 0 :=
      max_le_max (by linarith) le_rfl
    linarith
  have hwle : ∀ x : EuclideanSpace ℝ (Fin n),
      max (f x - k) 0 - max (f x - l) 0 ≤ l - k := by
    intro x
    rcases le_or_gt (f x) k with h1 | h1
    · rw [hw0 x (not_lt.2 h1)]; linarith
    · rcases le_or_gt (f x) l with h2 | h2
      · rw [max_eq_left (by linarith), max_eq_right (by linarith), sub_zero]
        linarith
      · rw [hwtop x h2]
  -- a measurable representative of `f`, used only for the null-measurability of
  -- the three level sets in the statement (`f` is only a.e. measurable on `B`)
  obtain ⟨f', hf'meas, hf'ae⟩ : ∃ f' : EuclideanSpace ℝ (Fin n) → ℝ, Measurable f' ∧
      f =ᵐ[volume.restrict (Metric.ball x₀ R)] f' :=
    ⟨hW.2.1.1.mk f, hW.2.1.1.stronglyMeasurable_mk.measurable, hW.2.1.1.ae_eq_mk⟩
  have hnull : volume ({x | f x = f' x}ᶜ ∩ Metric.ball x₀ R) = 0 := by
    have h := hf'ae
    rw [Filter.EventuallyEq, Filter.eventually_iff, mem_ae_iff,
      Measure.restrict_apply' measurableSet_ball] at h
    simpa using h
  have hkey : ∀ T U : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      (∀ y, ¬ (y ∈ T ↔ y ∈ U) → y ∈ {x | f x = f' x}ᶜ ∩ Metric.ball x₀ R) →
      NullMeasurableSet U volume := by
    intro T U hT hsub
    refine (hT.nullMeasurableSet).congr ?_
    rw [Filter.eventuallyEq_set]
    exact (MeasureTheory.ae_iff).2 (measure_mono_null hsub hnull)
  have hnmB : ∀ c : ℝ,
      NullMeasurableSet (Metric.ball x₀ R ∩ {y | c < f y}) volume := by
    intro c
    refine hkey (Metric.ball x₀ R ∩ {y | c < f' y}) _
      (measurableSet_ball.inter (measurableSet_lt measurable_const hf'meas)) ?_
    intro y hy
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff] at hy ⊢
    refine ⟨?_, ?_⟩
    · intro hfe
      rw [hfe] at hy
      tauto
    · by_contra hyB
      tauto
  have hnmZ : NullMeasurableSet (Metric.ball x₀ R \ {y | k < f y}) volume := by
    have hrw : Metric.ball x₀ R \ {y | k < f y}
        = Metric.ball x₀ R \ (Metric.ball x₀ R ∩ {y | k < f y}) := by
      ext y; constructor
      · intro hy; exact ⟨hy.1, fun hc => hy.2 hc.2⟩
      · intro hy; exact ⟨hy.1, fun hc => hy.2 ⟨hy.1, hc⟩⟩
    rw [hrw]
    exact measurableSet_ball.nullMeasurableSet.diff (hnmB k)
  have hnmE : NullMeasurableSet
      ((Metric.ball x₀ R ∩ {y | k < f y}) \ {y | l < f y}) volume := by
    have hrw : (Metric.ball x₀ R ∩ {y | k < f y}) \ {y | l < f y}
        = (Metric.ball x₀ R ∩ {y | k < f y})
          \ (Metric.ball x₀ R ∩ {y | l < f y}) := by
      ext y; constructor
      · intro hy; exact ⟨hy.1, fun hc => hy.2 hc.2⟩
      · intro hy; exact ⟨hy.1, fun hc => hy.2 ⟨hy.1.1, hc⟩⟩
    rw [hrw]
    exact (hnmB k).diff (hnmB l)
  -- the mean of `w` over `B`, and the `L^q` seminorm of `w - a`
  set a : ℝ := (volume (Metric.ball x₀ R)).toReal⁻¹
    * ∫ y in Metric.ball x₀ R, (max (f y - k) 0 - max (f y - l) 0) with hadef
  set S : ℝ := (eLpNorm (fun x => (max (f x - k) 0 - max (f x - l) 0) - a)
    (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
    (volume.restrict (Metric.ball x₀ R))).toReal with hSdef
  have ha0 : 0 ≤ a := by
    rw [hadef]
    refine mul_nonneg (by positivity) ?_
    exact integral_nonneg fun y => hwnn y
  have hfinB : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  have hp0 : (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1))) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hq0
  have hptop : (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1))) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqr : (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1))).toReal
      = (n : ℝ) / ((n : ℝ) - 1) := ENNReal.toReal_ofReal hq0.le
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)) :=
    ENNReal.one_le_ofReal.2 hq.le
  have hwmem : MemLp (fun x => (max (f x - k) 0 - max (f x - l) 0) - a)
      (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
      (volume.restrict (Metric.ball x₀ R)) := by
    refine MemLp.of_bound (hWw.2.1.1.sub aestronglyMeasurable_const) ((l - k) + |a|) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [le_abs_self a, neg_abs_le a, hwle x, hwnn x, hlk.le],
      by linarith [le_abs_self a, neg_abs_le a, hwle x, hwnn x, hlk.le]⟩
  have hStop : eLpNorm (fun x => (max (f x - k) 0 - max (f x - l) 0) - a)
      (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
      (volume.restrict (Metric.ball x₀ R)) ≠ ⊤ := hwmem.eLpNorm_lt_top.ne
  -- Step 1 (tail): the weak gradient of `w` is `g` on `E` and `0` elsewhere,
  -- so the Sobolev-Poincaré right-hand side is the paper's integral
  have hGnorm : (∫ x in Metric.ball x₀ R,
        ‖(if k < f x then g x else 0) - (if l < f x then g x else 0)‖)
      = ∫ x in (Metric.ball x₀ R ∩ {y | k < f y}) \ {y | l < f y}, ‖g x‖ := by
    have hptw : ∀ x ∈ Metric.ball x₀ R,
        ‖(if k < f x then g x else 0) - (if l < f x then g x else 0)‖
          = ((Metric.ball x₀ R ∩ {y | k < f y}) \ {y | l < f y}).indicator
              (fun y => ‖g y‖) x := by
      intro x hx
      by_cases hk : k < f x
      · by_cases hl : l < f x
        · rw [if_pos hk, if_pos hl, sub_self, norm_zero,
            Set.indicator_of_notMem (fun hc => hc.2 hl)]
        · have hmem : x ∈ (Metric.ball x₀ R ∩ {y | k < f y}) \ {y | l < f y} :=
            ⟨⟨hx, hk⟩, hl⟩
          rw [if_pos hk, if_neg hl, sub_zero, Set.indicator_of_mem hmem]
      · have hl : ¬ (l < f x) := fun hc => hk (lt_of_le_of_lt hkl hc)
        rw [if_neg hk, if_neg hl, sub_self, norm_zero,
          Set.indicator_of_notMem (fun hc => hk hc.1.2)]
    calc (∫ x in Metric.ball x₀ R,
          ‖(if k < f x then g x else 0) - (if l < f x then g x else 0)‖)
        = ∫ x in Metric.ball x₀ R,
            ((Metric.ball x₀ R ∩ {y | k < f y}) \ {y | l < f y}).indicator
              (fun y => ‖g y‖) x :=
          setIntegral_congr_fun measurableSet_ball hptw
      _ = ∫ x, (Metric.ball x₀ R).indicator
            (((Metric.ball x₀ R ∩ {y | k < f y}) \ {y | l < f y}).indicator
              (fun y => ‖g y‖)) x :=
          (integral_indicator measurableSet_ball).symm
      _ = ∫ x, ((Metric.ball x₀ R ∩ {y | k < f y}) \ {y | l < f y}).indicator
            (fun y => ‖g y‖) x := by
          rw [Set.indicator_indicator, Set.inter_eq_self_of_subset_right hEsub]
      _ = ∫ x in (Metric.ball x₀ R ∩ {y | k < f y}) \ {y | l < f y}, ‖g x‖ :=
          integral_indicator₀ hnmE
  -- Step 2: Sobolev-Poincaré applied to `w` on `B`
  have hS2 : S ≤ C * ∫ x in (Metric.ball x₀ R ∩ {y | k < f y}) \ {y | l < f y}, ‖g x‖ := by
    have hSPw := hSP x₀ R hR (fun x => max (f x - k) 0 - max (f x - l) 0)
      (fun x => (if k < f x then g x else 0) - (if l < f x then g x else 0)) hWw
    rw [hGnorm, ← hadef] at hSPw
    rw [hSdef, hwmem.eLpNorm_eq_integral_rpow_norm hp0 hptop, hqr,
      ENNReal.toReal_ofReal (by positivity),
      show ((n : ℝ) / ((n : ℝ) - 1))⁻¹ = ((n : ℝ) - 1) / (n : ℝ) from inv_div _ _]
    simp only [Real.norm_eq_abs]
    exact hSPw
  -- Step 3: bounding the mean.  This is where `hZpos` is used.
  have hS3 : a * (volume (Metric.ball x₀ R \ {y | k < f y})).toReal
      ≤ S * (volume (Metric.ball x₀ R \ {y | k < f y})).toReal ^ (1 / (n : ℝ)) := by
    have hZtop : volume (Metric.ball x₀ R \ {y | k < f y}) ≠ ⊤ := hmono _ hZsub
    have hZmem : MemLp (fun x => (max (f x - k) 0 - max (f x - l) 0) - a)
        (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
        (volume.restrict (Metric.ball x₀ R \ {y | k < f y})) :=
      hwmem.mono_measure (Measure.restrict_mono hZsub le_rfl)
    -- (i) on `Z` the integrand is the constant `a`
    have hi : (∫ x in Metric.ball x₀ R \ {y | k < f y},
          |(max (f x - k) 0 - max (f x - l) 0) - a|)
        = a * (volume (Metric.ball x₀ R \ {y | k < f y})).toReal := by
      have hcg : (∫ x in Metric.ball x₀ R \ {y | k < f y},
            |(max (f x - k) 0 - max (f x - l) 0) - a|)
          = ∫ _x in Metric.ball x₀ R \ {y | k < f y}, a := by
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem₀ hnmZ] with x hx
        rw [hw0 x hx.2, zero_sub, abs_neg, abs_of_nonneg ha0]
      rw [hcg, setIntegral_const, smul_eq_mul]
      simp [MeasureTheory.measureReal_def, mul_comm]
    -- (ii) Hölder at the conjugate pair `(1, q)`
    have hexp : (0 : ℝ) ≤ 1 - 1 / ((n : ℝ) / ((n : ℝ) - 1)) := by
      rw [hiq]
      have h1 : (0:ℝ) < 1 / (n : ℝ) := by positivity
      linarith
    have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := volume.restrict (Metric.ball x₀ R \ {y | k < f y})) (p := 1)
      (q := ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1))) hp1 hZmem.1
    rw [Measure.restrict_apply_univ, hqr] at hH
    simp only [ENNReal.toReal_one, one_div_one] at hH
    have hL1 : (∫ x in Metric.ball x₀ R \ {y | k < f y},
          |(max (f x - k) 0 - max (f x - l) 0) - a|)
        = (eLpNorm (fun x => (max (f x - k) 0 - max (f x - l) 0) - a) 1
            (volume.restrict (Metric.ball x₀ R \ {y | k < f y}))).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm hZmem.1]
      simp [Real.norm_eq_abs]
    have hstep : (eLpNorm (fun x => (max (f x - k) 0 - max (f x - l) 0) - a) 1
          (volume.restrict (Metric.ball x₀ R \ {y | k < f y}))).toReal
        ≤ (eLpNorm (fun x => (max (f x - k) 0 - max (f x - l) 0) - a)
            (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
            (volume.restrict (Metric.ball x₀ R \ {y | k < f y}))).toReal
          * (volume (Metric.ball x₀ R \ {y | k < f y})).toReal ^ (1 / (n : ℝ)) := by
      refine (ENNReal.toReal_mono ?_ hH).trans_eq ?_
      · exact ENNReal.mul_ne_top hZmem.eLpNorm_lt_top.ne
          (ENNReal.rpow_ne_top_of_nonneg hexp hZtop)
      · rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, hiq,
          show (1 : ℝ) - (1 - 1 / (n : ℝ)) = 1 / (n : ℝ) by ring]
    have hmono2 : (eLpNorm (fun x => (max (f x - k) 0 - max (f x - l) 0) - a)
          (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
          (volume.restrict (Metric.ball x₀ R \ {y | k < f y}))).toReal ≤ S := by
      rw [hSdef]
      exact ENNReal.toReal_mono hStop
        (eLpNorm_mono_measure _ (Measure.restrict_mono hZsub le_rfl))
    calc a * (volume (Metric.ball x₀ R \ {y | k < f y})).toReal
        = (eLpNorm (fun x => (max (f x - k) 0 - max (f x - l) 0) - a) 1
            (volume.restrict (Metric.ball x₀ R \ {y | k < f y}))).toReal := by
          rw [← hL1, hi]
      _ ≤ (eLpNorm (fun x => (max (f x - k) 0 - max (f x - l) 0) - a)
            (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
            (volume.restrict (Metric.ball x₀ R \ {y | k < f y}))).toReal
          * (volume (Metric.ball x₀ R \ {y | k < f y})).toReal ^ (1 / (n : ℝ)) := hstep
      _ ≤ S * (volume (Metric.ball x₀ R \ {y | k < f y})).toReal ^ (1 / (n : ℝ)) := by
          refine mul_le_mul_of_nonneg_right hmono2 ?_
          positivity
  -- Step 4: bounding the left-hand side
  have hS4 : (l - k) * (volume (Metric.ball x₀ R ∩ {y | l < f y})).toReal
        ^ (1 - 1 / (n : ℝ))
      ≤ S + a * (volume (Metric.ball x₀ R ∩ {y | l < f y})).toReal ^ (1 - 1 / (n : ℝ)) := by
    have hAltop : volume (Metric.ball x₀ R ∩ {y | l < f y}) ≠ ⊤ := hmono _ hAlsub
    have hAlmem : MemLp (fun x => (max (f x - k) 0 - max (f x - l) 0) - a)
        (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
        (volume.restrict (Metric.ball x₀ R ∩ {y | l < f y})) :=
      hwmem.mono_measure (Measure.restrict_mono hAlsub le_rfl)
    have hLHS : eLpNorm (fun x => max (f x - k) 0 - max (f x - l) 0)
          (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
          (volume.restrict (Metric.ball x₀ R ∩ {y | l < f y}))
        = ENNReal.ofReal (l - k)
          * (volume (Metric.ball x₀ R ∩ {y | l < f y})) ^ (1 - 1 / (n : ℝ)) := by
      have hcg : eLpNorm (fun x => max (f x - k) 0 - max (f x - l) 0)
            (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
            (volume.restrict (Metric.ball x₀ R ∩ {y | l < f y}))
          = eLpNorm (fun _ : EuclideanSpace ℝ (Fin n) => l - k)
            (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
            (volume.restrict (Metric.ball x₀ R ∩ {y | l < f y})) := by
        refine eLpNorm_congr_ae ?_
        filter_upwards [ae_restrict_mem₀ (hnmB l)] with x hx
        exact hwtop x hx.2
      rw [hcg, eLpNorm_const' _ hp0 hptop, Measure.restrict_apply_univ, hqr, hiq,
        ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ l - k)]
    have hRHS : eLpNorm (fun _ : EuclideanSpace ℝ (Fin n) => a)
          (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
          (volume.restrict (Metric.ball x₀ R ∩ {y | l < f y}))
        = ENNReal.ofReal a
          * (volume (Metric.ball x₀ R ∩ {y | l < f y})) ^ (1 - 1 / (n : ℝ)) := by
      rw [eLpNorm_const' _ hp0 hptop, Measure.restrict_apply_univ, hqr, hiq,
        ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ha0]
    have hadd : eLpNorm (fun x => max (f x - k) 0 - max (f x - l) 0)
          (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
          (volume.restrict (Metric.ball x₀ R ∩ {y | l < f y}))
        ≤ eLpNorm (fun x => (max (f x - k) 0 - max (f x - l) 0) - a)
            (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
            (volume.restrict (Metric.ball x₀ R ∩ {y | l < f y}))
          + eLpNorm (fun _ : EuclideanSpace ℝ (Fin n) => a)
            (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
            (volume.restrict (Metric.ball x₀ R ∩ {y | l < f y})) := by
      have h := eLpNorm_add_le
        (f := fun x => (max (f x - k) 0 - max (f x - l) 0) - a)
        (g := fun _ : EuclideanSpace ℝ (Fin n) => a)
        (μ := volume.restrict (Metric.ball x₀ R ∩ {y | l < f y}))
        (p := ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
        hAlmem.1 aestronglyMeasurable_const hp1
      have heq : ((fun x => (max (f x - k) 0 - max (f x - l) 0) - a)
            + (fun _ : EuclideanSpace ℝ (Fin n) => a))
          = fun x => max (f x - k) 0 - max (f x - l) 0 := by
        funext x
        simp
      rwa [heq] at h
    rw [hLHS, hRHS] at hadd
    have hfin1 : eLpNorm (fun x => (max (f x - k) 0 - max (f x - l) 0) - a)
        (ENNReal.ofReal ((n : ℝ) / ((n : ℝ) - 1)))
        (volume.restrict (Metric.ball x₀ R ∩ {y | l < f y})) ≠ ⊤ :=
      hAlmem.eLpNorm_lt_top.ne
    have hfin2 : (volume (Metric.ball x₀ R ∩ {y | l < f y})) ^ (1 - 1 / (n : ℝ)) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg hiqnn hAltop
    have htr := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hfin1, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin2⟩) hadd
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ l - k),
      ← ENNReal.toReal_rpow, ENNReal.toReal_add hfin1
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin2),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0, ← ENNReal.toReal_rpow] at htr
    refine htr.trans ?_
    refine add_le_add ?_ le_rfl
    rw [hSdef]
    exact ENNReal.toReal_mono hStop
      (eLpNorm_mono_measure _ (Measure.restrict_mono hAlsub le_rfl))
  -- Step 5: combining
  have hmBpos : 0 < (volume (Metric.ball x₀ R)).toReal :=
    ENNReal.toReal_pos hBpos.ne' hBtop
  have hmZB : (volume (Metric.ball x₀ R \ {y | k < f y})).toReal
      ≤ (volume (Metric.ball x₀ R)).toReal :=
    ENNReal.toReal_mono hBtop (measure_mono hZsub)
  have hmAlB : (volume (Metric.ball x₀ R ∩ {y | l < f y})).toReal
      ≤ (volume (Metric.ball x₀ R)).toReal :=
    ENNReal.toReal_mono hBtop (measure_mono hAlsub)
  have hSnn : 0 ≤ S := ENNReal.toReal_nonneg
  have hRpow : R ^ ((n : ℕ) : ℝ) = R ^ n := Real.rpow_natCast R n
  have hA : (volume (Metric.ball x₀ R \ {y | k < f y})).toReal ^ (1 / (n : ℝ))
        * (volume (Metric.ball x₀ R)).toReal ^ (1 - 1 / (n : ℝ))
      ≤ (volume (Metric.ball x₀ R)).toReal := by
    calc (volume (Metric.ball x₀ R \ {y | k < f y})).toReal ^ (1 / (n : ℝ))
          * (volume (Metric.ball x₀ R)).toReal ^ (1 - 1 / (n : ℝ))
        ≤ (volume (Metric.ball x₀ R)).toReal ^ (1 / (n : ℝ))
          * (volume (Metric.ball x₀ R)).toReal ^ (1 - 1 / (n : ℝ)) := by
          gcongr
      _ = (volume (Metric.ball x₀ R)).toReal := by
          rw [← Real.rpow_add hmBpos]
          norm_num
  have hC2 : a * (volume (Metric.ball x₀ R ∩ {y | l < f y})).toReal ^ (1 - 1 / (n : ℝ))
      ≤ S * (volume (Metric.ball x₀ R)).toReal
        / (volume (Metric.ball x₀ R \ {y | k < f y})).toReal := by
    have h2 : a ≤ S * (volume (Metric.ball x₀ R \ {y | k < f y})).toReal ^ (1 / (n : ℝ))
        / (volume (Metric.ball x₀ R \ {y | k < f y})).toReal := by
      rw [le_div_iff₀ hZpos]
      linarith [hS3]
    have hB2 : (volume (Metric.ball x₀ R ∩ {y | l < f y})).toReal ^ (1 - 1 / (n : ℝ))
        ≤ (volume (Metric.ball x₀ R)).toReal ^ (1 - 1 / (n : ℝ)) :=
      Real.rpow_le_rpow ENNReal.toReal_nonneg hmAlB hiqnn
    calc a * (volume (Metric.ball x₀ R ∩ {y | l < f y})).toReal ^ (1 - 1 / (n : ℝ))
        ≤ a * (volume (Metric.ball x₀ R)).toReal ^ (1 - 1 / (n : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hB2 ha0
      _ ≤ (S * (volume (Metric.ball x₀ R \ {y | k < f y})).toReal ^ (1 / (n : ℝ))
            / (volume (Metric.ball x₀ R \ {y | k < f y})).toReal)
            * (volume (Metric.ball x₀ R)).toReal ^ (1 - 1 / (n : ℝ)) := by
          exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hmBpos.le _)
      _ = S * ((volume (Metric.ball x₀ R \ {y | k < f y})).toReal ^ (1 / (n : ℝ))
            * (volume (Metric.ball x₀ R)).toReal ^ (1 - 1 / (n : ℝ)))
            / (volume (Metric.ball x₀ R \ {y | k < f y})).toReal := by ring
      _ ≤ S * (volume (Metric.ball x₀ R)).toReal
            / (volume (Metric.ball x₀ R \ {y | k < f y})).toReal := by
          gcongr
  have ht1 : 1 ≤ (volume (Metric.ball x₀ R)).toReal
      / (volume (Metric.ball x₀ R \ {y | k < f y})).toReal :=
    (one_le_div hZpos).2 hmZB
  calc (l - k) * (volume (Metric.ball x₀ R ∩ {y | l < f y})).toReal ^ (1 - 1 / (n : ℝ))
      ≤ S + a * (volume (Metric.ball x₀ R ∩ {y | l < f y})).toReal
          ^ (1 - 1 / (n : ℝ)) := hS4
    _ ≤ S + S * (volume (Metric.ball x₀ R)).toReal
          / (volume (Metric.ball x₀ R \ {y | k < f y})).toReal := by linarith [hC2]
    _ ≤ 2 * (S * ((volume (Metric.ball x₀ R)).toReal
          / (volume (Metric.ball x₀ R \ {y | k < f y})).toReal)) := by
        have h3 : S ≤ S * ((volume (Metric.ball x₀ R)).toReal
            / (volume (Metric.ball x₀ R \ {y | k < f y})).toReal) := by
          nlinarith [hSnn, ht1]
        have h4 : S * (volume (Metric.ball x₀ R)).toReal
              / (volume (Metric.ball x₀ R \ {y | k < f y})).toReal
            = S * ((volume (Metric.ball x₀ R)).toReal
              / (volume (Metric.ball x₀ R \ {y | k < f y})).toReal) := by ring
        rw [h4]
        linarith
    _ ≤ 2 * ((C * ∫ x in (Metric.ball x₀ R ∩ {y | k < f y}) \ {y | l < f y}, ‖g x‖)
          * ((volume (Metric.ball x₀ R)).toReal
            / (volume (Metric.ball x₀ R \ {y | k < f y})).toReal)) := by
        have hfr : 0 ≤ (volume (Metric.ball x₀ R)).toReal
            / (volume (Metric.ball x₀ R \ {y | k < f y})).toReal := by positivity
        nlinarith [hS2, hfr]
    _ = 2 * C * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
          * R ^ ((n : ℕ) : ℝ)
          / (volume (Metric.ball x₀ R \ {y | k < f y})).toReal
          * ∫ x in (Metric.ball x₀ R ∩ {y | k < f y}) \ {y | l < f y}, ‖g x‖ := by
        rw [hRpow, hball]
        field_simp
