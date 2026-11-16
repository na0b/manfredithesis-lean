import ManfrediThesis.Preamble
import ManfrediThesis.SegmentWeightIntegrable
open MeasureTheory

/-- The second-order expansion along a segment with integral remainder, valid
across one degenerate point.  This is the paper's "Integrating by parts, we
obtain ..." display in the proof of Lemma 4.1 (thesis l. 1088-1090), made
precise: the remainder integrand `q` is the second directional derivative of
`f` along the segment, which exists off the set where the weight
`ε + |·|²` vanishes -- at most one point of the segment -- and the identity
survives that point. -/
theorem SegmentSecondOrderIdentity :
    ∀ (n : ℕ) (p ε ν₁ : ℝ), 1 < p → 0 ≤ ε → 0 ≤ ν₁ →
      ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ)
        (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        (∀ h : EuclideanSpace ℝ (Fin n), DifferentiableAt ℝ f h) →
        (∀ h ζ : EuclideanSpace ℝ (Fin n), fderiv ℝ f h ζ = ∑ i, A h i * ζ i) →
        Continuous A →
        ∀ (a b : EuclideanSpace ℝ (Fin n)) (q : ℝ → ℝ),
          (∀ t : ℝ, ε + ‖t • a + (1 - t) • b‖ ^ 2 ≠ 0 →
            HasDerivAt (fun s : ℝ => ∑ i, A (s • a + (1 - s) • b) i * (a - b) i) (q t) t) →
          (∀ t : ℝ, ε + ‖t • a + (1 - t) • b‖ ^ 2 ≠ 0 →
            |q t| ≤ ν₁ * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2) →
          (∀ t : ℝ, ε + ‖t • a + (1 - t) • b‖ ^ 2 = 0 → q t = 0) →
          IntervalIntegrable (fun t : ℝ => (1 - t) * q t) volume 0 1 ∧
            f a - f b
              = (∑ i, A b i * (a - b) i) + ∫ t in (0:ℝ)..1, (1 - t) * q t := by
  intro n p ε ν₁ hp hε hν₁ f A hfd hfA hAc a b q hqd hqb hq0
  have hfc : Continuous f := Differentiable.continuous hfd
  have hξc : Continuous (fun s : ℝ => s • a + (1 - s) • b) := by fun_prop
  have hξd : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => s • a + (1 - s) • b) (a - b) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s • a) a t := by
      simpa using (hasDerivAt_id t).smul_const a
    have h2 : HasDerivAt (fun s : ℝ => (1 - s) • b) (-b) t := by
      have h := ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).smul_const b
      simpa using h
    have h3 : HasDerivAt (fun s : ℝ => s • a + (1 - s) • b) (a + -b) t := h1.add h2
    rwa [← sub_eq_add_neg] at h3
  -- the degenerate case `a = b`
  by_cases hab : a = b
  · have hζ : a - b = 0 := by rw [hab]; simp
    have hq00 : ∀ t : ℝ, q t = 0 := by
      intro t
      by_cases ht : ε + ‖t • a + (1 - t) • b‖ ^ 2 = 0
      · exact hq0 t ht
      · have h1 := hqd t ht
        have h2 : (fun s : ℝ => ∑ i, A (s • a + (1 - s) • b) i * (a - b) i)
            = fun _ : ℝ => (0:ℝ) := by
          funext s
          rw [hζ]
          simp
        rw [h2] at h1
        exact ((hasDerivAt_const t (0:ℝ)).unique h1).symm
    refine ⟨?_, ?_⟩
    · simp only [hq00, mul_zero]
      exact intervalIntegrable_const
    · simp only [hq00, mul_zero, hab]
      simp
  -- the main case
  have hζ0 : a - b ≠ 0 := sub_ne_zero.2 hab
  set ψ : ℝ → ℝ := fun t => ∑ i, A (t • a + (1 - t) • b) i * (a - b) i with hψdef
  have hinner : ∀ v w : EuclideanSpace ℝ (Fin n), ∑ i, v i * w i = inner ℝ v w := by
    intro v w
    rw [PiLp.inner_apply]
    simp [RCLike.inner_apply, mul_comm]
  have hψc : Continuous ψ := by
    have he : ψ = fun t : ℝ => (inner ℝ (A (t • a + (1 - t) • b)) (a - b) : ℝ) := by
      funext t
      rw [hψdef]
      exact hinner _ _
    rw [he]
    exact Continuous.inner (hAc.comp hξc) continuous_const
  have hfξd : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => f (s • a + (1 - s) • b)) (ψ t) t := by
    intro t
    have h2 : HasDerivAt ((fun y => f y) ∘ fun s : ℝ => s • a + (1 - s) • b)
        (fderiv ℝ f (t • a + (1 - t) • b) (a - b)) t :=
      (hfd _).hasFDerivAt.comp_hasDerivAt t (hξd t)
    rw [hfA] at h2
    exact h2
  set K : ℝ → ℝ := fun t => f (t • a + (1 - t) • b) + (1 - t) * ψ t with hKdef
  have hKc : Continuous K := by
    rw [hKdef]
    exact (hfc.comp hξc).add ((continuous_const.sub continuous_id).mul hψc)
  have hKd : ∀ t : ℝ, ε + ‖t • a + (1 - t) • b‖ ^ 2 ≠ 0 →
      HasDerivAt K ((1 - t) * q t) t := by
    intro t ht
    have h1 := hfξd t
    have h2 : HasDerivAt (fun s : ℝ => (1 - s) * ψ s)
        ((0 - 1) * ψ t + (1 - t) * q t) t :=
      ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).mul (hqd t ht)
    have h3 := h1.add h2
    have h4 : (1 - t) * q t = ψ t + ((0 - 1) * ψ t + (1 - t) * q t) := by ring
    rw [hKdef, h4]
    exact h3
  -- the exceptional set is at most a point
  have hTsub : ∀ t t' : ℝ, ε + ‖t • a + (1 - t) • b‖ ^ 2 = 0 →
      ε + ‖t' • a + (1 - t') • b‖ ^ 2 = 0 → t = t' := by
    have hz : ∀ s : ℝ, ε + ‖s • a + (1 - s) • b‖ ^ 2 = 0 →
        s • a + (1 - s) • b = 0 := by
      intro s hs
      have h1 : ‖s • a + (1 - s) • b‖ ^ 2 = 0 := by
        have h2 := sq_nonneg ‖s • a + (1 - s) • b‖
        linarith
      have h3 : ‖s • a + (1 - s) • b‖ = 0 := by
        exact pow_eq_zero_iff (two_ne_zero) |>.1 h1
      exact norm_eq_zero.1 h3
    intro t t' h h'
    have e1 := hz t h
    have e2 := hz t' h'
    have e0 : (t • a + (1 - t) • b) - (t' • a + (1 - t') • b) = (t - t') • (a - b) := by
      module
    have e3 : (t - t') • (a - b) = 0 := by rw [← e0, e1, e2, sub_zero]
    rcases smul_eq_zero.1 e3 with h5 | h5
    · exact sub_eq_zero.mp h5
    · exact absurd h5 hζ0
  have hS0 : volume {t : ℝ | ε + ‖t • a + (1 - t) • b‖ ^ 2 = 0} = 0 := by
    rcases Set.eq_empty_or_nonempty {t : ℝ | ε + ‖t • a + (1 - t) • b‖ ^ 2 = 0} with
      he | ⟨t₀, ht₀⟩
    · rw [he]; exact measure_empty
    · exact measure_mono_null (fun t ht => hTsub t t₀ ht ht₀) (measure_singleton t₀)
  have hae : deriv ψ =ᵐ[volume] q := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine measure_mono_null (fun t ht => ?_) hS0
    by_contra hc
    exact ht ((hqd t hc).deriv)
  have hqmeas : AEStronglyMeasurable q (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    refine ((measurable_deriv ψ).aestronglyMeasurable).congr ?_
    exact hae.filter_mono (ae_mono Measure.restrict_le_self)
  have hwnn : ∀ t : ℝ, (0:ℝ) ≤ (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1) := by
    intro t
    exact Real.rpow_nonneg (by positivity) _
  have hdom : IntervalIntegrable (fun t : ℝ => (1 - t) * q t) volume 0 1 := by
    have hw := (SegmentWeightIntegrable n p hp ε a b hε).const_mul (ν₁ * ‖a - b‖ ^ 2)
    refine IntervalIntegrable.mono_fun' hw ?_ ?_
    · exact ((continuous_const.sub continuous_id).aestronglyMeasurable).mul hqmeas
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      have ht1 : t ≤ 1 := ht.2
      have ht0 : 0 < t := ht.1
      have habs : |1 - t| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      have hqabs : |q t| ≤ ν₁ * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2 := by
        by_cases hc : ε + ‖t • a + (1 - t) • b‖ ^ 2 = 0
        · rw [hq0 t hc, abs_zero]
          positivity
        · exact hqb t hc
      calc ‖(1 - t) * q t‖ = |1 - t| * |q t| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ 1 * |q t| := by
            refine mul_le_mul_of_nonneg_right habs (abs_nonneg _)
        _ = |q t| := one_mul _
        _ ≤ ν₁ * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2 := hqabs
        _ = ν₁ * ‖a - b‖ ^ 2 * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1) := by ring
  -- the fundamental theorem of calculus, past the single bad point
  have hFTC : (∫ t in (0:ℝ)..1, (1 - t) * q t) = K 1 - K 0 := by
    by_cases hex : ∃ t₀ ∈ Set.Ioo (0:ℝ) 1, ε + ‖t₀ • a + (1 - t₀) • b‖ ^ 2 = 0
    · obtain ⟨t₀, ht₀mem, ht₀⟩ := hex
      have hd1 : ∀ x ∈ Set.Ioo (0:ℝ) t₀, HasDerivAt K ((1 - x) * q x) x := by
        intro x hx
        refine hKd x (fun hcon => ?_)
        have hxe := hTsub x t₀ hcon ht₀
        linarith [hxe.le, hxe.ge, hx.1, hx.2]
      have hd2 : ∀ x ∈ Set.Ioo t₀ (1:ℝ), HasDerivAt K ((1 - x) * q x) x := by
        intro x hx
        refine hKd x (fun hcon => ?_)
        have hxe := hTsub x t₀ hcon ht₀
        linarith [hxe.le, hxe.ge, hx.1, hx.2]
      have hsub1 : Set.uIcc (0:ℝ) t₀ ⊆ Set.uIcc (0:ℝ) 1 := by
        rw [Set.uIcc_of_le ht₀mem.1.le, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact Set.Icc_subset_Icc le_rfl ht₀mem.2.le
      have hsub2 : Set.uIcc t₀ (1:ℝ) ⊆ Set.uIcc (0:ℝ) 1 := by
        rw [Set.uIcc_of_le ht₀mem.2.le, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact Set.Icc_subset_Icc ht₀mem.1.le le_rfl
      have h1 : (∫ t in (0:ℝ)..t₀, (1 - t) * q t) = K t₀ - K 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht₀mem.1.le
          hKc.continuousOn hd1 (hdom.mono_set hsub1)
      have h2 : (∫ t in t₀..(1:ℝ), (1 - t) * q t) = K 1 - K t₀ :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht₀mem.2.le
          hKc.continuousOn hd2 (hdom.mono_set hsub2)
      have h3 := intervalIntegral.integral_add_adjacent_intervals
        (hdom.mono_set hsub1) (hdom.mono_set hsub2)
      rw [h1, h2] at h3
      rw [← h3]
      ring
    · have hex' : ∀ x ∈ Set.Ioo (0:ℝ) 1, ε + ‖x • a + (1 - x) • b‖ ^ 2 ≠ 0 := by
        intro x hx hcon
        exact hex ⟨x, hx, hcon⟩
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
        hKc.continuousOn (fun x hx => hKd x (hex' x hx)) hdom
  refine ⟨hdom, ?_⟩
  have hK1 : K 1 = f a := by
    rw [hKdef]; norm_num
  have hK0 : K 0 = f b + ∑ i, A b i * (a - b) i := by
    rw [hKdef]
    simp only [hψdef]
    norm_num
  rw [hFTC, hK1, hK0]
  ring
