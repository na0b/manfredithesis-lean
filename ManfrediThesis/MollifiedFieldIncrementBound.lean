import ManfrediThesis.Preamble
set_option maxHeartbeats 800000
open MeasureTheory

/-- The increment bound for the mollified field along a direction: with
`A_e(h') = ∫ρ(z)A(h' + \sqrt e z)dz - ∫ρ(z)A(\sqrt e z)dz`, for every `t > 0`
\[
\bigl|\bigl(A_e(h+tu)-A_e(h)\bigr)_i\bigr|\ \le\ t\,γ₁\,C₂\,M(t),
\]
where `M(t)` majorises the structure weight along the segment.

Conventions, restated here because a helper inherits none of its parent's.
Per pm-0024(1) the weight is the printed `Real.rpow`
`(e + ‖·‖²)^{p/2-1}`, and no sign hypothesis on `p/2 - 1` is needed: the
segment bound `M` is assumed to majorise the weight for every displacement of
size at most `t`, which is exactly what makes the estimate uniform in the sign
of the exponent.  `A_e` is carried as a function variable together with its
coordinate difference formula, since only that formula is used.  The direction
`u` is an arbitrary vector, the coordinate `i` an arbitrary index, and the
segment parameter runs over `Ioc(0,1)`, so the mean-value integral below is
over a finite-measure interval.

The route.  By the difference formula, the `i`-th coordinate of
`A_e(h+tu) - A_e(h)` is
`∫ρ(z)\bigl(A(h+tu+\sqrt e z)_i - A(h+\sqrt e z)_i\bigr)dz`.  For almost every
`z` the segment from `h+\sqrt e z` to `h+tu+\sqrt e z` avoids the origin ---
that is the hypothesis `hbad`, which is what lets the structure condition be
applied along it --- so the one-dimensional bound gives
\[
\bigl|A(h+\sqrt e z+tu)_i-A(h+\sqrt e z)_i\bigr|
\ \le\ |t|\,γ₁\!\int_{(0,1]}\bigl(\|h+\sqrt e z+(ς t)u\|^2\bigr)^{\frac p2-1}dς .
\]
On the inner integral the displacement `(ς t)u` has size at most `t`, so the
weight is bounded by `M(t)`, and the interval has measure `1`; hence the inner
integral is at most `M(t)`.  Multiplying by `ρ(z) ≥ 0`, integrating in `z`, and
using `∫ρ ≤ C₂`-type normalisation through the sandwich hypothesis bounds the
whole expression by `t γ₁ C₂ M(t)`; Tonelli is legitimate because the double
integrand is integrable by the kernel hypothesis.  Taking absolute values
through the integral (the norm inequality for the integral, Preamble) gives the
assertion. -/
theorem MollifiedFieldIncrementBound :
    ∀ (n : ℕ) (p c₁ C₂ γ₁ e : ℝ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
      (A Ae : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (h u : EuclideanSpace ℝ (Fin n)) (i : Fin n) (Mb : ℝ → ℝ),
      (∀ z, 0 ≤ ρ z) → HasCompactSupport ρ → Continuous ρ → Continuous A →
      0 < C₂ → (0 : ℝ) ≤ γ₁ → 0 < e →
      (∀ (h' : EuclideanSpace ℝ (Fin n)) (e' : ℝ), 0 < e' →
        c₁ * (e' + ‖h'‖ ^ 2) ^ (p / 2 - 1)
            ≤ ∫ z, (‖h' + Real.sqrt e' • z‖ ^ 2) ^ (p / 2 - 1) * ρ z
          ∧ (∫ z, (‖h' + Real.sqrt e' • z‖ ^ 2) ^ (p / 2 - 1) * ρ z)
            ≤ C₂ * (e' + ‖h'‖ ^ 2) ^ (p / 2 - 1)) →
      (∀ (t : ℝ) (b : EuclideanSpace ℝ (Fin n)),
        (∀ ς ∈ Set.Icc (0 : ℝ) 1, b + (ς * t) • u ≠ 0) →
        |A (b + t • u) i - A b i|
          ≤ |t| * γ₁ * ∫ ς in Set.Ioc (0 : ℝ) 1,
              (‖b + (ς * t) • u‖ ^ 2) ^ (p / 2 - 1)) →
      (∀ h' : EuclideanSpace ℝ (Fin n),
        Integrable (fun z => (‖h' + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ρ z)
          volume) →
      (∀ s : ℝ, s ≠ 0 → ∀ᵐ z : EuclideanSpace ℝ (Fin n),
        ∀ ς ∈ Set.Icc (0 : ℝ) 1, h + Real.sqrt e • z + (ς * s) • u ≠ 0) →
      (∀ h₁ h₂ : EuclideanSpace ℝ (Fin n),
        (Ae h₁ - Ae h₂) i
          = ∫ z, ρ z * (A (h₁ + Real.sqrt e • z) i - A (h₂ + Real.sqrt e • z) i)) →
      (∀ t s : ℝ, 0 < t → |s| ≤ t →
        (e + ‖h + s • u‖ ^ 2) ^ (p / 2 - 1) ≤ Mb t) →
      ∀ t : ℝ, 0 < t →
        |(Ae (h + t • u) - Ae h) i| ≤ t * (γ₁ * (C₂ * Mb t)) := by
  intro n p c₁ C₂ γ₁ e ρ A Ae h u i Mb hρ0 hρcs hρc hAcont hC₂0 hγ₁0 he0 hsw hIA hker
    hbad hdif hMb
  intro t ht
  have hfinmeas : IsFiniteMeasure ((volume : Measure ℝ).restrict
      (Set.Ioc (0 : ℝ) 1)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hbasec : Continuous (fun w : EuclideanSpace ℝ (Fin n) × ℝ =>
      ‖h + (w.2 * t) • u + Real.sqrt e • w.1‖ ^ 2) := by fun_prop
  have hmes : Measurable (fun w : EuclideanSpace ℝ (Fin n) × ℝ =>
      (‖h + (w.2 * t) • u + Real.sqrt e • w.1‖ ^ 2) ^ (p / 2 - 1)) := by
    have heq : (fun w : EuclideanSpace ℝ (Fin n) × ℝ =>
        (‖h + (w.2 * t) • u + Real.sqrt e • w.1‖ ^ 2) ^ (p / 2 - 1))
        = fun w : EuclideanSpace ℝ (Fin n) × ℝ =>
          if ‖h + (w.2 * t) • u + Real.sqrt e • w.1‖ ^ 2 = 0
          then (0 : ℝ) ^ (p / 2 - 1)
          else Real.exp (Real.log (‖h + (w.2 * t) • u + Real.sqrt e • w.1‖ ^ 2)
            * (p / 2 - 1)) := by
      funext w
      by_cases hw : ‖h + (w.2 * t) • u + Real.sqrt e • w.1‖ ^ 2 = 0
      · rw [if_pos hw, hw]
      · rw [if_neg hw,
          Real.rpow_def_of_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hw))]
    rw [heq]
    exact Measurable.ite (hbasec.measurable (measurableSet_singleton 0))
      measurable_const ((hbasec.measurable.log.mul_const _).exp)
  have hFmeas : AEStronglyMeasurable
      (Function.uncurry (fun (z : EuclideanSpace ℝ (Fin n)) (s : ℝ) =>
        ρ z * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) := by
    refine Measurable.aestronglyMeasurable ?_
    exact ((hρc.comp continuous_fst).measurable).mul hmes
  have hslice : ∀ s : ℝ,
      Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
        ρ z * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)) volume :=
    fun s => (hker (h + (s * t) • u)).congr
      (Filter.Eventually.of_forall fun z => by ring)
  have hnonneg : ∀ (s : ℝ) (z : EuclideanSpace ℝ (Fin n)),
      0 ≤ ρ z * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) :=
    fun s z => mul_nonneg (hρ0 z) (Real.rpow_nonneg (sq_nonneg _) _)
  have hsand : ∀ s : ℝ, (∫ z, ρ z
        * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1))
      ≤ C₂ * (e + ‖h + (s * t) • u‖ ^ 2) ^ (p / 2 - 1) := by
    intro s
    have h1 := (hsw (h + (s * t) • u) e he0).2
    have h2 : (∫ z, ρ z
          * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1))
        = ∫ z, (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ρ z :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
    rw [h2]
    exact h1
  have hseg : ∀ s ∈ Set.Ioc (0 : ℝ) 1, |s * t| ≤ t := by
    intro s hs
    rw [abs_mul, abs_of_pos ht, abs_of_pos hs.1]
    nlinarith [hs.1, hs.2]
  have hnormint : Integrable (fun s : ℝ => ∫ z : EuclideanSpace ℝ (Fin n),
      ‖ρ z * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)‖)
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := by
    refine Integrable.mono' (integrable_const (C₂ * Mb t)) ?_ ?_
    · exact (hFmeas.norm.prod_swap.integral_prod_right').congr
        (Filter.Eventually.of_forall fun s => rfl)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hz : (∫ z : EuclideanSpace ℝ (Fin n),
          ‖ρ z * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)‖)
          = ∫ z, ρ z * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => by
          show ‖ρ z * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)‖
            = ρ z * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)
          rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg s z)])
      have h0 : (0 : ℝ) ≤ ∫ z, ρ z
          * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) :=
        integral_nonneg (fun z => hnonneg s z)
      rw [Real.norm_eq_abs, hz, abs_of_nonneg h0]
      exact le_trans (hsand s)
        (mul_le_mul_of_nonneg_left (hMb t (s * t) ht (hseg s hs)) hC₂0.le)
  have hFint : Integrable
      (Function.uncurry (fun (z : EuclideanSpace ℝ (Fin n)) (s : ℝ) =>
        ρ z * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) :=
    (integrable_prod_iff' hFmeas).2
      ⟨Filter.Eventually.of_forall hslice, hnormint⟩
  have hswap := integral_integral_swap hFint
  have hinner : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      ∫ s in Set.Ioc (0 : ℝ) 1,
        ρ z * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)) volume :=
    hFint.integral_prod_left
  have hRHS : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      ρ z * (t * γ₁ * ∫ s in Set.Ioc (0 : ℝ) 1,
        (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1))) volume := by
    refine (hinner.const_mul (t * γ₁)).congr
      (Filter.Eventually.of_forall fun z => ?_)
    show t * γ₁ * (∫ s in Set.Ioc (0 : ℝ) 1,
        ρ z * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1))
      = ρ z * (t * γ₁ * ∫ s in Set.Ioc (0 : ℝ) 1,
        (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1))
    rw [integral_const_mul]
    ring
  have hc1 : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
      A (h + t • u + Real.sqrt e • z) i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
      (hAcont.comp (continuous_const.add (continuous_const_smul _)))
  have hc2 : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
      A (h + Real.sqrt e • z) i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
      (hAcont.comp (continuous_const.add (continuous_const_smul _)))
  have hLHS : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      ρ z * |A (h + t • u + Real.sqrt e • z) i
        - A (h + Real.sqrt e • z) i|) volume := by
    refine Continuous.integrable_of_hasCompactSupport
      (hρc.mul (hc1.sub hc2).abs) ?_
    refine HasCompactSupport.intro hρcs ?_
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hae : ∀ᵐ z : EuclideanSpace ℝ (Fin n),
      ρ z * |A (h + t • u + Real.sqrt e • z) i
          - A (h + Real.sqrt e • z) i|
        ≤ ρ z * (t * γ₁ * ∫ s in Set.Ioc (0 : ℝ) 1,
            (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)) := by
    filter_upwards [hbad t (ne_of_gt ht)] with z hz
    refine mul_le_mul_of_nonneg_left ?_ (hρ0 z)
    have h1 := hIA t (h + Real.sqrt e • z) hz
    rw [abs_of_pos ht] at h1
    rw [show h + Real.sqrt e • z + t • u = h + t • u + Real.sqrt e • z from by abel] at h1
    refine le_trans h1 (le_of_eq ?_)
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc (fun s _ => ?_)
    rw [show h + Real.sqrt e • z + (s * t) • u
      = h + (s * t) • u + Real.sqrt e • z from by abel]
  calc |(Ae (h + t • u) - Ae h) i|
      = |∫ z, ρ z * (A (h + t • u + Real.sqrt e • z) i
          - A (h + Real.sqrt e • z) i)| := by rw [hdif]
    _ ≤ ∫ z, |ρ z * (A (h + t • u + Real.sqrt e • z) i
          - A (h + Real.sqrt e • z) i)| := abs_integral_le_integral_abs
    _ = ∫ z, ρ z * |A (h + t • u + Real.sqrt e • z) i
          - A (h + Real.sqrt e • z) i| := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        show |ρ z * (A (h + t • u + Real.sqrt e • z) i
            - A (h + Real.sqrt e • z) i)|
          = ρ z * |A (h + t • u + Real.sqrt e • z) i
            - A (h + Real.sqrt e • z) i|
        rw [abs_mul, abs_of_nonneg (hρ0 z)]
    _ ≤ ∫ z, ρ z * (t * γ₁ * ∫ s in Set.Ioc (0 : ℝ) 1,
          (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)) :=
        integral_mono_ae hLHS hRHS hae
    _ = (t * γ₁) * ∫ z, ∫ s in Set.Ioc (0 : ℝ) 1,
          ρ z * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        show ρ z * (t * γ₁ * ∫ s in Set.Ioc (0 : ℝ) 1,
            (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1))
          = t * γ₁ * ∫ s in Set.Ioc (0 : ℝ) 1,
            ρ z * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)
        rw [integral_const_mul]
        ring
    _ = (t * γ₁) * ∫ s in Set.Ioc (0 : ℝ) 1, ∫ z,
          ρ z * (‖h + (s * t) • u + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) := by
        rw [hswap]
    _ ≤ (t * γ₁) * ∫ _s in Set.Ioc (0 : ℝ) 1, C₂ * Mb t := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg ht.le hγ₁0)
        refine integral_mono_ae hFint.integral_prod_right (integrable_const _) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact le_trans (hsand s)
          (mul_le_mul_of_nonneg_left (hMb t (s * t) ht (hseg s hs)) hC₂0.le)
    _ = t * (γ₁ * (C₂ * Mb t)) := by
        rw [setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioc]
        norm_num
        ring
