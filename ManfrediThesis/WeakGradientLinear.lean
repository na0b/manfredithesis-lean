import ManfrediThesis.Preamble
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
open MeasureTheory

/-- Linearity of the weak gradient, and the constants: on an open set,
`W^{1,q}` and `W^{1,q}_loc` are closed under real linear combinations, and
contain every constant function with weak gradient `0`. -/
theorem WeakGradientLinear :
    ∀ (n : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ q →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ)
        (g₁ g₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (a b c : ℝ),
        IsOpen Ω →
        (MemW1pLocOn n q Ω f₁ g₁ → MemW1pLocOn n q Ω f₂ g₂ →
            MemW1pLocOn n q Ω (fun x => a * f₁ x + b * f₂ x)
              (fun x => a • g₁ x + b • g₂ x))
          ∧ (MemW1pOn n q Ω f₁ g₁ → MemW1pOn n q Ω f₂ g₂ →
            MemW1pOn n q Ω (fun x => a * f₁ x + b * f₂ x)
              (fun x => a • g₁ x + b • g₂ x))
          ∧ MemW1pLocOn n q Ω (fun _ => c) (fun _ => 0)
          ∧ (volume Ω ≠ ⊤ → MemW1pOn n q Ω (fun _ => c) (fun _ => 0)) := by
  intro n q _hn hq Ω f₁ f₂ g₁ g₂ a b c _hΩ
  have hq1 : (1 : ENNReal) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 hq
  have hcoord : ∀ (u : EuclideanSpace ℝ (Fin n)) (i : Fin n), ‖u i‖ ≤ ‖u‖ := by
    intro u i
    rw [EuclideanSpace.norm_eq, Real.norm_eq_abs,
      show |u i| = Real.sqrt (|u i| ^ 2) by rw [Real.sqrt_sq (abs_nonneg _)]]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (f := fun j => |u j| ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i))
  have hproj : ∀ i : Fin n, Continuous (fun u : EuclideanSpace ℝ (Fin n) => u i) :=
    fun i => (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
  have hfin : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      IsFiniteMeasure (volume.restrict K) := by
    intro K hK
    exact ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  -- Step 1
  have key : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
        MemLp f (ENNReal.ofReal q) (volume.restrict K) →
      ∀ w : EuclideanSpace ℝ (Fin n) → ℝ, Continuous w → HasCompactSupport w →
        tsupport w ⊆ K → Integrable (fun x => f x * w x) volume := by
    intro K hK f hf w hwc hwcs hws
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    have := hfin K hK
    have hfI : IntegrableOn f K volume := hf.integrable hq1
    obtain ⟨C, hC⟩ := hwcs.exists_bound_of_continuous hwc
    have hprod : IntegrableOn (fun x => f x * w x) K volume :=
      (hfI.bdd_mul (f := w) hwc.aestronglyMeasurable
        (Filter.Eventually.of_forall hC)).congr
        (Filter.Eventually.of_forall fun x => mul_comm (w x) (f x))
    have heq : K.indicator (fun x => f x * w x) = fun x => f x * w x := by
      funext x
      by_cases hx : x ∈ K
      · simp [hx]
      · have hw0 : w x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hws h)
        simp [hx, hw0]
    rw [← heq]
    exact (integrable_indicator_iff hKm).2 hprod
  -- Steps 1-2: the weak-gradient identity for a linear combination
  have main : ∀ (F₁ F₂ : EuclideanSpace ℝ (Fin n) → ℝ)
      (G₁ G₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      HasWeakGradientOn n Ω F₁ G₁ → HasWeakGradientOn n Ω F₂ G₂ →
      (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω →
        MemLp F₁ (ENNReal.ofReal q) (volume.restrict K) ∧
        MemLp G₁ (ENNReal.ofReal q) (volume.restrict K)) →
      (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω →
        MemLp F₂ (ENNReal.ofReal q) (volume.restrict K) ∧
        MemLp G₂ (ENNReal.ofReal q) (volume.restrict K)) →
      HasWeakGradientOn n Ω (fun x => a * F₁ x + b * F₂ x)
        (fun x => a • G₁ x + b • G₂ x) := by
    intro F₁ F₂ G₁ G₂ hw1 hw2 hl1 hl2 φ hφ hφcs hφsupp i
    have hφc : Continuous φ := hφ.continuous
    have hdφ : Continuous
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdφcs : HasCompactSupport
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) :=
      hφcs.fderiv_apply ℝ _
    have hdφsupp :
        tsupport (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
          ⊆ tsupport φ := tsupport_fderiv_apply_subset ℝ _
    obtain ⟨hF1, hG1⟩ := hl1 (tsupport φ) hφcs hφsupp
    obtain ⟨hF2, hG2⟩ := hl2 (tsupport φ) hφcs hφsupp
    have hGc : ∀ G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        MemLp G (ENNReal.ofReal q) (volume.restrict (tsupport φ)) →
        MemLp (fun x => G x i) (ENNReal.ofReal q)
          (volume.restrict (tsupport φ)) :=
      fun G hG => hG.mono ((hproj i).comp_aestronglyMeasurable hG.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => hcoord (G x) i)
    have I1 : Integrable
        (fun x => F₁ x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) volume :=
      key (tsupport φ) hφcs F₁ hF1 _ hdφ hdφcs hdφsupp
    have I2 : Integrable
        (fun x => F₂ x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) volume :=
      key (tsupport φ) hφcs F₂ hF2 _ hdφ hdφcs hdφsupp
    have J1 : Integrable (fun x => G₁ x i * φ x) volume :=
      key (tsupport φ) hφcs _ (hGc G₁ hG1) φ hφc hφcs subset_rfl
    have J2 : Integrable (fun x => G₂ x i * φ x) volume :=
      key (tsupport φ) hφcs _ (hGc G₂ hG2) φ hφc hφcs subset_rfl
    have e1 := hw1 φ hφ hφcs hφsupp i
    have e2 := hw2 φ hφ hφcs hφsupp i
    show (∫ x in Ω, (a * F₁ x + b * F₂ x) *
            fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        = -∫ x in Ω, (a • G₁ x + b • G₂ x) i * φ x
    have hL : (∫ x in Ω, (a * F₁ x + b * F₂ x) *
          fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        = a * (∫ x in Ω, F₁ x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
          + b * (∫ x in Ω,
              F₂ x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) := by
      have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
          (a * F₁ x + b * F₂ x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))
            = a * (F₁ x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
              + b * (F₂ x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) :=
        fun x => by ring
      simp only [hpt]
      rw [integral_add (I1.const_mul a).integrableOn (I2.const_mul b).integrableOn,
        integral_const_mul, integral_const_mul]
    have hR : (∫ x in Ω, (a • G₁ x + b • G₂ x) i * φ x)
        = a * (∫ x in Ω, G₁ x i * φ x) + b * (∫ x in Ω, G₂ x i * φ x) := by
      have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
          (a • G₁ x + b • G₂ x) i * φ x
            = a * (G₁ x i * φ x) + b * (G₂ x i * φ x) := by
        intro x
        have hcoe : (a • G₁ x + b • G₂ x) i = a * G₁ x i + b * G₂ x i := by simp
        rw [hcoe]; ring
      simp only [hpt]
      rw [integral_add (J1.const_mul a).integrableOn (J2.const_mul b).integrableOn,
        integral_const_mul, integral_const_mul]
    rw [hL, hR, e1, e2]
    ring
  -- Step 4: the constant function has weak gradient zero
  have hconst : HasWeakGradientOn n Ω (fun _ => c) (fun _ => 0) := by
    intro φ hφ hφcs hφsupp i
    have hφc : Continuous φ := hφ.continuous
    have hdφ : Continuous
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdφcs : HasCompactSupport
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) :=
      hφcs.fderiv_apply ℝ _
    have hzero : (∫ x, fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) = 0 := by
      have hib := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        (f := fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) (g := φ)
        (v := EuclideanSpace.single i (1 : ℝ))
        (by simp)
        (by simpa using hdφ.integrable_of_hasCompactSupport hdφcs)
        (by simpa using hφc.integrable_of_hasCompactSupport hφcs)
        (fun x _ => differentiableAt_const _)
        (fun x _ => hφ.differentiable (by simp) x)
      simpa using hib
    have hΩ' : (∫ x in Ω, fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        = ∫ x, fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      have h0 : fderiv ℝ φ x = 0 :=
        fderiv_of_notMem_tsupport ℝ (fun h => hx (hφsupp h))
      simp [h0]
    show (∫ x in Ω, c * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        = -∫ x in Ω, (0 : EuclideanSpace ℝ (Fin n)) i * φ x
    rw [integral_const_mul, hΩ', hzero]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- clause (1)
    intro h1 h2
    obtain ⟨hw1, hl1⟩ := h1
    obtain ⟨hw2, hl2⟩ := h2
    refine ⟨main f₁ f₂ g₁ g₂ hw1 hw2 hl1 hl2, fun K hK hKΩ => ?_⟩
    obtain ⟨hF1, hG1⟩ := hl1 K hK hKΩ
    obtain ⟨hF2, hG2⟩ := hl2 K hK hKΩ
    exact ⟨(hF1.const_mul a).add (hF2.const_mul b),
      (hG1.const_smul a).add (hG2.const_smul b)⟩
  · -- clause (2)
    intro h1 h2
    obtain ⟨hw1, hf1, hg1⟩ := h1
    obtain ⟨hw2, hf2, hg2⟩ := h2
    refine ⟨main f₁ f₂ g₁ g₂ hw1 hw2 (fun K _ hKΩ => ?_) (fun K _ hKΩ => ?_),
      (hf1.const_mul a).add (hf2.const_mul b),
      (hg1.const_smul a).add (hg2.const_smul b)⟩
    · exact ⟨hf1.mono_measure (Measure.restrict_mono hKΩ le_rfl),
        hg1.mono_measure (Measure.restrict_mono hKΩ le_rfl)⟩
    · exact ⟨hf2.mono_measure (Measure.restrict_mono hKΩ le_rfl),
        hg2.mono_measure (Measure.restrict_mono hKΩ le_rfl)⟩
  · -- clause (3)
    refine ⟨hconst, fun K hK _ => ?_⟩
    have := hfin K hK
    exact ⟨memLp_const c, memLp_const 0⟩
  · -- clause (4)
    intro hvol
    have : IsFiniteMeasure (volume.restrict Ω) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hvol⟩
    exact ⟨hconst, memLp_const c, memLp_const 0⟩
