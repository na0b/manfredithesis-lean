import ManfrediThesis.Preamble
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.WeakGradientRestrict
open MeasureTheory

/-- Product rule against a smooth compactly supported factor.  Clause (1): if
`f ∈ W^{1,q}(Ω)` with weak gradient `g`, `Ω` has finite volume, and `ψ` is
smooth with compact support inside `Ω`, then `f ψ ∈ W^{1,q}(Ω)` with weak
gradient `ψ g + f ∇ψ`.  Clause (2): the same conclusion holds under the weaker
hypothesis `f ∈ W^{1,q}_loc(Ω)`, with no restriction on the volume of `Ω`. -/
theorem WeakGradientSmoothMul :
    ∀ (n : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ q →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (f : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (ψ : EuclideanSpace ℝ (Fin n) → ℝ),
        IsOpen Ω →
        ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
        (volume Ω ≠ ⊤ → MemW1pOn n q Ω f g →
            MemW1pOn n q Ω (fun x => f x * ψ x)
              (fun x => ψ x • g x
                + f x • (EuclideanSpace.equiv (Fin n) ℝ).symm
                    (fun i => fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))))
          ∧ (MemW1pLocOn n q Ω f g →
            MemW1pOn n q Ω (fun x => f x * ψ x)
              (fun x => ψ x • g x
                + f x • (EuclideanSpace.equiv (Fin n) ℝ).symm
                    (fun i => fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))))) := by
  intro n q hn hq Ω f g ψ hΩ hψ hcsψ htsψ
  have h1q : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]; exact ENNReal.ofReal_le_ofReal hq
  set D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x => (EuclideanSpace.equiv (Fin n) ℝ).symm
      (fun i => fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) with hD
  -- Basic facts about ψ and D.
  have hcdψ : Continuous (fun y => fderiv ℝ ψ y) := by
    have : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ ψ y) := by
      simpa using (hψ.fderiv_right (m := (⊤ : ℕ∞)) (by simp))
    exact this.continuous
  have hDcont : Continuous D :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp
      (continuous_pi fun i => (hcdψ.clm_apply continuous_const))
  have hDcoord : ∀ x i, D x i = fderiv ℝ ψ x (EuclideanSpace.single i (1:ℝ)) := by
    intro x i; simp [hD]
  have hfdψzero : ∀ x ∉ tsupport ψ, fderiv ℝ ψ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hh => hx (tsupport_fderiv_subset ℝ hh))
  have hDzero : ∀ x ∉ tsupport ψ, D x = 0 := by
    intro x hx
    simp only [hD, hfdψzero x hx, zero_apply]
    exact map_zero _
  have hDcs : HasCompactSupport D := HasCompactSupport.intro hcsψ.isCompact hDzero
  have hψzero : ∀ x ∉ tsupport ψ, ψ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  obtain ⟨Cψ, hCψ⟩ := hcsψ.exists_bound_of_continuous hψ.continuous
  obtain ⟨CD, hCD⟩ := hDcs.exists_bound_of_continuous hDcont
  have hCψ0 : 0 ≤ Cψ := le_trans (norm_nonneg _) (hCψ 0)
  have hCD0 : 0 ≤ CD := le_trans (norm_nonneg _) (hCD 0)
  have hmsψ : MeasurableSet (tsupport ψ) := hcsψ.isCompact.isClosed.measurableSet
  -- Zero-extension of an L^q bound from tsupport ψ to Ω, scalar and vector form.
  have hExtS : ∀ F : EuclideanSpace ℝ (Fin n) → ℝ,
      MemLp F (ENNReal.ofReal q) (volume.restrict (tsupport ψ)) →
      (∀ x ∉ tsupport ψ, F x = 0) →
      MemLp F (ENNReal.ofReal q) (volume.restrict Ω) := by
    intro F hF hvan
    have h1 : MemLp ((tsupport ψ).indicator F) (ENNReal.ofReal q) volume :=
      (memLp_indicator_iff_restrict hmsψ).2 hF
    have h2 : (tsupport ψ).indicator F = F := by
      funext x
      by_cases hx : x ∈ tsupport ψ
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx, hvan x hx]
    rw [h2] at h1
    exact h1.mono_measure Measure.restrict_le_self
  have hExtV : ∀ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      MemLp F (ENNReal.ofReal q) (volume.restrict (tsupport ψ)) →
      (∀ x ∉ tsupport ψ, F x = 0) →
      MemLp F (ENNReal.ofReal q) (volume.restrict Ω) := by
    intro F hF hvan
    have h1 : MemLp ((tsupport ψ).indicator F) (ENNReal.ofReal q) volume :=
      (memLp_indicator_iff_restrict hmsψ).2 hF
    have h2 : (tsupport ψ).indicator F = F := by
      funext x
      by_cases hx : x ∈ tsupport ψ
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx, hvan x hx]
    rw [h2] at h1
    exact h1.mono_measure Measure.restrict_le_self
  -- The main clause, from `W^{1,q}_loc`.
  have main : MemW1pLocOn n q Ω f g →
      MemW1pOn n q Ω (fun x => f x * ψ x) (fun x => ψ x • g x + f x • D x) := by
    intro hw
    obtain ⟨hwg, hfam⟩ := hw
    obtain ⟨hfLp, hgLp⟩ := hfam (tsupport ψ) hcsψ.isCompact htsψ
    refine ⟨?_, ?_, ?_⟩
    · -- (a) the weak-gradient identity, by testing `hwg` against `φ ψ`
      intro φ hφ hcsφ htsφ i
      set K : Set (EuclideanSpace ℝ (Fin n)) := tsupport φ with hK
      have hKc : IsCompact K := hcsφ.isCompact
      have hKsub : K ⊆ Ω := htsφ
      -- `f` and each coordinate of `g` are integrable on `K`.
      have hfin : IsFiniteMeasure (volume.restrict K) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
      obtain ⟨hfK, hgK⟩ := hfam K hKc hKsub
      have hfI : IntegrableOn f K volume :=
        memLp_one_iff_integrable.1 (hfK.mono_exponent h1q)
      have hgI : ∀ a : Fin n, IntegrableOn (fun x => g x a) K volume := by
        intro a
        refine memLp_one_iff_integrable.1 ((hgK.mono_exponent h1q).mono ?_ ?_)
        · exact (EuclideanSpace.proj a).continuous.comp_aestronglyMeasurable
            (hgK.mono_exponent h1q).aestronglyMeasurable
        · filter_upwards with x using PiLp.norm_apply_le _ a
      -- Multiplying an `L^1(K)` function by a bounded continuous factor that
      -- vanishes off `K` gives a function integrable on `Ω`.
      have hIB : ∀ (F B : EuclideanSpace ℝ (Fin n) → ℝ),
          IntegrableOn F K volume → Continuous B → (∃ C, ∀ x, ‖B x‖ ≤ C) →
          (∀ x ∉ K, B x = 0) → IntegrableOn (fun x => F x * B x) Ω volume := by
        intro F B hF hB hBb hvan
        obtain ⟨CB, hBb⟩ := hBb
        have hTS : IntegrableOn (fun x => F x * B x) K volume := by
          have h2 := hF.bdd_mul (hB.aestronglyMeasurable.restrict)
            (Filter.Eventually.of_forall hBb)
          simpa [mul_comm, IntegrableOn] using h2
        have hsupp : Function.support (fun x => F x * B x) ⊆ K := by
          intro x hx
          by_contra hcon
          simp only [Function.mem_support] at hx
          exact hx (by simp [hvan x hcon])
        exact ((integrableOn_iff_integrable_of_support_subset hsupp).1 hTS).integrableOn
      -- Bounds and vanishing for the three bounded factors.
      have hcdφ : Continuous (fun y => fderiv ℝ φ y) := by
        have : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ φ y) := by
          simpa using (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp))
        exact this.continuous
      have hDφcont : Continuous (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1:ℝ))) :=
        hcdφ.clm_apply continuous_const
      have hDφcs : HasCompactSupport
          (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1:ℝ))) :=
        (hcsφ.fderiv ℝ).comp_left (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
          L (EuclideanSpace.single i (1:ℝ))) (by simp)
      obtain ⟨Cdφ, hCdφ⟩ := hDφcs.exists_bound_of_continuous hDφcont
      obtain ⟨Cφ, hCφ⟩ := hcsφ.exists_bound_of_continuous hφ.continuous
      have hCdφ0 : 0 ≤ Cdφ := le_trans (norm_nonneg _) (hCdφ 0)
      have hCφ0 : 0 ≤ Cφ := le_trans (norm_nonneg _) (hCφ 0)
      have hDφzero : ∀ x ∉ K, fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ)) = 0 := by
        intro x hx
        have h0 : fderiv ℝ φ x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hh => hx (tsupport_fderiv_subset ℝ hh))
        simp [h0]
      have hφzero : ∀ x ∉ K, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
      -- The three integrands.
      have hA : IntegrableOn (fun x =>
          f x * (ψ x * fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ)))) Ω volume := by
        refine hIB f _ hfI (hψ.continuous.mul hDφcont) ⟨Cψ * Cdφ, fun x => ?_⟩
          (fun x hx => by simp [hDφzero x hx])
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using hCψ x)
          (by simpa [Real.norm_eq_abs] using hCdφ x) (abs_nonneg _) hCψ0
      have hB : IntegrableOn (fun x =>
          f x * (fderiv ℝ ψ x (EuclideanSpace.single i (1:ℝ)) * φ x)) Ω volume := by
        refine hIB f _ hfI ((hcdψ.clm_apply continuous_const).mul hφ.continuous)
          ⟨CD * Cφ, fun x => ?_⟩ (fun x hx => by simp [hφzero x hx])
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul ?_ (by simpa [Real.norm_eq_abs] using hCφ x) (abs_nonneg _) hCD0
        have := hCD x
        calc |fderiv ℝ ψ x (EuclideanSpace.single i (1:ℝ))| = ‖D x i‖ := by
              rw [hDcoord x i, Real.norm_eq_abs]
          _ ≤ ‖D x‖ := PiLp.norm_apply_le _ i
          _ ≤ CD := this
      have hC : IntegrableOn (fun x => g x i * (φ x * ψ x)) Ω volume := by
        refine hIB _ _ (hgI i) (hφ.continuous.mul hψ.continuous) ⟨Cφ * Cψ, fun x => ?_⟩
          (fun x hx => by simp [hφzero x hx])
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using hCφ x)
          (by simpa [Real.norm_eq_abs] using hCψ x) (abs_nonneg _) hCφ0
      -- The identity from `hwg` tested against `φ ψ`.
      have hφψcd : ContDiff ℝ (⊤ : ℕ∞) (fun y => φ y * ψ y) := hφ.mul hψ
      have hφψcs : HasCompactSupport (fun y => φ y * ψ y) := hcsφ.mul_right
      have hφψts : tsupport (fun y => φ y * ψ y) ⊆ Ω :=
        subset_trans (tsupport_mul_subset_left) htsφ
      have hI := hwg _ hφψcd hφψcs hφψts i
      have hpr : ∀ x, fderiv ℝ (fun y => φ y * ψ y) x (EuclideanSpace.single i (1:ℝ))
          = φ x * fderiv ℝ ψ x (EuclideanSpace.single i (1:ℝ))
            + ψ x * fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ)) := by
        intro x
        have h1 : HasFDerivAt (fun y => φ y * ψ y)
            (φ x • fderiv ℝ ψ x + ψ x • fderiv ℝ φ x) x :=
          ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt).mul
            ((hψ.differentiable (by simp)).differentiableAt.hasFDerivAt)
        rw [h1.fderiv]
        simp
      have hsplit : (∫ x in Ω, f x * fderiv ℝ (fun y => φ y * ψ y) x
            (EuclideanSpace.single i (1:ℝ)))
          = (∫ x in Ω, f x * (ψ x * fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ))))
            + ∫ x in Ω, f x * (fderiv ℝ ψ x (EuclideanSpace.single i (1:ℝ)) * φ x) := by
        rw [← integral_add hA hB]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hpr x]; ring
      rw [hsplit] at hI
      have hgoal : (∫ x in Ω, (ψ x • g x + f x • D x) i * φ x)
          = (∫ x in Ω, g x i * (φ x * ψ x))
            + ∫ x in Ω, f x * (fderiv ℝ ψ x (EuclideanSpace.single i (1:ℝ)) * φ x) := by
        rw [← integral_add hC hB]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hDcoord x i]
        ring
      have hlhs : (∫ x in Ω, (f x * ψ x) * fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ)))
          = ∫ x in Ω, f x * (ψ x * fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_); ring
      rw [hlhs, hgoal]
      linarith
    · -- (b) `f ψ ∈ L^q(Ω)`
      refine hExtS _ ?_ (fun x hx => by simp [hψzero x hx])
      refine (hfLp.const_mul Cψ).mono ?_ ?_
      · exact hfLp.aestronglyMeasurable.mul (hψ.continuous.aestronglyMeasurable.restrict)
      · filter_upwards with x
        have hb : |ψ x| ≤ Cψ := by simpa [Real.norm_eq_abs] using hCψ x
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hCψ0]
        nlinarith [abs_nonneg (f x)]
    · -- (c) the gradient is in `L^q(Ω)`
      refine hExtV _ ?_ (fun x hx => by simp [hψzero x hx, hDzero x hx])
      refine MemLp.add ?_ ?_
      · refine (hgLp.const_smul Cψ).mono ?_ ?_
        · exact (hψ.continuous.aestronglyMeasurable.restrict).smul hgLp.aestronglyMeasurable
        · filter_upwards with x
          have hb : |ψ x| ≤ Cψ := by simpa [Real.norm_eq_abs] using hCψ x
          simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hCψ0]
          nlinarith [norm_nonneg (g x)]
      · refine (hfLp.const_mul CD).mono ?_ ?_
        · exact hfLp.aestronglyMeasurable.smul (hDcont.aestronglyMeasurable.restrict)
        · filter_upwards with x
          have hb : ‖D x‖ ≤ CD := hCD x
          rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hCD0]
          nlinarith [abs_nonneg (f x), norm_nonneg (D x)]
  refine ⟨fun _ h => main ?_, main⟩
  exact (WeakGradientRestrict n q hn hq Ω Ω f g hΩ hΩ (subset_refl Ω)).2.2.1 h
