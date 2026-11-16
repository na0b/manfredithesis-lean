import ManfrediThesis.Preamble
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.MemW1pLocOn
open MeasureTheory

/-- The second weak derivatives of a `W^{2,q}_loc` function are symmetric: if
`g` is the weak gradient of `u` and `Dg i` the weak gradient of the component
`g i`, then `(Dg k) j = (Dg j) k` almost everywhere on `Ω`. -/
theorem WeakSecondDerivativeSymmetry :
    ∀ (n : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ q →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        IsOpen Ω → MemW1pLocOn n q Ω u g →
        (∀ i : Fin n, MemW1pLocOn n q Ω (fun x => g x i) (Dg i)) →
        ∀ j k : Fin n,
          ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
            x ∈ Ω → Dg k x j = Dg j x k := by
  intro n q _ hq Ω u g Dg hΩ hu hDg j k
  have h1q : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]; exact ENNReal.ofReal_le_ofReal hq
  -- Step 1: on every compact subset of Ω the data are integrable.
  have hcomp : ∀ (w : EuclideanSpace ℝ (Fin n) → ℝ)
      (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      MemW1pLocOn n q Ω w G → ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω →
      IntegrableOn w K volume ∧ ∀ i, IntegrableOn (fun x => G x i) K volume := by
    intro w G hw K hK hKsub
    obtain ⟨hwLp, hGLp⟩ := hw.2 K hK hKsub
    have hfin : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
    refine ⟨memLp_one_iff_integrable.1 (hwLp.mono_exponent h1q), fun i => ?_⟩
    refine memLp_one_iff_integrable.1 ((hGLp.mono_exponent h1q).mono ?_ ?_)
    · exact (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable
        (hGLp.mono_exponent h1q).aestronglyMeasurable
    · filter_upwards with x using PiLp.norm_apply_le _ i
  -- Step 2: the difference is locally integrable on Ω.
  have hli : LocallyIntegrableOn (fun x => Dg k x j - Dg j x k) Ω volume := by
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ x hx
    have hsub : Metric.closedBall x (r/2) ⊆ Ω :=
      subset_trans (Metric.closedBall_subset_ball (by linarith)) hball
    refine ⟨Metric.closedBall x (r/2), ?_, ?_⟩
    · exact nhdsWithin_le_nhds (Metric.closedBall_mem_nhds x (by linarith))
    · exact ((hcomp _ _ (hDg k) _ (isCompact_closedBall x (r/2)) hsub).2 j).sub
        ((hcomp _ _ (hDg j) _ (isCompact_closedBall x (r/2)) hsub).2 k)
  suffices h : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∈ Ω → Dg k x j - Dg j x k = 0 by
    filter_upwards [h] with x hx hxΩ
    linarith [hx hxΩ]
  refine hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hli ?_
  intro φ hφ hcs hts
  -- Step 3: the directional-derivative test functions.
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ φ y) := by
    simpa using (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp))
  have htest : ∀ i : Fin n,
      ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1:ℝ)))
        ∧ HasCompactSupport (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1:ℝ)))
        ∧ tsupport (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1:ℝ))) ⊆ Ω := by
    intro i
    refine ⟨hcd.clm_apply contDiff_const, ?_, ?_⟩
    · exact (hcs.fderiv ℝ).comp_left (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        L (EuclideanSpace.single i (1:ℝ))) (by simp)
    · refine subset_trans ?_ (subset_trans (tsupport_fderiv_subset ℝ (f := φ)) hts)
      exact tsupport_comp_subset (by simp) (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        L (EuclideanSpace.single i (1:ℝ))) (f := fun y => fderiv ℝ φ y)
  -- Step 4: the two identities, each from the weak gradients of g^k and of u.
  have hkey : ∀ a b : Fin n,
      (∫ x in Ω, Dg a x b * φ x)
        = ∫ x in Ω, u x * fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single b (1:ℝ))) x
            (EuclideanSpace.single a (1:ℝ)) := by
    intro a b
    have hA := (hDg a).1 φ hφ hcs hts b
    have hB := hu.1 _ (htest b).1 (htest b).2.1 (htest b).2.2 a
    simp only [] at hA hB
    rw [hA] at hB
    linarith
  -- Step 5: Clairaut.
  have hdiffe : ∀ z, DifferentiableAt ℝ (fun y => fderiv ℝ φ y) z :=
    fun z => (hcd.differentiable (by simp)).differentiableAt
  have hclair : ∀ x : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single j (1:ℝ))) x
          (EuclideanSpace.single k (1:ℝ))
        = fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single k (1:ℝ))) x
          (EuclideanSpace.single j (1:ℝ)) := by
    intro x
    have key : ∀ (a b : EuclideanSpace ℝ (Fin n)),
        fderiv ℝ (fun y => fderiv ℝ φ y a) x b = fderiv ℝ (fun y => fderiv ℝ φ y) x b a := by
      intro a b
      rw [fderiv_clm_apply (hdiffe x) (differentiableAt_const a)]; simp
    rw [key _ _, key _ _]
    exact second_derivative_symmetric
      (fun y => (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt)
      (hdiffe x).hasFDerivAt _ _
  -- Step 6: assemble.
  have hvan : ∀ x, x ∉ Ω → φ x • (Dg k x j - Dg j x k) = 0 := by
    intro x hx
    have : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hts hh))
    simp [this]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan]
  have hbound : ∃ C, ∀ x, ‖φ x‖ ≤ C := hcs.exists_bound_of_continuous (hφ.continuous)
  obtain ⟨C, hC⟩ := hbound
  have hintO : ∀ a b : Fin n, IntegrableOn (fun x => Dg a x b * φ x) Ω volume := by
    intro a b
    have hTS : IntegrableOn (fun x => Dg a x b * φ x) (tsupport φ) volume := by
      have h0 := (hcomp _ _ (hDg a) _ hcs hts).2 b
      have h2 := h0.bdd_mul ((hφ.continuous.aestronglyMeasurable).restrict)
        (Filter.Eventually.of_forall hC)
      simpa [mul_comm, IntegrableOn] using h2
    have hsupp : Function.support (fun x => Dg a x b * φ x) ⊆ tsupport φ := by
      intro x hx
      refine subset_tsupport φ ?_
      simp only [Function.mem_support] at hx ⊢
      exact fun h0 => hx (by simp [h0])
    exact ((integrableOn_iff_integrable_of_support_subset hsupp).1 hTS).integrableOn
  have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
      φ x • (Dg k x j - Dg j x k) = Dg k x j * φ x - Dg j x k * φ x := by
    intro x; simp only [smul_eq_mul]; ring
  simp only [hpt]
  rw [integral_sub (hintO k j) (hintO j k), hkey k j, hkey j k]
  simp only [hclair]
  simp
