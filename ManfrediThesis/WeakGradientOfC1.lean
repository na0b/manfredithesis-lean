import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pLocOn
open MeasureTheory

/-- A function that is differentiable at every point of an open set `Ω`, whose
classical partial derivatives there are the components of a field `g` that is
continuous on `Ω`, lies in `W^{1,q}_loc(Ω)` with `g` as its weak gradient, for
every `q ≥ 1`.

This is the entry point into the Sobolev predicates for classically
differentiable data, and the tablet had no statement-level home for it: the
`W^{1,q}` facts already present either start from a function that is *already*
known to have a weak gradient (`WeakGradientC1Comp`, `WeakGradientLinear`) or
require compact support (`SmoothCompactSupportMemW1p`).  The proof is the
Preamble's integration by parts in a direction, applied with `v = eᵢ` and the
test function in the role of the compactly supported factor.

The hypothesis shape is deliberately the first clause of `MemC1HolderOn`
together with continuity of `g`, so that the `C^1` representative produced by
`WeakGradientContinuousRep` feeds this lemma directly. -/
theorem WeakGradientOfC1 :
    ∀ (n : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ q →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        IsOpen Ω →
        (∀ x ∈ Ω, DifferentiableAt ℝ u x ∧
            ∀ i : Fin n, fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)) = g x i) →
        ContinuousOn g Ω →
        MemW1pLocOn n q Ω u g := by
  intro n q _hn _hq Ω u g hΩ hdata hg
  have hproj : ∀ i : Fin n, Continuous (fun y : EuclideanSpace ℝ (Fin n) => y i) :=
    fun i => (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
  have hfin : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      IsFiniteMeasure (volume.restrict K) := by
    intro K hK
    exact ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  -- Step 0
  have hu_on : ContinuousOn u Ω :=
    fun x hx => ((hdata x hx).1.continuousAt).continuousWithinAt
  have hgi_on : ∀ i : Fin n, ContinuousOn (fun x => g x i) Ω :=
    fun i => (hproj i).comp_continuousOn hg
  have hDu_on : ∀ i : Fin n,
      ContinuousOn (fun x => fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))) Ω :=
    fun i => (hgi_on i).congr fun x hx => (hdata x hx).2 i
  refine ⟨?_, ?_⟩
  · -- the weak-gradient identity
    intro φ hφ hφcs hφsupp i
    have hφc : Continuous φ := hφ.continuous
    have hdφ : Continuous
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hUopen : IsOpen ((tsupport φ)ᶜ) := (isClosed_tsupport φ).isOpen_compl
    -- Step 1: glue continuity over Ω ∪ (tsupport φ)ᶜ = ℝⁿ
    have glue : ∀ P : EuclideanSpace ℝ (Fin n) → ℝ, ContinuousOn P Ω →
        (∀ x, x ∉ tsupport φ → P x = 0) → Continuous P := by
      intro P hPΩ hP0
      rw [continuous_iff_continuousAt]
      intro x
      by_cases hx : x ∈ Ω
      · exact hPΩ.continuousAt (hΩ.mem_nhds hx)
      · have hxU : x ∈ (tsupport φ)ᶜ := fun h => hx (hφsupp h)
        exact (continuousOn_const.congr fun y hy => hP0 y hy).continuousAt
          (hUopen.mem_nhds hxU)
    have hcs : ∀ P : EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ x, x ∉ tsupport φ → P x = 0) → HasCompactSupport P := by
      intro P hP0
      refine hφcs.mono' fun x hx => ?_
      by_contra hx'
      exact hx (hP0 x hx')
    have hz1 : ∀ x : EuclideanSpace ℝ (Fin n), x ∉ tsupport φ →
        fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)) * φ x = 0 := by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    have hz3 : ∀ x : EuclideanSpace ℝ (Fin n), x ∉ tsupport φ → u x * φ x = 0 := by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    have hz2 : ∀ x : EuclideanSpace ℝ (Fin n), x ∉ tsupport φ →
        u x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) = 0 := by
      intro x hx
      have h0 : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx
      simp [h0]
    have hP1 : Continuous
        (fun x => fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)) * φ x) :=
      glue _ ((hDu_on i).mul hφc.continuousOn) hz1
    have hP2 : Continuous
        (fun x => u x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) :=
      glue _ (hu_on.mul hdφ.continuousOn) hz2
    have hP3 : Continuous (fun x => u x * φ x) :=
      glue _ (hu_on.mul hφc.continuousOn) hz3
    -- Step 2: integration by parts on ℝⁿ
    have hib := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (f := u) (g := φ) (v := EuclideanSpace.single i (1 : ℝ))
      (hP1.integrable_of_hasCompactSupport (hcs _ hz1))
      (hP2.integrable_of_hasCompactSupport (hcs _ hz2))
      (hP3.integrable_of_hasCompactSupport (hcs _ hz3))
      (fun x hx => (hdata x (hφsupp hx)).1)
      (fun x _ => hφ.differentiable (by simp) x)
    -- Step 3: back to Ω, then replace D_i u by gⁱ
    have hL : (∫ x in Ω, u x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        = ∫ x, u x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        fun x hx => hz2 x fun h => hx (hφsupp h)
    have hRc : (∫ x in Ω, g x i * φ x)
        = ∫ x in Ω, fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)) * φ x :=
      setIntegral_congr_fun hΩ.measurableSet fun x hx => by
        rw [← (hdata x hx).2 i]
    have hR : (∫ x in Ω, fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)) * φ x)
        = ∫ x, fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)) * φ x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        fun x hx => hz1 x fun h => hx (hφsupp h)
    show (∫ x in Ω, u x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        = -∫ x in Ω, g x i * φ x
    rw [hL, hRc, hR]
    exact hib
  · -- Step 4: the local L^q bounds
    intro K hK hKΩ
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    have := hfin K hK
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hu_on.mono hKΩ)
    obtain ⟨N, hN⟩ := hK.exists_bound_of_continuousOn (hg.mono hKΩ)
    exact ⟨MemLp.of_bound ((hu_on.mono hKΩ).aestronglyMeasurable hKm) M
        (ae_restrict_of_forall_mem hKm hM),
      MemLp.of_bound ((hg.mono hKΩ).aestronglyMeasurable hKm) N
        (ae_restrict_of_forall_mem hKm hN)⟩
