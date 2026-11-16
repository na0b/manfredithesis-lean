import ManfrediThesis.Preamble
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.MemW1pOn
open MeasureTheory

/-- A smooth function with compact support inside `Ω` lies in `W^{1,r}(Ω)` for
every `r ≥ 1`, with weak gradient its classical gradient. -/
theorem SmoothCompactSupportMemW1p :
    ∀ (n : ℕ) (r : ℝ), 1 ≤ n → 1 ≤ r →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (φ : EuclideanSpace ℝ (Fin n) → ℝ),
        IsOpen Ω → ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ Ω →
        MemW1pOn n r Ω φ
          (fun x => WithLp.toLp 2 fun i =>
            fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) := by
  intro n r _hn _hr Ω φ _hΩ hφ hcs hsupp
  -- Step 1: `φ` and `∇φ` are continuous, compactly supported, and vanish off
  -- `tsupport φ`.
  have hφc : Continuous φ := hφ.continuous
  have hdc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hGc : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      (WithLp.toLp 2 fun i => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) :
        EuclideanSpace ℝ (Fin n))) :=
    (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun _ => hdc.clm_apply continuous_const)
  have hGsupp : ∀ x : EuclideanSpace ℝ (Fin n), x ∉ tsupport φ →
      (WithLp.toLp 2 fun i => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) :
        EuclideanSpace ℝ (Fin n)) = 0 := by
    intro x hx
    have h0 : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx
    simp only [h0, zero_apply]
    rfl
  have hGcs : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin n) =>
      (WithLp.toLp 2 fun i => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) :
        EuclideanSpace ℝ (Fin n))) := by
    refine hcs.mono' fun x hx => ?_
    by_contra hx'
    exact hx (hGsupp x hx')
  refine ⟨?_, ?_, ?_⟩
  · -- The weak-gradient identity.
    intro ψ hψ hψcs hψsupp i
    -- Step 4's direction: `v = e_i`.
    set v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1 : ℝ) with hv
    have hψc : Continuous ψ := hψ.continuous
    have hdψ : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
    -- Step 5: both integrands vanish off `tsupport φ ⊆ Ω`, so the integrals over
    -- `Ω` and over the whole space agree.
    have h1 : (∫ x in Ω, φ x * fderiv ℝ ψ x v) = ∫ x, φ x * fderiv ℝ ψ x v := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
      have h0 : φ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))
      simp [h0]
    have h2 : (∫ x in Ω, (WithLp.toLp 2 fun j =>
          fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ)) :
            EuclideanSpace ℝ (Fin n)) i * ψ x)
        = ∫ x, fderiv ℝ φ x v * ψ x := by
      -- the `i`-th component of the gradient field is `fderiv ℝ φ x v`, by
      -- unfolding `WithLp.toLp`
      have hcomp : (∫ x in Ω, (WithLp.toLp 2 fun j =>
          fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ)) :
            EuclideanSpace ℝ (Fin n)) i * ψ x)
          = ∫ x in Ω, fderiv ℝ φ x v * ψ x := rfl
      rw [hcomp]
      refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
      have h0 : fderiv ℝ φ x = 0 :=
        fderiv_of_notMem_tsupport ℝ (fun h => hx (hsupp h))
      simp [h0]
    rw [h1, h2]
    -- Steps 3 and 4: the three integrability hypotheses and integration by parts.
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
    · exact ((hdc.clm_apply continuous_const).mul hψc).integrable_of_hasCompactSupport
        (HasCompactSupport.mul_left hψcs)
    · exact (hφc.mul (hdψ.clm_apply continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.mul_right hcs)
    · exact (hφc.mul hψc).integrable_of_hasCompactSupport
        (HasCompactSupport.mul_right hcs)
    · exact fun x _ => hφ.differentiable (by simp) x
    · exact fun x _ => hψ.differentiable (by simp) x
  · -- Step 2: `φ ∈ L^r(Ω)`.
    exact (hφc.memLp_of_hasCompactSupport hcs).restrict Ω
  · -- Step 2: `|∇φ| ∈ L^r(Ω)`.
    exact (hGc.memLp_of_hasCompactSupport hGcs).restrict Ω
