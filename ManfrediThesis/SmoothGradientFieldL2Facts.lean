import ManfrediThesis.Preamble
set_option maxHeartbeats 400000
open MeasureTheory

/-- Four elementary facts used by every approximation passage in a Sobolev
inequality: for the `EuclideanSpace`-valued gradient field
`x ↦ (∂_1Φ(x),…,∂_nΦ(x))` of a smooth compactly supported `Φ`, that field is
continuous, has compact support, and vanishes off `supp Φ`; each coordinate of
a vector is bounded by its norm; an `L²` vector field is square integrable on
the set carrying the measure; and `1 ≤ 2` as extended-real exponents.

Conventions, restated here because a helper inherits none of its parent's.
`supp Φ` is `tsupport Φ`, the CLOSED support, so "vanishes off `supp Φ`" is the
pointwise statement at every `x` outside it, which is what compact-support
arguments consume.  The gradient field is written with `WithLp.toLp 2`, i.e. a
vector of `EuclideanSpace ℝ (Fin n)` assembled from the directional
derivatives `fderiv ℝ Φ x (EuclideanSpace.single i 1)`, so its norm is the
Euclidean norm of the gradient and not an operator norm.  The exponent is
written `ENNReal.ofReal 2` throughout, the form the `MemLp` hypotheses of the
consumers carry, and the conclusion of the third fact is the integrability of
the SQUARE `‖v‖ ^ 2` with a natural-number power, which is the form the
Minkowski and Hölder steps downstream expect.  No hypothesis relates the four
facts: they are bundled because every consumer reads all four. -/
theorem SmoothGradientFieldL2Facts :
    ∀ n : ℕ,
      (∀ Φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) Φ →
         HasCompactSupport Φ →
         Continuous (fun x => (WithLp.toLp 2 fun i =>
             fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
           EuclideanSpace ℝ (Fin n)))
         ∧ HasCompactSupport (fun x => (WithLp.toLp 2 fun i =>
             fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
           EuclideanSpace ℝ (Fin n)))
         ∧ ∀ x, x ∉ tsupport Φ →
             (WithLp.toLp 2 fun i => fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
               EuclideanSpace ℝ (Fin n)) = 0)
      ∧ (∀ (v : EuclideanSpace ℝ (Fin n)) (i : Fin n), |v i| ≤ ‖v‖)
      ∧ (∀ (S : Set (EuclideanSpace ℝ (Fin n)))
         (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
         MemLp v (ENNReal.ofReal 2) (volume.restrict S) →
         IntegrableOn (fun x => ‖v x‖ ^ 2) S volume)
      ∧ (1 : ENNReal) ≤ ENNReal.ofReal 2 := by
  intro n
  have hnpow : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ^ (2 : ℝ) = ‖v‖ ^ 2 := by
    intro v
    rw [← Real.rpow_natCast ‖v‖ 2]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Φ hΦ hcs
    have hdc : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv (by simp)
    have hGc : Continuous (fun x => (WithLp.toLp 2 fun i =>
        fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
      EuclideanSpace ℝ (Fin n))) :=
      (PiLp.continuous_toLp 2 _).comp
        (continuous_pi fun _ => hdc.clm_apply continuous_const)
    have hGsupp : ∀ x : EuclideanSpace ℝ (Fin n), x ∉ tsupport Φ →
        (WithLp.toLp 2 fun i => fderiv ℝ Φ x (EuclideanSpace.single i (1 : ℝ)) :
          EuclideanSpace ℝ (Fin n)) = 0 := by
      intro x hx
      have h0 : fderiv ℝ Φ x = 0 := fderiv_of_notMem_tsupport ℝ hx
      simp only [h0, zero_apply]
      rfl
    refine ⟨hGc, ?_, hGsupp⟩
    refine hcs.mono' fun x hx => ?_
    by_contra hx'
    exact hx (hGsupp x hx')
  · intro v i
    have h1 : (inner ℝ (EuclideanSpace.single i (1 : ℝ) :
        EuclideanSpace ℝ (Fin n)) v) = v i := by
      simp [PiLp.inner_apply]
    calc |v i| = |inner ℝ (EuclideanSpace.single i (1 : ℝ) :
            EuclideanSpace ℝ (Fin n)) v| := by rw [h1]
      _ ≤ ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n))‖ * ‖v‖ :=
          abs_real_inner_le_norm _ _
      _ = ‖v‖ := by simp
  · intro S v hv
    have h1 : Integrable (fun x => ‖v x‖ ^ (ENNReal.ofReal 2).toReal)
        (volume.restrict S) :=
      hv.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp] at h1
    exact h1.congr (Filter.Eventually.of_forall fun x => hnpow _)
  · rw [ENNReal.one_le_ofReal]; norm_num
