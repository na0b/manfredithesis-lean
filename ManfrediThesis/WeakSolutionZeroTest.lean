import ManfrediThesis.Preamble
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pZeroOn
import ManfrediThesis.SmoothCompactSupportMemW1p
open MeasureTheory

/-- The weak-solution identity extends from the compactly supported test pairs of
`IsWeakSolutionOn` to the whole of `W^{1,p}_0(Ω)`, provided the coefficient
`A(·, u, ∇u)` lies in `L^{p'}(Ω)` for the conjugate exponent `p' = p/(p-1)`. -/
theorem WeakSolutionZeroTest :
    ∀ (n : ℕ) (p : ℝ), 1 ≤ n → 1 < p →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (v : EuclideanSpace ℝ (Fin n) → ℝ)
        (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        IsOpen Ω →
        IsWeakSolutionOn n p Ω A (fun _ _ _ => 0) u g →
        MemLp (fun x => A x (u x) (g x)) (ENNReal.ofReal (p / (p - 1)))
          (volume.restrict Ω) →
        MemW1pZeroOn n p Ω v gv →
        (∫ x in Ω, ∑ i, (A x (u x) (g x)) i * gv x i) = 0 := by
  intro n p hn hp Ω A u g v gv hΩ hsol hA hv
  have hp0 : (0:ℝ) < p := by linarith
  have hp10 : (0:ℝ) < p - 1 := by linarith
  have hconj : Real.HolderConjugate p (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have hconj' : Real.HolderConjugate (p / (p - 1)) p := hconj.symm
  have hHT : ENNReal.HolderTriple (ENNReal.ofReal (p / (p - 1)))
      (ENNReal.ofReal p) 1 := ⟨by rw [inv_one]; exact hconj'.inv_add_inv_ennreal⟩
  have hIP : ∀ a b : EuclideanSpace ℝ (Fin n), (∑ i, a i * b i) = inner ℝ b a := by
    intro a b
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hCS : ∀ a b : EuclideanSpace ℝ (Fin n), |∑ i, a i * b i| ≤ ‖a‖ * ‖b‖ := by
    intro a b
    rw [hIP a b]
    rw [mul_comm ‖a‖ ‖b‖]
    exact abs_real_inner_le_norm b a
  -- the `L^{p'} × L^p` pairing
  have hpair : ∀ F H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      MemLp F (ENNReal.ofReal (p / (p - 1))) (volume.restrict Ω) →
      MemLp H (ENNReal.ofReal p) (volume.restrict Ω) →
      IntegrableOn (fun x => ∑ i, F x i * H x i) Ω volume
        ∧ |∫ x in Ω, ∑ i, F x i * H x i|
          ≤ (∫ x in Ω, ‖F x‖ ^ (p / (p - 1))) ^ ((p - 1) / p)
            * (∫ x in Ω, ‖H x‖ ^ p) ^ (1 / p) := by
    intro F H hF hH
    have hprod : Integrable (fun x => ‖F x‖ * ‖H x‖) (volume.restrict Ω) :=
      hF.norm.integrable_mul hH.norm
    have hmeas : AEStronglyMeasurable (fun x => ∑ i, F x i * H x i)
        (volume.restrict Ω) := by
      have hinner : AEStronglyMeasurable
          (fun x => (inner ℝ (H x) (F x) : ℝ)) (volume.restrict Ω) :=
        (continuous_inner (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))).comp_aestronglyMeasurable
          (hH.aestronglyMeasurable.prodMk hF.aestronglyMeasurable)
      exact hinner.congr (Filter.Eventually.of_forall fun x => (hIP (F x) (H x)).symm)
    have hint : IntegrableOn (fun x => ∑ i, F x i * H x i) Ω volume := by
      refine hprod.mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs]
      exact hCS _ _
    refine ⟨hint, ?_⟩
    have h1 : |∫ x in Ω, ∑ i, F x i * H x i| ≤ ∫ x in Ω, ‖F x‖ * ‖H x‖ := by
      refine le_trans abs_integral_le_integral_abs ?_
      exact integral_mono hint.abs hprod (fun x => hCS _ _)
    refine le_trans h1 ?_
    have h2 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict Ω) hconj'
      (Filter.Eventually.of_forall fun x => norm_nonneg (F x))
      (Filter.Eventually.of_forall fun x => norm_nonneg (H x)) hF.norm hH.norm
    rwa [show 1 / (p / (p - 1)) = (p - 1) / p by field_simp] at h2
  obtain ⟨hvW, φ, hφ, -, hφ2⟩ := hv
  obtain ⟨-, htest⟩ := hsol
  have hnorm : ∀ w : EuclideanSpace ℝ (Fin n),
      (∑ i, |w i| ^ 2) ^ (p / 2) = ‖w‖ ^ p := by
    intro w
    have hS : (0:ℝ) ≤ ∑ i, |w i| ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hw : ‖w‖ = (∑ i, |w i| ^ 2) ^ ((1:ℝ) / 2) := by
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_rpow]
      congr 1
    rw [hw, ← Real.rpow_mul hS, show (1:ℝ) / 2 * p = p / 2 by ring]
  have hadm : ∀ k : ℕ, MemW1pOn n p Ω (φ k)
      (fun x => WithLp.toLp 2 fun i =>
        fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ))) :=
    fun k => SmoothCompactSupportMemW1p n p hn hp.le Ω (φ k) hΩ
      (hφ k).1 (hφ k).2.1 (hφ k).2.2
  have hgradLp : ∀ k : ℕ, MemLp
      (fun x => WithLp.toLp 2 fun i =>
        fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ)))
      (ENNReal.ofReal p) (volume.restrict Ω) := fun k => (hadm k).2.2
  have hkey : ∀ k : ℕ,
      (∫ x in Ω, ∑ i, (A x (u x) (g x)) i
          * (WithLp.toLp 2 fun i =>
            fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ))) i) = 0 := by
    intro k
    have h := (htest (φ k) _ (hadm k) (hφ k).2.1 (hφ k).2.2).2
    simp only [zero_mul, add_zero] at h
    exact h
  have hdiffLp : ∀ k : ℕ, MemLp
      (fun x => gv x - (WithLp.toLp 2 fun i =>
        fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ))))
      (ENNReal.ofReal p) (volume.restrict Ω) := fun k => hvW.2.2.sub (hgradLp k)
  have hsplit : ∀ k : ℕ, (∫ x in Ω, ∑ i, (A x (u x) (g x)) i * gv x i)
      = ∫ x in Ω, ∑ i, (A x (u x) (g x)) i
          * (gv x - (WithLp.toLp 2 fun i =>
            fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ)))) i := by
    intro k
    have h1 := (hpair _ _ hA (hgradLp k)).1
    have h2 := (hpair _ _ hA (hdiffLp k)).1
    have hadd : (∫ x in Ω, ((∑ i, (A x (u x) (g x)) i
            * (WithLp.toLp 2 fun i =>
              fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ))) i)
          + ∑ i, (A x (u x) (g x)) i
            * (gv x - (WithLp.toLp 2 fun i =>
              fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ)))) i))
        = (∫ x in Ω, ∑ i, (A x (u x) (g x)) i
            * (WithLp.toLp 2 fun i =>
              fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ))) i)
          + ∫ x in Ω, ∑ i, (A x (u x) (g x)) i
            * (gv x - (WithLp.toLp 2 fun i =>
              fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ)))) i :=
      integral_add h1 h2
    have hpt : (∫ x in Ω, ∑ i, (A x (u x) (g x)) i * gv x i)
        = ∫ x in Ω, ((∑ i, (A x (u x) (g x)) i
            * (WithLp.toLp 2 fun i =>
              fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ))) i)
          + ∑ i, (A x (u x) (g x)) i
            * (gv x - (WithLp.toLp 2 fun i =>
              fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ)))) i) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (∑ i, (A x (u x) (g x)) i * gv x i)
        = (∑ i, (A x (u x) (g x)) i
            * (WithLp.toLp 2 fun i =>
              fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ))) i)
          + ∑ i, (A x (u x) (g x)) i
            * (gv x - (WithLp.toLp 2 fun i =>
              fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ)))) i
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = _ + (A x (u x) (g x)) i
        * (gv x i - fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ)))
      ring
    rw [hpt, hadd, hkey k, zero_add]
  have hto : Filter.Tendsto (fun k : ℕ =>
      (∫ x in Ω, ‖A x (u x) (g x)‖ ^ (p / (p - 1))) ^ ((p - 1) / p)
        * (∫ x in Ω, ‖gv x - (WithLp.toLp 2 fun i =>
            fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ)))‖ ^ p) ^ (1 / p))
      Filter.atTop (nhds 0) := by
    have hinv0 : (0:ℝ) < 1 / p := by positivity
    have hg2 : Filter.Tendsto (fun k : ℕ => ∫ x in Ω,
        ‖gv x - (WithLp.toLp 2 fun i =>
          fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ)))‖ ^ p)
        Filter.atTop (nhds 0) := by
      refine hφ2.congr fun k => ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (∑ i, |gv x i
          - fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ))| ^ 2) ^ (p / 2)
        = ‖gv x - (WithLp.toLp 2 fun i =>
            fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ)))‖ ^ p
      exact hnorm (gv x - (WithLp.toLp 2 fun i =>
        fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ))))
    have hc : Filter.Tendsto (fun t : ℝ => t ^ (1 / p))
        (nhds 0) (nhds ((0:ℝ) ^ (1 / p))) :=
      (Real.continuousAt_rpow_const (0:ℝ) _ (Or.inr hinv0.le)).tendsto
    rw [Real.zero_rpow (ne_of_gt hinv0)] at hc
    have h := ((hc.comp hg2).congr fun k => rfl).const_mul
      ((∫ x in Ω, ‖A x (u x) (g x)‖ ^ (p / (p - 1))) ^ ((p - 1) / p))
    rw [mul_zero] at h
    exact h
  have hle : |∫ x in Ω, ∑ i, (A x (u x) (g x)) i * gv x i| ≤ 0 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hto
      (Filter.Eventually.of_forall fun k => ?_)
    rw [hsplit k]
    exact (hpair _ _ hA (hdiffLp k)).2
  exact abs_eq_zero.1 (le_antisymm hle (abs_nonneg _))
