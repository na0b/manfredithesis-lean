import ManfrediThesis.Preamble
import ManfrediThesis.HasWeakGradientOn
set_option maxHeartbeats 800000
open MeasureTheory

/-- Differentiating a mollification gives the mollification of the weak
gradient: if `f` has weak gradient `G_f` on `Ω`, if the truncation
`1_{K_3}f` is locally integrable, and if `ρ` is smooth with
`supp ρ = \overline{B_d(0)}`, then at every point `x` whose closed
`d`-neighbourhood lies inside both `K_3` and `Ω`,
\[
∂_i\bigl((1_{K_3}f)*ρ\bigr)(x)=\bigl((1_{K_3}G_f^{\,i})*ρ\bigr)(x)
\qquad\text{for every coordinate }i .
\]

Conventions, restated here because a helper inherits none of its parent's.
`supp ρ` means `tsupport ρ`, the CLOSED support, and the hypothesis fixes it to
be exactly the closed ball of radius `d` about the origin, which is what makes
the `d`-neighbourhood condition on `x` the right one; `∂_i` is
`fderiv ℝ · x (EuclideanSpace.single i 1)`; the convolution is
`convolution · · (ContinuousLinearMap.lsmul ℝ ℝ) volume`, i.e. scalar
multiplication as the pairing, against Lebesgue measure; and `1_{K_3}f` is
`K₃.indicator f`.  Nothing here refers to a Sobolev exponent, a composition or
an outer function: it is a statement about one weakly differentiable function
and one mollifier.

The route.  Differentiation passes under the convolution integral, because
`ρ` is smooth with compact support and `1_{K_3}f` is locally integrable, so
`∂_i\bigl((1_{K_3}f)*ρ\bigr)(x)=\bigl((1_{K_3}f)*∂_iρ\bigr)(x)`, the
convolution with `∂_iρ` existing for the same reason.  Writing both sides as
integrals over `y`, the right-hand side is
`∫(1_{K_3}f)(y)\,∂_iρ(x - y)\,dy`, and `y ↦ ρ(x - y)` is an admissible test
function for the weak gradient of `f`: it is smooth, its support is contained in
`x - \operatorname{supp}ρ = \overline{B_d(x)} ⊆ Ω` by the hypothesis on `x`,
and `∂_{y_i}\bigl(ρ(x-y)\bigr) = -∂_iρ(x-y)`.  The defining identity of the
weak gradient therefore converts
`∫f(y)\,∂_{y_i}\bigl(ρ(x-y)\bigr)dy` into `-∫G_f^{\,i}(y)\,ρ(x-y)\,dy`, and the
two sign changes cancel.  Finally the indicator may be inserted or removed on
either side without changing the integrals, because the integrands vanish off
`\overline{B_d(x)} ⊆ K_3`; that is the only role of `K_3`, and it is why the
statement is about the truncated function rather than `f` itself. -/
theorem ConvolutionFDerivWeakGradient :
    ∀ (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))), MeasurableSet Ω →
      (∀ (A B : Set (EuclideanSpace ℝ (Fin n)))
        (h : EuclideanSpace ℝ (Fin n) → ℝ),
        (∀ y, y ∉ A → h y = 0) → A ⊆ B → (∫ y in B, h y) = ∫ y in A, h y) →
      ∀ (K3 : Set (EuclideanSpace ℝ (Fin n)))
      (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (Gf : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      HasWeakGradientOn n Ω f Gf → LocallyIntegrable (K3.indicator f) volume →
      ∀ (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (d : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ρ → HasCompactSupport ρ →
      tsupport ρ = Metric.closedBall 0 d →
      ∀ x : EuclideanSpace ℝ (Fin n), Metric.closedBall x d ⊆ K3 →
      Metric.closedBall x d ⊆ Ω → ∀ i : Fin n,
      fderiv ℝ (convolution (K3.indicator f) ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
      (EuclideanSpace.single i (1 : ℝ))
      = convolution (K3.indicator (fun z => Gf z i)) ρ
      (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  intro n Ω hΩm hsetset
  intro K3 f Gf hwgf hfloc ρ d hρsm hρcs hρts x hballK3 hballΩ i
  have hdρc : Continuous (fderiv ℝ ρ) := hρsm.continuous_fderiv (by simp)
  have hdρcs : HasCompactSupport (fderiv ℝ ρ) := hρcs.fderiv ℝ
  have hce : ConvolutionExists (K3.indicator f) (fderiv ℝ ρ)
      (ContinuousLinearMap.precompR (EuclideanSpace ℝ (Fin n))
        (ContinuousLinearMap.lsmul ℝ ℝ)) volume :=
    hdρcs.convolutionExists_right _ hfloc hdρc
  have hFD := hρcs.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    hfloc (hρsm.of_le (by simp)) x
  have hB : fderiv ℝ (convolution (K3.indicator f) ρ
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (EuclideanSpace.single i (1 : ℝ))
      = ∫ y, (K3.indicator f) y *
          (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)) := by
    have hc := ContinuousLinearMap.integral_comp_comm
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))) (hce x)
    simp only [ContinuousLinearMap.apply_apply] at hc
    rw [hFD.fderiv, convolution_def, ← hc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [ContinuousLinearMap.precompR_apply]
  have hρvan : ∀ z : EuclideanSpace ℝ (Fin n), d < ‖z‖ →
      ρ z = 0 ∧ fderiv ℝ ρ z = 0 := by
    intro z hz
    have hzn : z ∉ tsupport ρ := by rw [hρts]; simpa using not_le.2 hz
    exact ⟨image_eq_zero_of_notMem_tsupport hzn, fderiv_of_notMem_tsupport ℝ hzn⟩
  have hnormsub : ∀ y : EuclideanSpace ℝ (Fin n), ‖x - y‖ = dist y x := by
    intro y; rw [dist_eq_norm, ← norm_neg]; simp
  have houtside : ∀ y : EuclideanSpace ℝ (Fin n), y ∉ Metric.closedBall x d →
      d < ‖x - y‖ := by
    intro y hy
    rw [hnormsub y]
    simpa using hy
  have hψsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => ρ (x - y)) :=
    hρsm.comp (contDiff_const.sub contDiff_id)
  have hψts : tsupport (fun y => ρ (x - y)) ⊆ Metric.closedBall x d := by
    refine closure_minimal (fun y hy => ?_) Metric.isClosed_closedBall
    by_contra hy'
    exact hy (hρvan _ (houtside y hy')).1
  have hψcs : HasCompactSupport (fun y => ρ (x - y)) :=
    IsCompact.of_isClosed_subset (isCompact_closedBall x d) (isClosed_tsupport _) hψts
  have hψΩ : tsupport (fun y => ρ (x - y)) ⊆ Ω := hψts.trans hballΩ
  have hψd : ∀ y, fderiv ℝ (fun y' => ρ (x - y')) y (EuclideanSpace.single i (1 : ℝ))
      = -((fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ))) := by
    intro y
    have h1 : HasFDerivAt (fun y' : EuclideanSpace ℝ (Fin n) => x - y')
        (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y :=
      (hasFDerivAt_id y).const_sub x
    have h2 : HasFDerivAt ρ (fderiv ℝ ρ (x - y)) (x - y) :=
      (hρsm.differentiable (by simp) (x - y)).hasFDerivAt
    have h3 : HasFDerivAt (fun y' => ρ (x - y'))
        ((fderiv ℝ ρ (x - y)).comp
          (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) y := h2.comp y h1
    rw [h3.fderiv]
    simp
  have hWG := hwgf (fun y => ρ (x - y)) hψsm hψcs hψΩ i
  have hLid : (∫ y in Ω, f y *
        fderiv ℝ (fun y' => ρ (x - y')) y (EuclideanSpace.single i (1 : ℝ)))
      = -∫ y in Ω, f y * (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun hΩm fun y _ => ?_
    rw [hψd y]; ring
  rw [hLid] at hWG
  have hCid : (∫ y in Ω, f y * (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)))
      = ∫ y in Ω, Gf y i * ρ (x - y) := neg_inj.1 hWG
  -- move both sides onto the small ball and then onto the whole space
  have hLball : (∫ y in Ω, f y * (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)))
      = ∫ y in Metric.closedBall x d,
          f y * (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)) :=
    hsetset _ _ _ (fun y hy => by rw [(hρvan _ (houtside y hy)).2]; simp) hballΩ
  have hLind : (∫ y, (K3.indicator f) y *
        (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)))
      = ∫ y in Metric.closedBall x d,
          f y * (fderiv ℝ ρ (x - y)) (EuclideanSpace.single i (1 : ℝ)) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.closedBall x d)
      (fun y hy => by rw [(hρvan _ (houtside y hy)).2]; simp)]
    refine setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet fun y hy => ?_
    rw [Set.indicator_of_mem (hballK3 hy)]
  have hRball : (∫ y in Ω, Gf y i * ρ (x - y))
      = ∫ y in Metric.closedBall x d, Gf y i * ρ (x - y) :=
    hsetset _ _ _ (fun y hy => by rw [(hρvan _ (houtside y hy)).1]; ring) hballΩ
  have hRind : (∫ y, (K3.indicator (fun z => Gf z i)) y * ρ (x - y))
      = ∫ y in Metric.closedBall x d, Gf y i * ρ (x - y) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.closedBall x d)
      (fun y hy => by rw [(hρvan _ (houtside y hy)).1]; ring)]
    refine setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet fun y hy => ?_
    rw [Set.indicator_of_mem (hballK3 hy)]
  rw [hB, hLind, ← hLball, hCid, hRball, ← hRind, convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [ContinuousLinearMap.lsmul_apply]
