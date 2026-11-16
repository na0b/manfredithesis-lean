import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.WeakGradientDifferenceQuotient
set_option maxHeartbeats 1600000
open MeasureTheory

/-- The limit `h → 0` in the difference-quotient identity: passing from the
exact identity at the increment `h` to the differentiated equation itself.

Conventions, restated here because a helper inherits none of its parent's.
`supp` is the CLOSED support.  `Dg j` is the weak gradient of the `j`-th
component `g^j` of `g`, so `(Dg j x) k = D_kD_j u(x)`; the coefficient of the
differentiated equation pairs with `D_kD_j u`, and that index placement is
load-bearing, not cosmetic.  The identity is an `L²` statement, so its test
class is `W^{1,2}` with compact support in `Ω` and never `W^{1,p}`; the
exponent `2` below is that of the test class and is not a stand-in for `p`.
`e_k` is the `k`-th coordinate vector and `M` is an almost-everywhere bound for
every component of `A(g(\cdot))` on a `δ`-neighbourhood of `supp φ`.

Given the exact identity at every admissible increment `h` --- hypothesis (H)
below, which is the integrated difference quotient tested against `g_φ` ---
the conclusion is
`∫_Ω Σ_i (Σ_j (dA(g)e_j)_i • Dg j)_k · (g_φ)_i = 0`.

The route is: the difference quotients
`y ↦ (A(g(y + h e_k))_i - A(g(y))_i)/h` converge in `L²(supp φ)` to
`(Σ_j (dA(g)e_j)_i • Dg j)_k` as `h → 0`, by
`WeakGradientDifferenceQuotient` applied to the pair of the chain rule for
`A^i ∘ g` on `Ω`; pairing with the fixed `L²` factor `(g_φ)_i` is continuous
for that convergence by Cauchy--Schwarz, so the integral of the pairing
converges.  The identity (H) makes every term of the approximating sequence
zero, so the limit is zero as well, and the integral over `Ω` equals the one
over `supp φ` because `g_φ` vanishes almost everywhere off `supp φ`. -/
theorem DifferenceQuotientLimitIdentity :
    ∀ (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))), 1 ≤ n → IsOpen Ω →
      ∀ (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (k : Fin n)
        (φ : EuclideanSpace ℝ (Fin n) → ℝ)
        (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        MemW1pOn n 2 Ω φ gφ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        (∀ i : Fin n, MemW1pLocOn n 2 Ω (fun x => A (g x) i)
          (fun x => ∑ j, (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i • Dg j x)) →
        (∀ (S T : Set (EuclideanSpace ℝ (Fin n))) (w : EuclideanSpace ℝ (Fin n) → ℝ),
          (∀ y, y ∉ S → w y = 0) → S ⊆ T → (∫ y in T, w y) = ∫ y in S, w y) →
        (∀ (S : Set (EuclideanSpace ℝ (Fin n)))
          (F G : EuclideanSpace ℝ (Fin n) → ℝ),
          MemLp F (ENNReal.ofReal 2) (volume.restrict S) →
          MemLp G (ENNReal.ofReal 2) (volume.restrict S) →
          (∫ y in S, |F y * G y|)
            ≤ Real.sqrt (∫ y in S, |F y| ^ (2:ℝ))
              * Real.sqrt (∫ y in S, |G y| ^ (2:ℝ))) →
        (∀ (S : Set (EuclideanSpace ℝ (Fin n)))
          (F G : EuclideanSpace ℝ (Fin n) → ℝ),
          MemLp F (ENNReal.ofReal 2) (volume.restrict S) →
          MemLp G (ENNReal.ofReal 2) (volume.restrict S) →
          IntegrableOn (fun y => F y * G y) S volume) →
      ∀ δ : ℝ, 0 < δ →
        (∀ᵐ x ∂(volume.restrict Ω), (tsupport φ).indicator gφ x = gφ x) →
        (∀ i : Fin n, AEStronglyMeasurable (fun y => A (g y) i)
          (volume.restrict (tsupport φ))) →
        (∀ h : ℝ, |h| ≤ δ → ∀ i : Fin n, AEStronglyMeasurable
          (fun y => A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i)
          (volume.restrict (tsupport φ))) →
      ∀ M : ℝ,
        (∀ᵐ y ∂(volume.restrict (tsupport φ)), ∀ i : Fin n, |A (g y) i| ≤ M) →
        (∀ h : ℝ, |h| ≤ δ → ∀ᵐ y ∂(volume.restrict (tsupport φ)),
          ∀ i : Fin n, |A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i| ≤ M) →
        (∀ h : ℝ, 0 < |h| → |h| ≤ δ →
          (∫ y in tsupport φ, ∑ i, ((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i
              - A (g y) i) / h) * gφ y i) = 0) →
        (∫ x in Ω, ∑ i,
          (∑ j, (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i • Dg j x) k
            * gφ x i) = 0 := by
  intro n Ω hn1 hΩ A g Dg k φ gφ hφW hφcs hφΩ hstep2 hsetset hCS hintL2 δ hδ0
    hĝ hAESM1 hAESM2 M hMK0 hMshift h7
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hK0m : MeasurableSet (tsupport φ) := hφcs.isClosed.measurableSet
  have hproj : ∀ i : Fin n, Continuous fun w : EuclideanSpace ℝ (Fin n) => w i :=
    fun i => (EuclideanSpace.proj i).continuous
  have hcoord : ∀ (w : EuclideanSpace ℝ (Fin n)) (j : Fin n), |w j| ≤ ‖w‖ := by
    intro w j
    rw [EuclideanSpace.norm_eq,
      show |w j| = Real.sqrt (|w j| ^ 2) by rw [Real.sqrt_sq (abs_nonneg _)]]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (f := fun l => |w l| ^ 2) (fun l _ => sq_nonneg _)
        (Finset.mem_univ j))
  have hfinK0 : IsFiniteMeasure (volume.restrict (tsupport φ)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hφcs.measure_lt_top
  -- the `L²` data on `tsupport φ`
  have hVL2 : ∀ i : Fin n, MemLp
      (fun y => (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k)
      (ENNReal.ofReal 2) (volume.restrict (tsupport φ)) := by
    intro i
    have hV := ((hstep2 i).2 (tsupport φ) hφcs hφΩ).2
    exact hV.mono ((hproj k).comp_aestronglyMeasurable hV.1)
      (Filter.Eventually.of_forall fun y => hcoord _ k)
  have hgφiL2 : ∀ i : Fin n, MemLp (fun y => gφ y i) (ENNReal.ofReal 2)
      (volume.restrict (tsupport φ)) := by
    intro i
    have h1 : MemLp gφ (ENNReal.ofReal 2) (volume.restrict (tsupport φ)) :=
      hφW.2.2.mono_measure (Measure.restrict_mono hφΩ le_rfl)
    exact h1.mono ((hproj i).comp_aestronglyMeasurable h1.1)
      (Filter.Eventually.of_forall fun y => hcoord _ i)
  have hDQL2 : ∀ h : ℝ, 0 < |h| → |h| ≤ δ → ∀ i : Fin n,
      MemLp (fun y => (A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
        (ENNReal.ofReal 2) (volume.restrict (tsupport φ)) := by
    intro h hh0 hhδ i
    have hm : AEStronglyMeasurable
        (fun y => (A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
        (volume.restrict (tsupport φ)) :=
      (continuous_id.div_const h).comp_aestronglyMeasurable
        ((hAESM2 h hhδ i).sub (hAESM1 i))
    refine MemLp.of_bound hm (2 * M / |h|) ?_
    filter_upwards [hMK0, hMshift h hhδ] with y hy1 hy2
    rw [Real.norm_eq_abs, abs_div]
    have hb := norm_sub_le
      (A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i) (A (g y) i)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at hb
    have h1 : |A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i| ≤ 2 * M := by
      linarith [hy1 i, hy2 i]
    exact div_le_div_of_nonneg_right h1 hh0.le
  -- the target is an integral over `tsupport φ`
  have htgt : (∫ x in Ω, ∑ i,
        (∑ j, (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i • Dg j x) k * gφ x i)
      = ∫ y in tsupport φ, ∑ i,
        (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k
          * gφ y i := by
    have e1 : (∫ x in Ω, ∑ i,
          (∑ j, (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i • Dg j x) k
            * gφ x i)
        = ∫ x in Ω, ∑ i,
          (∑ j, (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i • Dg j x) k
            * (tsupport φ).indicator gφ x i := by
      refine setIntegral_congr_ae hΩm ?_
      filter_upwards [(ae_restrict_iff' hΩm).1 hĝ] with x hx hxΩ
      rw [hx hxΩ]
    have e2 : (∫ x in Ω, ∑ i,
          (∑ j, (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i • Dg j x) k
            * (tsupport φ).indicator gφ x i)
        = ∫ y in tsupport φ, ∑ i,
          (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k
            * (tsupport φ).indicator gφ y i :=
      hsetset _ _ _ (fun y hy => by simp [Set.indicator_of_notMem hy]) hφΩ
    have e3 : (∫ y in tsupport φ, ∑ i,
          (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k
            * (tsupport φ).indicator gφ y i)
        = ∫ y in tsupport φ, ∑ i,
          (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k
            * gφ y i := by
      refine setIntegral_congr_fun hK0m fun y hy => ?_
      simp [Set.indicator_of_mem hy]
    rw [e1, e2, e3]
  rw [htgt]
  -- integrability
  have hiV : IntegrableOn (fun y => ∑ i,
      (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k * gφ y i)
      (tsupport φ) volume :=
    integrable_finsetSum _ fun i _ => hintL2 _ _ _ (hVL2 i) (hgφiL2 i)
  have hiDQ : ∀ h : ℝ, 0 < |h| → |h| ≤ δ → IntegrableOn
      (fun y => ∑ i, ((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
        * gφ y i) (tsupport φ) volume :=
    fun h hh0 hhδ =>
      integrable_finsetSum _ fun i _ => hintL2 _ _ _ (hDQL2 h hh0 hhδ i) (hgφiL2 i)
  have hiD : ∀ h : ℝ, 0 < |h| → |h| ≤ δ → IntegrableOn
      (fun y => ∑ i, (((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
        - (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k)
        * gφ y i) (tsupport φ) volume :=
    fun h hh0 hhδ => integrable_finsetSum _ fun i _ =>
      hintL2 _ _ _ ((hDQL2 h hh0 hhδ i).sub (hVL2 i)) (hgφiL2 i)
  have hiDa : ∀ h : ℝ, 0 < |h| → |h| ≤ δ → IntegrableOn
      (fun y => ∑ i, abs ((((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i
          - A (g y) i) / h)
        - (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k)
        * gφ y i)) (tsupport φ) volume :=
    fun h hh0 hhδ => integrable_finsetSum _ fun i _ =>
      (hintL2 _ _ _ ((hDQL2 h hh0 hhδ i).sub (hVL2 i)) (hgφiL2 i)).abs
  -- the Cauchy–Schwarz bound
  have hbnd : ∀ h : ℝ, 0 < |h| → |h| ≤ δ →
      |∫ y in tsupport φ, ∑ i,
          (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k * gφ y i|
        ≤ ∑ i, Real.sqrt (∫ y in tsupport φ,
            |((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
              - (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k|
              ^ (2:ℝ))
          * Real.sqrt (∫ y in tsupport φ, |gφ y i| ^ (2:ℝ)) := by
    intro h hh0 hhδ
    have hdiff : (∫ y in tsupport φ, ∑ i,
          (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k * gφ y i)
        = -∫ y in tsupport φ, ∑ i,
          (((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
            - (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k)
            * gφ y i := by
      have hstep : (∫ y in tsupport φ, ∑ i,
            (((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
              - (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k)
              * gφ y i)
          = (∫ y in tsupport φ, ∑ i,
              ((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
                * gφ y i)
            - ∫ y in tsupport φ, ∑ i,
              (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k
                * gφ y i := by
        rw [← integral_sub (hiDQ h hh0 hhδ) hiV]
        refine setIntegral_congr_fun hK0m fun y _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [hstep, h7 h hh0 hhδ]
      ring
    rw [hdiff, abs_neg]
    calc |∫ y in tsupport φ, ∑ i,
            (((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
              - (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k)
              * gφ y i|
        ≤ ∫ y in tsupport φ, |∑ i,
            (((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
              - (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k)
              * gφ y i| := abs_integral_le_integral_abs
      _ ≤ ∫ y in tsupport φ, ∑ i, abs
            ((((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
              - (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k)
              * gφ y i) := by
          refine setIntegral_mono_on (hiD h hh0 hhδ).abs (hiDa h hh0 hhδ) hK0m
            fun y _ => ?_
          exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, ∫ y in tsupport φ, abs
            ((((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
              - (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k)
              * gφ y i) := by
          refine integral_finsetSum _ fun i _ => ?_
          exact (hintL2 _ _ _ ((hDQL2 h hh0 hhδ i).sub (hVL2 i)) (hgφiL2 i)).abs
      _ ≤ ∑ i, Real.sqrt (∫ y in tsupport φ,
              |((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
                - (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k|
                ^ (2:ℝ))
            * Real.sqrt (∫ y in tsupport φ, |gφ y i| ^ (2:ℝ)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact hCS _ _ _ ((hDQL2 h hh0 hhδ i).sub (hVL2 i)) (hgφiL2 i)
  -- the bound tends to zero along the punctured filter
  have hDQ : ∀ i : Fin n, Filter.Tendsto (fun h : ℝ => ∫ y in tsupport φ,
      |((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
        - (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k|
        ^ (2:ℝ)) (nhdsWithin 0 {h | h ≠ 0}) (nhds 0) := fun i =>
    WeakGradientDifferenceQuotient n 2 hn1 one_le_two Ω (fun x => A (g x) i)
      (fun x => ∑ j, (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i • Dg j x)
      (tsupport φ) k hΩ (hstep2 i) hφcs hφΩ
  have hlim : Filter.Tendsto (fun h : ℝ =>
      ∑ i, Real.sqrt (∫ y in tsupport φ,
          |((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
            - (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k|
            ^ (2:ℝ))
        * Real.sqrt (∫ y in tsupport φ, |gφ y i| ^ (2:ℝ)))
      (nhdsWithin 0 {h | h ≠ 0}) (nhds 0) := by
    have h0 : (0 : ℝ) = ∑ _i : Fin n, (0 : ℝ) := by simp
    rw [h0]
    refine tendsto_finsetSum _ fun i _ => ?_
    have hs : Filter.Tendsto (fun h : ℝ => Real.sqrt (∫ y in tsupport φ,
        |((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
          - (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k|
          ^ (2:ℝ))) (nhdsWithin 0 {h | h ≠ 0}) (nhds 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp (hDQ i)
      simpa [Function.comp_def] using this
    have := hs.mul_const (Real.sqrt (∫ y in tsupport φ, |gφ y i| ^ (2:ℝ)))
    simpa using this
  -- the bound is eventually available
  have hev : ∀ᶠ h : ℝ in nhdsWithin 0 {h | h ≠ 0},
      |∫ y in tsupport φ, ∑ i,
          (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k * gφ y i|
        ≤ ∑ i, Real.sqrt (∫ y in tsupport φ,
            |((A (g (y + h • EuclideanSpace.single k (1 : ℝ))) i - A (g y) i) / h)
              - (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k|
              ^ (2:ℝ))
          * Real.sqrt (∫ y in tsupport φ, |gφ y i| ^ (2:ℝ)) := by
    have hsmall : ∀ᶠ h : ℝ in nhdsWithin 0 {h | h ≠ 0}, |h| < δ := by
      have hc := (continuous_abs (G := ℝ)).tendsto 0
      have h0 : |(0 : ℝ)| < δ := by simpa using hδ0
      exact (hc.eventually (eventually_lt_nhds h0)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall, self_mem_nhdsWithin] with h hh hne
    exact hbnd h (abs_pos.2 hne) hh.le
  have hnb : (nhdsWithin (0:ℝ) {h : ℝ | h ≠ 0}).NeBot := by
    have hset : {h : ℝ | h ≠ 0} = ({(0:ℝ)}ᶜ : Set ℝ) := by ext x; simp
    rw [hset]
    infer_instance
  have hle : |∫ y in tsupport φ, ∑ i,
      (∑ j, (fderiv ℝ A (g y) (EuclideanSpace.single j (1 : ℝ))) i • Dg j y) k * gφ y i| ≤ 0 :=
    ge_of_tendsto hlim hev
  exact abs_eq_zero.1 (le_antisymm hle (abs_nonneg _))
