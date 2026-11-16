import ManfrediThesis.Preamble
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.WeakGradientSmoothApprox
import ManfrediThesis.SmoothCompactSupportMemW1p
set_option maxHeartbeats 800000
open MeasureTheory

/-- The weak formulation extends from its printed test class to the
compactly supported `W^{1,2}` test class: if `u` is a weak solution of
`div A(∇u) = 0` on `Ω` with `∇u = g`, then
`∫_Ω ∑_i A(g)_i(g₀)_i = 0` for every pair `(ψ₀, g₀)` with
`ψ₀ ∈ W^{1,2}(Ω)` of compact support in `Ω` and weak gradient `g₀`.

Conventions, restated here because a helper inherits none of its parent's.
`supp ψ₀` means `tsupport ψ₀`, the CLOSED support; `g` plays the role of `∇u`
and `Dg j` of `∇D_ju`, with the index placement pm-0017 records as load
bearing.  Per pm-0018 the differentiated equation is an `L²` statement whose
test class is `W^{1,2}` with compact support, which is exactly the class this
lemma reaches; the exponent `2` is written as the natural number in
`MemW1pOn n 2` and as `ENNReal.ofReal 2` where an `L²` membership is asserted,
each as the hypotheses print it.  The two integral tools (Cauchy--Schwarz and
the integrability of a product of `L²` functions) and the coordinate and
projection facts are taken as hypotheses rather than re-derived, so the lemma
states precisely what it consumes.

The route.  Approximate `ψ₀` in `W^{1,2}` by smooth functions `Ψ_m` supported
in a fixed compact `K ⊆ Ω` (\noderef{WeakGradientSmoothApprox}), so that
`∇Ψ_m → g₀` in `L²(Ω)` and every `Ψ_m` is an admissible test function for the
weak formulation; each therefore satisfies `∫_Ω ∑_iA(g)_i(∇Ψ_m)_i = 0`
(\noderef{IsWeakSolutionOn}).  The integrand difference is
`∑_iA(g)_i\bigl((∇Ψ_m)_i - (g₀)_i\bigr)`, and `|A(g)|` lies in `L²(K)`,
because each `A(g)_i` lies in `W^{1,2}_loc(Ω)` by the chain-rule hypothesis and
`K` is compact in `Ω`.  Cauchy--Schwarz on `K` therefore bounds
`\bigl|∫_K∑_iA(g)_i\bigl((∇Ψ_m)_i - (g₀)_i\bigr)\bigr|`
by `\|A(g)\|_{L²(K)}` times `\|∇Ψ_m - g₀\|_{L²(K)}`, which tends to `0`.
Since `g₀` vanishes almost everywhere off `supp ψ₀ ⊆ K`, the integral over `Ω`
equals the integral over `K`, so the limit passage gives
`|∫_K∑_iA(g)_i(g₀)_i| ≤ 0` and hence the asserted identity. -/
theorem WeakSolutionTestClassExtension :
    ∀ (n : ℕ) (p : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
      (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (u : EuclideanSpace ℝ (Fin n) → ℝ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      1 < p → IsOpen Ω → (1 : ℕ) ≤ n → MeasurableSet Ω →
      IsWeakSolutionOn n p Ω (fun _ _ h => A h) (fun _ _ _ => 0) u g →
      (∀ i : Fin n, Continuous fun w : EuclideanSpace ℝ (Fin n) => w i) →
      (∀ (w : EuclideanSpace ℝ (Fin n)) (j : Fin n), |w j| ≤ ‖w‖) →
      (∀ i : Fin n, MemW1pLocOn n 2 Ω (fun x => A (g x) i)
        (fun x => ∑ j, (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i
          • Dg j x)) →
      (∀ (S T : Set (EuclideanSpace ℝ (Fin n)))
        (w : EuclideanSpace ℝ (Fin n) → ℝ),
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
      (∀ (ψ₀ : EuclideanSpace ℝ (Fin n) → ℝ)
        (g₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        MemW1pOn n 2 Ω ψ₀ g₀ → HasCompactSupport ψ₀ → tsupport ψ₀ ⊆ Ω →
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          x ∈ Ω → x ∉ tsupport ψ₀ → g₀ x = 0) →
      ∀ (ψ₀ : EuclideanSpace ℝ (Fin n) → ℝ)
        (g₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        MemW1pOn n 2 Ω ψ₀ g₀ → HasCompactSupport ψ₀ → tsupport ψ₀ ⊆ Ω →
        (∫ x in Ω, ∑ i, A (g x) i * g₀ x i) = 0 := by
  intro n p Ω A u g Dg hp hΩ hn1 hΩm hsol hproj hcoord hstep2 hsetset hCS hintL2
    hstep3
  intro ψ₀ g₀ hW0 hcs0 hsupp0
  obtain ⟨K, Ψ, hKcpt, hKΩ, h0K, hΨsm, hΨcs, hΨK, _, hconv⟩ :=
    WeakGradientSmoothApprox n 2 hn1 one_le_two Ω ψ₀ g₀ hΩ hW0 hcs0 hsupp0
  obtain ⟨hwg0, hψLp, hgLp⟩ := hW0
  have hKm : MeasurableSet K := hKcpt.isClosed.measurableSet
  have hfinK : IsFiniteMeasure (volume.restrict K) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hKcpt.measure_lt_top
  -- the `L²` data on `K`
  have hAL2 : ∀ i : Fin n, MemLp (fun y => A (g y) i) (ENNReal.ofReal 2)
      (volume.restrict K) := fun i => ((hstep2 i).2 K hKcpt hKΩ).1
  have hg0L2 : MemLp g₀ (ENNReal.ofReal 2) (volume.restrict K) :=
    hgLp.mono_measure (Measure.restrict_mono hKΩ le_rfl)
  have hg0iL2 : ∀ i : Fin n, MemLp (fun y => g₀ y i) (ENNReal.ofReal 2)
      (volume.restrict K) := fun i =>
    hg0L2.mono ((hproj i).comp_aestronglyMeasurable hg0L2.1)
      (Filter.Eventually.of_forall fun y => hcoord _ i)
  have hDΨL2 : ∀ (m : ℕ) (i : Fin n),
      MemLp (fun y => fderiv ℝ (Ψ m) y (EuclideanSpace.single i (1 : ℝ)))
        (ENNReal.ofReal 2) (volume.restrict K) := by
    intro m i
    have hc : Continuous
        (fun y => fderiv ℝ (Ψ m) y (EuclideanSpace.single i (1 : ℝ))) :=
      ((hΨsm m).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcsupp : HasCompactSupport
        (fun y => fderiv ℝ (Ψ m) y (EuclideanSpace.single i (1 : ℝ))) :=
      ((hΨcs m).fderiv ℝ).comp_left
        (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
          L (EuclideanSpace.single i (1 : ℝ))) (by simp)
    obtain ⟨C, hC⟩ := hcsupp.exists_bound_of_continuous hc
    exact MemLp.of_bound hc.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => hC y)
  -- (6), restricted to `K`
  have heq : ∀ m : ℕ, (∫ x in K, ∑ i, A (g x) i *
      fderiv ℝ (Ψ m) x (EuclideanSpace.single i (1 : ℝ))) = 0 := by
    intro m
    have hmem := SmoothCompactSupportMemW1p n p hn1 hp.le Ω (Ψ m) hΩ (hΨsm m)
      (hΨcs m) ((hΨK m).trans hKΩ)
    have hw := (hsol.2 (Ψ m) _ hmem (hΨcs m) ((hΨK m).trans hKΩ)).2
    simp only [zero_mul, add_zero] at hw
    have hgoal : (∫ x in K, ∑ i, A (g x) i *
          fderiv ℝ (Ψ m) x (EuclideanSpace.single i (1 : ℝ)))
        = ∫ x in Ω, ∑ i, A (g x) i *
          fderiv ℝ (Ψ m) x (EuclideanSpace.single i (1 : ℝ)) := by
      refine (hsetset K Ω _ ?_ hKΩ).symm
      intro y hy
      have h0 : fderiv ℝ (Ψ m) y = 0 :=
        fderiv_of_notMem_tsupport ℝ fun hc => hy (hΨK m hc)
      simp [h0]
    rw [hgoal]
    exact hw
  -- the target is an integral over `K`
  have htgt : (∫ x in Ω, ∑ i, A (g x) i * g₀ x i)
      = ∫ x in K, ∑ i, A (g x) i * g₀ x i := by
    have hzero : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        x ∈ Ω → K.indicator g₀ x = g₀ x := by
      filter_upwards [hstep3 ψ₀ g₀ ⟨hwg0, hψLp, hgLp⟩ hcs0 hsupp0] with x hx hxΩ
      by_cases hxK : x ∈ K
      · rw [Set.indicator_of_mem hxK]
      · rw [Set.indicator_of_notMem hxK, hx hxΩ fun hc => hxK (h0K hc)]
    have e1 : (∫ x in Ω, ∑ i, A (g x) i * g₀ x i)
        = ∫ x in Ω, ∑ i, A (g x) i * K.indicator g₀ x i := by
      refine setIntegral_congr_ae hΩm ?_
      filter_upwards [hzero] with x hx hxΩ
      rw [hx hxΩ]
    have e2 : (∫ x in Ω, ∑ i, A (g x) i * K.indicator g₀ x i)
        = ∫ x in K, ∑ i, A (g x) i * K.indicator g₀ x i :=
      hsetset _ _ _ (fun y hy => by simp [Set.indicator_of_notMem hy]) hKΩ
    have e3 : (∫ x in K, ∑ i, A (g x) i * K.indicator g₀ x i)
        = ∫ x in K, ∑ i, A (g x) i * g₀ x i := by
      refine setIntegral_congr_fun hKm fun y hy => ?_
      simp [Set.indicator_of_mem hy]
    rw [e1, e2, e3]
  rw [htgt]
  -- integrability of the summands
  have hintA : ∀ F : Fin n → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ i, MemLp (F i) (ENNReal.ofReal 2) (volume.restrict K)) →
      IntegrableOn (fun x => ∑ i, A (g x) i * F i x) K volume := by
    intro F hFL2
    exact integrable_finsetSum _ fun i _ => hintL2 K _ _ (hAL2 i) (hFL2 i)
  have hi1 := hintA (fun i x => g₀ x i) hg0iL2
  have hi2 : ∀ m : ℕ, IntegrableOn
      (fun x => ∑ i, A (g x) i *
        fderiv ℝ (Ψ m) x (EuclideanSpace.single i (1 : ℝ))) K volume :=
    fun m => hintA _ fun i => hDΨL2 m i
  have hi3 : ∀ m : ℕ, IntegrableOn
      (fun x => ∑ i, A (g x) i *
        (fderiv ℝ (Ψ m) x (EuclideanSpace.single i (1 : ℝ)) - g₀ x i)) K volume :=
    fun m => hintA _ fun i => (hDΨL2 m i).sub (hg0iL2 i)
  have hi4 : ∀ m : ℕ, IntegrableOn
      (fun x => ∑ i, |A (g x) i *
        (fderiv ℝ (Ψ m) x (EuclideanSpace.single i (1 : ℝ)) - g₀ x i)|) K volume :=
    fun m => integrable_finsetSum _ fun i _ =>
      (hintL2 K _ _ (hAL2 i) ((hDΨL2 m i).sub (hg0iL2 i))).abs
  -- the Cauchy–Schwarz bound
  have hbnd : ∀ m : ℕ, |∫ x in K, ∑ i, A (g x) i * g₀ x i|
      ≤ ∑ i, Real.sqrt (∫ y in K, |A (g y) i| ^ (2:ℝ))
          * Real.sqrt (∫ y in K,
            |fderiv ℝ (Ψ m) y (EuclideanSpace.single i (1 : ℝ)) - g₀ y i| ^ (2:ℝ)) := by
    intro m
    have hdiff : (∫ x in K, ∑ i, A (g x) i * g₀ x i)
        = -∫ x in K, ∑ i, A (g x) i *
          (fderiv ℝ (Ψ m) x (EuclideanSpace.single i (1 : ℝ)) - g₀ x i) := by
      have hstep : (∫ x in K, ∑ i, A (g x) i *
            (fderiv ℝ (Ψ m) x (EuclideanSpace.single i (1 : ℝ)) - g₀ x i))
          = (∫ x in K, ∑ i, A (g x) i *
              fderiv ℝ (Ψ m) x (EuclideanSpace.single i (1 : ℝ)))
            - ∫ x in K, ∑ i, A (g x) i * g₀ x i := by
        rw [← integral_sub (hi2 m) hi1]
        refine setIntegral_congr_fun hKm fun x _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [hstep, heq m]
      ring
    rw [hdiff, abs_neg]
    calc |∫ x in K, ∑ i, A (g x) i *
            (fderiv ℝ (Ψ m) x (EuclideanSpace.single i (1 : ℝ)) - g₀ x i)|
        ≤ ∫ x in K, |∑ i, A (g x) i *
            (fderiv ℝ (Ψ m) x (EuclideanSpace.single i (1 : ℝ)) - g₀ x i)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x in K, ∑ i, |A (g x) i *
            (fderiv ℝ (Ψ m) x (EuclideanSpace.single i (1 : ℝ)) - g₀ x i)| := by
          refine setIntegral_mono_on (hi3 m).abs (hi4 m) hKm fun x _ => ?_
          exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, ∫ x in K, |A (g x) i *
            (fderiv ℝ (Ψ m) x (EuclideanSpace.single i (1 : ℝ)) - g₀ x i)| := by
          refine integral_finsetSum _ fun i _ => ?_
          exact (hintL2 K _ _ (hAL2 i) ((hDΨL2 m i).sub (hg0iL2 i))).abs
      _ ≤ ∑ i, Real.sqrt (∫ y in K, |A (g y) i| ^ (2:ℝ))
            * Real.sqrt (∫ y in K,
              |fderiv ℝ (Ψ m) y (EuclideanSpace.single i (1 : ℝ)) - g₀ y i| ^ (2:ℝ)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact hCS K _ _ (hAL2 i) ((hDΨL2 m i).sub (hg0iL2 i))
  -- the bound tends to zero
  have hlim : Filter.Tendsto (fun m : ℕ =>
      ∑ i, Real.sqrt (∫ y in K, |A (g y) i| ^ (2:ℝ))
        * Real.sqrt (∫ y in K,
          |fderiv ℝ (Ψ m) y (EuclideanSpace.single i (1 : ℝ)) - g₀ y i| ^ (2:ℝ)))
      Filter.atTop (nhds 0) := by
    have h0 : (0 : ℝ) = ∑ _i : Fin n, (0 : ℝ) := by simp
    rw [h0]
    refine tendsto_finsetSum _ fun i _ => ?_
    have hs : Filter.Tendsto (fun m : ℕ => Real.sqrt (∫ y in K,
        |fderiv ℝ (Ψ m) y (EuclideanSpace.single i (1 : ℝ)) - g₀ y i| ^ (2:ℝ)))
        Filter.atTop (nhds 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp (hconv i)
      simpa [Function.comp_def] using this
    have := hs.const_mul (Real.sqrt (∫ y in K, |A (g y) i| ^ (2:ℝ)))
    simpa using this
  have hle : |∫ x in K, ∑ i, A (g x) i * g₀ x i| ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hbnd)
  exact abs_eq_zero.1 (le_antisymm hle (abs_nonneg _))
