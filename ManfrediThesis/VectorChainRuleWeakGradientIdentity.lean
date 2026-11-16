import ManfrediThesis.Preamble
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.ConvolutionLqContraction
import ManfrediThesis.MollifierLqConvergence
import ManfrediThesis.VectorChainRuleLimitPassage
set_option maxHeartbeats 1600000
open MeasureTheory

/-- The weak-gradient identity for a `C¹` composition with a vector field: if
each `G_j` lies in `W^{1,q}_loc(Ω)` with weak gradient `DG^j`, if the `G_j` are
locally uniformly bounded on compact subsets of `Ω`, and if `F` is `C¹`, then
`x ↦ F(G(x))` has weak gradient
`x ↦ ∑_j\bigl(∂F/∂y_j(G(x))\bigr)DG^j(x)` on `Ω`.

Conventions, restated here because a helper inherits none of its parent's.
`supp φ` means `tsupport φ`, the CLOSED support; `∂_iφ` is
`fderiv ℝ φ x (EuclideanSpace.single i 1)`, while the partial derivatives of
the OUTER map are `fderiv ℝ F y (Pi.single j 1)`, taken on the plain product
`Fin m → ℝ` rather than on `EuclideanSpace`, which is the index convention the
coefficient carries.  Per pm-0013 this is the VECTOR composition: `F` is a
function of all `m` components at once, which is exactly what the scalar
chain rule cannot do.  The conclusion is `HasWeakGradientOn`, i.e. the
integration-by-parts identity against every smooth compactly supported test
function on `Ω`, and nothing about `L^q` membership of the composite: that part
of the parent's statement is proved separately.  The auxiliary facts about `F`,
the coordinate projections, the `L¹` norm and the derivative of a mollification
are taken as hypotheses, so the lemma states exactly what it consumes.

The route.  Fix a test function `φ` and a coordinate `i`.  Choose a compact
`K ⊆ Ω` containing a closed `3δ`-neighbourhood of `supp φ`, and mollify: for
the standard mollifier `ρ_d` of radius `d → 0`, the truncated components
`1_{K}G_j` converge in `L^q(K)` to `G_j` and their mollifications
`(1_KG_j)*ρ_d` converge to `G_j` almost everywhere and in `L^q` on a
neighbourhood of `supp φ`.  On that neighbourhood each mollification is smooth,
so the classical chain rule applies to `F` composed with the mollified vector,
and integration by parts is available without any weak-derivative theory:
\[
∫F\bigl(G^{(d)}\bigr)\,∂_iφ
=-∫\sum_j\frac{∂F}{∂y_j}\bigl(G^{(d)}\bigr)\,∂_iG_j^{(d)}\,φ .
\]
The hypothesis on the derivative of a mollification identifies `∂_iG_j^{(d)}`
with the mollification of `DG^j_i`, so the right-hand side is an integral of
mollified data.  Letting `d → 0`: on the left, `F` is continuous and the `G_j`
are locally uniformly bounded, so `F(G^{(d)}) → F(G)` with a uniform bound and
dominated convergence applies; on the right, `∂F/∂y_j` is continuous and
bounded on the relevant compact range by the hypothesis on `F`, while
`(1_KDG^j_i)*ρ_d → DG^j_i` in `L^1` near `supp φ`, so each term converges.  The
limit identity is precisely the assertion, and the linearity hypothesis on a
continuous linear map is what rewrites the pairing
`fderiv ℝ F y` applied to a vector as the sum over `j` of its values on the
coordinate vectors. -/
theorem VectorChainRuleWeakGradientIdentity :
    ∀ (n m : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ q →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (G : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
        (DG : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (F : (Fin m → ℝ) → ℝ),
        IsOpen Ω →
        (∀ j, MemW1pLocOn n q Ω (G j) (DG j)) →
        (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω →
          ∃ L : ℝ, ∀ x ∈ K, ∀ j, |G j x| ≤ L) →
        ContDiff ℝ 1 F →
        MeasurableSet Ω →
        Continuous F → Continuous (fderiv ℝ F) → Differentiable ℝ F →
        (∀ Lb : ℝ, ∃ C : ℝ, 0 ≤ C
          ∧ (∀ y : Fin m → ℝ, ‖y‖ ≤ Lb → |F y| ≤ C)
          ∧ (∀ (y : Fin m → ℝ), ‖y‖ ≤ Lb → ∀ j,
              |fderiv ℝ F y (Pi.single j (1 : ℝ))| ≤ C)) →
        (∀ k : Fin n, Continuous (fun y : EuclideanSpace ℝ (Fin n) => y k)) →
        (∀ (w : EuclideanSpace ℝ (Fin n)) (k : Fin n), ‖w k‖ ≤ ‖w‖) →
        (∀ h : EuclideanSpace ℝ (Fin n) → ℝ, AEStronglyMeasurable h volume →
          ∫ x, |h x| = (eLpNorm h 1 volume).toReal) →
        (∀ (T : (Fin m → ℝ) →L[ℝ] ℝ) (a : Fin m → ℝ),
          T a = ∑ j, T (Pi.single j (1 : ℝ)) * a j) →
        (∀ (A B : Set (EuclideanSpace ℝ (Fin n)))
          (h : EuclideanSpace ℝ (Fin n) → ℝ),
          (∀ y, y ∉ A → h y = 0) → A ⊆ B → (∫ y in B, h y) = ∫ y in A, h y) →
        (∀ (K3 : Set (EuclideanSpace ℝ (Fin n)))
          (f : EuclideanSpace ℝ (Fin n) → ℝ)
          (Gf : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          HasWeakGradientOn n Ω f Gf →
          LocallyIntegrable (K3.indicator f) volume →
          ∀ (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (d : ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ρ → HasCompactSupport ρ →
          tsupport ρ = Metric.closedBall 0 d →
          ∀ x : EuclideanSpace ℝ (Fin n), Metric.closedBall x d ⊆ K3 →
          Metric.closedBall x d ⊆ Ω → ∀ i : Fin n,
          fderiv ℝ (convolution (K3.indicator f) ρ
              (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
              (EuclideanSpace.single i (1 : ℝ))
            = convolution (K3.indicator (fun z => Gf z i)) ρ
                (ContinuousLinearMap.lsmul ℝ ℝ) volume x) →
        HasWeakGradientOn n Ω (fun x => F (fun j => G j x))
          (fun x => ∑ j, (fderiv ℝ F (fun i => G i x) (Pi.single j (1 : ℝ)))
            • DG j x) := by
  intro n m q _hn hq Ω G DG F hΩ hW hbdd hF hΩm hFc hFd hFdiff hMM hproj hcoord
    l1norm hlin hsetset step4b
  intro φ hφ hφcs hφsupp i
  have hφc : Continuous φ := hφ.continuous
  have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφcs : HasCompactSupport
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) := hφcs.fderiv_apply ℝ _
  have hK0cpt : IsCompact (tsupport φ) := hφcs
  have hK0m : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
  -- Step 2: geometry
  obtain ⟨dd, hdd0, hddsub⟩ := hφcs.exists_cthickening_subset_open hΩ hφsupp
  obtain ⟨d0, hd00, hK3Ω⟩ : ∃ d0 : ℝ, 0 < d0 ∧
      Metric.cthickening (3 * d0) (tsupport φ) ⊆ Ω := by
    refine ⟨dd / 3, by positivity, ?_⟩
    rw [show 3 * (dd / 3) = dd by ring]; exact hddsub
  have hK3cpt : IsCompact (Metric.cthickening (3 * d0) (tsupport φ)) := hφcs.cthickening
  have hK3m : MeasurableSet (Metric.cthickening (3 * d0) (tsupport φ)) :=
    Metric.isClosed_cthickening.measurableSet
  have hK0K3 : tsupport φ ⊆ Metric.cthickening (3 * d0) (tsupport φ) :=
    Metric.self_subset_cthickening _
  have hfinK3 : IsFiniteMeasure
      (volume.restrict (Metric.cthickening (3 * d0) (tsupport φ))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK3cpt.measure_lt_top⟩
  obtain ⟨L, hL⟩ := hbdd _ hK3cpt hK3Ω
  obtain ⟨C, hC0, hCF, hCD⟩ := hMM (max L 0)
  have hVbdK3 : ∀ x ∈ Metric.cthickening (3 * d0) (tsupport φ),
      ‖(fun j => G j x : Fin m → ℝ)‖ ≤ max L 0 := fun x hx =>
    (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun j => by
      rw [Real.norm_eq_abs]
      exact le_trans (hL x hx j) (le_max_left _ _)
  -- Step 3: the mollifier family
  have hδpos : ∀ l : ℕ, (0 : ℝ) < d0 / (l + 1) := fun l => by positivity
  have hδle : ∀ l : ℕ, d0 / (l + 1) ≤ d0 := by
    intro l
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) l, hd00]
  have hδlim : Filter.Tendsto (fun l : ℕ => d0 / ((l : ℝ) + 1)) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul d0
  set B : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun l =>
    ⟨d0 / (l + 1) / 2, d0 / (l + 1), by positivity, by linarith [hδpos l]⟩ with hBdef
  set ρ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun l => (B l).normed volume with hρdef
  have hρsmooth : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (ρ l) := fun l => (B l).contDiff_normed
  have hρnonneg : ∀ l x, 0 ≤ ρ l x := fun l x => (B l).nonneg_normed x
  have hρint : ∀ l, ∫ z, ρ l z = 1 := fun l => (B l).integral_normed
  have hρts : ∀ l, tsupport (ρ l) = Metric.closedBall 0 (d0 / (l + 1)) := by
    intro l
    simpa [hBdef] using
      (B l).tsupport_normed_eq (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
  have hρcs : ∀ l, HasCompactSupport (ρ l) := fun l => (B l).hasCompactSupport_normed
  have hρc : ∀ l, Continuous (ρ l) := fun l => (hρsmooth l).continuous
  have hρI : ∀ l, Integrable (ρ l) volume :=
    fun l => (hρc l).integrable_of_hasCompactSupport (hρcs l)
  have hmass : ∀ (l : ℕ) (x : EuclideanSpace ℝ (Fin n)), ∫ y, ρ l (x - y) = 1 := by
    intro l x
    rw [integral_sub_left_eq_self (ρ l) volume x]; exact hρint l
  have hball : ∀ (l : ℕ) (x : EuclideanSpace ℝ (Fin n)), x ∈ tsupport φ →
      Metric.closedBall x (d0 / (l + 1))
        ⊆ Metric.cthickening (3 * d0) (tsupport φ) := by
    intro l x hx y hy
    refine Metric.mem_cthickening_of_dist_le y x (3 * d0) _ hx ?_
    have h1 : dist y x ≤ d0 / (l + 1) := by simpa using hy
    linarith [hδle l, hd00]
  -- the truncated data
  have hGK3 : ∀ j, MemLp (G j) (ENNReal.ofReal q)
      (volume.restrict (Metric.cthickening (3 * d0) (tsupport φ))) :=
    fun j => ((hW j).2 _ hK3cpt hK3Ω).1
  have hDGK3 : ∀ j, MemLp (DG j) (ENNReal.ofReal q)
      (volume.restrict (Metric.cthickening (3 * d0) (tsupport φ))) :=
    fun j => ((hW j).2 _ hK3cpt hK3Ω).2
  have hDGiK3 : ∀ j, MemLp (fun x => DG j x i) (ENNReal.ofReal q)
      (volume.restrict (Metric.cthickening (3 * d0) (tsupport φ))) :=
    fun j => (hDGK3 j).mono ((hproj i).comp_aestronglyMeasurable (hDGK3 j).1)
      (Filter.Eventually.of_forall fun x => hcoord _ i)
  have hGhat : ∀ j, Integrable
      ((Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j)) volume :=
    fun j => (integrable_indicator_iff hK3m).2
      (((hGK3 j).mono_exponent (ENNReal.one_le_ofReal.2 hq)).integrable le_rfl)
  have hDGhat : ∀ j, Integrable
      ((Metric.cthickening (3 * d0) (tsupport φ)).indicator (fun x => DG j x i)) volume :=
    fun j => (integrable_indicator_iff hK3m).2
      (((hDGiK3 j).mono_exponent (ENNReal.one_le_ofReal.2 hq)).integrable le_rfl)
  -- the mollifications
  set U : ℕ → Fin m → EuclideanSpace ℝ (Fin n) → ℝ := fun l j =>
    convolution ((Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j)) (ρ l)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume with hUdef
  set W : ℕ → Fin m → EuclideanSpace ℝ (Fin n) → ℝ := fun l j =>
    convolution ((Metric.cthickening (3 * d0) (tsupport φ)).indicator
      (fun x => DG j x i)) (ρ l) (ContinuousLinearMap.lsmul ℝ ℝ) volume with hWdef
  have hUsm : ∀ l j, ContDiff ℝ (⊤ : ℕ∞) (U l j) := fun l j =>
    (hρcs l).contDiff_convolution_right _ (hGhat j).locallyIntegrable (hρsmooth l)
  have hWsm : ∀ l j, ContDiff ℝ (⊤ : ℕ∞) (W l j) := fun l j =>
    (hρcs l).contDiff_convolution_right _ (hDGhat j).locallyIntegrable (hρsmooth l)
  -- (4b)
  have hUW : ∀ (l : ℕ) (j : Fin m), ∀ x ∈ tsupport φ,
      fderiv ℝ (U l j) x (EuclideanSpace.single i (1 : ℝ)) = W l j x := fun l j x hx =>
    step4b _ (G j) (DG j) (hW j).1 (hGhat j).locallyIntegrable (ρ l) (d0 / (l + 1))
      (hρsmooth l) (hρcs l) (hρts l) x (hball l x hx) ((hball l x hx).trans hK3Ω) i
  -- (4c) the uniform bound
  have hUbd : ∀ (l : ℕ), ∀ x ∈ tsupport φ,
      ‖(fun j => U l j x : Fin m → ℝ)‖ ≤ max L 0 := by
    intro l x hx
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun j => ?_
    rw [Real.norm_eq_abs]
    have hint : Integrable (fun y =>
        (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) y * ρ l (x - y))
        volume := by
      refine ((hρcs l).convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
        (hGhat j).locallyIntegrable (hρc l) x).congr
        (Filter.Eventually.of_forall fun y => ?_)
      simp [ContinuousLinearMap.lsmul_apply]
    have hptw : ∀ y, |(Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) y *
        ρ l (x - y)| ≤ max L 0 * ρ l (x - y) := by
      intro y
      rw [abs_mul, abs_of_nonneg (hρnonneg l _)]
      by_cases hz : ρ l (x - y) = 0
      · simp [hz]
      · have hmem : x - y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n))
            (d0 / (l + 1)) := by
          rw [← hρts l]; exact subset_tsupport _ hz
        have hyb : y ∈ Metric.closedBall x (d0 / (l + 1)) := by
          have h1 : ‖x - y‖ ≤ d0 / (l + 1) := by simpa using hmem
          have h2 : dist y x = ‖x - y‖ := by rw [dist_eq_norm, ← norm_neg]; simp
          simpa [h2] using h1
        rw [Set.indicator_of_mem (hball l x hx hyb)]
        exact mul_le_mul_of_nonneg_right
          (le_trans (hL y (hball l x hx hyb) j) (le_max_left _ _)) (hρnonneg l _)
    rw [hUdef]
    simp only [convolution_def]
    calc |∫ y, (ContinuousLinearMap.lsmul ℝ ℝ)
            ((Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) y) (ρ l (x - y))|
        = |∫ y, (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) y *
            ρ l (x - y)| := by
          simp [ContinuousLinearMap.lsmul_apply]
      _ ≤ ∫ y, |(Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) y *
            ρ l (x - y)| := abs_integral_le_integral_abs
      _ ≤ ∫ y, max L 0 * ρ l (x - y) :=
          integral_mono hint.abs (((hρI l).comp_sub_left x).const_mul _) hptw
      _ = max L 0 := by rw [integral_const_mul, hmass l x, mul_one]
  -- Steps 5 and 6: `L^1` convergence and an almost everywhere convergent subsequence
  have contract1 : ∀ (l : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ), MemLp w 1 volume →
      eLpNorm (convolution w (ρ l) (ContinuousLinearMap.lsmul ℝ ℝ) volume) 1 volume
        ≤ eLpNorm w 1 volume := by
    intro l w hw
    simpa [ENNReal.ofReal_one] using
      ConvolutionLqContraction n 1 le_rfl (ρ l) (hρc l) (hρnonneg l) (hρcs l)
        (hρint l) w
        (by simpa [ENNReal.ofReal_one] using hw)
  have hconvmem : ∀ (l : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ), MemLp w 1 volume →
      LocallyIntegrable w volume →
      Integrable (convolution w (ρ l) (ContinuousLinearMap.lsmul ℝ ℝ) volume) volume := by
    intro l w hw hwl
    refine memLp_one_iff_integrable.1 ⟨((hρcs l).contDiff_convolution_right _ hwl
      (hρsmooth l)).continuous.aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (contract1 l w hw) hw.2
  have converge1 : ∀ w : EuclideanSpace ℝ (Fin n) → ℝ, MemLp w 1 volume →
      Filter.Tendsto (fun l => eLpNorm
        (fun x => convolution w (ρ l) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - w x)
        1 volume) Filter.atTop (nhds 0) := by
    intro w hw
    have hct : ∀ v : EuclideanSpace ℝ (Fin n) → ℝ,
        MemLp v (ENNReal.ofReal 1) volume → ∀ l,
        eLpNorm (convolution v (ρ l) (ContinuousLinearMap.lsmul ℝ ℝ) volume)
            (ENNReal.ofReal 1) volume ≤ eLpNorm v (ENNReal.ofReal 1) volume := by
      intro v hv l
      simpa [ENNReal.ofReal_one] using
        contract1 l v (by simpa [ENNReal.ofReal_one] using hv)
    simpa [ENNReal.ofReal_one] using
      MollifierLqConvergence n 1 _hn le_rfl ρ (fun l => d0 / ((l : ℝ) + 1)) hδlim hρsmooth hρnonneg hρcs
        (fun l => (hρts l).subset) hρint hct w (by simpa [ENNReal.ofReal_one] using hw)
  have hcvU : ∀ j, Filter.Tendsto (fun l => eLpNorm
      (fun x => U l j x -
        (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x) 1 volume)
      Filter.atTop (nhds 0) :=
    fun j => converge1 _ (memLp_one_iff_integrable.2 (hGhat j))
  have hcvW : ∀ j, Filter.Tendsto (fun l => eLpNorm
      (fun x => W l j x -
        (Metric.cthickening (3 * d0) (tsupport φ)).indicator
          (fun z => DG j z i) x) 1 volume)
      Filter.atTop (nhds 0) :=
    fun j => converge1 _ (memLp_one_iff_integrable.2 (hDGhat j))
  have hUint : ∀ l j, Integrable (U l j) volume := fun l j =>
    hconvmem l _ (memLp_one_iff_integrable.2 (hGhat j)) (hGhat j).locallyIntegrable
  have hWint : ∀ l j, Integrable (W l j) volume := fun l j =>
    hconvmem l _ (memLp_one_iff_integrable.2 (hDGhat j)) (hDGhat j).locallyIntegrable
  -- the aggregate scalar
  have hZmeas : ∀ l : ℕ, AEStronglyMeasurable
      (fun x => ∑ j, |U l j x -
        (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x|) volume := by
    intro l
    have hm : ∀ j : Fin m, AEStronglyMeasurable
        (fun x => |U l j x -
          (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x|) volume := by
      intro j
      have h0 : AEStronglyMeasurable
          (fun x => U l j x -
            (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x) volume :=
        (hUint l j).1.sub (hGhat j).1
      exact continuous_abs.comp_aestronglyMeasurable h0
    have h : AEStronglyMeasurable
        (∑ j, fun x => |U l j x -
          (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x|) volume :=
      Finset.aestronglyMeasurable_sum _ fun j _ => hm j
    have heq : (∑ j, fun x => |U l j x -
          (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x|)
        = fun x => ∑ j, |U l j x -
          (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x| := by
      funext x; rw [Finset.sum_apply]
    rw [heq] at h
    exact h
  have hZnorm : ∀ l : ℕ, eLpNorm
      (fun x => ∑ j, |U l j x -
        (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x|) 1 volume
      = ∑ j, eLpNorm (fun x => U l j x -
          (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x) 1 volume := by
    intro l
    have he : ∀ x : EuclideanSpace ℝ (Fin n),
        ‖∑ j, |U l j x -
          (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x|‖ₑ
        = ∑ j, ‖U l j x -
          (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x‖ₑ := by
      intro x
      rw [← ofReal_norm, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => abs_nonneg _)]
      exact Finset.sum_congr rfl fun j _ => by
        rw [← ofReal_norm, Real.norm_eq_abs]
    calc eLpNorm (fun x => ∑ j, |U l j x -
            (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x|) 1 volume
        = ∫⁻ x, ∑ j, ‖U l j x -
            (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x‖ₑ := by
          rw [eLpNorm_one_eq_lintegral_enorm]; simp only [he]
      _ = ∑ j, ∫⁻ x, ‖U l j x -
            (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x‖ₑ :=
          lintegral_finsetSum' _ fun j _ => ((hUint l j).1.sub (hGhat j).1).enorm
      _ = ∑ j, eLpNorm (fun x => U l j x -
            (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x) 1 volume :=
          Finset.sum_congr rfl fun j _ => eLpNorm_one_eq_lintegral_enorm.symm
  have hZlim : Filter.Tendsto (fun l : ℕ => eLpNorm
      (fun x => ∑ j, |U l j x -
        (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x|) 1 volume)
      Filter.atTop (nhds 0) := by
    simp only [hZnorm]
    simpa using tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun j _ => hcvU j
  obtain ⟨ns, hns, hZae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top
    (p := (1 : ENNReal)) one_ne_zero ENNReal.one_ne_top hZmeas
    aestronglyMeasurable_zero (by simpa using hZlim)).exists_seq_tendsto_ae
  have hae : ∀ᵐ x ∂(volume.restrict (tsupport φ)),
      Filter.Tendsto (fun l => (fun j => U (ns l) j x : Fin m → ℝ)) Filter.atTop
        (nhds (fun j => G j x)) := by
    filter_upwards [ae_restrict_of_ae hZae, ae_restrict_mem hK0m] with x hx hxK
    refine tendsto_pi_nhds.2 fun j => ?_
    have hb : ∀ l : ℕ, ‖U (ns l) j x -
        (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x‖
        ≤ ∑ k, |U (ns l) k x -
          (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G k) x| := by
      intro l
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun k => |U (ns l) k x -
        (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G k) x|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ j)
    have h0 : Filter.Tendsto (fun l => U (ns l) j x -
        (Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x)
        Filter.atTop (nhds 0) := squeeze_zero_norm hb (by simpa using hx)
    have h1 := h0.add_const
      ((Metric.cthickening (3 * d0) (tsupport φ)).indicator (G j) x)
    rw [Set.indicator_of_mem (hK0K3 hxK)] at h1
    simpa using h1
  -- the `L^1` convergence of the mollified gradients on the support of `φ`
  have hL1W : ∀ j, Filter.Tendsto
      (fun l => ∫ x in tsupport φ, |W (ns l) j x - DG j x i|) Filter.atTop (nhds 0) := by
    intro j
    have hg : Filter.Tendsto (fun l => ∫ x, |W l j x -
        (Metric.cthickening (3 * d0) (tsupport φ)).indicator
          (fun z => DG j z i) x|) Filter.atTop (nhds 0) := by
      have heq : ∀ l : ℕ, (∫ x, |W l j x -
            (Metric.cthickening (3 * d0) (tsupport φ)).indicator
              (fun z => DG j z i) x|)
          = (eLpNorm (fun x => W l j x -
              (Metric.cthickening (3 * d0) (tsupport φ)).indicator
                (fun z => DG j z i) x) 1 volume).toReal :=
        fun l => l1norm _ ((hWint l j).1.sub (hDGhat j).1)
      simp only [heq]
      simpa [Function.comp_def] using
        (ENNReal.tendsto_toReal (a := 0) (by simp)).comp (hcvW j)
    refine squeeze_zero (fun l => integral_nonneg fun x => abs_nonneg _) (fun l => ?_)
      (by simpa [Function.comp_def] using hg.comp hns.tendsto_atTop)
    rw [show (∫ x in tsupport φ, |W (ns l) j x - DG j x i|)
        = ∫ x in tsupport φ, |W (ns l) j x -
          (Metric.cthickening (3 * d0) (tsupport φ)).indicator
            (fun z => DG j z i) x| from
      setIntegral_congr_fun hK0m fun x hx => by
        rw [Set.indicator_of_mem (hK0K3 hx)]]
    exact setIntegral_le_integral ((hWint (ns l) j).sub (hDGhat j)).abs
      (Filter.Eventually.of_forall fun x => abs_nonneg _)
  have step7 : ∀ (U : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
      (W : Fin m → EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (U j)) → (∀ j, Continuous (W j)) →
      (∀ j, ∀ x ∈ tsupport φ,
        fderiv ℝ (U j) x (EuclideanSpace.single i (1 : ℝ)) = W j x) →
      (∫ x in tsupport φ,
          F (fun j => U j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        = -∫ x in tsupport φ,
            (∑ j, (fderiv ℝ F (fun j => U j x) (Pi.single j (1 : ℝ))) * W j x) * φ x := by
    intro U W hUsm hWc hUW
    have hVUc : Continuous (fun x => (fun j => U j x : Fin m → ℝ)) :=
      continuous_pi fun j => (hUsm j).continuous
    have hVU : ∀ x, HasFDerivAt (fun x => (fun j => U j x : Fin m → ℝ))
        (ContinuousLinearMap.pi (fun j => fderiv ℝ (U j) x)) x :=
      fun x => hasFDerivAt_pi.2 fun j => ((hUsm j).differentiable (by simp) x).hasFDerivAt
    have hHH : ∀ x, HasFDerivAt (fun x => F (fun j => U j x))
        ((fderiv ℝ F (fun j => U j x)).comp
          (ContinuousLinearMap.pi (fun j => fderiv ℝ (U j) x))) x :=
      fun x => (hFdiff _).hasFDerivAt.comp x (hVU x)
    have hHHd : ∀ x, fderiv ℝ (fun x => F (fun j => U j x)) x
          (EuclideanSpace.single i (1 : ℝ))
        = ∑ j, (fderiv ℝ F (fun j => U j x) (Pi.single j (1 : ℝ))) *
            (fderiv ℝ (U j) x (EuclideanSpace.single i (1 : ℝ))) := by
      intro x
      rw [(hHH x).fderiv]
      simpa using hlin (fderiv ℝ F (fun j => U j x))
        (fun j => fderiv ℝ (U j) x (EuclideanSpace.single i (1 : ℝ)))
    have hHHc : Continuous (fun x => F (fun j => U j x)) := hFc.comp hVUc
    have hdHHc : Continuous (fun x => fderiv ℝ (fun x => F (fun j => U j x)) x
        (EuclideanSpace.single i (1 : ℝ))) := by
      rw [show (fun x => fderiv ℝ (fun x => F (fun j => U j x)) x
            (EuclideanSpace.single i (1 : ℝ)))
          = fun x => ∑ j, (fderiv ℝ F (fun j => U j x) (Pi.single j (1 : ℝ))) *
              (fderiv ℝ (U j) x (EuclideanSpace.single i (1 : ℝ))) from funext hHHd]
      exact continuous_finsetSum _ fun j _ =>
        ((((ContinuousLinearMap.apply ℝ ℝ
          (Pi.single j (1 : ℝ) : Fin m → ℝ)).continuous.comp hFd).comp hVUc)).mul
          (((hUsm j).continuous_fderiv (by simp)).clm_apply continuous_const)
    have hIBP : (∫ x, F (fun j => U j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        = -∫ x, fderiv ℝ (fun x => F (fun j => U j x)) x
            (EuclideanSpace.single i (1 : ℝ)) * φ x :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        (f := fun x => F (fun j => U j x)) (g := φ)
        (v := EuclideanSpace.single i (1 : ℝ))
        ((hdHHc.mul hφc).integrable_of_hasCompactSupport (HasCompactSupport.mul_left hφcs))
        ((hHHc.mul hdφ).integrable_of_hasCompactSupport (HasCompactSupport.mul_left hdφcs))
        ((hHHc.mul hφc).integrable_of_hasCompactSupport (HasCompactSupport.mul_left hφcs))
        (fun x _ => (hHH x).differentiableAt)
        (fun x _ => hφ.differentiable (by simp) x)
    have hLhs : (∫ x in tsupport φ,
          F (fun j => U j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        = ∫ x, F (fun j => U j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      have h0 : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx
      simp [h0]
    have hR1 : (∫ x, fderiv ℝ (fun x => F (fun j => U j x)) x
          (EuclideanSpace.single i (1 : ℝ)) * φ x)
        = ∫ x, (∑ j, (fderiv ℝ F (fun j => U j x) (Pi.single j (1 : ℝ))) *
            (fderiv ℝ (U j) x (EuclideanSpace.single i (1 : ℝ)))) * φ x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hHHd x]
    have hR2 : (∫ x in tsupport φ,
          (∑ j, (fderiv ℝ F (fun j => U j x) (Pi.single j (1 : ℝ))) *
            (fderiv ℝ (U j) x (EuclideanSpace.single i (1 : ℝ)))) * φ x)
        = ∫ x, (∑ j, (fderiv ℝ F (fun j => U j x) (Pi.single j (1 : ℝ))) *
            (fderiv ℝ (U j) x (EuclideanSpace.single i (1 : ℝ)))) * φ x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport hx]; ring
    have hR3 : (∫ x in tsupport φ,
          (∑ j, (fderiv ℝ F (fun j => U j x) (Pi.single j (1 : ℝ))) *
            (fderiv ℝ (U j) x (EuclideanSpace.single i (1 : ℝ)))) * φ x)
        = ∫ x in tsupport φ,
            (∑ j, (fderiv ℝ F (fun j => U j x) (Pi.single j (1 : ℝ))) * W j x) * φ x :=
      setIntegral_congr_fun (isClosed_tsupport φ).measurableSet fun x hx => by
        refine congrArg (· * φ x) (Finset.sum_congr rfl fun j _ => ?_)
        rw [hUW j x hx]
    rw [hLhs, hIBP, hR1, ← hR2, hR3]
  -- The limit passage: `VectorChainRuleLimitPassage`, whose docstring records
  -- the route (dominated convergence on the left against the majorant `C|D_i φ|`,
  -- and the `L¹(tsupport φ)` split of each summand on the right).
  have limitpass := VectorChainRuleLimitPassage n m F hF φ hφ hφcs i
  -- Step 7 and Step 8
  have h10 : ∀ l : ℕ, (∫ x in tsupport φ,
        F (fun j => U (ns l) j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
      = -∫ x in tsupport φ,
          (∑ j, (fderiv ℝ F (fun j => U (ns l) j x) (Pi.single j (1 : ℝ))) *
            W (ns l) j x) * φ x :=
    fun l => step7 (U (ns l)) (W (ns l)) (fun j => hUsm (ns l) j)
      (fun j => (hWsm (ns l) j).continuous) (fun j => hUW (ns l) j)
  have hGmeasK0 : AEStronglyMeasurable (fun x => (fun j => G j x : Fin m → ℝ))
      (volume.restrict (tsupport φ)) := by
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_iff.2 fun j => ?_
    exact ((hGK3 j).1.mono_measure (Measure.restrict_mono hK0K3 le_rfl)).aemeasurable
  have hDGiK0 : ∀ j, IntegrableOn (fun x => DG j x i) (tsupport φ) volume := by
    intro j
    have h : IntegrableOn (fun x => DG j x i)
        (Metric.cthickening (3 * d0) (tsupport φ)) volume :=
      ((hDGiK3 j).mono_exponent (ENNReal.one_le_ofReal.2 hq)).integrable le_rfl
    exact h.mono_set hK0K3
  have hkey := limitpass (max L 0) C hC0 hCF hCD G (fun j x => DG j x i)
    hGmeasK0 hDGiK0 (fun x hx => hVbdK3 x (hK0K3 hx))
    (fun l j => U (ns l) j) (fun l j => W (ns l) j)
    (fun l j => (hUsm (ns l) j).continuous) (fun l j => (hWsm (ns l) j).continuous)
    (fun l => hUbd (ns l)) hL1W hae h10
  -- assemble the goal
  have hgoalL : (∫ x in Ω,
        F (fun j => G j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
      = ∫ x in tsupport φ,
        F (fun j => G j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) :=
    hsetset _ _ _ (fun x hx => by
      have h0 : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx
      simp [h0]) hφsupp
  have hgoalR : (∫ x in Ω,
        (∑ j, (fderiv ℝ F (fun i => G i x) (Pi.single j (1 : ℝ))) • DG j x) i * φ x)
      = ∫ x in tsupport φ,
        (∑ j, (fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DG j x i) * φ x := by
    rw [show (∫ x in Ω,
          (∑ j, (fderiv ℝ F (fun i => G i x) (Pi.single j (1 : ℝ))) • DG j x) i * φ x)
        = ∫ x in Ω,
          (∑ j, (fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DG j x i) * φ x from
      setIntegral_congr_fun hΩm fun x _ => by simp]
    exact hsetset _ _ _
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx]; ring) hφsupp
  show (∫ x in Ω,
        F (fun j => G j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
      = -∫ x in Ω,
        (∑ j, (fderiv ℝ F (fun i => G i x) (Pi.single j (1 : ℝ))) • DG j x) i * φ x
  rw [hgoalL, hgoalR]
  exact hkey
