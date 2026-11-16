import ManfrediThesis.Preamble
import ManfrediThesis.WeightedCaccioppoliMeasurabilityData
import ManfrediThesis.WeightedCaccioppoliIntegrandIntegrability
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.DifferentiatedEquationWeak
import ManfrediThesis.WeakGradientSmoothMul
set_option maxHeartbeats 1600000
open MeasureTheory

/-- The sign-free core of the weighted Caccioppoli estimate at a level.

Throughout, `w = ε + ‖g‖²` is the weight of the structure conditions and
`W = w^{p/2-1}` its power, written with `Real.rpow` exactly as (Q1)/(Q2) are
printed, so that at `ε = 0` and `g = 0` the value is `0` for `p ≠ 2` and `1`
for `p = 2`; `W` enters as a function argument together with its defining
equation, so that a consumer may pass its own copy.  `ζ` is a `C^∞` cut-off
with compact support and `supp ζ ⊆ Ω`, where `supp` is the closed support.
`Dg k` is the weak gradient of the `k`-th component `g^k` of `g`, and
`(Dg^k)_j` is its `j`-th component — the index placement of the differentiated
equation, which is load-bearing and not cosmetic.

The statement is the estimate for an ARBITRARY measurable `T ⊆ Ω`, an arbitrary
sign `σ ∈ {1, -1}`, an arbitrary nonnegative test datum `v` and an arbitrary
field `Z` tied to `σ • Dg k` on `T` and vanishing, together with `v`, off `T`:
`∫_T W ‖Dg^k‖² ζ² ≤ 4n²r² ∫_Ω W v² Σ_i (∂_i ζ)²`.
Stating it in that generality once is what lets the two level sets
`Ω ∩ {g^k > l}` and `Ω ∩ {g^k < l}` be treated by the same argument, at
`σ = 1` with `v = (g^k - l)^+` and at `σ = -1` with `v = (l - g^k)^+`; the
caller supplies the two pairs, and nothing is read back out of the choice.

The route is Steps 3-9 of the parent's argument.  The test pair is
`(v ζ², ζ² Z + v ∇(ζ²))`, admissible for the differentiated equation because
`v ∈ W^{1,2}_loc(Ω)` with weak gradient `Z` and `ζ²` is smooth with compact
support in `Ω`; `DifferentiatedEquationWeak` applied to it, with the
coefficient matrix `M = DA(g)`, splits into the `ζ²Z` term and the
`v ∇(ζ²)` term.  On the first, `Q1` with `ξ = Dg^k` and the almost-everywhere
identity `Z = σ • Dg^k` on `T` give the left-hand side after multiplying by
`σ`, using `σ² = 1`; on the second, `Q2` bounds every entry of `M` by
`γ₁ W` and two applications of Cauchy-Schwarz in the index, together with
`∇(ζ²) = 2ζ∇ζ`, produce `2nγ₁ ∫_Ω W ‖Dg^k‖ v |ζ| |∇ζ|`.  One more
Cauchy-Schwarz in the integral, against the splitting
`(W^{1/2}‖Dg^k‖|ζ|) · (W^{1/2} v |∇ζ|)`, gives
`X ≤ 2nγ₁γ₀^{-1} X^{1/2} Y^{1/2}` with `X` the left-hand side and `Y` the
right-hand integral; `γ₁ ≤ rγ₀` and squaring turn that into the constant
`4n²r²`.  The `X = 0` branch is handled separately, the right-hand side being
nonnegative. -/
theorem WeightedCaccioppoliSignedCore :
    ∀ (n : ℕ) (p r : ℝ), 2 ≤ n → 1 < p → 0 < r →
      ∀ (ε γ₀ γ₁ : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (ζ : EuclideanSpace ℝ (Fin n) → ℝ) (k : Fin n),
        0 < ε → 0 < γ₀ → γ₁ ≤ r * γ₀ → γ₀ ≤ γ₁ → IsOpen Ω → Ω.Nonempty →
        EllipticStructureQ12 n p ε γ₀ γ₁ Ω (fun _ _ h => A h) →
        CitedRegularityEpsPos n p ε γ₀ γ₁ Ω A →
        IsWeakSolutionOn n p Ω (fun _ _ h => A h) (fun _ _ _ => 0) u g →
        (∀ i : Fin n, MemW1pLocOn n 2 Ω (fun x => g x i) (Dg i)) →
        ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
      ∀ W : EuclideanSpace ℝ (Fin n) → ℝ,
        W = (fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)) →
      ∀ (T : Set (EuclideanSpace ℝ (Fin n))) (σ : ℝ)
        (v : EuclideanSpace ℝ (Fin n) → ℝ)
        (Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        (σ = 1 ∨ σ = -1) → MeasurableSet T → T ⊆ Ω →
        (∀ x, 0 ≤ v x) →
        (∀ᵐ x ∂(volume.restrict Ω),
          (x ∈ T → Z x = σ • Dg k x) ∧ (x ∉ T → Z x = 0 ∧ v x = 0)) →
        MemW1pLocOn n 2 Ω v Z →
        (∫ x in T, W x * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
          ≤ 4 * (n : ℝ) ^ 2 * r ^ 2
            * ∫ x in Ω, W x * v x ^ 2
              * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 := by
  intro n p r hn hp hr ε γ₀ γ₁ Ω A u g Dg ζ k hε hγ₀ hγ₁r hγ hΩ hΩne hQ hC1 hsol hDg
    hζsm hζcs hζΩ W hWdef
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR0 : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨w, hwdef⟩ : ∃ w : EuclideanSpace ℝ (Fin n) → ℝ,
      w = fun x => ε + ‖g x‖ ^ 2 := ⟨_, rfl⟩
  have hweq : ∀ x, w x = ε + ‖g x‖ ^ 2 := fun x => by rw [hwdef]
  have hwpos : ∀ x, 0 < w x := by
    intro x
    rw [hweq x]
    have h := sq_nonneg ‖g x‖
    linarith
  have hWeq : ∀ x, W x = w x ^ (p / 2 - 1) := fun x => by rw [hWdef, hweq x]
  have hWpos : ∀ x, 0 < W x := fun x => by
    rw [hWeq x]
    exact Real.rpow_pos_of_pos (hwpos x) _
  have hWval : ∀ x, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) = W x := fun x => by
    rw [hWeq x, hweq x]
  have hγ₁p : (0 : ℝ) < γ₁ := lt_of_lt_of_le hγ₀ hγ
  obtain ⟨-, g', hg'cont, hg'ae, -⟩ := hC1 hε hQ u g hsol
  obtain ⟨w', hw'def⟩ : ∃ w' : EuclideanSpace ℝ (Fin n) → ℝ,
      w' = fun x => ε + ‖g' x‖ ^ 2 := ⟨_, rfl⟩
  have hw'eq : ∀ x, w' x = ε + ‖g' x‖ ^ 2 := fun x => by rw [hw'def]
  have hw'pos : ∀ x, 0 < w' x := by
    intro x
    rw [hw'eq x]
    have h := sq_nonneg ‖g' x‖
    linarith
  have hw'cont : ContinuousOn w' Ω := by
    rw [hw'def]
    exact continuousOn_const.add (hg'cont.norm.pow 2)
  have hWae : ∀ᵐ x ∂(volume.restrict Ω), W x = w' x ^ (p / 2 - 1) := by
    filter_upwards [hg'ae] with x hx
    rw [hWeq x, hweq x, hw'eq x, hx]
  have hwpowbd : ∀ (σ : ℝ) (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K → K ⊆ Ω →
      ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, w' x ^ σ ≤ L := by
    intro σ K hK hKΩ
    have hc : ContinuousOn (fun x => w' x ^ σ) K := by
      refine ContinuousOn.rpow_const (hw'cont.mono hKΩ) ?_
      intro x hx
      exact Or.inl (ne_of_gt (hw'pos x))
    obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn hc
    refine ⟨max L 0, le_max_right _ _, fun x hx => ?_⟩
    refine le_trans ?_ (le_max_left L 0)
    exact le_trans (le_abs_self _) (by simpa using hL x hx)
  obtain ⟨M, hMdef⟩ : ∃ M : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ,
      M = fun x i j => (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i := ⟨_, rfl⟩
  have hMeq : ∀ x i j, M x i j
      = (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i :=
    fun x i j => by rw [hMdef]
  have hKcpt : IsCompact (tsupport ζ) := hζcs
  have hKmeas : MeasurableSet (tsupport ζ) := hKcpt.measurableSet
  have hζ0 : ∀ x, x ∉ tsupport ζ → ζ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport hx
  have hDζ0 : ∀ x, x ∉ tsupport ζ → ∀ i : Fin n,
      fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)) = 0 := by
    intro x hx i
    rw [fderiv_of_notMem_tsupport ℝ hx]
    simp
  have hextend : ∀ F : EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ x, x ∉ tsupport ζ → F x = 0) →
      IntegrableOn F (tsupport ζ) volume → IntegrableOn F Ω volume := by
    intro F hF0 hFK
    have hsplit : Ω = tsupport ζ ∪ (Ω \ tsupport ζ) := by
      rw [Set.union_sdiff_cancel hζΩ]
    rw [hsplit]
    refine IntegrableOn.union hFK ?_
    exact IntegrableOn.congr_fun integrableOn_zero (fun x hx => (hF0 x hx.2).symm)
      (hΩ.measurableSet.diff hKmeas)
  have hAcd : ContDiff ℝ 1 (fun h : EuclideanSpace ℝ (Fin n) => A h) := by
    obtain ⟨x0, hx0⟩ := hΩne
    have h1 := hQ.hdiff x0 hx0 0
    have h2 : {h : EuclideanSpace ℝ (Fin n) | ε + ‖h‖ ^ 2 ≠ 0} = Set.univ := by
      ext h
      constructor
      · intro _; trivial
      · intro _
        have h3 : (0 : ℝ) ≤ ‖h‖ ^ 2 := sq_nonneg _
        exact ne_of_gt (by linarith)
    rw [h2] at h1
    exact contDiffOn_univ.1 h1
  have hdecomp : ∀ ξ : EuclideanSpace ℝ (Fin n),
      ξ = ∑ j, ξ j • EuclideanSpace.single j (1 : ℝ) := by
    intro ξ
    refine PiLp.ext fun i => ?_
    simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq]
  have hlin : ∀ (x ξ : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      (fderiv ℝ A (g x) ξ) i = ∑ j, M x i j * ξ j := by
    intro x ξ i
    conv_lhs => rw [hdecomp ξ]
    rw [map_sum]
    simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
      Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [hMeq x i j]; ring
  have hQ1b : ∀ᵐ x ∂(volume.restrict Ω), ∀ ξ : EuclideanSpace ℝ (Fin n),
      γ₀ * W x * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, M x i j * ξ j * ξ i := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet, ae_restrict_of_ae hQ.Q1]
      with x hxΩ hxQ1
    intro ξ
    have hwne : ε + ‖g x‖ ^ 2 ≠ 0 := by
      have h1 : (0 : ℝ) ≤ ‖g x‖ ^ 2 := sq_nonneg _
      exact ne_of_gt (by linarith)
    have h1 := hxQ1 hxΩ 0 (g x) ξ hwne
    rw [hWval x] at h1
    refine le_trans h1 (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => by rw [hlin x ξ i, Finset.sum_mul]
  have hQ2b : ∀ᵐ x ∂(volume.restrict Ω), ∀ i j : Fin n,
      |M x i j| ≤ γ₁ * W x := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet, ae_restrict_of_ae hQ.Q2]
      with x hxΩ hxQ2
    intro i j
    have hwne : ε + ‖g x‖ ^ 2 ≠ 0 := by
      have h1 : (0 : ℝ) ≤ ‖g x‖ ^ 2 := sq_nonneg _
      exact ne_of_gt (by linarith)
    have h1 := hxQ2 hxΩ 0 (g x) i j hwne
    rw [← hMeq x i j, hWval x] at h1
    exact h1
  obtain ⟨hWm, hMm, hDgcm, hζm, hDζm, haemul, haesum, hMint, ⟨Lζ, hLζ0, hLζ⟩,
    ⟨LDζ, hLDζ0, hLDζ⟩, ⟨LW, hLW0, hLW⟩⟩ :=
    WeightedCaccioppoliMeasurabilityData n p ε Ω A u g Dg ζ k w w' W M hsol hDg
      hζsm hζcs hζΩ hweq hwpos hWeq hWae hwpowbd hMeq hAcd hζ0 hDζ0
  have hsumbd : ∀ (f : Fin n → ℝ) (Mb : ℝ), (∀ i, |f i| ≤ Mb) →
      |∑ i, f i| ≤ (n : ℝ) * Mb := by
    intro f Mb hM
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ i, |f i| ≤ ∑ _i : Fin n, Mb := Finset.sum_le_sum fun i _ => hM i
      _ = (n : ℝ) * Mb := by simp [mul_comm]
  have habs2 : ∀ a b : ℝ, |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    intro a b
    have h1 : (0 : ℝ) ≤ (|a| - |b|) ^ 2 := sq_nonneg _
    have h2 : (|a| - |b|) ^ 2 = a ^ 2 - 2 * (|a| * |b|) + b ^ 2 := by
      rw [sub_sq, sq_abs, sq_abs]; ring
    linarith [h1, h2]
  have hDgb : ∀ (x : EuclideanSpace ℝ (Fin n)) (j : Fin n),
      |Dg k x j| ≤ ‖Dg k x‖ := by
    intro x j
    have hns : ∑ m, (Dg k x m) ^ 2 = ‖Dg k x‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      exact (Finset.sum_congr rfl fun m _ => by rw [Real.norm_eq_abs, sq_abs]).symm
    have h1 : (Dg k x j) ^ 2 ≤ ‖Dg k x‖ ^ 2 := by
      rw [← hns]
      exact Finset.single_le_sum (f := fun m => (Dg k x m) ^ 2)
        (fun m _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg _)] at h2
  have hpull2 : ∀ (c : ℝ) (f : Fin n → Fin n → ℝ),
      (∑ i, ∑ j, c * f i j) = c * ∑ i, ∑ j, f i j := by
    intro c f
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  intro T σ v Z hσ hTm hTΩ hv0 hvZ hmemloc
  have hσabs : |σ| = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσsq : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  -- Step 3e: the admissible test pair
  have hsupp2 : Function.support (fun x => ζ x ^ 2) ⊆ Function.support ζ := by
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro h
    exact hx (by rw [h]; ring)
  have hζ2cs : HasCompactSupport (fun x => ζ x ^ 2) :=
    HasCompactSupport.mono hζcs hsupp2
  have htsub2 : tsupport (fun x => ζ x ^ 2) ⊆ tsupport ζ := closure_mono hsupp2
  have hζ2sm : ContDiff ℝ (⊤ : ℕ∞) (fun x => ζ x ^ 2) := hζsm.pow 2
  have hDζ2 : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      fderiv ℝ (fun y => ζ y ^ 2) x (EuclideanSpace.single i (1 : ℝ))
        = 2 * ζ x * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)) := by
    intro x i
    have hd : HasFDerivAt ζ (fderiv ℝ ζ x) x :=
      ((hζsm.differentiable (by simp)).differentiableAt).hasFDerivAt
    have h2 := hd.pow 2
    rw [h2.fderiv]
    simp
  obtain ⟨gφ, hgφdef⟩ : ∃ gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      gφ = fun x => ζ x ^ 2 • Z x
        + v x • (EuclideanSpace.equiv (Fin n) ℝ).symm
            (fun i => fderiv ℝ (fun y => ζ y ^ 2) x
              (EuclideanSpace.single i (1 : ℝ))) := ⟨_, rfl⟩
  have hgφeq : ∀ x i, gφ x i = ζ x ^ 2 * Z x i
      + v x * (2 * ζ x * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) := by
    intro x i
    have hco : ((EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun i => fderiv ℝ (fun y => ζ y ^ 2) x
          (EuclideanSpace.single i (1 : ℝ)))) i
        = fderiv ℝ (fun y => ζ y ^ 2) x
          (EuclideanSpace.single i (1 : ℝ)) := by simp
    rw [hgφdef]
    simp only [WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul, Pi.smul_apply,
      smul_eq_mul]
    rw [hco, hDζ2 x i]
  have hadm : MemW1pOn n 2 Ω (fun x => v x * ζ x ^ 2) gφ := by
    simp only [hgφdef]
    exact (WeakGradientSmoothMul n 2 (by omega) (by norm_num) Ω v Z
      (fun x => ζ x ^ 2) hΩ hζ2sm hζ2cs (htsub2.trans hζΩ)).2 hmemloc
  have hφcs : HasCompactSupport (fun x => v x * ζ x ^ 2) := by
    refine HasCompactSupport.mono hζ2cs ?_
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro h
    exact hx (by rw [h]; ring)
  have hφts : tsupport (fun x => v x * ζ x ^ 2) ⊆ Ω := by
    refine subset_trans (closure_mono ?_) (htsub2.trans hζΩ)
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro h
    exact hx (by rw [h]; ring)
  have hzero : (∫ x in Ω, ∑ i, ∑ j, M x i j * Dg k x j * gφ x i) = 0 := by
    have h0 := DifferentiatedEquationWeak n p ε γ₀ γ₁ hn hp hε hγ₀ hγ Ω A u g Dg
      hΩ hQ hC1 hsol hDg k _ gφ hadm hφcs hφts
    rw [← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (∑ i, ∑ j, M x i j * Dg k x j * gφ x i)
      = ∑ i, ∑ j,
        (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i * Dg k x j * gφ x i
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by rw [hMeq x i j]
  -- the two terms of (11)
  obtain ⟨Q0, hQ0def⟩ : ∃ Q0 : EuclideanSpace ℝ (Fin n) → ℝ,
      Q0 = fun x => ∑ i, ∑ j, M x i j * Dg k x j * Dg k x i := ⟨_, rfl⟩
  have hQ0eq : ∀ x, Q0 x = ∑ i, ∑ j, M x i j * Dg k x j * Dg k x i :=
    fun x => by rw [hQ0def]
  obtain ⟨P1, hP1def⟩ : ∃ P1 : EuclideanSpace ℝ (Fin n) → ℝ,
      P1 = fun x => ζ x ^ 2 * ∑ i, ∑ j, M x i j * Dg k x j * Z x i := ⟨_, rfl⟩
  obtain ⟨P2, hP2def⟩ : ∃ P2 : EuclideanSpace ℝ (Fin n) → ℝ,
      P2 = fun x => (2 * v x * ζ x) * ∑ i, ∑ j, M x i j * Dg k x j
        * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)) := ⟨_, rfl⟩
  have hP1eq : ∀ x, P1 x = ζ x ^ 2 * ∑ i, ∑ j, M x i j * Dg k x j * Z x i :=
    fun x => by rw [hP1def]
  have hP2eq : ∀ x, P2 x = (2 * v x * ζ x) * ∑ i, ∑ j, M x i j * Dg k x j
      * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)) := fun x => by rw [hP2def]
  have hsplitptw : ∀ x, (∑ i, ∑ j, M x i j * Dg k x j * gφ x i) = P1 x + P2 x := by
    intro x
    have hA1 : (∑ i, ∑ j, M x i j * Dg k x j * gφ x i)
        = (∑ i, ∑ j, ζ x ^ 2 * (M x i j * Dg k x j * Z x i))
          + ∑ i, ∑ j, (2 * v x * ζ x) * (M x i j * Dg k x j
            * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hgφeq x i]
      ring
    rw [hA1, hpull2, hpull2, hP1eq x, hP2eq x]
  -- the a.e. description of `Z`
  have hZae : ∀ᵐ x ∂(volume.restrict (tsupport ζ)),
      (∀ i, |Z x i| ≤ ‖Dg k x‖) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hζΩ hvZ] with x hx
    intro i
    by_cases hxT : x ∈ T
    · rw [hx.1 hxT]
      show |σ * Dg k x i| ≤ ‖Dg k x‖
      rw [abs_mul, hσabs, one_mul]
      exact hDgb x i
    · rw [(hx.2 hxT).1]
      show |(0 : ℝ)| ≤ ‖Dg k x‖
      rw [abs_zero]
      exact norm_nonneg _
  -- integrability of every integrand of Steps 6-8
  obtain ⟨hvm, hP1Ω, hP2Ω, hXΩ, hQ0Ω, hYΩ⟩ :=
    WeightedCaccioppoliIntegrandIntegrability n γ₁ Lζ LDζ LW Ω g Dg ζ W v Q0 P1 P2
      Z M k hDg hζΩ hWpos hγ₁p hKcpt hζ0 hDζ0 hextend hQ2b hWm hMm hDgcm hζm hDζm
      haemul haesum hMint hLζ hLDζ hLW0 hLW hsumbd habs2 hDgb hv0 hmemloc hQ0eq
      hP1def hP2def hP1eq hP2eq hZae
  -- (11) splits
  have hsum0 : (∫ x in Ω, P1 x) + ∫ x in Ω, P2 x = 0 := by
    have e1 : (∫ x in Ω, (P1 x + P2 x)) = 0 := by
      rw [← hzero]
      exact integral_congr_ae
        (Filter.Eventually.of_forall fun x => (hsplitptw x).symm)
    rw [← integral_add hP1Ω hP2Ω]
    exact e1
  -- the three quantities
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = ∫ x in T, W x * ‖Dg k x‖ ^ 2 * ζ x ^ 2 := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = ∫ x in Ω, W x * v x ^ 2
    * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Qv, hQvdef⟩ : ∃ Qv : ℝ, Qv = ∫ x in T, ζ x ^ 2 * Q0 x := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    refine integral_nonneg fun x => ?_
    exact mul_nonneg (mul_nonneg (hWpos x).le (sq_nonneg _)) (sq_nonneg _)
  have hY0 : 0 ≤ Y := by
    rw [hYdef]
    refine integral_nonneg fun x => ?_
    exact mul_nonneg (mul_nonneg (hWpos x).le (sq_nonneg _))
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  -- Step 7: the first term, localized to `T`
  have hP1T : (∫ x in Ω, P1 x) = σ * Qv := by
    have e1 : (∫ x in Ω, P1 x)
        = ∫ x in Ω, T.indicator (fun y => σ * (ζ y ^ 2 * Q0 y)) x := by
      refine integral_congr_ae ?_
      filter_upwards [hvZ] with x hx
      by_cases hxT : x ∈ T
      · rw [Set.indicator_of_mem hxT]
        have hZi : ∀ i : Fin n, Z x i = σ * Dg k x i := by
          intro i
          rw [hx.1 hxT]
          show (σ • Dg k x) i = σ * Dg k x i
          simp
        have e2 : (∑ i, ∑ j, M x i j * Dg k x j * Z x i)
            = σ * ∑ i, ∑ j, M x i j * Dg k x j * Dg k x i := by
          rw [← hpull2 σ (fun i j => M x i j * Dg k x j * Dg k x i)]
          exact Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => by rw [hZi i]; ring
        rw [hP1eq x, e2, hQ0eq x]
        ring
      · rw [Set.indicator_of_notMem hxT, hP1eq x, (hx.2 hxT).1]
        simp
    rw [e1, setIntegral_indicator hTm, Set.inter_eq_self_of_subset_right hTΩ,
      integral_const_mul, ← hQvdef]
  -- the lower bound of Step 7
  have hQvlow : γ₀ * X ≤ Qv := by
    rw [hXdef, hQvdef, ← integral_const_mul]
    refine integral_mono_ae ((hXΩ.mono_set hTΩ).const_mul γ₀) (hQ0Ω.mono_set hTΩ) ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hTΩ hQ1b] with x hx
    show γ₀ * (W x * ‖Dg k x‖ ^ 2 * ζ x ^ 2) ≤ ζ x ^ 2 * Q0 x
    have h1 := hx (Dg k x)
    rw [← hQ0eq x] at h1
    calc γ₀ * (W x * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
        = (γ₀ * W x * ‖Dg k x‖ ^ 2) * ζ x ^ 2 := by ring
      _ ≤ Q0 x * ζ x ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = ζ x ^ 2 * Q0 x := by ring
  -- Step 8: the second term, localized to `T`
  have hP2T : (∫ x in Ω, P2 x) = ∫ x in T, P2 x := by
    have e1 : (∫ x in Ω, P2 x) = ∫ x in Ω, T.indicator P2 x := by
      refine integral_congr_ae ?_
      filter_upwards [hvZ] with x hx
      by_cases hxT : x ∈ T
      · rw [Set.indicator_of_mem hxT]
      · rw [Set.indicator_of_notMem hxT, hP2eq x, (hx.2 hxT).2]
        ring
    rw [e1, setIntegral_indicator hTm, Set.inter_eq_self_of_subset_right hTΩ]
  -- Step 8: the sharp bilinear bound and Cauchy-Schwarz
  have hcsn : ∀ f : Fin n → ℝ, ∑ j, |f j| ≤ Real.sqrt ((n : ℝ) * ∑ j, (f j) ^ 2) := by
    intro f
    have h1 : (∑ j, |f j|) ^ 2 ≤ (n : ℝ) * ∑ j, (f j) ^ 2 := by
      have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1 : ℝ))
        (fun j => |f j|)
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, sq_abs] at h2
      exact h2
    have h3 : (0 : ℝ) ≤ ∑ j, |f j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have h4 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq h3] at h4
  have hDgns : ∀ x : EuclideanSpace ℝ (Fin n),
      ∑ m, (Dg k x m) ^ 2 = ‖Dg k x‖ ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact (Finset.sum_congr rfl fun m _ => by rw [Real.norm_eq_abs, sq_abs]).symm
  obtain ⟨F, hFdef⟩ : ∃ F : EuclideanSpace ℝ (Fin n) → ℝ,
    F = fun x => Real.sqrt (W x) * |ζ x| * ‖Dg k x‖ := ⟨_, rfl⟩
  obtain ⟨G2, hG2def⟩ : ∃ G2 : EuclideanSpace ℝ (Fin n) → ℝ,
    G2 = fun x => Real.sqrt (W x) * v x
      * Real.sqrt (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) := ⟨_, rfl⟩
  have hFeq : ∀ x, F x = Real.sqrt (W x) * |ζ x| * ‖Dg k x‖ := fun x => by rw [hFdef]
  have hG2eq : ∀ x, G2 x = Real.sqrt (W x) * v x
      * Real.sqrt (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) :=
    fun x => by rw [hG2def]
  have hB0 : ∀ x : EuclideanSpace ℝ (Fin n), (0 : ℝ)
      ≤ ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 :=
    fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hF0 : ∀ x, 0 ≤ F x := fun x => by
    rw [hFeq x]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) (norm_nonneg _)
  have hG20 : ∀ x, 0 ≤ G2 x := fun x => by
    rw [hG2eq x]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hv0 x)) (Real.sqrt_nonneg _)
  have hFsq : ∀ x, F x ^ 2 = W x * ‖Dg k x‖ ^ 2 * ζ x ^ 2 := by
    intro x
    rw [hFeq x, mul_pow, mul_pow, Real.sq_sqrt (hWpos x).le, sq_abs]
    ring
  have hG2sq : ∀ x, G2 x ^ 2 = W x * v x ^ 2
      * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 := by
    intro x
    rw [hG2eq x, mul_pow, mul_pow, Real.sq_sqrt (hWpos x).le, Real.sq_sqrt (hB0 x)]
  have hFvan : ∀ x, x ∉ tsupport ζ → F x = 0 := fun x hx => by
    rw [hFeq x, hζ0 x hx]; simp
  have hG2van : ∀ x, x ∉ tsupport ζ → G2 x = 0 := by
    intro x hx
    have hz : ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hDζ0 x hx i]; ring
    rw [hG2eq x, hz]
    simp
  have hindext : ∀ F' : EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ x, x ∉ tsupport ζ → F' x = 0) →
      AEStronglyMeasurable F' (volume.restrict (tsupport ζ)) →
      AEStronglyMeasurable F' volume := by
    intro F' hvan hm
    have h1 : AEStronglyMeasurable (Set.indicator (tsupport ζ) F') volume :=
      (aestronglyMeasurable_indicator_iff hKmeas).2 hm
    have h2 : Set.indicator (tsupport ζ) F' = F' := by
      funext x
      by_cases hx : x ∈ tsupport ζ
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, hvan x hx]
    rwa [h2] at h1
  have hsqWm : AEMeasurable (fun x => Real.sqrt (W x))
      (volume.restrict (tsupport ζ)) :=
    Real.continuous_sqrt.measurable.comp_aemeasurable hWm
  have hFm : AEStronglyMeasurable F volume := by
    refine hindext F hFvan ?_
    rw [hFdef]
    refine AEMeasurable.aestronglyMeasurable ?_
    exact haemul _ _ (haemul _ _ hsqWm
      (continuous_abs.measurable.comp_aemeasurable hζm))
      ((((hDg k).2 (tsupport ζ) hKcpt hζΩ).2.1.aemeasurable).norm)
  have hG2m : AEStronglyMeasurable G2 volume := by
    refine hindext G2 hG2van ?_
    rw [hG2def]
    refine AEMeasurable.aestronglyMeasurable ?_
    exact haemul _ _ (haemul _ _ hsqWm hvm)
      (Real.continuous_sqrt.measurable.comp_aemeasurable
        (haesum _ fun i => (hDζm i).pow_const 2))
  have hrp2 : ∀ a : ℝ, a ^ (2 : ℝ) = a ^ 2 := by
    intro a
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have hFmem : MemLp F (ENNReal.ofReal 2) (volume.restrict T) := by
    refine (integrable_norm_rpow_iff hFm.restrict (by simp) (by simp)).1 ?_
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp]
    refine (hXΩ.mono_set hTΩ).congr (Filter.Eventually.of_forall fun x => ?_)
    show W x * ‖Dg k x‖ ^ 2 * ζ x ^ 2 = ‖F x‖ ^ (2 : ℝ)
    rw [Real.norm_eq_abs, hrp2, sq_abs, hFsq x]
  have hG2mem : MemLp G2 (ENNReal.ofReal 2) (volume.restrict T) := by
    refine (integrable_norm_rpow_iff hG2m.restrict (by simp) (by simp)).1 ?_
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp]
    refine (hYΩ.mono_set hTΩ).congr (Filter.Eventually.of_forall fun x => ?_)
    show W x * v x ^ 2 * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2
      = ‖G2 x‖ ^ (2 : ℝ)
    rw [Real.norm_eq_abs, hrp2, sq_abs, hG2sq x]
  have hFGint : IntegrableOn (fun x => F x * G2 x) T volume := by
    have hXT := hXΩ.mono_set hTΩ
    have hYT := hYΩ.mono_set hTΩ
    refine Integrable.mono' ((hXT.add hYT).const_mul (1 / 2))
      ((hFm.mul hG2m).restrict) ?_
    filter_upwards with x
    show ‖F x * G2 x‖ ≤ 1 / 2 * (W x * ‖Dg k x‖ ^ 2 * ζ x ^ 2
      + W x * v x ^ 2 * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hF0 x) (hG20 x))]
    have h2 := habs2 (F x) (G2 x)
    rw [abs_of_nonneg (hF0 x), abs_of_nonneg (hG20 x), hFsq x, hG2sq x] at h2
    linarith [h2]
  -- the pointwise bound of Step 8
  have hP2b : ∀ᵐ x ∂(volume.restrict T),
      |P2 x| ≤ 2 * (n : ℝ) * γ₁ * (F x * G2 x) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hTΩ hQ2b] with x hQ2x
    have hW0 : (0 : ℝ) ≤ W x := (hWpos x).le
    have hq0 : (0 : ℝ) ≤ γ₁ * W x := mul_nonneg hγ₁p.le hW0
    have hA1 : ∑ j, |Dg k x j| ≤ Real.sqrt (n : ℝ) * ‖Dg k x‖ := by
      have h := hcsn (fun j => Dg k x j)
      rw [hDgns x, Real.sqrt_mul hnR0.le, Real.sqrt_sq (norm_nonneg _)] at h
      exact h
    have hB1 : ∑ i, |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
        ≤ Real.sqrt (n : ℝ)
          * Real.sqrt (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) := by
      have h := hcsn (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)))
      rw [Real.sqrt_mul hnR0.le] at h
      exact h
    have hstep1 : |∑ i, ∑ j, M x i j * Dg k x j
          * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
        ≤ ∑ i, ∑ j, (γ₁ * W x) * (|Dg k x j|
          * |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_mul]
      calc |M x i j| * |Dg k x j|
            * |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
          ≤ (γ₁ * W x) * |Dg k x j|
            * |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hQ2x i j) (abs_nonneg _)) (abs_nonneg _)
        _ = (γ₁ * W x) * (|Dg k x j|
            * |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|) := by ring
    have hstep2 : (∑ i, ∑ j, (γ₁ * W x) * (|Dg k x j|
          * |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|))
        = (γ₁ * W x) * ((∑ j, |Dg k x j|)
          * ∑ i, |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|) := by
      have e1 : ∀ i : Fin n, (∑ j, (γ₁ * W x) * (|Dg k x j|
            * |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|))
          = ((γ₁ * W x) * |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|)
            * ∑ j, |Dg k x j| := by
        intro i
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.sum_mul, ← Finset.mul_sum]
      ring
    have hin : |∑ i, ∑ j, M x i j * Dg k x j
          * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
        ≤ (n : ℝ) * (γ₁ * W x) * (‖Dg k x‖
          * Real.sqrt (∑ i, (fderiv ℝ ζ x
            (EuclideanSpace.single i (1 : ℝ))) ^ 2)) := by
      rw [hstep2] at hstep1
      refine le_trans hstep1 ?_
      have hprod : (∑ j, |Dg k x j|)
            * ∑ i, |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
          ≤ (Real.sqrt (n : ℝ) * ‖Dg k x‖)
            * (Real.sqrt (n : ℝ) * Real.sqrt (∑ i, (fderiv ℝ ζ x
              (EuclideanSpace.single i (1 : ℝ))) ^ 2)) :=
        mul_le_mul hA1 hB1 (Finset.sum_nonneg fun i _ => abs_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      refine le_trans (mul_le_mul_of_nonneg_left hprod hq0) (le_of_eq ?_)
      rw [show (Real.sqrt (n : ℝ) * ‖Dg k x‖)
            * (Real.sqrt (n : ℝ) * Real.sqrt (∑ i, (fderiv ℝ ζ x
              (EuclideanSpace.single i (1 : ℝ))) ^ 2))
          = (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) * (‖Dg k x‖
            * Real.sqrt (∑ i, (fderiv ℝ ζ x
              (EuclideanSpace.single i (1 : ℝ))) ^ 2)) from by ring,
        Real.mul_self_sqrt hnR0.le]
      ring
    have hpre : |2 * v x * ζ x| ≤ 2 * v x * |ζ x| := by
      have h2v : (0 : ℝ) ≤ 2 * v x := by linarith [hv0 x]
      rw [abs_mul, abs_of_nonneg h2v]
    rw [hP2eq x]
    calc |2 * v x * ζ x * ∑ i, ∑ j, M x i j * Dg k x j
            * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
        = |2 * v x * ζ x| * |∑ i, ∑ j, M x i j * Dg k x j
            * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))| := abs_mul _ _
      _ ≤ (2 * v x * |ζ x|) * ((n : ℝ) * (γ₁ * W x) * (‖Dg k x‖
            * Real.sqrt (∑ i, (fderiv ℝ ζ x
              (EuclideanSpace.single i (1 : ℝ))) ^ 2))) :=
          mul_le_mul hpre hin (abs_nonneg _)
            (mul_nonneg (by linarith [hv0 x]) (abs_nonneg _))
      _ = 2 * (n : ℝ) * γ₁ * ((Real.sqrt (W x) * Real.sqrt (W x))
            * (|ζ x| * ‖Dg k x‖) * (v x
            * Real.sqrt (∑ i, (fderiv ℝ ζ x
              (EuclideanSpace.single i (1 : ℝ))) ^ 2))) := by
          rw [Real.mul_self_sqrt hW0]
          ring
      _ = 2 * (n : ℝ) * γ₁ * (F x * G2 x) := by
          rw [hFeq x, hG2eq x]
          ring
  have hconj : Real.HolderConjugate (2 : ℝ) (2 : ℝ) :=
    Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have hhol := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict T) hconj
    (f := F) (g := G2) (Filter.Eventually.of_forall hF0)
    (Filter.Eventually.of_forall hG20) hFmem hG2mem
  have hFX : (∫ x in T, F x ^ (2 : ℝ)) = X := by
    rw [hXdef]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show F x ^ (2 : ℝ) = W x * ‖Dg k x‖ ^ 2 * ζ x ^ 2
    rw [hrp2, hFsq x]
  have hGY : (∫ x in T, G2 x ^ (2 : ℝ)) ≤ Y := by
    have e1 : (∫ x in T, G2 x ^ (2 : ℝ))
        = ∫ x in T, W x * v x ^ 2
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show G2 x ^ (2 : ℝ) = W x * v x ^ 2
        * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2
      rw [hrp2, hG2sq x]
    rw [e1, hYdef]
    refine setIntegral_mono_set hYΩ ?_ (Filter.Eventually.of_forall fun x hx => hTΩ hx)
    exact Filter.Eventually.of_forall fun x =>
      mul_nonneg (mul_nonneg (hWpos x).le (sq_nonneg _))
        (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [hFX, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hhol
  have hcoef0 : (0 : ℝ) ≤ 2 * (n : ℝ) * γ₁ :=
    mul_nonneg (mul_nonneg (by norm_num) hnR0.le) hγ₁p.le
  have hP2bd : |∫ x in T, P2 x|
      ≤ 2 * (n : ℝ) * γ₁ * (Real.sqrt X * Real.sqrt Y) := by
    calc |∫ x in T, P2 x| ≤ ∫ x in T, |P2 x| := abs_integral_le_integral_abs
      _ ≤ ∫ x in T, 2 * (n : ℝ) * γ₁ * (F x * G2 x) :=
          integral_mono_ae (hP2Ω.mono_set hTΩ).abs (hFGint.const_mul _) hP2b
      _ = 2 * (n : ℝ) * γ₁ * ∫ x in T, F x * G2 x := integral_const_mul _ _
      _ ≤ 2 * (n : ℝ) * γ₁ * (Real.sqrt X * Real.sqrt Y) := by
          refine mul_le_mul_of_nonneg_left (le_trans hhol ?_) hcoef0
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hGY) (Real.sqrt_nonneg _)
  have hQvabs : |Qv| ≤ 2 * (n : ℝ) * γ₁ * (Real.sqrt X * Real.sqrt Y) := by
    have e1 : σ * Qv = -(∫ x in T, P2 x) := by
      rw [← hP1T, ← hP2T]
      linarith [hsum0]
    have e2 : |σ * Qv| = |Qv| := by rw [abs_mul, hσabs, one_mul]
    rw [← e2, e1, abs_neg]
    exact hP2bd
  have hlow : γ₀ * X ≤ 2 * (n : ℝ) * γ₁ * (Real.sqrt X * Real.sqrt Y) :=
    le_trans (le_trans hQvlow (le_abs_self _)) hQvabs
  rw [← hXdef, ← hYdef]
  rcases eq_or_lt_of_le hX0 with hXe | hXp
  · rw [← hXe]
    exact mul_nonneg (by positivity) hY0
  · have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hXp
    have hXX : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0
    have hYY : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY0
    have hstep : γ₀ * Real.sqrt X ≤ 2 * (n : ℝ) * γ₁ * Real.sqrt Y := by
      refine le_of_mul_le_mul_right ?_ hsX
      calc γ₀ * Real.sqrt X * Real.sqrt X = γ₀ * X := by rw [mul_assoc, hXX]
        _ ≤ 2 * (n : ℝ) * γ₁ * (Real.sqrt X * Real.sqrt Y) := hlow
        _ = 2 * (n : ℝ) * γ₁ * Real.sqrt Y * Real.sqrt X := by ring
    have hstep2 : Real.sqrt X ≤ 2 * (n : ℝ) * r * Real.sqrt Y := by
      refine le_of_mul_le_mul_left ?_ hγ₀
      calc γ₀ * Real.sqrt X ≤ 2 * (n : ℝ) * γ₁ * Real.sqrt Y := hstep
        _ ≤ 2 * (n : ℝ) * (r * γ₀) * Real.sqrt Y := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
            exact mul_le_mul_of_nonneg_left hγ₁r (by positivity)
        _ = γ₀ * (2 * (n : ℝ) * r * Real.sqrt Y) := by ring
    have hrhs0 : (0 : ℝ) ≤ 2 * (n : ℝ) * r * Real.sqrt Y := by positivity
    calc X = Real.sqrt X * Real.sqrt X := hXX.symm
      _ ≤ (2 * (n : ℝ) * r * Real.sqrt Y) * (2 * (n : ℝ) * r * Real.sqrt Y) :=
          mul_le_mul hstep2 hstep2 (Real.sqrt_nonneg _) hrhs0
      _ = 4 * (n : ℝ) ^ 2 * r ^ 2 * (Real.sqrt Y * Real.sqrt Y) := by ring
      _ = 4 * (n : ℝ) ^ 2 * r ^ 2 * Y := by rw [hYY]
