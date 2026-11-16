import ManfrediThesis.Preamble
import ManfrediThesis.PowerWeightIntegrandMeasurability
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.PowerWeightWeakFormIdentity
set_option maxHeartbeats 400000
open MeasureTheory

/-- The two-sided estimate at the heart of inequality (3.3): the weighted
Dirichlet energy `I` of the power weight is controlled by the geometric mean of
itself and the cut-off energy `J`,
`γ₀((1+t)/4) I ≤ γ₁ n √I √J`.

Conventions, restated here because a helper inherits none of its parent's.
`w = ε + ‖g‖²` is the weight, `g` plays the role of `∇u` and `Dg k` of
`∇D_ku`, and `Dw` is the weak gradient of `w`,
`Dw(x)_i = 2 Σ_k g^k(x) (Dg^k)_i(x)`.  Every power of `w` is `Real.rpow`,
written exactly as the structure conditions (Q1)/(Q2) print the weight
`(ε + |h|²)^{p/2-1}`, and is never rewritten as a natural power.  `ζ` is the
cut-off; `supp ζ` means its CLOSED support, i.e. Mathlib's `tsupport ζ`.  The
two integrals are
`I = ∫_Ω w^{(p+t)/2-2} |Dw|² ζ²` and `J = ∫_Ω w^{(p+t)/2} |∇ζ|²`,
and `a_{ij}(x) = (dA(g(x))e_j)_i` is the coefficient field of the
differentiated equation (3.2), paired throughout with `(Dg^k)_j = D_jD_ku`
exactly as `DifferentiatedEquationWeak` states it; *that index placement is
load-bearing, not cosmetic*.

The route is Steps 2--7 of the parent's argument.  Step 2 fixes the continuous
representative of `g` on `Ω` supplied by the cited regularity for `ε > 0`,
records the local bounds for the powers `w^σ` on compact subsets of `Ω`, and
establishes that the two integrands of `I` and `J` are integrable on `Ω` ---
each vanishes off `supp ζ`, which is compact and contained in `Ω`.  Steps 3--5
are the weak-form transport of the differentiated equation to the power weight
and are cited wholesale from `PowerWeightWeakFormIdentity`: they give the
identity `T₁ + T₂ = -T₃` of (5) together with the integrability of the three
integrands, where
`T₁ = ∫_Ω ζ²w^{t/2}Σ_{k,i,j}a_{ij}(Dg^k)_j(Dg^k)_i`,
`T₂ = (t/4)∫_Ω ζ²w^{t/2-1}Σ_{i,j}a_{ij}(Dw)_j(Dw)_i` and
`T₃ = ∫_Ω ζw^{t/2}Σ_{i,j}a_{ij}(Dw)_jD_iζ`.
Step 6 bounds `T₁` and `T₂` from below by the ellipticity (Q1): pointwise
`γ₀w^{p/2-1}|ξ|² ≤ Σ_{i,j}a_{ij}ξ_jξ_i` at `ξ = Dg^k` and at `ξ = Dw`, and the
two exponent identities `w^{t/2}w^{p/2-1} = w·w^{(p+t)/2-2}` and
`w^{t/2-1}w^{p/2-1} = w^{(p+t)/2-2}` turn those into `γ₀/4·I ≤ T₁` and
`γ₀(t/4)I ≤ T₂`, using `|Dw|² ≤ 4w Σ_k|Dg^k|²` for the first.  Step 7 bounds
`|T₃|` from above by (Q2) and Cauchy--Schwarz on `supp ζ`: the operator bound
`|a_{ij}| ≤ γ₁w^{p/2-1}` gives
`|T₃| ≤ γ₁ n ∫_{supp ζ} (w^{(p+t)/4-1}|Dw|ζ)(w^{(p+t)/4}|∇ζ|)`, and Hölder with
exponent `2` in both factors bounds that by `γ₁ n √I √J`.  Adding the three
estimates to the identity, through `-T₃ ≤ |T₃|`, is the conclusion. -/
theorem PowerWeightCaccioppoliCore :
    ∀ (n : ℕ) (p : ℝ), 2 ≤ n → 1 < p →
      ∀ (ε γ₀ γ₁ t : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (ζ : EuclideanSpace ℝ (Fin n) → ℝ),
        0 < ε → 0 < γ₀ → γ₀ ≤ γ₁ → 0 < t → IsOpen Ω → Ω.Nonempty →
        EllipticStructureQ12 n p ε γ₀ γ₁ Ω (fun _ _ h => A h) →
        CitedRegularityEpsPos n p ε γ₀ γ₁ Ω A →
        IsWeakSolutionOn n p Ω (fun _ _ h => A h) (fun _ _ _ => 0) u g →
        (∀ i : Fin n, MemW1pLocOn n 2 Ω (fun x => g x i) (Dg i)) →
        ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
      ∀ (w : EuclideanSpace ℝ (Fin n) → ℝ),
        (∀ x, w x = ε + ‖g x‖ ^ 2) → (∀ x, 0 < w x) →
      ∀ (Dw : EuclideanSpace ℝ (Fin n) → Fin n → ℝ),
        (∀ x i, Dw x i = 2 * ∑ k, g x k * Dg k x i) →
      ∀ I : ℝ, I = (∫ x in Ω,
          w x ^ ((p + t) / 2 - 2) * (∑ i, (Dw x i) ^ 2) * ζ x ^ 2) →
      ∀ J : ℝ, J = (∫ x in Ω, w x ^ ((p + t) / 2)
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) →
        γ₀ * ((1 + t) / 4) * I ≤ γ₁ * (n : ℝ) * (Real.sqrt I * Real.sqrt J) := by
  intro n p hn hp ε γ₀ γ₁ t Ω A u g Dg ζ hε hγ₀ hγ ht hΩ hΩne hQ hC1 hsol hDg
    hζsm hζcs hζΩ w hweq hwpos Dw hDweq I hIdef J hJdef
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  -- the coefficient field `a_{ij}` of (3.2)
  obtain ⟨aij, haijdef⟩ : ∃ aij : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ,
      aij = fun x i j =>
        (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i := ⟨_, rfl⟩
  have haijeq : ∀ x i j, aij x i j
      = (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i :=
    fun x i j => by rw [haijdef]
  -- the three integrals of (5)
  obtain ⟨T1, hT1def⟩ : ∃ T1 : ℝ, T1 = ∫ x in Ω,
      ζ x ^ 2 * w x ^ (t / 2)
        * ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i := ⟨_, rfl⟩
  obtain ⟨T2, hT2def⟩ : ∃ T2 : ℝ, T2 = (t / 4) * ∫ x in Ω,
      ζ x ^ 2 * w x ^ (t / 2 - 1)
        * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i := ⟨_, rfl⟩
  obtain ⟨T3, hT3def⟩ : ∃ T3 : ℝ, T3 = ∫ x in Ω,
      ζ x * w x ^ (t / 2)
        * ∑ i, ∑ j, aij x i j * Dw x j
          * (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) := ⟨_, rfl⟩
  -- Step 2: the continuous representative supplied by (C1)
  obtain ⟨-, g', hg'cont, hg'ae, -⟩ := hC1 hε hQ u g hsol
  obtain ⟨w', hw'def⟩ : ∃ w' : EuclideanSpace ℝ (Fin n) → ℝ,
      w' = fun x => ε + ‖g' x‖ ^ 2 := ⟨_, rfl⟩
  have hw'eq : ∀ x, w' x = ε + ‖g' x‖ ^ 2 := fun x => by rw [hw'def]
  have hw'pos : ∀ x, 0 < w' x := by
    intro x
    rw [hw'eq x]
    have := sq_nonneg ‖g' x‖
    linarith
  have hw'cont : ContinuousOn w' Ω := by
    rw [hw'def]
    exact continuousOn_const.add (hg'cont.norm.pow 2)
  have hwae : ∀ᵐ x ∂(volume.restrict Ω), w x = w' x := by
    filter_upwards [hg'ae] with x hx
    rw [hweq x, hw'eq x, hx]
  -- every real power of `w'` is bounded on a compact subset of `Ω`
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
  -- (2): the Cauchy-Schwarz bound in the index `k`
  have hCS2 : ∀ x, (∑ i, (Dw x i) ^ 2) ≤ 4 * w x * ∑ k, ‖Dg k x‖ ^ 2 := by
    intro x
    have hgsq : ∑ k, (g x k) ^ 2 = ‖g x‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      exact (Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])).symm
    have hMsq : ∀ k, ∑ i, (Dg k x i) ^ 2 = ‖Dg k x‖ ^ 2 := by
      intro k
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      exact (Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])).symm
    have hptw : ∀ i : Fin n, (Dw x i) ^ 2
        ≤ 4 * ‖g x‖ ^ 2 * ∑ k, (Dg k x i) ^ 2 := by
      intro i
      rw [hDweq x i, mul_pow]
      have hcs2 : (∑ k, g x k * Dg k x i) ^ 2
          ≤ (∑ k, (g x k) ^ 2) * ∑ k, (Dg k x i) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => g x k) (fun k => Dg k x i)
      rw [hgsq] at hcs2
      nlinarith [hcs2]
    calc (∑ i, (Dw x i) ^ 2)
        ≤ ∑ i, 4 * ‖g x‖ ^ 2 * ∑ k, (Dg k x i) ^ 2 :=
          Finset.sum_le_sum fun i _ => hptw i
      _ = 4 * ‖g x‖ ^ 2 * ∑ k, ‖Dg k x‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          exact Finset.sum_congr rfl fun k _ => hMsq k
      _ ≤ 4 * w x * ∑ k, ‖Dg k x‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun k _ => sq_nonneg _)
          have : ‖g x‖ ^ 2 ≤ w x := by rw [hweq x]; linarith
          linarith
  -- the support of the cut-off, and extension of integrability from it to `Ω`
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
    refine IntegrableOn.congr_fun integrableOn_zero (fun x hx => (hF0 x hx.2).symm)
      (hΩ.measurableSet.diff hKmeas)
  -- `∑_k ‖Dg^k‖²` is integrable on the support
  have hMint : IntegrableOn (fun x => ∑ k, ‖Dg k x‖ ^ 2) (tsupport ζ) volume := by
    refine integrable_finsetSum _ fun k _ => ?_
    have hmem := ((hDg k).2 (tsupport ζ) hKcpt hζΩ).2
    have h1 : Integrable (fun x => ‖Dg k x‖ ^ (ENNReal.ofReal 2).toReal)
        (volume.restrict (tsupport ζ)) :=
      hmem.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp] at h1
    refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
    show ‖Dg k x‖ ^ (2 : ℝ) = ‖Dg k x‖ ^ 2
    rw [← Real.rpow_natCast ‖Dg k x‖ 2]
    norm_num
  -- `ζ` and `∇ζ` are bounded
  obtain ⟨Lζ, hLζ0, hLζ⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ x, ζ x ^ 2 ≤ L := by
    obtain ⟨L, hL⟩ := hζcs.exists_bound_of_continuousOn hζsm.continuous.continuousOn
    refine ⟨max L 0 ^ 2, by positivity, fun x => ?_⟩
    by_cases hx : x ∈ tsupport ζ
    · have h1 : |ζ x| ≤ max L 0 := le_trans (by simpa using hL x hx) (le_max_left _ _)
      calc ζ x ^ 2 = |ζ x| ^ 2 := (sq_abs _).symm
        _ ≤ max L 0 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    · rw [hζ0 x hx]
      have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h0]
      positivity
  -- the two integrands of `I` and `J`
  obtain ⟨Lw2, hLw20, hLw2⟩ := hwpowbd ((p + t) / 2 - 2) (tsupport ζ) hζcs hζΩ
  obtain ⟨Lw1, hLw10, hLw1⟩ := hwpowbd 1 (tsupport ζ) hζcs hζΩ
  obtain ⟨LwJ, hLwJ0, hLwJ⟩ := hwpowbd ((p + t) / 2) (tsupport ζ) hζcs hζΩ
  have hwrpow1 : ∀ x, w' x ^ (1 : ℝ) = w' x := fun x => Real.rpow_one _
  -- a bound for `|∇ζ|²`
  obtain ⟨LDζ, hLDζ0, hLDζ⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ x,
      ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 ≤ L := by
    have hcont : Continuous (fun x => ∑ i, (fderiv ℝ ζ x
        (EuclideanSpace.single i (1 : ℝ))) ^ 2) := by
      refine continuous_finsetSum _ fun i _ => ?_
      exact ((hζsm.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2
    obtain ⟨L, hL⟩ := hζcs.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max L 0, le_max_right _ _, fun x => ?_⟩
    by_cases hx : x ∈ tsupport ζ
    · exact le_trans (le_trans (le_abs_self _) (by simpa using hL x hx)) (le_max_left _ _)
    · have hz : ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hDζ0 x hx i]; ring
      rw [hz]
      exact le_max_right _ _
  -- measurability on the support
  obtain ⟨hgK, hwm, hrpowm, hgcm, hDgcm, hDwm, hIint, hJint, haesum, hζm, hDζm,
    haemul⟩ :=
    PowerWeightIntegrandMeasurability n p ε t Lζ Lw2 Lw1 LwJ LDζ Ω A u g Dg ζ w w'
      Dw hsol hDg hζsm hζΩ hweq hwpos hDweq hwae hCS2 hKcpt hKmeas hζ0 hDζ0 hextend
      hMint hLζ hLw20 hLw2 hLw10 hLw1 hLwJ0 hLwJ hwrpow1 hLDζ
  have hγ₁p : (0 : ℝ) < γ₁ := lt_of_lt_of_le hγ₀ hγ
  have habs2 : ∀ a b : ℝ, |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    intro a b
    have h1 : (0 : ℝ) ≤ (|a| - |b|) ^ 2 := sq_nonneg _
    have h2 : (|a| - |b|) ^ 2 = a ^ 2 - 2 * (|a| * |b|) + b ^ 2 := by
      rw [sub_sq, sq_abs, sq_abs]; ring
    linarith [h1, h2]
  -- Steps 3-5: the weak-form transport of the differentiated equation to the
  -- power weight, and the identity (5) `T1 + T2 = -T3`.  This is
  -- `PowerWeightWeakFormIdentity`, whose docstring records the route (the
  -- VECTOR-argument chain rule for `w^{t/2}` via `WeakGradientVectorComp`,
  -- the admissible test pair `φ_k = g^k w^{t/2} ζ²` via
  -- `WeakGradientSmoothMul`, `DifferentiatedEquationWeak` at each `φ_k`, and
  -- the integrable split of the sum).  It also returns the integrability
  -- facts the Cauchy-Schwarz tail below consumes.
  obtain ⟨hid5, hT1Ω, hT2Ω, hT3Ω, hT3int⟩ :=
    PowerWeightWeakFormIdentity n p hn hp ε γ₀ γ₁ t Ω A u g Dg ζ hε hγ₀ hγ hΩ
      hΩne hQ hC1 hsol hDg hζsm hζcs hζΩ w hweq hwpos Dw hDweq aij haijeq
      T1 T2 T3 hT1def hT2def hT3def g' hg'cont hg'ae w' hwae hwpowbd hwrpow1
      hCS2 hKcpt hKmeas hζ0 hDζ0 hextend hMint Lζ hLζ0 hLζ Lw1 hLw1 LDζ hLDζ
      hgK hrpowm hgcm hDgcm hDwm
  -- Step 6: the lower bounds from (Q1)
  have hdecomp : ∀ ξ : EuclideanSpace ℝ (Fin n),
      ξ = ∑ j, ξ j • EuclideanSpace.single j (1 : ℝ) := by
    intro ξ
    refine PiLp.ext fun i => ?_
    simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq]
  have hlin : ∀ (x ξ : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      (fderiv ℝ A (g x) ξ) i = ∑ j, aij x i j * ξ j := by
    intro x ξ i
    conv_lhs => rw [hdecomp ξ]
    rw [map_sum]
    simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
      Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [haijeq x i j]; ring
  have hQ1pt : ∀ᵐ x ∂(volume.restrict Ω), ∀ ξ : EuclideanSpace ℝ (Fin n),
      γ₀ * w x ^ (p / 2 - 1) * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, aij x i j * ξ j * ξ i := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet, ae_restrict_of_ae hQ.Q1]
      with x hxΩ hxQ1
    intro ξ
    have hwne : ε + ‖g x‖ ^ 2 ≠ 0 := by
      have h1 : (0 : ℝ) ≤ ‖g x‖ ^ 2 := sq_nonneg _
      exact ne_of_gt (by linarith)
    have h1 := hxQ1 hxΩ 0 (g x) ξ hwne
    rw [show ε + ‖g x‖ ^ 2 = w x from (hweq x).symm] at h1
    refine le_trans h1 (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => by rw [hlin x ξ i, Finset.sum_mul]
  have hexpid1 : ∀ x : EuclideanSpace ℝ (Fin n),
      w x ^ (t / 2) * w x ^ (p / 2 - 1) = w x * w x ^ ((p + t) / 2 - 2) := by
    intro x
    have h1 : w x ^ (1 + ((p + t) / 2 - 2)) = w x * w x ^ ((p + t) / 2 - 2) := by
      rw [Real.rpow_add (hwpos x), Real.rpow_one]
    rw [← Real.rpow_add (hwpos x), ← h1]
    congr 1
    ring
  have hexpid2 : ∀ x : EuclideanSpace ℝ (Fin n),
      w x ^ (t / 2 - 1) * w x ^ (p / 2 - 1) = w x ^ ((p + t) / 2 - 2) := by
    intro x
    rw [← Real.rpow_add (hwpos x)]
    congr 1
    ring
  have hlow1 : γ₀ / 4 * I ≤ T1 := by
    rw [hIdef, hT1def, ← integral_const_mul]
    refine integral_mono_ae (hIint.const_mul (γ₀ / 4)) hT1Ω ?_
    filter_upwards [hQ1pt] with x hx1
    show γ₀ / 4 * (w x ^ ((p + t) / 2 - 2) * (∑ i, (Dw x i) ^ 2) * ζ x ^ 2)
      ≤ ζ x ^ 2 * w x ^ (t / 2)
        * ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i
    have hco : (0 : ℝ) ≤ γ₀ / 4 * w x ^ ((p + t) / 2 - 2) * ζ x ^ 2 :=
      mul_nonneg (mul_nonneg (by linarith)
        (le_of_lt (Real.rpow_pos_of_pos (hwpos x) _))) (sq_nonneg _)
    have hz0 : (0 : ℝ) ≤ ζ x ^ 2 * w x ^ (t / 2) :=
      mul_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos (hwpos x) _))
    have hTR : γ₀ * w x ^ (p / 2 - 1) * (∑ k, ‖Dg k x‖ ^ 2)
        ≤ ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => hx1 (Dg k x)
    calc γ₀ / 4 * (w x ^ ((p + t) / 2 - 2) * (∑ i, (Dw x i) ^ 2) * ζ x ^ 2)
        = (γ₀ / 4 * w x ^ ((p + t) / 2 - 2) * ζ x ^ 2) * (∑ i, (Dw x i) ^ 2) := by
          ring
      _ ≤ (γ₀ / 4 * w x ^ ((p + t) / 2 - 2) * ζ x ^ 2)
          * (4 * w x * ∑ k, ‖Dg k x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hCS2 x) hco
      _ = ζ x ^ 2 * w x ^ (t / 2) * (γ₀ * w x ^ (p / 2 - 1) * ∑ k, ‖Dg k x‖ ^ 2) := by
          rw [show ζ x ^ 2 * w x ^ (t / 2)
                * (γ₀ * w x ^ (p / 2 - 1) * ∑ k, ‖Dg k x‖ ^ 2)
              = γ₀ * ζ x ^ 2 * (w x ^ (t / 2) * w x ^ (p / 2 - 1))
                * ∑ k, ‖Dg k x‖ ^ 2 from by ring, hexpid1 x]
          ring
      _ ≤ ζ x ^ 2 * w x ^ (t / 2)
          * ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i :=
          mul_le_mul_of_nonneg_left hTR hz0
  have hDwnorm : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖((EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => Dw x i) :
          EuclideanSpace ℝ (Fin n))‖ ^ 2 = ∑ i, (Dw x i) ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl fun i _ => by
      rw [show ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun m => Dw x m) :
          EuclideanSpace ℝ (Fin n)) i = Dw x i from by simp,
        Real.norm_eq_abs, sq_abs]
  have hlow2 : γ₀ * t / 4 * I ≤ T2 := by
    rw [hT2def]
    have hmain : γ₀ * I ≤ ∫ x in Ω, ζ x ^ 2 * w x ^ (t / 2 - 1)
        * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i := by
      rw [hIdef, ← integral_const_mul]
      refine integral_mono_ae (hIint.const_mul γ₀) hT2Ω ?_
      filter_upwards [hQ1pt] with x hx1
      show γ₀ * (w x ^ ((p + t) / 2 - 2) * (∑ i, (Dw x i) ^ 2) * ζ x ^ 2)
        ≤ ζ x ^ 2 * w x ^ (t / 2 - 1)
          * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i
      have hz0 : (0 : ℝ) ≤ ζ x ^ 2 * w x ^ (t / 2 - 1) :=
        mul_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos (hwpos x) _))
      have hTR := hx1 ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => Dw x i))
      rw [hDwnorm x] at hTR
      have hTR2 : γ₀ * w x ^ (p / 2 - 1) * (∑ i, (Dw x i) ^ 2)
          ≤ ∑ i, ∑ j, aij x i j * Dw x j * Dw x i := by
        refine le_trans hTR (le_of_eq ?_)
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [show ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun m => Dw x m) :
            EuclideanSpace ℝ (Fin n)) j = Dw x j from by simp,
          show ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun m => Dw x m) :
            EuclideanSpace ℝ (Fin n)) i = Dw x i from by simp]
      calc γ₀ * (w x ^ ((p + t) / 2 - 2) * (∑ i, (Dw x i) ^ 2) * ζ x ^ 2)
          = ζ x ^ 2 * w x ^ (t / 2 - 1)
            * (γ₀ * w x ^ (p / 2 - 1) * (∑ i, (Dw x i) ^ 2)) := by
            rw [show ζ x ^ 2 * w x ^ (t / 2 - 1)
                  * (γ₀ * w x ^ (p / 2 - 1) * (∑ i, (Dw x i) ^ 2))
                = γ₀ * ζ x ^ 2 * (w x ^ (t / 2 - 1) * w x ^ (p / 2 - 1))
                  * (∑ i, (Dw x i) ^ 2) from by ring, hexpid2 x]
            ring
        _ ≤ ζ x ^ 2 * w x ^ (t / 2 - 1)
            * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i :=
            mul_le_mul_of_nonneg_left hTR2 hz0
    have ht4 : (0 : ℝ) ≤ t / 4 := by linarith
    calc γ₀ * t / 4 * I = t / 4 * (γ₀ * I) := by ring
      _ ≤ t / 4 * ∫ x in Ω, ζ x ^ 2 * w x ^ (t / 2 - 1)
            * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i :=
          mul_le_mul_of_nonneg_left hmain ht4
  -- Step 7: the upper bound from (Q2) and Cauchy-Schwarz
  have hrestr : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ x, x ∉ tsupport ζ → f x = 0) → IntegrableOn f Ω volume →
      (∫ x in Ω, f x) = ∫ x in tsupport ζ, f x := by
    intro f hf0 hfi
    have hsp : Ω = tsupport ζ ∪ (Ω \ tsupport ζ) := by
      rw [Set.union_sdiff_cancel hζΩ]
    have h2 : (∫ x in Ω \ tsupport ζ, f x) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [ae_restrict_mem (hΩ.measurableSet.diff hKmeas)] with x hx
      show f x = 0
      exact hf0 x hx.2
    rw [hsp, setIntegral_union Set.disjoint_sdiff_right
      (hΩ.measurableSet.diff hKmeas) (hfi.mono_set hζΩ)
      (hfi.mono_set Set.sdiff_subset), h2, add_zero]
  have hrp2 : ∀ a : ℝ, a ^ (2 : ℝ) = a ^ 2 := by
    intro a
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
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
  have hsqrtn : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Real.sqrt ((n : ℝ) * a) * Real.sqrt ((n : ℝ) * b)
        = (n : ℝ) * (Real.sqrt a * Real.sqrt b) := by
    intro a b ha hb
    rw [Real.sqrt_mul hnR0.le a, Real.sqrt_mul hnR0.le b,
      show Real.sqrt (n : ℝ) * Real.sqrt a * (Real.sqrt (n : ℝ) * Real.sqrt b)
        = (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) * (Real.sqrt a * Real.sqrt b)
        from by ring, Real.mul_self_sqrt hnR0.le]
  have haeQ2 : ∀ᵐ x ∂(volume.restrict Ω), ∀ i j : Fin n,
      |aij x i j| ≤ γ₁ * w x ^ (p / 2 - 1) := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet, ae_restrict_of_ae hQ.Q2]
      with x hxΩ hxQ2
    intro i j
    have hwne : ε + ‖g x‖ ^ 2 ≠ 0 := by
      have h1 : (0 : ℝ) ≤ ‖g x‖ ^ 2 := sq_nonneg _
      exact ne_of_gt (by linarith)
    have h1 := hxQ2 hxΩ 0 (g x) i j hwne
    rw [← haijeq x i j] at h1
    rwa [show ε + ‖g x‖ ^ 2 = w x from (hweq x).symm] at h1
  obtain ⟨F, hFdef⟩ : ∃ F : EuclideanSpace ℝ (Fin n) → ℝ, F = fun x =>
    w x ^ ((p + t) / 4 - 1) * Real.sqrt (∑ i, (Dw x i) ^ 2) * |ζ x| := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : EuclideanSpace ℝ (Fin n) → ℝ, G = fun x =>
    w x ^ ((p + t) / 4)
      * Real.sqrt (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) := ⟨_, rfl⟩
  have hFeq : ∀ x, F x = w x ^ ((p + t) / 4 - 1)
      * Real.sqrt (∑ i, (Dw x i) ^ 2) * |ζ x| := fun x => by rw [hFdef]
  have hGeq : ∀ x, G x = w x ^ ((p + t) / 4)
      * Real.sqrt (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) :=
    fun x => by rw [hGdef]
  have hA0 : ∀ x : EuclideanSpace ℝ (Fin n), (0 : ℝ) ≤ ∑ i, (Dw x i) ^ 2 :=
    fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB0 : ∀ x : EuclideanSpace ℝ (Fin n), (0 : ℝ)
      ≤ ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 :=
    fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hF0 : ∀ x, 0 ≤ F x := fun x => by
    rw [hFeq x]
    exact mul_nonneg (mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (hwpos x) _))
      (Real.sqrt_nonneg _)) (abs_nonneg _)
  have hG0 : ∀ x, 0 ≤ G x := fun x => by
    rw [hGeq x]
    exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (hwpos x) _)) (Real.sqrt_nonneg _)
  have hE1 : ∀ x : EuclideanSpace ℝ (Fin n),
      (w x ^ ((p + t) / 4 - 1)) ^ 2 = w x ^ ((p + t) / 2 - 2) := by
    intro x
    rw [← Real.rpow_natCast (w x ^ ((p + t) / 4 - 1)) 2,
      ← Real.rpow_mul (hwpos x).le]
    congr 1
    push_cast
    ring
  have hE2 : ∀ x : EuclideanSpace ℝ (Fin n),
      (w x ^ ((p + t) / 4)) ^ 2 = w x ^ ((p + t) / 2) := by
    intro x
    rw [← Real.rpow_natCast (w x ^ ((p + t) / 4)) 2, ← Real.rpow_mul (hwpos x).le]
    congr 1
    push_cast
    ring
  have hE3 : ∀ x : EuclideanSpace ℝ (Fin n),
      w x ^ ((p + t) / 4 - 1) * w x ^ ((p + t) / 4)
        = w x ^ (t / 2) * w x ^ (p / 2 - 1) := by
    intro x
    rw [← Real.rpow_add (hwpos x), ← Real.rpow_add (hwpos x)]
    congr 1
    ring
  have hFsq : ∀ x, F x ^ 2
      = w x ^ ((p + t) / 2 - 2) * (∑ i, (Dw x i) ^ 2) * ζ x ^ 2 := by
    intro x
    rw [hFeq x, mul_pow, mul_pow, hE1 x, Real.sq_sqrt (hA0 x), sq_abs]
  have hGsq : ∀ x, G x ^ 2 = w x ^ ((p + t) / 2)
      * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 := by
    intro x
    rw [hGeq x, mul_pow, hE2 x, Real.sq_sqrt (hB0 x)]
  have hFm : AEMeasurable F (volume.restrict (tsupport ζ)) := by
    rw [hFdef]
    exact haemul _ _ (haemul _ _ (hrpowm _)
      (Real.continuous_sqrt.measurable.comp_aemeasurable
        (haesum _ fun i => (hDwm i).pow_const 2)))
      (continuous_abs.measurable.comp_aemeasurable hζm)
  have hGm : AEMeasurable G (volume.restrict (tsupport ζ)) := by
    rw [hGdef]
    exact haemul _ _ (hrpowm _)
      (Real.continuous_sqrt.measurable.comp_aemeasurable
        (haesum _ fun i => (hDζm i).pow_const 2))
  have hIintK : IntegrableOn (fun x =>
      w x ^ ((p + t) / 2 - 2) * (∑ i, (Dw x i) ^ 2) * ζ x ^ 2)
      (tsupport ζ) volume := hIint.mono_set hζΩ
  have hJintK : IntegrableOn (fun x => w x ^ ((p + t) / 2)
      * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2)
      (tsupport ζ) volume := hJint.mono_set hζΩ
  have hFmem : MemLp F (ENNReal.ofReal 2) (volume.restrict (tsupport ζ)) := by
    refine (integrable_norm_rpow_iff hFm.aestronglyMeasurable (by simp) (by simp)).1 ?_
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp]
    refine hIintK.congr (Filter.Eventually.of_forall fun x => ?_)
    show w x ^ ((p + t) / 2 - 2) * (∑ i, (Dw x i) ^ 2) * ζ x ^ 2 = ‖F x‖ ^ (2 : ℝ)
    rw [Real.norm_eq_abs, hrp2, sq_abs, hFsq x]
  have hGmem : MemLp G (ENNReal.ofReal 2) (volume.restrict (tsupport ζ)) := by
    refine (integrable_norm_rpow_iff hGm.aestronglyMeasurable (by simp) (by simp)).1 ?_
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp]
    refine hJintK.congr (Filter.Eventually.of_forall fun x => ?_)
    show w x ^ ((p + t) / 2)
        * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 = ‖G x‖ ^ (2 : ℝ)
    rw [Real.norm_eq_abs, hrp2, sq_abs, hGsq x]
  have hFGint : IntegrableOn (fun x => F x * G x) (tsupport ζ) volume := by
    refine Integrable.mono' ((hIintK.add hJintK).const_mul (1 / 2))
      (haemul _ _ hFm hGm).aestronglyMeasurable ?_
    filter_upwards with x
    show ‖F x * G x‖ ≤ 1 / 2 * (w x ^ ((p + t) / 2 - 2) * (∑ i, (Dw x i) ^ 2) * ζ x ^ 2
      + w x ^ ((p + t) / 2)
        * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hF0 x) (hG0 x))]
    have h2 := habs2 (F x) (G x)
    rw [abs_of_nonneg (hF0 x), abs_of_nonneg (hG0 x), hFsq x, hGsq x] at h2
    linarith [h2]
  have hT3bd : ∀ᵐ x ∂(volume.restrict (tsupport ζ)),
      |ζ x * w x ^ (t / 2) * ∑ i, ∑ j, aij x i j * Dw x j
          * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
        ≤ γ₁ * (n : ℝ) * (F x * G x) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hζΩ haeQ2] with x hQ2b
    have hwt20 : (0 : ℝ) ≤ w x ^ (t / 2) :=
      le_of_lt (Real.rpow_pos_of_pos (hwpos x) _)
    have hq0 : (0 : ℝ) ≤ γ₁ * w x ^ (p / 2 - 1) :=
      mul_nonneg hγ₁p.le (le_of_lt (Real.rpow_pos_of_pos (hwpos x) _))
    have hstep1 : |∑ i, ∑ j, aij x i j * Dw x j
          * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
        ≤ ∑ i, ∑ j, (γ₁ * w x ^ (p / 2 - 1))
            * (|Dw x j| * |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_mul]
      calc |aij x i j| * |Dw x j|
            * |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
          ≤ (γ₁ * w x ^ (p / 2 - 1)) * |Dw x j|
            * |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hQ2b i j) (abs_nonneg _)) (abs_nonneg _)
        _ = (γ₁ * w x ^ (p / 2 - 1))
            * (|Dw x j| * |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|) := by ring
    have hstep2 : (∑ i, ∑ j, (γ₁ * w x ^ (p / 2 - 1))
          * (|Dw x j| * |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|))
        = (γ₁ * w x ^ (p / 2 - 1)) * ((∑ j, |Dw x j|)
          * ∑ i, |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|) := by
      have e1 : ∀ i : Fin n, (∑ j, (γ₁ * w x ^ (p / 2 - 1))
            * (|Dw x j| * |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|))
          = ((γ₁ * w x ^ (p / 2 - 1))
            * |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|) * ∑ j, |Dw x j| := by
        intro i
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.sum_mul, ← Finset.mul_sum]
      ring
    have hstep3 : (∑ j, |Dw x j|)
          * (∑ i, |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|)
        ≤ (n : ℝ) * (Real.sqrt (∑ i, (Dw x i) ^ 2)
          * Real.sqrt (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2)) := by
      have h1 := hcsn (fun j => Dw x j)
      have h2 := hcsn (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)))
      have h3 := mul_le_mul h1 h2 (Finset.sum_nonneg fun i _ => abs_nonneg _)
        (Real.sqrt_nonneg _)
      rwa [hsqrtn _ _ (hA0 x) (hB0 x)] at h3
    have hin : |∑ i, ∑ j, aij x i j * Dw x j
          * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
        ≤ (γ₁ * w x ^ (p / 2 - 1)) * ((n : ℝ) * (Real.sqrt (∑ i, (Dw x i) ^ 2)
          * Real.sqrt (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2))) := by
      rw [hstep2] at hstep1
      exact le_trans hstep1 (mul_le_mul_of_nonneg_left hstep3 hq0)
    calc |ζ x * w x ^ (t / 2) * ∑ i, ∑ j, aij x i j * Dw x j
            * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
        = |ζ x| * w x ^ (t / 2) * |∑ i, ∑ j, aij x i j * Dw x j
            * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hwt20]
      _ ≤ |ζ x| * w x ^ (t / 2) * ((γ₁ * w x ^ (p / 2 - 1))
          * ((n : ℝ) * (Real.sqrt (∑ i, (Dw x i) ^ 2)
            * Real.sqrt (∑ i,
              (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2)))) :=
          mul_le_mul_of_nonneg_left hin (mul_nonneg (abs_nonneg _) hwt20)
      _ = γ₁ * (n : ℝ) * (F x * G x) := by
          rw [hFeq x, hGeq x,
            show (w x ^ ((p + t) / 4 - 1) * Real.sqrt (∑ i, (Dw x i) ^ 2) * |ζ x|)
                * (w x ^ ((p + t) / 4)
                  * Real.sqrt (∑ i,
                    (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2))
              = (w x ^ ((p + t) / 4 - 1) * w x ^ ((p + t) / 4))
                * (Real.sqrt (∑ i, (Dw x i) ^ 2)
                  * Real.sqrt (∑ i,
                    (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2))
                * |ζ x| from by ring, hE3 x]
          ring
  have hup : |T3| ≤ γ₁ * (n : ℝ) * (Real.sqrt I * Real.sqrt J) := by
    have hconj : Real.HolderConjugate (2 : ℝ) (2 : ℝ) :=
      Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
    have hhol := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume.restrict (tsupport ζ)) hconj (f := F) (g := G)
      (Filter.Eventually.of_forall hF0) (Filter.Eventually.of_forall hG0) hFmem hGmem
    have hIK : (∫ x in tsupport ζ, F x ^ (2 : ℝ)) = I := by
      rw [hIdef, hrestr _ (fun x hx => by rw [hζ0 x hx]; ring) hIint]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show F x ^ (2 : ℝ) = w x ^ ((p + t) / 2 - 2) * (∑ i, (Dw x i) ^ 2) * ζ x ^ 2
      rw [hrp2, hFsq x]
    have hJK : (∫ x in tsupport ζ, G x ^ (2 : ℝ)) = J := by
      rw [hJdef, hrestr _ (fun x hx => ?_) hJint]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show G x ^ (2 : ℝ) = w x ^ ((p + t) / 2)
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2
        rw [hrp2, hGsq x]
      · have hz : ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 = 0 :=
          Finset.sum_eq_zero fun i _ => by rw [hDζ0 x hx i]; ring
        rw [hz, mul_zero]
    rw [hIK, hJK] at hhol
    have hT3K : T3 = ∫ x in tsupport ζ, ζ x * w x ^ (t / 2)
        * ∑ i, ∑ j, aij x i j * Dw x j
          * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)) := by
      rw [hT3def]
      exact hrestr _ (fun x hx => by rw [hζ0 x hx]; ring) hT3Ω
    calc |T3| = |∫ x in tsupport ζ, ζ x * w x ^ (t / 2)
            * ∑ i, ∑ j, aij x i j * Dw x j
              * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))| := by rw [hT3K]
      _ ≤ ∫ x in tsupport ζ, |ζ x * w x ^ (t / 2)
            * ∑ i, ∑ j, aij x i j * Dw x j
              * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x in tsupport ζ, γ₁ * (n : ℝ) * (F x * G x) :=
          integral_mono_ae hT3int.abs (hFGint.const_mul _) hT3bd
      _ = γ₁ * (n : ℝ) * ∫ x in tsupport ζ, F x * G x := integral_const_mul _ _
      _ ≤ γ₁ * (n : ℝ) * (Real.sqrt I * Real.sqrt J) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hγ₁p.le hnR0.le)
          rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
          exact hhol
  have hneg : -T3 ≤ |T3| := neg_le_abs T3
  linarith [hid5, hlow1, hlow2, hup, hneg]
