import ManfrediThesis.Preamble
import ManfrediThesis.PowerWeightIntegrandIntegrability
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.DifferentiatedEquationWeak
import ManfrediThesis.WeakGradientSmoothMul
import ManfrediThesis.WeakGradientVectorComp
set_option maxHeartbeats 1600000
open MeasureTheory

/-- The weak-form transport of the differentiated equation to the power weight,
and the identity `T₁ + T₂ = -T₃` of (5).

Conventions, restated here because a helper inherits none of its parent's.
`w = ε + ‖g‖²` is the weight and `Dw` its weak gradient,
`Dw(x)_i = 2 Σ_k g^k(x) (Dg^k)_i(x)`; all powers of `w` are `Real.rpow`,
written exactly as the structure conditions (Q1)/(Q2) print them, so that at
`ε = 0` and `g = 0` the value is `0` for the negative exponents and `1` at
exponent `0`.  `ζ` is the cut-off and `supp ζ` is its CLOSED support.
`a_{ij}(x) = (dA(g(x))e_j)_i` is the coefficient field of the differentiated
equation, and throughout it is paired with `(Dg^k)_j = D_jD_ku` -- exactly as
`DifferentiatedEquationWeak` states it, and *that index placement is
load-bearing, not cosmetic*.  The three integrals
of (5) are
`T₁ = ∫_Ω ζ²w^{t/2}Σ_{k,i,j}a_{ij}(Dg^k)_j(Dg^k)_i`,
`T₂ = (t/4)∫_Ω ζ²w^{t/2-1}Σ_{i,j}a_{ij}(Dw)_j(Dw)_i` and
`T₃ = ∫_Ω ζw^{t/2}Σ_{i,j}a_{ij}(Dw)_jD_iζ`.
The identity is an `L²` statement, whose test class is `W^{1,2}` with compact
support in `Ω`; the exponent `2` throughout is that test exponent and never a
stand-in for `p`.

The route is Steps 3--5 of the parent's argument.  Step 3 is the chain rule for
the power weight: `w^{t/2}` is a `C¹` function of the VECTOR of the weak
derivatives `(g^1,…,g^n)`, so the product `g^k w^{t/2}` lies in
`W^{1,2}_{loc}(Ω)` with weak gradient
`Ψ^k = w^{t/2}Dg^k + (t/2)g^k w^{t/2-1}Dw`
by `WeakGradientVectorComp` --- *the vector-argument chain rule, not the
scalar one*: the composition differentiates `w` as a function of all `n`
components at once, which the scalar chain rule cannot do.  Step 4 multiplies
by the smooth compactly supported `ζ²` (`WeakGradientSmoothMul`) to get the
admissible test pair `φ_k = g^k w^{t/2}ζ²` with weak gradient
`g_{φ_k} = ζ²Ψ^k + g^k w^{t/2}∇(ζ²)`.  Step 5 feeds each `φ_k` to
`DifferentiatedEquationWeak`, which gives `∫_Ω Σ_{i,j}a_{ij}(Dg^k)_j(g_{φ_k})_i = 0`
for every `k`; summing over `k`, expanding `g_{φ_k}` pointwise and splitting the
integral --- legitimate because each of the three integrands is integrable, which
is established on `supp ζ` by the explicit bounds on `ζ`, `∇ζ`, `w^σ`, `Dg^k`
and `Dw` and then extended to `Ω` because they all vanish off `supp ζ` ---
turns that into `T₁ + T₂ + T₃ = 0`, i.e. `T₁ + T₂ = -T₃`.

The conclusion also carries the integrability facts the parent's
Cauchy--Schwarz tail consumes: `T₁`, `T₂` and `T₃`'s integrands are integrable
on `Ω`, and `T₃`'s is integrable on `supp ζ`. -/
theorem PowerWeightWeakFormIdentity :
    ∀ (n : ℕ) (p : ℝ), 2 ≤ n → 1 < p →
      ∀ (ε γ₀ γ₁ t : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (ζ : EuclideanSpace ℝ (Fin n) → ℝ),
        0 < ε → 0 < γ₀ → γ₀ ≤ γ₁ → IsOpen Ω → Ω.Nonempty →
        EllipticStructureQ12 n p ε γ₀ γ₁ Ω (fun _ _ h => A h) →
        CitedRegularityEpsPos n p ε γ₀ γ₁ Ω A →
        IsWeakSolutionOn n p Ω (fun _ _ h => A h) (fun _ _ _ => 0) u g →
        (∀ i : Fin n, MemW1pLocOn n 2 Ω (fun x => g x i) (Dg i)) →
        ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
      ∀ (w : EuclideanSpace ℝ (Fin n) → ℝ),
        (∀ x, w x = ε + ‖g x‖ ^ 2) → (∀ x, 0 < w x) →
      ∀ (Dw : EuclideanSpace ℝ (Fin n) → Fin n → ℝ),
        (∀ x i, Dw x i = 2 * ∑ k, g x k * Dg k x i) →
      ∀ (aij : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ),
        (∀ x i j, aij x i j
          = (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i) →
      ∀ T1 T2 T3 : ℝ,
        T1 = (∫ x in Ω, ζ x ^ 2 * w x ^ (t / 2)
            * ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i) →
        T2 = (t / 4) * (∫ x in Ω, ζ x ^ 2 * w x ^ (t / 2 - 1)
            * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i) →
        T3 = (∫ x in Ω, ζ x * w x ^ (t / 2)
            * ∑ i, ∑ j, aij x i j * Dw x j
              * (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)))) →
      ∀ (g' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        ContinuousOn g' Ω →
        (∀ᵐ x ∂(volume.restrict Ω), g x = g' x) →
      ∀ (w' : EuclideanSpace ℝ (Fin n) → ℝ),
        (∀ᵐ x ∂(volume.restrict Ω), w x = w' x) →
        (∀ (σ : ℝ) (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K → K ⊆ Ω →
          ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, w' x ^ σ ≤ L) →
        (∀ x, w' x ^ (1 : ℝ) = w' x) →
        (∀ x, (∑ i, (Dw x i) ^ 2) ≤ 4 * w x * ∑ k, ‖Dg k x‖ ^ 2) →
        IsCompact (tsupport ζ) → MeasurableSet (tsupport ζ) →
        (∀ x, x ∉ tsupport ζ → ζ x = 0) →
        (∀ x, x ∉ tsupport ζ → ∀ i : Fin n,
          fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)) = 0) →
        (∀ F : EuclideanSpace ℝ (Fin n) → ℝ,
          (∀ x, x ∉ tsupport ζ → F x = 0) →
          IntegrableOn F (tsupport ζ) volume → IntegrableOn F Ω volume) →
        IntegrableOn (fun x => ∑ k, ‖Dg k x‖ ^ 2) (tsupport ζ) volume →
      ∀ Lζ : ℝ, 0 ≤ Lζ → (∀ x, ζ x ^ 2 ≤ Lζ) →
      ∀ Lw1 : ℝ, (∀ x ∈ tsupport ζ, w' x ^ (1 : ℝ) ≤ Lw1) →
      ∀ LDζ : ℝ,
        (∀ x, ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 ≤ LDζ) →
        AEStronglyMeasurable g (volume.restrict (tsupport ζ)) →
        (∀ σ : ℝ, AEMeasurable (fun x => w x ^ σ) (volume.restrict (tsupport ζ))) →
        (∀ k : Fin n, AEMeasurable (fun x => g x k) (volume.restrict (tsupport ζ))) →
        (∀ k i : Fin n, AEMeasurable (fun x => Dg k x i)
          (volume.restrict (tsupport ζ))) →
        (∀ i : Fin n, AEMeasurable (fun x => Dw x i)
          (volume.restrict (tsupport ζ))) →
        T1 + T2 = -T3
          ∧ IntegrableOn (fun x => ζ x ^ 2 * w x ^ (t / 2)
              * ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i) Ω volume
          ∧ IntegrableOn (fun x => ζ x ^ 2 * w x ^ (t / 2 - 1)
              * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i) Ω volume
          ∧ IntegrableOn (fun x => ζ x * w x ^ (t / 2)
              * ∑ i, ∑ j, aij x i j * Dw x j
                * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) Ω volume
          ∧ IntegrableOn (fun x => ζ x * w x ^ (t / 2)
              * ∑ i, ∑ j, aij x i j * Dw x j
                * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)))
              (tsupport ζ) volume := by
  intro n p hn hp ε γ₀ γ₁ t Ω A u g Dg ζ hε hγ₀ hγ hΩ hΩne hQ hC1 hsol hDg hζsm hζcs
    hζΩ w hweq hwpos Dw hDweq aij haijeq T1 T2 T3 hT1def hT2def hT3def g' hg'cont
    hg'ae w' hwae hwpowbd hwrpow1 hCS2 hKcpt hKmeas hζ0 hDζ0 hextend hMint
    Lζ hLζ0 hLζ Lw1 hLw1 LDζ hLDζ hgK hrpowm hgcm hDgcm hDwm
  -- Step 3: the chain rule for `F_k(y) = y_k (ε + |y|²)^{t/2}` (pm-0013)
  have hNpos : ∀ y : (Fin n → ℝ), 0 < ε + ∑ j, (y j) ^ 2 := by
    intro y
    have h : (0 : ℝ) ≤ ∑ j, (y j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    linarith
  have hNfd : ∀ y : (Fin n → ℝ),
      HasFDerivAt (fun z : (Fin n → ℝ) => ε + ∑ j, (z j) ^ 2)
        (∑ j, (2 * y j) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) y := by
    intro y
    have h1 : ∀ j : Fin n, HasFDerivAt (fun z : (Fin n → ℝ) => (z j) ^ 2)
        ((2 * y j) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) y := by
      intro j
      have hp : HasFDerivAt (fun z : (Fin n → ℝ) => z j)
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) y :=
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt
      have h2 := hp.pow 2
      simpa [pow_one, mul_comm] using h2
    have h3 : HasFDerivAt (fun z : (Fin n → ℝ) => ∑ j, (z j) ^ 2)
        (∑ j, (2 * y j) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) y :=
      HasFDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => h1 j)
    simpa using (hasFDerivAt_const ε y).fun_add h3
  have hFcd : ∀ k : Fin n,
      ContDiff ℝ 1 (fun z : (Fin n → ℝ) => z k * (ε + ∑ j, (z j) ^ 2) ^ (t / 2)) := by
    intro k
    have h1 : ContDiff ℝ 1 (fun z : (Fin n → ℝ) => z k) :=
      (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ).contDiff
    have h2 : ContDiff ℝ 1 (fun z : (Fin n → ℝ) => ε + ∑ j, (z j) ^ 2) := by
      refine contDiff_const.add ?_
      exact ContDiff.sum fun j _ =>
        ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).contDiff.pow 2)
    exact h1.mul (h2.rpow_const_of_ne fun z => ne_of_gt (hNpos z))
  have hFval : ∀ (k : Fin n) (y : (Fin n → ℝ)) (j : Fin n),
      fderiv ℝ (fun z : (Fin n → ℝ) => z k * (ε + ∑ i, (z i) ^ 2) ^ (t / 2)) y
          (Pi.single j (1 : ℝ))
        = (if j = k then (1 : ℝ) else 0) * (ε + ∑ i, (y i) ^ 2) ^ (t / 2)
          + t * y k * y j * (ε + ∑ i, (y i) ^ 2) ^ (t / 2 - 1) := by
    intro k y j
    have hFfd : HasFDerivAt (fun z : (Fin n → ℝ) => z k * (ε + ∑ i, (z i) ^ 2) ^ (t / 2))
        (y k • (((t / 2) * (ε + ∑ i, (y i) ^ 2) ^ (t / 2 - 1)) •
            (∑ i, (2 * y i) • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)))
          + (ε + ∑ i, (y i) ^ 2) ^ (t / 2) •
            (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ)) y := by
      have hp : HasFDerivAt (fun z : (Fin n → ℝ) => z k)
          (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ) y :=
        (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt
      exact hp.fun_mul ((hNfd y).rpow_const (Or.inl (ne_of_gt (hNpos y))))
    rw [hFfd.fderiv]
    simp only [add_apply, smul_apply,
      FunLike.coe_sum, Finset.sum_apply, smul_eq_mul]
    simp [Pi.single_apply, eq_comm]
    ring
  -- (3a): the primed family has the same weak gradients
  have hcongrf : ∀ (f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ)
      (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      (∀ᵐ x ∂(volume.restrict Ω), f₁ x = f₂ x) →
      MemW1pLocOn n 2 Ω f₁ G → MemW1pLocOn n 2 Ω f₂ G := by
    intro f₁ f₂ G hae h
    refine ⟨fun φ hφ hcs hsub i => ?_, fun K hK hKΩ => ?_⟩
    · rw [← h.1 φ hφ hcs hsub i]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
    · refine ⟨(h.2 K hK hKΩ).1.ae_eq ?_, (h.2 K hK hKΩ).2⟩
      exact ae_restrict_of_ae_restrict_of_subset hKΩ hae
  have hcongrg : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (G₁ G₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      (∀ᵐ x ∂(volume.restrict Ω), G₁ x = G₂ x) →
      MemW1pLocOn n 2 Ω f G₁ → MemW1pLocOn n 2 Ω f G₂ := by
    intro f G₁ G₂ hae h
    refine ⟨fun φ hφ hcs hsub i => ?_, fun K hK hKΩ => ?_⟩
    · rw [h.1 φ hφ hcs hsub i]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
    · refine ⟨(h.2 K hK hKΩ).1, (h.2 K hK hKΩ).2.ae_eq ?_⟩
      exact ae_restrict_of_ae_restrict_of_subset hKΩ hae
  have hg'cmp : ∀ j : Fin n, ∀ᵐ x ∂(volume.restrict Ω), g x j = g' x j := by
    intro j
    filter_upwards [hg'ae] with x hx
    rw [hx]
  have hDg' : ∀ j : Fin n, MemW1pLocOn n 2 Ω (fun x => g' x j) (Dg j) :=
    fun j => hcongrf _ _ _ (hg'cmp j) (hDg j)
  -- the local uniform bound that forces the representative
  have hbdd : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω →
      ∃ L : ℝ, ∀ x ∈ K, ∀ j, |g' x j| ≤ L := by
    intro K hK hKΩ
    obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn (hg'cont.mono hKΩ)
    refine ⟨L, fun x hx j => ?_⟩
    have hns : ∑ i, (g' x i) ^ 2 = ‖g' x‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      exact (Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]).symm
    have h1 : (g' x j) ^ 2 ≤ ‖g' x‖ ^ 2 := by
      rw [← hns]
      exact Finset.single_le_sum (f := fun i => (g' x i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg _)] at h2
    exact le_trans h2 (hL x hx)
  -- (3b): the composition, on the representative
  have hVC : ∀ k : Fin n, MemW1pLocOn n 2 Ω
      (fun x => (fun j => g' x j) k * (ε + ∑ i, ((fun j => g' x j) i) ^ 2) ^ (t / 2))
      (fun x => ∑ j, (fderiv ℝ
          (fun z : (Fin n → ℝ) => z k * (ε + ∑ i, (z i) ^ 2) ^ (t / 2))
          (fun i => g' x i) (Pi.single j (1 : ℝ))) • Dg j x) := fun k =>
    WeakGradientVectorComp n n 2 (by omega) (by norm_num) Ω
      (fun j x => g' x j) Dg _ hΩ hDg' hbdd (hFcd k)
  -- (3c): transport back to the unprimed quantities
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      Ψ = fun k x => (EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun i => w x ^ (t / 2) * Dg k x i
          + (t / 2) * g x k * w x ^ (t / 2 - 1) * Dw x i) := ⟨_, rfl⟩
  have hΨeq : ∀ k x i, Ψ k x i = w x ^ (t / 2) * Dg k x i
      + (t / 2) * g x k * w x ^ (t / 2 - 1) * Dw x i := by
    intro k x i
    rw [hΨdef]
    simp
  have hΨmem : ∀ k : Fin n, MemW1pLocOn n 2 Ω (fun x => g x k * w x ^ (t / 2)) (Ψ k) := by
    intro k
    refine hcongrg _ _ _ ?_ (hcongrf _ _ _ ?_ (hVC k))
    · filter_upwards [hg'ae] with x hx
      refine PiLp.ext fun i => ?_
      have hgx : ∀ j, g' x j = g x j := fun j => by rw [hx]
      have hNx : ε + ∑ i, (g' x i) ^ 2 = w x := by
        have h1 : ∑ i, (g' x i) ^ 2 = ‖g x‖ ^ 2 := by
          rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
          exact Finset.sum_congr rfl fun i _ => by
            rw [hgx i, Real.norm_eq_abs, sq_abs]
        rw [h1, hweq x]
      have hsum : ∑ j, g' x j * Dg j x i = (1 / 2) * Dw x i := by
        rw [hDweq x i, Finset.sum_congr rfl (fun j _ => by rw [hgx j] :
          ∀ j ∈ Finset.univ, g' x j * Dg j x i = g x j * Dg j x i)]
        ring
      have hcoord : (∑ j, (fderiv ℝ
          (fun z : (Fin n → ℝ) => z k * (ε + ∑ i, (z i) ^ 2) ^ (t / 2))
          (fun i => g' x i) (Pi.single j (1 : ℝ))) • Dg j x) i
          = ∑ j, ((if j = k then (1 : ℝ) else 0) * (ε + ∑ i, (g' x i) ^ 2) ^ (t / 2)
            + t * g' x k * g' x j * (ε + ∑ i, (g' x i) ^ 2) ^ (t / 2 - 1))
              * Dg j x i := by
        simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
          smul_eq_mul]
        exact Finset.sum_congr rfl fun j _ => by rw [hFval k (fun i => g' x i) j]
      rw [hcoord, hΨeq k x i, hNx]
      have hsplit : ∑ j, ((if j = k then (1 : ℝ) else 0) * w x ^ (t / 2)
          + t * g' x k * g' x j * w x ^ (t / 2 - 1)) * Dg j x i
          = (∑ j, (if j = k then (1 : ℝ) else 0) * w x ^ (t / 2) * Dg j x i)
            + ∑ j, (t * g' x k * w x ^ (t / 2 - 1)) * (g' x j * Dg j x i) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsplit, ← Finset.mul_sum, hsum]
      have hfirst : (∑ j, (if j = k then (1 : ℝ) else 0) * w x ^ (t / 2) * Dg j x i)
          = w x ^ (t / 2) * Dg k x i := by
        rw [Finset.sum_congr rfl (fun j _ => by
          by_cases hjk : j = k
          · simp [hjk]
          · simp [hjk] :
          ∀ j ∈ Finset.univ, (if j = k then (1 : ℝ) else 0) * w x ^ (t / 2) * Dg j x i
            = if j = k then w x ^ (t / 2) * Dg j x i else 0)]
        simp
      rw [hfirst, hgx k]
      ring
    · filter_upwards [hg'ae] with x hx
      have hgx : ∀ j, g' x j = g x j := fun j => by rw [hx]
      have hNx : ε + ∑ i, (g' x i) ^ 2 = w x := by
        have h1 : ∑ i, (g' x i) ^ 2 = ‖g x‖ ^ 2 := by
          rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
          exact Finset.sum_congr rfl fun i _ => by
            rw [hgx i, Real.norm_eq_abs, sq_abs]
        rw [h1, hweq x]
      show g' x k * (ε + ∑ i, (g' x i) ^ 2) ^ (t / 2) = g x k * w x ^ (t / 2)
      rw [hNx, hgx k]
  -- Step 4: `φ_k ζ²` is an admissible test function for (3.2)
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
  obtain ⟨gφ, hgφdef⟩ : ∃ gφ : Fin n → EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n),
      gφ = fun k x => ζ x ^ 2 • Ψ k x
        + (g x k * w x ^ (t / 2)) • (EuclideanSpace.equiv (Fin n) ℝ).symm
            (fun i => fderiv ℝ (fun y => ζ y ^ 2) x
              (EuclideanSpace.single i (1 : ℝ))) := ⟨_, rfl⟩
  have hgφeq : ∀ k x i, gφ k x i
      = ζ x ^ 2 * (w x ^ (t / 2) * Dg k x i
          + (t / 2) * g x k * w x ^ (t / 2 - 1) * Dw x i)
        + (g x k * w x ^ (t / 2)) * (2 * ζ x
          * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) := by
    intro k x i
    have hco : ((EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun i => fderiv ℝ (fun y => ζ y ^ 2) x
          (EuclideanSpace.single i (1 : ℝ)))) i
        = fderiv ℝ (fun y => ζ y ^ 2) x (EuclideanSpace.single i (1 : ℝ)) := by simp
    rw [hgφdef]
    simp only [WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul, Pi.smul_apply,
      smul_eq_mul]
    rw [hΨeq k x i, hco, hDζ2 x i]
  have hadm : ∀ k : Fin n, MemW1pOn n 2 Ω
      (fun x => (g x k * w x ^ (t / 2)) * ζ x ^ 2) (gφ k) := by
    intro k
    simp only [hgφdef]
    exact (WeakGradientSmoothMul n 2 (by omega) (by norm_num) Ω
      (fun x => g x k * w x ^ (t / 2)) (Ψ k) (fun x => ζ x ^ 2)
      hΩ hζ2sm hζ2cs (htsub2.trans hζΩ)).2 (hΨmem k)
  have hφcs : ∀ k : Fin n,
      HasCompactSupport (fun x => (g x k * w x ^ (t / 2)) * ζ x ^ 2) := by
    intro k
    refine HasCompactSupport.mono hζ2cs ?_
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro h
    exact hx (by rw [h]; ring)
  have hφts : ∀ k : Fin n,
      tsupport (fun x => (g x k * w x ^ (t / 2)) * ζ x ^ 2) ⊆ Ω := by
    intro k
    refine subset_trans (closure_mono ?_) (htsub2.trans hζΩ)
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro h
    exact hx (by rw [h]; ring)
  -- Step 5: the differentiated equation at the test pair
  have hzero : ∀ k : Fin n, (∫ x in Ω, ∑ i, ∑ j,
      (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i * Dg k x j * gφ k x i)
      = 0 := fun k =>
    DifferentiatedEquationWeak n p ε γ₀ γ₁ hn hp hε hγ₀ hγ Ω A u g Dg hΩ hQ hC1 hsol
      hDg k _ (gφ k) (hadm k) (hφcs k) (hφts k)
  -- `A` is `C¹` on all of the space, because `ε > 0`
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
  have haijm : ∀ i j : Fin n, AEMeasurable (fun x => aij x i j)
      (volume.restrict (tsupport ζ)) := by
    intro i j
    have hc : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ (fun h : EuclideanSpace ℝ (Fin n) => A h) y
          (EuclideanSpace.single j (1 : ℝ))) i) := by
      have h1 : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
          fderiv ℝ (fun h : EuclideanSpace ℝ (Fin n) => A h) y) :=
        hAcd.continuous_fderiv (by norm_num)
      exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
        (h1.clm_apply continuous_const)
    have h2 : AEStronglyMeasurable
        (fun x => (fderiv ℝ (fun h : EuclideanSpace ℝ (Fin n) => A h) (g x)
          (EuclideanSpace.single j (1 : ℝ))) i) (volume.restrict (tsupport ζ)) :=
      hc.comp_aestronglyMeasurable hgK
    exact h2.aemeasurable.congr
      (Filter.Eventually.of_forall fun x => (haijeq x i j).symm)
  have haesum : ∀ f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ i, AEMeasurable (f i) (volume.restrict (tsupport ζ))) →
      AEMeasurable (fun x => ∑ i, f i x) (volume.restrict (tsupport ζ)) := by
    intro f hf
    have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin n))
      (fun i (_ : i ∈ Finset.univ) => hf i)
    exact h.congr (Filter.Eventually.of_forall fun x => by simp)
  have hζm : AEMeasurable ζ (volume.restrict (tsupport ζ)) :=
    hζsm.continuous.measurable.aemeasurable
  have hDζm : ∀ i : Fin n, AEMeasurable
      (fun x => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)))
      (volume.restrict (tsupport ζ)) := fun i =>
    (((hζsm.continuous_fderiv (by simp)).clm_apply continuous_const).measurable).aemeasurable
  -- the finite-sum bound used throughout Step 5
  obtain ⟨hT1int, hT2int, hT3int, hIkint⟩ :=
    PowerWeightIntegrandIntegrability n p ε γ₀ γ₁ t Lζ Lw1 LDζ Ω A g Dg ζ w w' Dw
      aij gφ hε hγ₀ hγ hQ hζcs hζΩ hweq hwpos haijeq hwae hwpowbd hwrpow1 hCS2
      hKcpt hKmeas hMint hLζ0 hLζ hLw1 hLDζ hrpowm hgcm hDgcm hDwm hgφeq haijm
      haesum hζm hDζm
  -- the pointwise identity of (5)
  have hpull3 : ∀ (c : ℝ) (f : Fin n → Fin n → Fin n → ℝ),
      (∑ k, ∑ i, ∑ j, c * f k i j) = c * ∑ k, ∑ i, ∑ j, f k i j := by
    intro c f
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hpull2 : ∀ (c : ℝ) (f : Fin n → Fin n → ℝ),
      (∑ i, ∑ j, c * f i j) = c * ∑ i, ∑ j, f i j := by
    intro c f
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hDwhalf : ∀ (x : EuclideanSpace ℝ (Fin n)) (j : Fin n),
      ∑ k, g x k * Dg k x j = Dw x j / 2 := by
    intro x j
    rw [hDweq x j]; ring
  have hptw : ∀ x : EuclideanSpace ℝ (Fin n),
      (∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * gφ k x i) = ζ x ^ 2 * w x ^ (t / 2)
        * ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i + t / 4 * (ζ x ^ 2 * w x ^ (t / 2 - 1)
        * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i) + (ζ x * w x ^ (t / 2)
        * ∑ i, ∑ j, aij x i j * Dw x j
          * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) := by
    intro x
    have hAid : (∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * gφ k x i)
        = (∑ k, ∑ i, ∑ j, (ζ x ^ 2 * w x ^ (t / 2))
            * (aij x i j * Dg k x j * Dg k x i))
          + (∑ k, ∑ i, ∑ j,
              (ζ x ^ 2 * (t / 2) * w x ^ (t / 2 - 1) * (aij x i j * Dw x i))
                * (g x k * Dg k x j))
          + (∑ k, ∑ i, ∑ j,
              (2 * ζ x * w x ^ (t / 2)
                * (aij x i j * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))))
                * (g x k * Dg k x j)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hgφeq k x i]
      ring
    rw [hAid]
    congr 1
    · congr 1
      · rw [hpull3]
      · have hL : (∑ k, ∑ i, ∑ j,
            (ζ x ^ 2 * (t / 2) * w x ^ (t / 2 - 1) * (aij x i j * Dw x i))
              * (g x k * Dg k x j))
            = ∑ i, ∑ j, (t / 4 * (ζ x ^ 2 * w x ^ (t / 2 - 1)))
                * (aij x i j * Dw x j * Dw x i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.mul_sum, hDwhalf x j]
          ring
        rw [hL, hpull2]
        ring
    · have hL : (∑ k, ∑ i, ∑ j,
          (2 * ζ x * w x ^ (t / 2)
            * (aij x i j * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))))
            * (g x k * Dg k x j))
          = ∑ i, ∑ j, (ζ x * w x ^ (t / 2))
              * (aij x i j * Dw x j
                * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.mul_sum, hDwhalf x j]
        ring
      rw [hL, hpull2]
  -- the four integrands vanish off the support, so integrability lifts to `Ω`
  have hgφzero : ∀ (k : Fin n) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      x ∉ tsupport ζ → gφ k x i = 0 := by
    intro k x i hx
    rw [hgφeq k x i, hζ0 x hx, hDζ0 x hx i]
    ring
  have hIkΩ : ∀ k : Fin n,
      IntegrableOn (fun x => ∑ i, ∑ j, aij x i j * Dg k x j * gφ k x i) Ω volume := by
    intro k
    refine hextend _ (fun x hx => ?_) (hIkint k)
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [hgφzero k x i hx]
    ring
  have hT1Ω : IntegrableOn (fun x => ζ x ^ 2 * w x ^ (t / 2)
        * ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i) Ω volume :=
    hextend _ (fun x hx => by rw [hζ0 x hx]; ring) hT1int
  have hT2Ω : IntegrableOn (fun x => ζ x ^ 2 * w x ^ (t / 2 - 1)
        * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i) Ω volume :=
    hextend _ (fun x hx => by rw [hζ0 x hx]; ring) hT2int
  have hT3Ω : IntegrableOn (fun x => ζ x * w x ^ (t / 2)
        * ∑ i, ∑ j, aij x i j * Dw x j
          * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) Ω volume :=
    hextend _ (fun x hx => by rw [hζ0 x hx]; ring) hT3int
  have hid5 : T1 + T2 = -T3 := by
    have hzero' : ∀ k : Fin n,
        (∫ x in Ω, ∑ i, ∑ j, aij x i j * Dg k x j * gφ k x i) = 0 := by
      intro k
      rw [← hzero k]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (∑ i, ∑ j, aij x i j * Dg k x j * gφ k x i)
        = ∑ i, ∑ j,
          (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i * Dg k x j * gφ k x i
      exact Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by rw [haijeq x i j]
    have hsum0 : (∑ k, ∫ x in Ω, ∑ i, ∑ j, aij x i j * Dg k x j * gφ k x i) = 0 :=
      Finset.sum_eq_zero fun k _ => hzero' k
    have hswap : (∫ x in Ω, ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * gφ k x i)
        = ∑ k, ∫ x in Ω, ∑ i, ∑ j, aij x i j * Dg k x j * gφ k x i :=
      integral_finsetSum _ fun k _ => hIkΩ k
    have hsplit : (∫ x in Ω, ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * gφ k x i) = T1 + T2 + T3 := by
      have e0 : (∫ x in Ω, ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * gφ k x i)
          = ∫ x in Ω, (ζ x ^ 2 * w x ^ (t / 2)
            * ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i + t / 4 * (ζ x ^ 2 * w x ^ (t / 2 - 1)
            * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i) + (ζ x * w x ^ (t / 2)
            * ∑ i, ∑ j, aij x i j * Dw x j
              * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)))) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => hptw x)
      have e1 : (∫ x in Ω, (ζ x ^ 2 * w x ^ (t / 2)
            * ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i + t / 4 * (ζ x ^ 2 * w x ^ (t / 2 - 1)
            * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i) + (ζ x * w x ^ (t / 2)
            * ∑ i, ∑ j, aij x i j * Dw x j
              * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)))))
          = (∫ x in Ω, (ζ x ^ 2 * w x ^ (t / 2)
            * ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i + t / 4 * (ζ x ^ 2 * w x ^ (t / 2 - 1)
            * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i))) + ∫ x in Ω, ζ x * w x ^ (t / 2)
            * ∑ i, ∑ j, aij x i j * Dw x j
              * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)) :=
        integral_add (hT1Ω.add (hT2Ω.const_mul (t / 4))) hT3Ω
      have e2 : (∫ x in Ω, (ζ x ^ 2 * w x ^ (t / 2)
            * ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i + t / 4 * (ζ x ^ 2 * w x ^ (t / 2 - 1)
            * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i)))
          = (∫ x in Ω, ζ x ^ 2 * w x ^ (t / 2)
            * ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i) + ∫ x in Ω, t / 4 * (ζ x ^ 2 * w x ^ (t / 2 - 1)
            * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i) :=
        integral_add hT1Ω (hT2Ω.const_mul (t / 4))
      have e3 : (∫ x in Ω, t / 4 * (ζ x ^ 2 * w x ^ (t / 2 - 1)
            * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i))
          = t / 4 * ∫ x in Ω, ζ x ^ 2 * w x ^ (t / 2 - 1)
            * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i := by
        rw [integral_const_mul]
      rw [e0, e1, e2, e3, hT1def, hT2def, hT3def]
    linarith [hswap, hsum0, hsplit]
  exact ⟨hid5, hT1Ω, hT2Ω, hT3Ω, hT3int⟩
