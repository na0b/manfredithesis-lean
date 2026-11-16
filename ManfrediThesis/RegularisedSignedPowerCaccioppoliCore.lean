import ManfrediThesis.Preamble
import ManfrediThesis.RegularisedCaccioppoliIntegrandIntegrability
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.DifferentiatedEquationWeak
import ManfrediThesis.WeakGradientSmoothMul
set_option maxHeartbeats 1600000
open MeasureTheory

/-- The sign-free core of inequality (D.5): the Caccioppoli bound for one
truncation pair of the regularised signed power.

Conventions, restated here because a helper inherits none of its parent's.
`g` plays the role of `∇u` and `Dg k` of `∇D_ku`; `W` is the weight, which in
the parent is the `Real.rpow` power `(ε + ‖g‖²)^{p/2-1}` written exactly as the
structure conditions (Q1)/(Q2) print it, but which enters here only through the
hypotheses below, so that no form of it is assumed; `M x i j = (dA(g(x))e_j)_i`
is the coefficient field of the differentiated equation; `η > 0` is the
regularisation level and `Dpi η` stands for the derivative `π'_η` of the
regularised signed power, of which only the lower bound
`(p-1)(|s|+η)^{p-2} ≤ π'_η(s)` and the uniform bound `|π'_η(s)| ≤ η^{p-2}` are
used; `ζ` is the cut-off and `supp ζ` means its CLOSED support, which every
bound and measurability hypothesis below is taken on; `Lζ`, `LDζ` and `LW` are
sup bounds for `ζ²`, `|∇ζ|²` and `W` there.  All powers of positive reals are
real powers, never rewritten as integer powers.

The statement is the one the parent needs at both of its call sites: for a
measurable `T ⊆ B_R(x₀)`, a sign `sg = ±1`, a nonnegative `v` and a field `Z`
which on `T` equals `(sg·π'_η(g^k))·Dg^k` and which vanishes off `T` together
with `v`, and with `v ∈ W^{1,2}_{loc}(B_R(x₀))` with weak gradient `Z`,
\[
∫_T W(|g^k|+η)^{p-2}‖Dg^k‖²ζ²
  ≤ \Bigl(\frac{2nr2^{1-p/2}}{p-1}\Bigr)^2∫_{B_R(x₀)}v²|∇ζ|² .
\]
It is sign-free in the sense that `sg` enters only through `|sg| = 1`, which is
why one statement serves both the superlevel and the sublevel set.

The proof is Steps 3e--7 of the parent's argument, unchanged.  The test pair is
`(vζ², ζ²Z + v∇(ζ²))`: `ζ²` is smooth with compact support in `B_R(x₀)`, so the
product rule for a `W^{1,2}_{loc}` factor against a smooth compactly supported
one makes it admissible, and feeding it to the differentiated equation gives an
identity whose left-hand side is bounded below by (Q1) --- here the lower bound
on `π'_η` enters, next to `γ₀W‖ξ‖² ≤ Σa_{ij}ξ_jξ_i` at `ξ = Dg^k` --- and whose
right-hand side is bounded above by (Q2) together with two index
Cauchy--Schwarz steps and then one Cauchy--Schwarz in the integral, pairing
`√(W(|g^k|+η)^{p-2})|ζ|‖Dg^k‖` against `v|∇ζ|`.  Dividing by the left factor,
which is finite because every integrand vanishes off `supp ζ` and is dominated
there by the stated bounds, gives the displayed inequality with the constant as
printed. -/
theorem RegularisedSignedPowerCaccioppoliCore :
    ∀ (n : ℕ) (p r η : ℝ) (Dpi : ℝ → ℝ → ℝ)
      (x₀ : EuclideanSpace ℝ (Fin n)) (R ε γ₀ γ₁ : ℝ)
      (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (u : EuclideanSpace ℝ (Fin n) → ℝ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (k : Fin n) (ζ W : EuclideanSpace ℝ (Fin n) → ℝ)
      (M : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (Lζ LDζ LW : ℝ),
      2 ≤ n → 1 < p → 0 < r →
      (∀ (η : ℝ), 0 < η → ∀ s : ℝ, (p - 1) * (|s| + η) ^ (p - 2) ≤ Dpi η s) →
      (∀ (η : ℝ), 0 < η → ∀ s : ℝ, |Dpi η s| ≤ η ^ (p - 2)) →
      0 < η → 0 < ε → 0 < γ₀ → γ₁ ≤ r * γ₀ → γ₀ ≤ γ₁ → 0 < R → (0:ℝ) < γ₁ →
      EllipticStructureQ12 n p ε γ₀ γ₁ (Metric.ball x₀ R) (fun _ _ h => A h) →
      CitedRegularityEpsPos n p ε γ₀ γ₁ (Metric.ball x₀ R) A →
      IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h)
        (fun _ _ _ => 0) u g →
      (∀ i : Fin n, MemW1pLocOn n 2 (Metric.ball x₀ R) (fun x => g x i) (Dg i)) →
      ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball x₀ R →
      (∀ x, 0 < W x) →
      (∀ x i j, M x i j
        = (fderiv ℝ A (g x) (EuclideanSpace.single j (1:ℝ))) i) →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
        ∀ ξ : EuclideanSpace ℝ (Fin n),
          γ₀ * W x * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, M x i j * ξ j * ξ i) →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), ∀ i j : Fin n,
        |M x i j| ≤ γ₁ * W x) →
      IsCompact (tsupport ζ) → MeasurableSet (tsupport ζ) →
      (∀ x, x ∉ tsupport ζ → ζ x = 0) →
      (∀ x, x ∉ tsupport ζ → ∀ i : Fin n,
        fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ)) = 0) →
      (∀ F : EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ x, x ∉ tsupport ζ → F x = 0) →
        IntegrableOn F (tsupport ζ) volume →
        IntegrableOn F (Metric.ball x₀ R) volume) →
      AEMeasurable W (volume.restrict (tsupport ζ)) →
      (∀ i j : Fin n, AEMeasurable (fun x => M x i j)
        (volume.restrict (tsupport ζ))) →
      (∀ j : Fin n, AEMeasurable (fun x => Dg k x j)
        (volume.restrict (tsupport ζ))) →
      AEMeasurable ζ (volume.restrict (tsupport ζ)) →
      (∀ i : Fin n, AEMeasurable
        (fun x => fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ)))
        (volume.restrict (tsupport ζ))) →
      (∀ f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ,
        AEMeasurable f₁ (volume.restrict (tsupport ζ)) →
        AEMeasurable f₂ (volume.restrict (tsupport ζ)) →
        AEMeasurable (fun x => f₁ x * f₂ x) (volume.restrict (tsupport ζ))) →
      (∀ f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ i, AEMeasurable (f i) (volume.restrict (tsupport ζ))) →
        AEMeasurable (fun x => ∑ i, f i x) (volume.restrict (tsupport ζ))) →
      IntegrableOn (fun x => ‖Dg k x‖ ^ 2) (tsupport ζ) volume →
      0 ≤ Lζ → (∀ x, ζ x ^ 2 ≤ Lζ) →
      0 ≤ LDζ →
      (∀ x, ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 ≤ LDζ) →
      0 ≤ LW → (∀ᵐ x ∂(volume.restrict (tsupport ζ)), W x ≤ LW) →
      (∀ (f : Fin n → ℝ) (Mb : ℝ), (∀ i, |f i| ≤ Mb) →
        |∑ i, f i| ≤ (n:ℝ) * Mb) →
      (∀ a b : ℝ, |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2) →
      (∀ x : EuclideanSpace ℝ (Fin n),
        ∑ m, (Dg k x m) ^ 2 = ‖Dg k x‖ ^ 2) →
      (∀ (x : EuclideanSpace ℝ (Fin n)) (j : Fin n),
        |Dg k x j| ≤ ‖Dg k x‖) →
      (∀ (cc : ℝ) (f : Fin n → Fin n → ℝ),
        (∑ i, ∑ j, cc * f i j) = cc * ∑ i, ∑ j, f i j) →
      (∀ f : Fin n → ℝ, ∑ j, |f j| ≤ Real.sqrt ((n:ℝ) * ∑ j, (f j) ^ 2)) →
      (∀ x : EuclideanSpace ℝ (Fin n), 0 < |g x k| + η) →
      (∀ x : EuclideanSpace ℝ (Fin n),
        (|g x k| + η) ^ (p - 2) ≤ η ^ (p - 2)) →
      AEMeasurable (fun x => (|g x k| + η) ^ (p - 2))
        (volume.restrict (tsupport ζ)) →
      AEMeasurable (fun x => Dpi η (g x k)) (volume.restrict (tsupport ζ)) →
      (0:ℝ) ≤ η ^ (p - 2) →
      (∀ x : EuclideanSpace ℝ (Fin n),
        W x ≤ (2:ℝ) ^ (2 - p) * (|g x k| + η) ^ (p - 2)) →
      ∀ (T : Set (EuclideanSpace ℝ (Fin n))) (sg : ℝ)
      (v : EuclideanSpace ℝ (Fin n) → ℝ)
      (Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      (sg = 1 ∨ sg = -1) → MeasurableSet T → T ⊆ Metric.ball x₀ R →
      (∀ x, 0 ≤ v x) →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      (x ∈ T → Z x = (sg * Dpi η (g x k)) • Dg k x)
      ∧ (x ∉ T → Z x = 0 ∧ v x = 0)) →
      MemW1pLocOn n 2 (Metric.ball x₀ R) v Z →
      (∫ x in T, W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
      ≤ (2 * (n:ℝ) * r * (2:ℝ) ^ (1 - p / 2) / (p - 1)) ^ 2
      * ∫ x in Metric.ball x₀ R, v x ^ 2
      * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 := by
  intro n p r η Dpi x₀ R ε γ₀ γ₁ A u g Dg k ζ W M Lζ LDζ LW hn hp hr
    hDpilow hDpibd hη hε hγ₀ hγ₁ hγ01 hR hγ₁p hQ hC1 hsol hDg hζsm hζcs hζΩ
    hWpos hMeq hQ1b hQ2b hKcpt hKmeas hζ0 hDζ0 hextend hWm hMm hDgcm hζm hDζm
    haemul haesum hMint hLζ0 hLζ hLDζ0 hLDζ hLW0 hLW hsumbd habs2 hDgns hDgb
    hpull2 hcsn hbpos hbbd hbm hDpim hDη0 hD4
  have hp0 : (0:ℝ) < p := by linarith
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR0 : (0:ℝ) < (n:ℝ) := by
    have : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hp10 : (0:ℝ) < p - 1 := by linarith
  have hΩ : IsOpen (Metric.ball x₀ R) := Metric.isOpen_ball
  intro T sg v Z hsg hTm hTΩ hv0 hvZ hmemloc
  have hsgabs : |sg| = 1 := by rcases hsg with h | h <;> rw [h] <;> norm_num
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
      fderiv ℝ (fun y => ζ y ^ 2) x (EuclideanSpace.single i (1:ℝ))
        = 2 * ζ x * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ)) := by
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
              (EuclideanSpace.single i (1:ℝ))) := ⟨_, rfl⟩
  have hgφeq : ∀ x i, gφ x i = ζ x ^ 2 * Z x i
      + v x * (2 * ζ x * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) := by
    intro x i
    have hco : ((EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun i => fderiv ℝ (fun y => ζ y ^ 2) x
          (EuclideanSpace.single i (1:ℝ)))) i
        = fderiv ℝ (fun y => ζ y ^ 2) x
          (EuclideanSpace.single i (1:ℝ)) := by simp
    rw [hgφdef]
    simp only [WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul, Pi.smul_apply,
      smul_eq_mul]
    rw [hco, hDζ2 x i]
  have hadm : MemW1pOn n 2 (Metric.ball x₀ R) (fun x => v x * ζ x ^ 2) gφ := by
    simp only [hgφdef]
    exact (WeakGradientSmoothMul n 2 hn1 (by norm_num) (Metric.ball x₀ R) v Z
      (fun x => ζ x ^ 2) hΩ hζ2sm hζ2cs (htsub2.trans hζΩ)).2 hmemloc
  have hφcs : HasCompactSupport (fun x => v x * ζ x ^ 2) := by
    refine HasCompactSupport.mono hζ2cs ?_
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro h
    exact hx (by rw [h]; ring)
  have hφts : tsupport (fun x => v x * ζ x ^ 2) ⊆ Metric.ball x₀ R := by
    refine subset_trans (closure_mono ?_) (htsub2.trans hζΩ)
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro h
    exact hx (by rw [h]; ring)
  have hzero : (∫ x in Metric.ball x₀ R,
      ∑ i, ∑ j, M x i j * Dg k x j * gφ x i) = 0 := by
    have h0 := DifferentiatedEquationWeak n p ε γ₀ γ₁ hn hp hε hγ₀ hγ01
      (Metric.ball x₀ R) A u g Dg hΩ hQ hC1 hsol hDg k _ gφ hadm hφcs hφts
    rw [← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (∑ i, ∑ j, M x i j * Dg k x j * gφ x i)
      = ∑ i, ∑ j,
        (fderiv ℝ A (g x) (EuclideanSpace.single j (1:ℝ))) i * Dg k x j * gφ x i
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by rw [hMeq x i j]
  -- the two terms of the differentiated equation
  obtain ⟨Q0, hQ0def⟩ : ∃ Q0 : EuclideanSpace ℝ (Fin n) → ℝ,
      Q0 = fun x => ∑ i, ∑ j, M x i j * Dg k x j * Dg k x i := ⟨_, rfl⟩
  have hQ0eq : ∀ x, Q0 x = ∑ i, ∑ j, M x i j * Dg k x j * Dg k x i :=
    fun x => by rw [hQ0def]
  obtain ⟨P1, hP1def⟩ : ∃ P1 : EuclideanSpace ℝ (Fin n) → ℝ,
      P1 = fun x => ζ x ^ 2 * ∑ i, ∑ j, M x i j * Dg k x j * Z x i := ⟨_, rfl⟩
  obtain ⟨P2, hP2def⟩ : ∃ P2 : EuclideanSpace ℝ (Fin n) → ℝ,
      P2 = fun x => (2 * v x * ζ x) * ∑ i, ∑ j, M x i j * Dg k x j
        * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ)) := ⟨_, rfl⟩
  have hP1eq : ∀ x, P1 x = ζ x ^ 2 * ∑ i, ∑ j, M x i j * Dg k x j * Z x i :=
    fun x => by rw [hP1def]
  have hP2eq : ∀ x, P2 x = (2 * v x * ζ x) * ∑ i, ∑ j, M x i j * Dg k x j
      * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ)) := fun x => by rw [hP2def]
  have hsplitptw : ∀ x,
      (∑ i, ∑ j, M x i j * Dg k x j * gφ x i) = P1 x + P2 x := by
    intro x
    have hA1 : (∑ i, ∑ j, M x i j * Dg k x j * gφ x i)
        = (∑ i, ∑ j, ζ x ^ 2 * (M x i j * Dg k x j * Z x i))
          + ∑ i, ∑ j, (2 * v x * ζ x) * (M x i j * Dg k x j
            * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hgφeq x i]
      ring
    rw [hA1, hpull2, hpull2, hP1eq x, hP2eq x]
  -- the a.e. description of `Z`
  have hZae : ∀ᵐ x ∂(volume.restrict (tsupport ζ)),
      ∀ i, |Z x i| ≤ η ^ (p - 2) * ‖Dg k x‖ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hζΩ hvZ] with x hx
    intro i
    by_cases hxT : x ∈ T
    · have hZi : Z x i = (sg * Dpi η (g x k)) * Dg k x i := by
        rw [hx.1 hxT]; simp
      rw [hZi, abs_mul, abs_mul, hsgabs, one_mul]
      exact mul_le_mul (hDpibd η hη (g x k)) (hDgb x i) (abs_nonneg _) hDη0
    · rw [(hx.2 hxT).1]
      show |(0:ℝ)| ≤ η ^ (p - 2) * ‖Dg k x‖
      rw [abs_zero]
      exact mul_nonneg hDη0 (norm_nonneg _)
  -- integrability of every integrand
  obtain ⟨hvm, hP1Ω, hP2Ω, hXΩ, hQDΩ, hYΩ⟩ :=
    RegularisedCaccioppoliIntegrandIntegrability n p η γ₁ Lζ LDζ LW R Dpi x₀ g Dg
      k ζ W v Q0 P1 P2 Z M hDpibd hη hγ₁p hDg hζΩ hWpos hQ2b hKcpt hζ0 hDζ0
      hextend hWm hMm hDgcm hζm hDζm haemul haesum hMint hLζ0 hLζ hLDζ0 hLW0 hDη0
      hLDζ hLW hsumbd habs2 hDgb hbpos hbbd hbm hDpim hv0 hmemloc hQ0eq hP1def
      hP2def hP1eq hP2eq hZae
  have hsum0 : (∫ x in Metric.ball x₀ R, P1 x)
      + ∫ x in Metric.ball x₀ R, P2 x = 0 := by
    have e1 : (∫ x in Metric.ball x₀ R, (P1 x + P2 x)) = 0 := by
      rw [← hzero]
      exact integral_congr_ae
        (Filter.Eventually.of_forall fun x => (hsplitptw x).symm)
    rw [← integral_add hP1Ω hP2Ω]
    exact e1
  -- the three quantities
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = ∫ x in T,
    W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2 := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = ∫ x in Metric.ball x₀ R, v x ^ 2
    * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Qv, hQvdef⟩ : ∃ Qv : ℝ, Qv = ∫ x in T,
    ζ x ^ 2 * (Dpi η (g x k) * Q0 x) := ⟨_, rfl⟩
  have hb0 : ∀ x : EuclideanSpace ℝ (Fin n),
      (0:ℝ) ≤ (|g x k| + η) ^ (p - 2) :=
    fun x => Real.rpow_nonneg (hbpos x).le _
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    refine integral_nonneg fun x => ?_
    exact mul_nonneg (mul_nonneg (mul_nonneg (hWpos x).le (hb0 x))
      (sq_nonneg _)) (sq_nonneg _)
  have hY0 : 0 ≤ Y := by
    rw [hYdef]
    refine integral_nonneg fun x => ?_
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  -- Step 7: the first term, localized to `T`
  have hP1T : (∫ x in Metric.ball x₀ R, P1 x) = sg * Qv := by
    have e1 : (∫ x in Metric.ball x₀ R, P1 x)
        = ∫ x in Metric.ball x₀ R,
          T.indicator (fun y => sg * (ζ y ^ 2 * (Dpi η (g y k) * Q0 y))) x := by
      refine integral_congr_ae ?_
      filter_upwards [hvZ] with x hx
      by_cases hxT : x ∈ T
      · rw [Set.indicator_of_mem hxT]
        have hZi : ∀ i : Fin n, Z x i = (sg * Dpi η (g x k)) * Dg k x i := by
          intro i
          rw [hx.1 hxT]; simp
        have e2 : (∑ i, ∑ j, M x i j * Dg k x j * Z x i)
            = (sg * Dpi η (g x k))
              * ∑ i, ∑ j, M x i j * Dg k x j * Dg k x i := by
          rw [← hpull2 (sg * Dpi η (g x k))
            (fun i j => M x i j * Dg k x j * Dg k x i)]
          exact Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => by rw [hZi i]; ring
        rw [hP1eq x, e2, ← hQ0eq x]
        ring
      · rw [Set.indicator_of_notMem hxT, hP1eq x, (hx.2 hxT).1]
        simp
    rw [e1, setIntegral_indicator hTm, Set.inter_eq_self_of_subset_right hTΩ,
      integral_const_mul, ← hQvdef]
  -- the lower bound of Step 7
  have hQvlow : γ₀ * (p - 1) * X ≤ Qv := by
    rw [hXdef, hQvdef, ← integral_const_mul]
    refine integral_mono_ae ((hXΩ.mono_set hTΩ).const_mul (γ₀ * (p - 1)))
      (hQDΩ.mono_set hTΩ) ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hTΩ hQ1b] with x hx
    show γ₀ * (p - 1)
        * (W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
      ≤ ζ x ^ 2 * (Dpi η (g x k) * Q0 x)
    have h1 := hx (Dg k x)
    rw [← hQ0eq x] at h1
    have hgw0 : (0:ℝ) ≤ γ₀ * W x * ‖Dg k x‖ ^ 2 :=
      mul_nonneg (mul_nonneg hγ₀.le (hWpos x).le) (sq_nonneg _)
    have h2 : (p - 1) * (|g x k| + η) ^ (p - 2) ≤ Dpi η (g x k) :=
      hDpilow η hη (g x k)
    have h3 : (0:ℝ) ≤ (p - 1) * (|g x k| + η) ^ (p - 2) :=
      mul_nonneg (by linarith only [hp]) (hb0 x)
    have h4 : ((p - 1) * (|g x k| + η) ^ (p - 2)) * (γ₀ * W x * ‖Dg k x‖ ^ 2)
        ≤ Dpi η (g x k) * Q0 x :=
      mul_le_mul h2 h1 hgw0 (le_trans h3 h2)
    calc γ₀ * (p - 1)
          * (W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
        = (((p - 1) * (|g x k| + η) ^ (p - 2)) * (γ₀ * W x * ‖Dg k x‖ ^ 2))
          * ζ x ^ 2 := by ring
      _ ≤ (Dpi η (g x k) * Q0 x) * ζ x ^ 2 :=
          mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
      _ = ζ x ^ 2 * (Dpi η (g x k) * Q0 x) := by ring
  -- Step 8: the second term, localized to `T`
  have hP2T : (∫ x in Metric.ball x₀ R, P2 x) = ∫ x in T, P2 x := by
    have e1 : (∫ x in Metric.ball x₀ R, P2 x)
        = ∫ x in Metric.ball x₀ R, T.indicator P2 x := by
      refine integral_congr_ae ?_
      filter_upwards [hvZ] with x hx
      by_cases hxT : x ∈ T
      · rw [Set.indicator_of_mem hxT]
      · rw [Set.indicator_of_notMem hxT, hP2eq x, (hx.2 hxT).2]
        ring
    rw [e1, setIntegral_indicator hTm, Set.inter_eq_self_of_subset_right hTΩ]
  -- (D4) in the form the Cauchy-Schwarz pairing needs
  have hWroot : ∀ x : EuclideanSpace ℝ (Fin n),
      W x ≤ (2:ℝ) ^ (1 - p / 2)
        * Real.sqrt (W x * (|g x k| + η) ^ (p - 2)) := by
    intro x
    have hW0 : (0:ℝ) ≤ W x := (hWpos x).le
    have h1 : W x ^ 2 ≤ (2:ℝ) ^ (2 - p) * (W x * (|g x k| + η) ^ (p - 2)) := by
      have h0 := hD4 x
      nlinarith only [h0, hW0, hb0 x]
    have h2 : ((2:ℝ) ^ (1 - p / 2)) ^ 2 = (2:ℝ) ^ (2 - p) := by
      rw [← Real.rpow_natCast ((2:ℝ) ^ (1 - p / 2)) 2,
        ← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    have h4 : (0:ℝ) ≤ (2:ℝ) ^ (1 - p / 2)
        * Real.sqrt (W x * (|g x k| + η) ^ (p - 2)) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
    have h3 : W x ^ 2 ≤ ((2:ℝ) ^ (1 - p / 2)
        * Real.sqrt (W x * (|g x k| + η) ^ (p - 2))) ^ 2 := by
      rw [mul_pow, h2, Real.sq_sqrt (mul_nonneg hW0 (hb0 x))]
      exact h1
    have h5 := Real.sqrt_le_sqrt h3
    rwa [Real.sqrt_sq hW0, Real.sqrt_sq h4] at h5
  -- the Cauchy-Schwarz pair
  obtain ⟨F, hFdef⟩ : ∃ F : EuclideanSpace ℝ (Fin n) → ℝ,
    F = fun x => Real.sqrt (W x * (|g x k| + η) ^ (p - 2))
      * |ζ x| * ‖Dg k x‖ := ⟨_, rfl⟩
  obtain ⟨G2, hG2def⟩ : ∃ G2 : EuclideanSpace ℝ (Fin n) → ℝ,
    G2 = fun x => v x
      * Real.sqrt (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2) :=
    ⟨_, rfl⟩
  have hFeq : ∀ x, F x = Real.sqrt (W x * (|g x k| + η) ^ (p - 2))
      * |ζ x| * ‖Dg k x‖ := fun x => by rw [hFdef]
  have hG2eq : ∀ x, G2 x = v x
      * Real.sqrt (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2) :=
    fun x => by rw [hG2def]
  have hB0 : ∀ x : EuclideanSpace ℝ (Fin n), (0:ℝ)
      ≤ ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 :=
    fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hF0 : ∀ x, 0 ≤ F x := fun x => by
    rw [hFeq x]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
      (norm_nonneg _)
  have hG20 : ∀ x, 0 ≤ G2 x := fun x => by
    rw [hG2eq x]
    exact mul_nonneg (hv0 x) (Real.sqrt_nonneg _)
  have hFsq : ∀ x, F x ^ 2
      = W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2 := by
    intro x
    rw [hFeq x, mul_pow, mul_pow,
      Real.sq_sqrt (mul_nonneg (hWpos x).le (hb0 x)), sq_abs]
    ring
  have hG2sq : ∀ x, G2 x ^ 2 = v x ^ 2
      * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 := by
    intro x
    rw [hG2eq x, mul_pow, Real.sq_sqrt (hB0 x)]
  have hFvan : ∀ x, x ∉ tsupport ζ → F x = 0 := fun x hx => by
    rw [hFeq x, hζ0 x hx]; simp
  have hG2van : ∀ x, x ∉ tsupport ζ → G2 x = 0 := by
    intro x hx
    have hz : ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 = 0 :=
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
  have hFm : AEStronglyMeasurable F volume := by
    refine hindext F hFvan ?_
    rw [hFdef]
    refine AEMeasurable.aestronglyMeasurable ?_
    exact haemul _ _ (haemul _ _
      (Real.continuous_sqrt.measurable.comp_aemeasurable (haemul _ _ hWm hbm))
      (continuous_abs.measurable.comp_aemeasurable hζm))
      ((((hDg k).2 (tsupport ζ) hKcpt hζΩ).2.1.aemeasurable).norm)
  have hG2m : AEStronglyMeasurable G2 volume := by
    refine hindext G2 hG2van ?_
    rw [hG2def]
    refine AEMeasurable.aestronglyMeasurable ?_
    exact haemul _ _ hvm
      (Real.continuous_sqrt.measurable.comp_aemeasurable
        (haesum _ fun i => (hDζm i).pow_const 2))
  have hrp2 : ∀ a : ℝ, a ^ (2:ℝ) = a ^ 2 := by
    intro a
    rw [show (2:ℝ) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  have hFmem : MemLp F (ENNReal.ofReal 2) (volume.restrict T) := by
    refine (integrable_norm_rpow_iff hFm.restrict (by simp) (by simp)).1 ?_
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp]
    refine (hXΩ.mono_set hTΩ).congr (Filter.Eventually.of_forall fun x => ?_)
    show W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2
      = ‖F x‖ ^ (2:ℝ)
    rw [Real.norm_eq_abs, hrp2, sq_abs, hFsq x]
  have hG2mem : MemLp G2 (ENNReal.ofReal 2) (volume.restrict T) := by
    refine (integrable_norm_rpow_iff hG2m.restrict (by simp) (by simp)).1 ?_
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp]
    refine (hYΩ.mono_set hTΩ).congr (Filter.Eventually.of_forall fun x => ?_)
    show v x ^ 2 * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2
      = ‖G2 x‖ ^ (2:ℝ)
    rw [Real.norm_eq_abs, hrp2, sq_abs, hG2sq x]
  have hFGint : IntegrableOn (fun x => F x * G2 x) T volume := by
    have hXT := hXΩ.mono_set hTΩ
    have hYT := hYΩ.mono_set hTΩ
    refine Integrable.mono' ((hXT.add hYT).const_mul (1 / 2))
      ((hFm.mul hG2m).restrict) ?_
    filter_upwards with x
    show ‖F x * G2 x‖ ≤ 1 / 2
      * (W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2
        + v x ^ 2 * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hF0 x) (hG20 x))]
    have h2 := habs2 (F x) (G2 x)
    rw [abs_of_nonneg (hF0 x), abs_of_nonneg (hG20 x), hFsq x, hG2sq x] at h2
    linarith [h2]
  -- the pointwise bound of Step 8
  have hP2b : ∀ᵐ x ∂(volume.restrict T),
      |P2 x| ≤ 2 * (n:ℝ) * γ₁ * (2:ℝ) ^ (1 - p / 2) * (F x * G2 x) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hTΩ hQ2b] with x hQ2x
    have hW0 : (0:ℝ) ≤ W x := (hWpos x).le
    have hq0 : (0:ℝ) ≤ γ₁ * W x := mul_nonneg hγ₁p.le hW0
    have hA1 : ∑ j, |Dg k x j| ≤ Real.sqrt (n:ℝ) * ‖Dg k x‖ := by
      have h := hcsn (fun j => Dg k x j)
      rw [hDgns x, Real.sqrt_mul hnR0.le, Real.sqrt_sq (norm_nonneg _)] at h
      exact h
    have hB1 : ∑ i, |fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))|
        ≤ Real.sqrt (n:ℝ)
          * Real.sqrt (∑ i, (fderiv ℝ ζ x
            (EuclideanSpace.single i (1:ℝ))) ^ 2) := by
      have h := hcsn (fun i => fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ)))
      rw [Real.sqrt_mul hnR0.le] at h
      exact h
    have hstep1 : |∑ i, ∑ j, M x i j * Dg k x j
          * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))|
        ≤ ∑ i, ∑ j, (γ₁ * W x) * (|Dg k x j|
          * |fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))|) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _)
        (Finset.sum_le_sum fun i _ => ?_)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _)
        (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_mul]
      calc |M x i j| * |Dg k x j|
            * |fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))|
          ≤ (γ₁ * W x) * |Dg k x j|
            * |fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hQ2x i j) (abs_nonneg _))
              (abs_nonneg _)
        _ = (γ₁ * W x) * (|Dg k x j|
            * |fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))|) := by ring
    have hstep2 : (∑ i, ∑ j, (γ₁ * W x) * (|Dg k x j|
          * |fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))|))
        = (γ₁ * W x) * ((∑ j, |Dg k x j|)
          * ∑ i, |fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))|) := by
      have e1 : ∀ i : Fin n, (∑ j, (γ₁ * W x) * (|Dg k x j|
            * |fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))|))
          = ((γ₁ * W x) * |fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))|)
            * ∑ j, |Dg k x j| := by
        intro i
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.sum_mul,
        ← Finset.mul_sum]
      ring
    have hin : |∑ i, ∑ j, M x i j * Dg k x j
          * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))|
        ≤ (n:ℝ) * (γ₁ * W x) * (‖Dg k x‖
          * Real.sqrt (∑ i, (fderiv ℝ ζ x
            (EuclideanSpace.single i (1:ℝ))) ^ 2)) := by
      rw [hstep2] at hstep1
      refine le_trans hstep1 ?_
      have hprod : (∑ j, |Dg k x j|)
            * ∑ i, |fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))|
          ≤ (Real.sqrt (n:ℝ) * ‖Dg k x‖)
            * (Real.sqrt (n:ℝ) * Real.sqrt (∑ i, (fderiv ℝ ζ x
              (EuclideanSpace.single i (1:ℝ))) ^ 2)) :=
        mul_le_mul hA1 hB1 (Finset.sum_nonneg fun i _ => abs_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      refine le_trans (mul_le_mul_of_nonneg_left hprod hq0) (le_of_eq ?_)
      rw [show (Real.sqrt (n:ℝ) * ‖Dg k x‖)
            * (Real.sqrt (n:ℝ) * Real.sqrt (∑ i, (fderiv ℝ ζ x
              (EuclideanSpace.single i (1:ℝ))) ^ 2))
          = (Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ)) * (‖Dg k x‖
            * Real.sqrt (∑ i, (fderiv ℝ ζ x
              (EuclideanSpace.single i (1:ℝ))) ^ 2)) from by ring,
        Real.mul_self_sqrt hnR0.le]
      ring
    have hpre : |2 * v x * ζ x| ≤ 2 * v x * |ζ x| := by
      have h2v : (0:ℝ) ≤ 2 * v x := by linarith [hv0 x]
      rw [abs_mul, abs_of_nonneg h2v]
    have hfac0 : (0:ℝ) ≤ |ζ x| * ‖Dg k x‖
        * (v x * Real.sqrt (∑ i, (fderiv ℝ ζ x
          (EuclideanSpace.single i (1:ℝ))) ^ 2)) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))
        (mul_nonneg (hv0 x) (Real.sqrt_nonneg _))
    have hcoef0 : (0:ℝ) ≤ 2 * (n:ℝ) * γ₁ :=
      mul_nonneg (mul_nonneg (by norm_num) hnR0.le) hγ₁p.le
    rw [hP2eq x]
    calc |2 * v x * ζ x * ∑ i, ∑ j, M x i j * Dg k x j
            * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))|
        = |2 * v x * ζ x| * |∑ i, ∑ j, M x i j * Dg k x j
            * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))| := abs_mul _ _
      _ ≤ (2 * v x * |ζ x|) * ((n:ℝ) * (γ₁ * W x) * (‖Dg k x‖
            * Real.sqrt (∑ i, (fderiv ℝ ζ x
              (EuclideanSpace.single i (1:ℝ))) ^ 2))) :=
          mul_le_mul hpre hin (abs_nonneg _)
            (mul_nonneg (by linarith [hv0 x]) (abs_nonneg _))
      _ = 2 * (n:ℝ) * γ₁ * (W x * (|ζ x| * ‖Dg k x‖
            * (v x * Real.sqrt (∑ i, (fderiv ℝ ζ x
              (EuclideanSpace.single i (1:ℝ))) ^ 2)))) := by ring
      _ ≤ 2 * (n:ℝ) * γ₁ * (((2:ℝ) ^ (1 - p / 2)
            * Real.sqrt (W x * (|g x k| + η) ^ (p - 2)))
            * (|ζ x| * ‖Dg k x‖
            * (v x * Real.sqrt (∑ i, (fderiv ℝ ζ x
              (EuclideanSpace.single i (1:ℝ))) ^ 2)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hWroot x) hfac0) hcoef0
      _ = 2 * (n:ℝ) * γ₁ * (2:ℝ) ^ (1 - p / 2) * (F x * G2 x) := by
          rw [hFeq x, hG2eq x]
          ring
  -- Cauchy-Schwarz and the division
  have hconj : Real.HolderConjugate (2:ℝ) (2:ℝ) :=
    Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have hhol := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict T)
    hconj (f := F) (g := G2) (Filter.Eventually.of_forall hF0)
    (Filter.Eventually.of_forall hG20) hFmem hG2mem
  have hFX : (∫ x in T, F x ^ (2:ℝ)) = X := by
    rw [hXdef]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show F x ^ (2:ℝ)
      = W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2
    rw [hrp2, hFsq x]
  have hGY : (∫ x in T, G2 x ^ (2:ℝ)) ≤ Y := by
    have e1 : (∫ x in T, G2 x ^ (2:ℝ))
        = ∫ x in T, v x ^ 2
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show G2 x ^ (2:ℝ) = v x ^ 2
        * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2
      rw [hrp2, hG2sq x]
    rw [e1, hYdef]
    refine setIntegral_mono_set hYΩ ?_
      (Filter.Eventually.of_forall fun x hx => hTΩ hx)
    exact Filter.Eventually.of_forall fun x =>
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [hFX, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hhol
  have hKc0 : (0:ℝ) ≤ 2 * (n:ℝ) * γ₁ * (2:ℝ) ^ (1 - p / 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hnR0.le) hγ₁p.le)
      (Real.rpow_nonneg (by norm_num) _)
  have hP2bd : |∫ x in T, P2 x|
      ≤ 2 * (n:ℝ) * γ₁ * (2:ℝ) ^ (1 - p / 2)
        * (Real.sqrt X * Real.sqrt Y) := by
    calc |∫ x in T, P2 x| ≤ ∫ x in T, |P2 x| := abs_integral_le_integral_abs
      _ ≤ ∫ x in T, 2 * (n:ℝ) * γ₁ * (2:ℝ) ^ (1 - p / 2) * (F x * G2 x) :=
          integral_mono_ae (hP2Ω.mono_set hTΩ).abs (hFGint.const_mul _) hP2b
      _ = 2 * (n:ℝ) * γ₁ * (2:ℝ) ^ (1 - p / 2) * ∫ x in T, F x * G2 x :=
          integral_const_mul _ _
      _ ≤ 2 * (n:ℝ) * γ₁ * (2:ℝ) ^ (1 - p / 2)
            * (Real.sqrt X * Real.sqrt Y) := by
          refine mul_le_mul_of_nonneg_left (le_trans hhol ?_) hKc0
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hGY)
            (Real.sqrt_nonneg _)
  have hQvabs : |Qv| ≤ 2 * (n:ℝ) * γ₁ * (2:ℝ) ^ (1 - p / 2)
      * (Real.sqrt X * Real.sqrt Y) := by
    have e1 : sg * Qv = -(∫ x in T, P2 x) := by
      rw [← hP1T, ← hP2T]
      linarith [hsum0]
    have e2 : |sg * Qv| = |Qv| := by rw [abs_mul, hsgabs, one_mul]
    rw [← e2, e1, abs_neg]
    exact hP2bd
  have hlow : γ₀ * (p - 1) * X ≤ 2 * (n:ℝ) * γ₁ * (2:ℝ) ^ (1 - p / 2)
      * (Real.sqrt X * Real.sqrt Y) :=
    le_trans (le_trans hQvlow (le_abs_self _)) hQvabs
  rw [← hXdef, ← hYdef]
  have h2pow0 : (0:ℝ) < (2:ℝ) ^ (1 - p / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rcases eq_or_lt_of_le hX0 with hXe | hXp
  · rw [← hXe]
    exact mul_nonneg (by positivity) hY0
  · have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hXp
    have hXX : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0
    have hYY : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY0
    have hstep : γ₀ * (p - 1) * Real.sqrt X
        ≤ 2 * (n:ℝ) * γ₁ * (2:ℝ) ^ (1 - p / 2) * Real.sqrt Y := by
      refine le_of_mul_le_mul_right ?_ hsX
      calc γ₀ * (p - 1) * Real.sqrt X * Real.sqrt X = γ₀ * (p - 1) * X := by
            rw [mul_assoc, hXX]
        _ ≤ 2 * (n:ℝ) * γ₁ * (2:ℝ) ^ (1 - p / 2)
            * (Real.sqrt X * Real.sqrt Y) := hlow
        _ = 2 * (n:ℝ) * γ₁ * (2:ℝ) ^ (1 - p / 2) * Real.sqrt Y
            * Real.sqrt X := by ring
    have hstep2 : (p - 1) * Real.sqrt X
        ≤ 2 * (n:ℝ) * r * (2:ℝ) ^ (1 - p / 2) * Real.sqrt Y := by
      refine le_of_mul_le_mul_left ?_ hγ₀
      calc γ₀ * ((p - 1) * Real.sqrt X) = γ₀ * (p - 1) * Real.sqrt X := by ring
        _ ≤ 2 * (n:ℝ) * γ₁ * (2:ℝ) ^ (1 - p / 2) * Real.sqrt Y := hstep
        _ ≤ 2 * (n:ℝ) * (r * γ₀) * (2:ℝ) ^ (1 - p / 2) * Real.sqrt Y := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right ?_ h2pow0.le) (Real.sqrt_nonneg _)
            exact mul_le_mul_of_nonneg_left hγ₁ (by positivity)
        _ = γ₀ * (2 * (n:ℝ) * r * (2:ℝ) ^ (1 - p / 2) * Real.sqrt Y) := by
            ring
    have hstep3 : Real.sqrt X
        ≤ 2 * (n:ℝ) * r * (2:ℝ) ^ (1 - p / 2) / (p - 1) * Real.sqrt Y := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hp10]
      nlinarith only [hstep2]
    have hrhs0 : (0:ℝ)
        ≤ 2 * (n:ℝ) * r * (2:ℝ) ^ (1 - p / 2) / (p - 1) * Real.sqrt Y := by
      have : (0:ℝ) ≤ 2 * (n:ℝ) * r * (2:ℝ) ^ (1 - p / 2) / (p - 1) := by
        apply div_nonneg _ hp10.le
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hnR0.le) hr.le)
          h2pow0.le
      exact mul_nonneg this (Real.sqrt_nonneg _)
    calc X = Real.sqrt X * Real.sqrt X := hXX.symm
      _ ≤ (2 * (n:ℝ) * r * (2:ℝ) ^ (1 - p / 2) / (p - 1) * Real.sqrt Y)
          * (2 * (n:ℝ) * r * (2:ℝ) ^ (1 - p / 2) / (p - 1) * Real.sqrt Y) :=
          mul_le_mul hstep3 hstep3 (Real.sqrt_nonneg _) hrhs0
      _ = (2 * (n:ℝ) * r * (2:ℝ) ^ (1 - p / 2) / (p - 1)) ^ 2
          * (Real.sqrt Y * Real.sqrt Y) := by ring
      _ = (2 * (n:ℝ) * r * (2:ℝ) ^ (1 - p / 2) / (p - 1)) ^ 2 * Y := by
          rw [hYY]
