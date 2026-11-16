import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pLocOn
set_option maxHeartbeats 1200000
open MeasureTheory

/-- Integrability on `B_R(x₀)` of every integrand of the REGULARISED weighted
Caccioppoli argument: the two pairing terms `P_1`, `P_2`, the regularised
energy density `W(|g^k| + η)^{p-2}‖Dg^k‖²ζ²`, the regularised quadratic form
`ζ²·Dπ_η(g^k)Q_0`, and the right-hand density `v²|∇ζ|²`, together with the
measurability of the test factor `v` on `supp ζ`.

Conventions, restated here because a helper inherits none of its parent's.
`supp ζ` means `tsupport ζ`, the CLOSED support, and `|∇ζ|²` abbreviates
`∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i 1))²`; `g` plays the role of `∇u`
and `Dg k` of `∇D_ku`; `M x i j` is the coefficient matrix `∂A_i/∂h_j(g x)`,
kept ABSTRACT here because only its measurability and the (Q2) bound
`|M x i j| ≤ γ₁W x` are used, and the weight `W` is likewise abstract and
positive.  `η > 0` is the regularisation parameter and `Dπ_η` the derivative of
the regularised signed power; the exponent `p - 2` may be negative, which is
why the regularised base `|g^k| + η` is bounded away from `0` and why the
`m`-free majorant `η^{p-2}` appears in the hypotheses rather than a bound at
`η = 0`.  Every power of a nonnegative real is the real power.  `P_1`, `P_2`
and `Q_0` are carried as function variables with their defining equations, as
the parent holds them.  The extension hypothesis is the parent's `hextend`: a
function vanishing off `supp ζ` and integrable there is integrable on
`B_R(x₀)`.

The route is uniform across the five terms.  On the compact set `supp ζ` the
weight is bounded by `L_W` almost everywhere, `ζ²` by `L_ζ`, `|∇ζ|²` by
`L_{∇ζ}` and the regularised factors `(|g^k| + η)^{p-2}`, `|Dπ_η(g^k)|` by the
constant `η^{p-2}`, while `‖Dg^k‖²` is integrable there and `v`, `Z` lie in
`W^{1,2}_loc` with `|Z_i| ≤ η^{p-2}‖Dg^k‖` almost everywhere.  Each integrand
is then dominated almost everywhere on `supp ζ` by a CONSTANT multiple of
`‖Dg^k‖² + v²`: for `P_1` and the regularised quadratic form one bounds the
double sum by `n²γ₁L_Wη^{p-2}` times `‖Dg^k‖²`, using `|∑| ≤ n·max` twice;
for `P_2` one factor `|Z_i|` is replaced by `|∂_iζ|` and `|v|·|Dg^k|` is split
by `|ab| ≤ (a² + b²)/2`; the two densities are immediate from the constants.
Measurability on `supp ζ` holds because each integrand is built from measurable
factors by products and finite sums, so domination by an integrable function
gives integrability there (Preamble), and `hextend` carries each conclusion to
`B_R(x₀)`, every integrand carrying a factor `ζ²`, `∇ζ` or `Z` that vanishes
off `supp ζ`. -/
theorem RegularisedCaccioppoliIntegrandIntegrability :
    ∀ (n : ℕ) (p η γ₁ Lζ LDζ LW R : ℝ) (Dpi : ℝ → ℝ → ℝ)
      (x₀ : EuclideanSpace ℝ (Fin n))
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (k : Fin n) (ζ W v Q0 P1 P2 : EuclideanSpace ℝ (Fin n) → ℝ)
      (Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (M : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ),
      (∀ (η : ℝ), 0 < η → ∀ s : ℝ, |Dpi η s| ≤ η ^ (p - 2)) →
      0 < η → (0:ℝ) < γ₁ →
      (∀ i : Fin n, MemW1pLocOn n 2 (Metric.ball x₀ R) (fun x => g x i) (Dg i)) →
      tsupport ζ ⊆ Metric.ball x₀ R →
      (∀ x, 0 < W x) →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), ∀ i j : Fin n,
        |M x i j| ≤ γ₁ * W x) →
      IsCompact (tsupport ζ) →
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
      0 ≤ LDζ → 0 ≤ LW → (0:ℝ) ≤ η ^ (p - 2) →
      (∀ x, ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 ≤ LDζ) →
      (∀ᵐ x ∂(volume.restrict (tsupport ζ)), W x ≤ LW) →
      (∀ (f : Fin n → ℝ) (Mb : ℝ), (∀ i, |f i| ≤ Mb) →
        |∑ i, f i| ≤ (n:ℝ) * Mb) →
      (∀ a b : ℝ, |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2) →
      (∀ (x : EuclideanSpace ℝ (Fin n)) (j : Fin n), |Dg k x j| ≤ ‖Dg k x‖) →
      (∀ x : EuclideanSpace ℝ (Fin n), 0 < |g x k| + η) →
      (∀ x : EuclideanSpace ℝ (Fin n), (|g x k| + η) ^ (p - 2) ≤ η ^ (p - 2)) →
      AEMeasurable (fun x => (|g x k| + η) ^ (p - 2))
        (volume.restrict (tsupport ζ)) →
      AEMeasurable (fun x => Dpi η (g x k)) (volume.restrict (tsupport ζ)) →
      (∀ x, 0 ≤ v x) →
      MemW1pLocOn n 2 (Metric.ball x₀ R) v Z →
      (∀ x, Q0 x = ∑ i, ∑ j, M x i j * Dg k x j * Dg k x i) →
      P1 = (fun x => ζ x ^ 2 * ∑ i, ∑ j, M x i j * Dg k x j * Z x i) →
      P2 = (fun x => (2 * v x * ζ x) * ∑ i, ∑ j, M x i j * Dg k x j
        * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) →
      (∀ x, P1 x = ζ x ^ 2 * ∑ i, ∑ j, M x i j * Dg k x j * Z x i) →
      (∀ x, P2 x = (2 * v x * ζ x) * ∑ i, ∑ j, M x i j * Dg k x j
        * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) →
      (∀ᵐ x ∂(volume.restrict (tsupport ζ)),
        ∀ i, |Z x i| ≤ η ^ (p - 2) * ‖Dg k x‖) →
      AEMeasurable v (volume.restrict (tsupport ζ))
      ∧ IntegrableOn P1 (Metric.ball x₀ R) volume
      ∧ IntegrableOn P2 (Metric.ball x₀ R) volume
      ∧ IntegrableOn
          (fun x => W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
          (Metric.ball x₀ R) volume
      ∧ IntegrableOn (fun x => ζ x ^ 2 * (Dpi η (g x k) * Q0 x))
          (Metric.ball x₀ R) volume
      ∧ IntegrableOn (fun x => v x ^ 2
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
          (Metric.ball x₀ R) volume := by
  intro n p η γ₁ Lζ LDζ LW R Dpi x₀ g Dg k ζ W v Q0 P1 P2 Z M hDpibd hη hγ₁p hDg
    hζΩ hWpos hQ2b hKcpt hζ0 hDζ0 hextend hWm hMm hDgcm hζm hDζm haemul haesum
    hMint hLζ0 hLζ hLDζ0 hLW0 hDη0 hLDζ hLW hsumbd habs2 hDgb hbpos hbbd hbm hDpim hv0 hmemloc hQ0eq
    hP1def hP2def hP1eq hP2eq hZae
  have hvm : AEMeasurable v (volume.restrict (tsupport ζ)) :=
    (hmemloc.2 (tsupport ζ) hKcpt hζΩ).1.aemeasurable
  have hZcm : ∀ i : Fin n, AEMeasurable (fun x => Z x i)
      (volume.restrict (tsupport ζ)) := by
    intro i
    have h1 := (hmemloc.2 (tsupport ζ) hKcpt hζΩ).2.1.aemeasurable
    exact ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable).comp_aemeasurable h1
  have hDgnm : AEMeasurable (fun x => ‖Dg k x‖ ^ 2)
      (volume.restrict (tsupport ζ)) :=
    (((hDg k).2 (tsupport ζ) hKcpt hζΩ).2.1.aemeasurable.norm).pow_const 2
  have hvint : IntegrableOn (fun x => v x ^ 2) (tsupport ζ) volume := by
    have hmem := (hmemloc.2 (tsupport ζ) hKcpt hζΩ).1
    have h1 : Integrable (fun x => ‖v x‖ ^ (ENNReal.ofReal 2).toReal)
        (volume.restrict (tsupport ζ)) :=
      hmem.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp] at h1
    refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
    show ‖v x‖ ^ (2:ℝ) = v x ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (hv0 x), ← Real.rpow_natCast (v x) 2]
    norm_num
  have hdom : ∀ (F : EuclideanSpace ℝ (Fin n) → ℝ) (Ca Cb' : ℝ),
      AEMeasurable F (volume.restrict (tsupport ζ)) →
      (∀ᵐ x ∂(volume.restrict (tsupport ζ)),
        |F x| ≤ Ca * ‖Dg k x‖ ^ 2 + Cb' * v x ^ 2) →
      IntegrableOn F (tsupport ζ) volume := by
    intro F Ca Cb' hFm hFb
    refine Integrable.mono' ((hMint.const_mul Ca).add (hvint.const_mul Cb'))
      hFm.aestronglyMeasurable ?_
    filter_upwards [hFb] with x hx
    rwa [Real.norm_eq_abs]
  have hζb : ∀ x, |ζ x| ≤ Real.sqrt Lζ := by
    intro x
    have h1 := Real.sqrt_le_sqrt (hLζ x)
    rwa [Real.sqrt_sq_eq_abs] at h1
  have hDζb : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      |fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))| ≤ Real.sqrt LDζ := by
    intro x i
    have hle : (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 ≤ LDζ :=
      le_trans (Finset.single_le_sum
        (f := fun m => (fderiv ℝ ζ x (EuclideanSpace.single m (1:ℝ))) ^ 2)
        (fun m _ => sq_nonneg _) (Finset.mem_univ i)) (hLDζ x)
    have h1 := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq_eq_abs] at h1
  have hMb : ∀ᵐ x ∂(volume.restrict (tsupport ζ)), ∀ i j : Fin n,
      |M x i j| ≤ γ₁ * LW := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hζΩ hQ2b, hLW]
      with x h1 h2
    intro i j
    exact le_trans (h1 i j) (mul_le_mul_of_nonneg_left h2 hγ₁p.le)
  have hmulb : ∀ a b Ma Mb : ℝ, |a| ≤ Ma → |b| ≤ Mb → |a * b| ≤ Ma * Mb := by
    intro a b Ma Mb ha hb
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)
  have hP1int : IntegrableOn P1 (tsupport ζ) volume := by
    refine hdom _ (Lζ * ((n:ℝ) * ((n:ℝ) * (γ₁ * LW * (η ^ (p - 2)))))) 0
      (by
        rw [hP1def]
        exact haemul _ _ (hζm.pow_const 2)
          (haesum _ fun i => haesum _ fun j =>
            haemul _ _ (haemul _ _ (hMm i j) (hDgcm j)) (hZcm i))) ?_
    filter_upwards [hMb, hZae] with x hMx hZx
    have hin : ∀ i j : Fin n, |M x i j * Dg k x j * Z x i|
        ≤ γ₁ * LW * ‖Dg k x‖ * (η ^ (p - 2) * ‖Dg k x‖) :=
      fun i j => hmulb _ _ _ _ (hmulb _ _ _ _ (hMx i j) (hDgb x j)) (hZx i)
    have h3 : |∑ i, ∑ j, M x i j * Dg k x j * Z x i|
        ≤ (n:ℝ) * ((n:ℝ)
          * (γ₁ * LW * ‖Dg k x‖ * (η ^ (p - 2) * ‖Dg k x‖))) :=
      hsumbd _ _ fun i => hsumbd _ _ fun j => hin i j
    rw [hP1eq x]
    calc |ζ x ^ 2 * ∑ i, ∑ j, M x i j * Dg k x j * Z x i|
        ≤ Lζ * ((n:ℝ) * ((n:ℝ)
            * (γ₁ * LW * ‖Dg k x‖ * (η ^ (p - 2) * ‖Dg k x‖)))) :=
          hmulb _ _ _ _ (by rw [abs_of_nonneg (sq_nonneg _)]; exact hLζ x) h3
      _ = Lζ * ((n:ℝ) * ((n:ℝ) * (γ₁ * LW * (η ^ (p - 2)))))
          * ‖Dg k x‖ ^ 2 + 0 * v x ^ 2 := by ring
  have hQDint : IntegrableOn
      (fun x => ζ x ^ 2 * (Dpi η (g x k) * Q0 x)) (tsupport ζ) volume := by
    refine hdom _ (Lζ * (η ^ (p - 2) * ((n:ℝ) * ((n:ℝ) * (γ₁ * LW))))) 0
      (by
        refine haemul _ _ (hζm.pow_const 2) (haemul _ _ hDpim ?_)
        have h1 : AEMeasurable
            (fun x => ∑ i, ∑ j, M x i j * Dg k x j * Dg k x i)
            (volume.restrict (tsupport ζ)) :=
          haesum _ fun i => haesum _ fun j =>
            haemul _ _ (haemul _ _ (hMm i j) (hDgcm j)) (hDgcm i)
        exact h1.congr (Filter.Eventually.of_forall fun x => (hQ0eq x).symm)) ?_
    filter_upwards [hMb] with x hMx
    have hin : ∀ i j : Fin n, |M x i j * Dg k x j * Dg k x i|
        ≤ γ₁ * LW * ‖Dg k x‖ * ‖Dg k x‖ :=
      fun i j => hmulb _ _ _ _ (hmulb _ _ _ _ (hMx i j) (hDgb x j)) (hDgb x i)
    have h3 : |Q0 x| ≤ (n:ℝ) * ((n:ℝ) * (γ₁ * LW * ‖Dg k x‖ * ‖Dg k x‖)) := by
      rw [hQ0eq x]
      exact hsumbd _ _ fun i => hsumbd _ _ fun j => hin i j
    have h4 : |Dpi η (g x k) * Q0 x|
        ≤ η ^ (p - 2) * ((n:ℝ) * ((n:ℝ) * (γ₁ * LW * ‖Dg k x‖ * ‖Dg k x‖))) :=
      hmulb _ _ _ _ (hDpibd η hη (g x k)) h3
    calc |ζ x ^ 2 * (Dpi η (g x k) * Q0 x)|
        ≤ Lζ * (η ^ (p - 2)
            * ((n:ℝ) * ((n:ℝ) * (γ₁ * LW * ‖Dg k x‖ * ‖Dg k x‖)))) :=
          hmulb _ _ _ _ (by rw [abs_of_nonneg (sq_nonneg _)]; exact hLζ x) h4
      _ = Lζ * (η ^ (p - 2) * ((n:ℝ) * ((n:ℝ) * (γ₁ * LW))))
          * ‖Dg k x‖ ^ 2 + 0 * v x ^ 2 := by ring
  have hP2int : IntegrableOn P2 (tsupport ζ) volume := by
    refine hdom _
      (Real.sqrt Lζ * ((n:ℝ) * ((n:ℝ) * (γ₁ * LW * Real.sqrt LDζ))))
      (Real.sqrt Lζ * ((n:ℝ) * ((n:ℝ) * (γ₁ * LW * Real.sqrt LDζ))))
      (by
        rw [hP2def]
        exact haemul _ _ (haemul _ _ (hvm.const_mul 2) hζm)
          (haesum _ fun i => haesum _ fun j =>
            haemul _ _ (haemul _ _ (hMm i j) (hDgcm j)) (hDζm i))) ?_
    filter_upwards [hMb] with x hMx
    have hin : ∀ i j : Fin n, |M x i j * Dg k x j
          * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))|
        ≤ γ₁ * LW * ‖Dg k x‖ * Real.sqrt LDζ :=
      fun i j => hmulb _ _ _ _ (hmulb _ _ _ _ (hMx i j) (hDgb x j)) (hDζb x i)
    have h3 : |∑ i, ∑ j, M x i j * Dg k x j
          * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))|
        ≤ (n:ℝ) * ((n:ℝ) * (γ₁ * LW * ‖Dg k x‖ * Real.sqrt LDζ)) :=
      hsumbd _ _ fun i => hsumbd _ _ fun j => hin i j
    have hpre : |2 * v x * ζ x| ≤ 2 * v x * Real.sqrt Lζ := by
      have h2v : (0:ℝ) ≤ 2 * v x := by linarith [hv0 x]
      rw [abs_mul, abs_of_nonneg h2v]
      exact mul_le_mul_of_nonneg_left (hζb x) h2v
    have hvd : v x * ‖Dg k x‖ ≤ (v x ^ 2 + ‖Dg k x‖ ^ 2) / 2 := by
      have h1 := habs2 (v x) ‖Dg k x‖
      rwa [abs_of_nonneg (hv0 x), abs_of_nonneg (norm_nonneg _)] at h1
    have hcc : (0:ℝ) ≤ Real.sqrt Lζ * ((n:ℝ) * ((n:ℝ)
        * (γ₁ * LW * Real.sqrt LDζ))) := by positivity
    rw [hP2eq x]
    calc |2 * v x * ζ x * ∑ i, ∑ j, M x i j * Dg k x j
            * fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))|
        ≤ (2 * v x * Real.sqrt Lζ)
          * ((n:ℝ) * ((n:ℝ) * (γ₁ * LW * ‖Dg k x‖ * Real.sqrt LDζ))) :=
          hmulb _ _ _ _ hpre h3
      _ = (Real.sqrt Lζ * ((n:ℝ) * ((n:ℝ) * (γ₁ * LW * Real.sqrt LDζ))))
            * (2 * (v x * ‖Dg k x‖)) := by ring
      _ ≤ (Real.sqrt Lζ * ((n:ℝ) * ((n:ℝ) * (γ₁ * LW * Real.sqrt LDζ))))
            * (2 * ((v x ^ 2 + ‖Dg k x‖ ^ 2) / 2)) :=
          mul_le_mul_of_nonneg_left (by linarith [hvd]) hcc
      _ = Real.sqrt Lζ * ((n:ℝ) * ((n:ℝ) * (γ₁ * LW * Real.sqrt LDζ)))
            * ‖Dg k x‖ ^ 2
          + Real.sqrt Lζ * ((n:ℝ) * ((n:ℝ) * (γ₁ * LW * Real.sqrt LDζ)))
            * v x ^ 2 := by ring
  have hXint : IntegrableOn
      (fun x => W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
      (tsupport ζ) volume := by
    refine hdom _ (LW * (η ^ (p - 2)) * Lζ) 0
      (haemul _ _ (haemul _ _ (haemul _ _ hWm hbm) hDgnm) (hζm.pow_const 2)) ?_
    filter_upwards [hLW] with x hWx
    have hW0 : (0:ℝ) ≤ W x := (hWpos x).le
    have hb0 : (0:ℝ) ≤ (|g x k| + η) ^ (p - 2) :=
      Real.rpow_nonneg (hbpos x).le _
    calc |W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2|
        = W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2 :=
          abs_of_nonneg (by positivity)
      _ ≤ LW * (η ^ (p - 2)) * ‖Dg k x‖ ^ 2 * Lζ := by
          refine mul_le_mul (mul_le_mul (mul_le_mul hWx (hbbd x) hb0
            (le_trans hW0 hWx)) le_rfl (sq_nonneg _) (by positivity))
            (hLζ x) (sq_nonneg _) (by positivity)
      _ = LW * (η ^ (p - 2)) * Lζ * ‖Dg k x‖ ^ 2 + 0 * v x ^ 2 := by ring
  have hYint : IntegrableOn (fun x => v x ^ 2
      * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
      (tsupport ζ) volume := by
    refine hdom _ 0 LDζ
      (haemul _ _ (hvm.pow_const 2)
        (haesum _ fun i => (hDζm i).pow_const 2)) ?_
    filter_upwards with x
    have hB0 : (0:ℝ)
        ≤ ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    calc |v x ^ 2 * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2|
        = v x ^ 2 * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 :=
          abs_of_nonneg (by positivity)
      _ ≤ v x ^ 2 * LDζ := mul_le_mul_of_nonneg_left (hLDζ x) (sq_nonneg _)
      _ = 0 * ‖Dg k x‖ ^ 2 + LDζ * v x ^ 2 := by ring
  -- the integrands vanish off the support, so everything lifts to `B_R`
  have hvanP1 : ∀ x, x ∉ tsupport ζ → P1 x = 0 := fun x hx => by
    rw [hP1eq x, hζ0 x hx]; ring
  have hvanP2 : ∀ x, x ∉ tsupport ζ → P2 x = 0 := fun x hx => by
    rw [hP2eq x, hζ0 x hx]; ring
  have hvanX : ∀ x, x ∉ tsupport ζ →
      W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2 = 0 :=
    fun x hx => by rw [hζ0 x hx]; ring
  have hvanQD : ∀ x, x ∉ tsupport ζ →
      ζ x ^ 2 * (Dpi η (g x k) * Q0 x) = 0 := fun x hx => by
    rw [hζ0 x hx]; ring
  have hvanY : ∀ x, x ∉ tsupport ζ → v x ^ 2
      * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 = 0 := by
    intro x hx
    have hz : ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hDζ0 x hx i]; ring
    rw [hz, mul_zero]
  have hP1Ω : IntegrableOn P1 (Metric.ball x₀ R) volume :=
    hextend _ hvanP1 hP1int
  have hP2Ω : IntegrableOn P2 (Metric.ball x₀ R) volume :=
    hextend _ hvanP2 hP2int
  have hXΩ : IntegrableOn
      (fun x => W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
      (Metric.ball x₀ R) volume := hextend _ hvanX hXint
  have hQDΩ : IntegrableOn (fun x => ζ x ^ 2 * (Dpi η (g x k) * Q0 x))
      (Metric.ball x₀ R) volume := hextend _ hvanQD hQDint
  have hYΩ : IntegrableOn (fun x => v x ^ 2
      * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
      (Metric.ball x₀ R) volume := hextend _ hvanY hYint
  exact ⟨hvm, hP1Ω, hP2Ω, hXΩ, hQDΩ, hYΩ⟩
