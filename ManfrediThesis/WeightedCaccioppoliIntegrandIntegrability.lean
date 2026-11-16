import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pLocOn
set_option maxHeartbeats 1200000
open MeasureTheory

/-- Integrability on `Ω` of every integrand of the weighted Caccioppoli
argument: the two pairing terms `P_1`, `P_2`, the energy density
`W‖Dg^k‖²ζ²`, the quadratic form `ζ²Q_0`, and the right-hand density
`Wv²|∇ζ|²`, together with the measurability of the test factor `v` on
`supp ζ`.

Conventions, restated here because a helper inherits none of its parent's.
`supp ζ` means `tsupport ζ`, the CLOSED support, and `|∇ζ|²` abbreviates
`∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i 1))²`; `g` plays the role of `∇u`
and `Dg k` of `∇D_ku`; `M x i j` is the coefficient matrix
`∂A_i/∂h_j(g x)` and is kept ABSTRACT here, since only its measurability and
the (Q2) bound `|M x i j| ≤ γ₁W x` are used.  The weight `W` is likewise
abstract and positive, so no `rpow` convention is needed and pm-0024(1)'s
printed weight is whatever the parent substitutes.  `P_1`, `P_2` and `Q_0` are
carried as function variables with their defining equations as hypotheses,
exactly as the parent holds them.  The extension hypothesis is the parent's
`hextend`: a function vanishing off `supp ζ` and integrable there is integrable
on `Ω`, which is how every conclusion below is transported from the compact
support to `Ω`.

The route is uniform across the five terms.  On the compact set `supp ζ` the
weight is bounded by `L_W` almost everywhere, `ζ²` by `L_ζ`, and `|∇ζ|²` by
`L_{∇ζ}`, while `‖Dg^k‖²` is integrable there and `v`, `Z` are in
`W^{1,2}_loc(Ω)`, hence measurable on `supp ζ` with `|Z_i| ≤ ‖Dg^k‖` almost
everywhere.  Each integrand is then dominated almost everywhere on `supp ζ` by
a CONSTANT multiple of `‖Dg^k‖² + v² + 1`-type integrable data: for `P_1` and
`ζ²Q_0` one bounds the double sum by `n²γ₁L_W` times `‖Dg^k‖²` using
`|∑| ≤ n·max` twice and `|ab| ≤ (a² + b²)/2`; for `P_2` one does the same with
one factor `|Z_i|` replaced by `|∂_iζ|`, absorbing `2vζ` into the constant via
`L_ζ` and the elementary bound `|v| ≤ v² + 1`; and for the two densities the
bound is immediate from `L_W`, `L_ζ` and `L_{∇ζ}`.  Each integrand is
measurable on `supp ζ`, being built from measurable factors by products and
finite sums, so domination by an integrable function gives integrability there
(Preamble), and `hextend` carries it to `Ω` because every integrand carries the
factor `ζ²`, `∇ζ` or `Z`, each of which vanishes off `supp ζ`. -/
theorem WeightedCaccioppoliIntegrandIntegrability :
    ∀ (n : ℕ) (γ₁ Lζ LDζ LW : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (ζ W v Q0 P1 P2 : EuclideanSpace ℝ (Fin n) → ℝ)
      (Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (M : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (k : Fin n),
      (∀ i : Fin n, MemW1pLocOn n 2 Ω (fun x => g x i) (Dg i)) →
      tsupport ζ ⊆ Ω →
      (∀ x, 0 < W x) → (0 : ℝ) < γ₁ →
      IsCompact (tsupport ζ) →
      (∀ x, x ∉ tsupport ζ → ζ x = 0) →
      (∀ x, x ∉ tsupport ζ → ∀ i : Fin n,
        fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)) = 0) →
      (∀ F : EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ x, x ∉ tsupport ζ → F x = 0) →
        IntegrableOn F (tsupport ζ) volume → IntegrableOn F Ω volume) →
      (∀ᵐ x ∂(volume.restrict Ω), ∀ i j : Fin n, |M x i j| ≤ γ₁ * W x) →
      AEMeasurable W (volume.restrict (tsupport ζ)) →
      (∀ i j : Fin n, AEMeasurable (fun x => M x i j)
        (volume.restrict (tsupport ζ))) →
      (∀ j : Fin n, AEMeasurable (fun x => Dg k x j)
        (volume.restrict (tsupport ζ))) →
      AEMeasurable ζ (volume.restrict (tsupport ζ)) →
      (∀ i : Fin n, AEMeasurable
        (fun x => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)))
        (volume.restrict (tsupport ζ))) →
      (∀ f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ,
        AEMeasurable f₁ (volume.restrict (tsupport ζ)) →
        AEMeasurable f₂ (volume.restrict (tsupport ζ)) →
        AEMeasurable (fun x => f₁ x * f₂ x) (volume.restrict (tsupport ζ))) →
      (∀ f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ i, AEMeasurable (f i) (volume.restrict (tsupport ζ))) →
        AEMeasurable (fun x => ∑ i, f i x) (volume.restrict (tsupport ζ))) →
      IntegrableOn (fun x => ‖Dg k x‖ ^ 2) (tsupport ζ) volume →
      (∀ x, ζ x ^ 2 ≤ Lζ) →
      (∀ x, ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 ≤ LDζ) →
      (0:ℝ) ≤ LW →
      (∀ᵐ x ∂(volume.restrict (tsupport ζ)), W x ≤ LW) →
      (∀ (f : Fin n → ℝ) (Mb : ℝ), (∀ i, |f i| ≤ Mb) →
        |∑ i, f i| ≤ (n : ℝ) * Mb) →
      (∀ a b : ℝ, |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2) →
      (∀ (x : EuclideanSpace ℝ (Fin n)) (j : Fin n), |Dg k x j| ≤ ‖Dg k x‖) →
      (∀ x, 0 ≤ v x) →
      MemW1pLocOn n 2 Ω v Z →
      (∀ x, Q0 x = ∑ i, ∑ j, M x i j * Dg k x j * Dg k x i) →
      P1 = (fun x => ζ x ^ 2 * ∑ i, ∑ j, M x i j * Dg k x j * Z x i) →
      P2 = (fun x => (2 * v x * ζ x) * ∑ i, ∑ j, M x i j * Dg k x j
        * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) →
      (∀ x, P1 x = ζ x ^ 2 * ∑ i, ∑ j, M x i j * Dg k x j * Z x i) →
      (∀ x, P2 x = (2 * v x * ζ x) * ∑ i, ∑ j, M x i j * Dg k x j
        * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) →
      (∀ᵐ x ∂(volume.restrict (tsupport ζ)), (∀ i, |Z x i| ≤ ‖Dg k x‖)) →
      AEMeasurable v (volume.restrict (tsupport ζ))
      ∧ IntegrableOn P1 Ω volume
      ∧ IntegrableOn P2 Ω volume
      ∧ IntegrableOn (fun x => W x * ‖Dg k x‖ ^ 2 * ζ x ^ 2) Ω volume
      ∧ IntegrableOn (fun x => ζ x ^ 2 * Q0 x) Ω volume
      ∧ IntegrableOn (fun x => W x * v x ^ 2
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) Ω volume := by
  intro n γ₁ Lζ LDζ LW Ω g Dg ζ W v Q0 P1 P2 Z M k hDg hζΩ hWpos hγ₁p hKcpt hζ0
    hDζ0 hextend hQ2b hWm hMm hDgcm hζm hDζm haemul haesum hMint hLζ hLDζ hLW0 hLW
    hsumbd habs2 hDgb hv0 hmemloc hQ0eq hP1def hP2def hP1eq hP2eq hZae
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
    show ‖v x‖ ^ (2 : ℝ) = v x ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (hv0 x), ← Real.rpow_natCast (v x) 2]
    norm_num
  have hdom : ∀ (F : EuclideanSpace ℝ (Fin n) → ℝ) (C₁ C₂ : ℝ),
      AEMeasurable F (volume.restrict (tsupport ζ)) →
      (∀ᵐ x ∂(volume.restrict (tsupport ζ)),
        |F x| ≤ C₁ * ‖Dg k x‖ ^ 2 + C₂ * v x ^ 2) →
      IntegrableOn F (tsupport ζ) volume := by
    intro F C₁ C₂ hFm hFb
    refine Integrable.mono' ((hMint.const_mul C₁).add (hvint.const_mul C₂))
      hFm.aestronglyMeasurable ?_
    filter_upwards [hFb] with x hx
    rwa [Real.norm_eq_abs]
  have hζb : ∀ x, |ζ x| ≤ Real.sqrt Lζ := by
    intro x
    have h1 := Real.sqrt_le_sqrt (hLζ x)
    rwa [Real.sqrt_sq_eq_abs] at h1
  have hDζb : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))| ≤ Real.sqrt LDζ := by
    intro x i
    have hle : (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 ≤ LDζ :=
      le_trans (Finset.single_le_sum
        (f := fun m => (fderiv ℝ ζ x (EuclideanSpace.single m (1 : ℝ))) ^ 2)
        (fun m _ => sq_nonneg _) (Finset.mem_univ i)) (hLDζ x)
    have h1 := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq_eq_abs] at h1
  have hMb : ∀ᵐ x ∂(volume.restrict (tsupport ζ)), ∀ i j : Fin n,
      |M x i j| ≤ γ₁ * LW := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hζΩ hQ2b, hLW] with x h1 h2
    intro i j
    exact le_trans (h1 i j) (mul_le_mul_of_nonneg_left h2 hγ₁p.le)
  have hC0 : (0 : ℝ) ≤ γ₁ * LW := mul_nonneg hγ₁p.le hLW0
  have hmulb : ∀ a b Ma Mb : ℝ, |a| ≤ Ma → |b| ≤ Mb → |a * b| ≤ Ma * Mb := by
    intro a b Ma Mb ha hb
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)
  -- the three `K`-integrabilities, then their extensions to `Ω`
  have hP1int : IntegrableOn P1 (tsupport ζ) volume := by
    refine hdom _ (Lζ * ((n : ℝ) * ((n : ℝ) * (γ₁ * LW)))) 0
      (by
        rw [hP1def]
        exact haemul _ _ (hζm.pow_const 2)
          (haesum _ fun i => haesum _ fun j =>
            haemul _ _ (haemul _ _ (hMm i j) (hDgcm j)) (hZcm i))) ?_
    filter_upwards [hMb, hZae] with x hMx hZx
    have hin : ∀ i j : Fin n, |M x i j * Dg k x j * Z x i|
        ≤ γ₁ * LW * ‖Dg k x‖ * ‖Dg k x‖ :=
      fun i j => hmulb _ _ _ _ (hmulb _ _ _ _ (hMx i j) (hDgb x j)) (hZx i)
    have h3 : |∑ i, ∑ j, M x i j * Dg k x j * Z x i|
        ≤ (n : ℝ) * ((n : ℝ) * (γ₁ * LW * ‖Dg k x‖ * ‖Dg k x‖)) :=
      hsumbd _ _ fun i => hsumbd _ _ fun j => hin i j
    rw [hP1eq x]
    calc |ζ x ^ 2 * ∑ i, ∑ j, M x i j * Dg k x j * Z x i|
        ≤ Lζ * ((n : ℝ) * ((n : ℝ) * (γ₁ * LW * ‖Dg k x‖ * ‖Dg k x‖))) :=
          hmulb _ _ _ _ (by rw [abs_of_nonneg (sq_nonneg _)]; exact hLζ x) h3
      _ = Lζ * ((n : ℝ) * ((n : ℝ) * (γ₁ * LW))) * ‖Dg k x‖ ^ 2 + 0 * v x ^ 2 := by
          ring
  have hQ0int : IntegrableOn (fun x => ζ x ^ 2 * Q0 x) (tsupport ζ) volume := by
    refine hdom _ (Lζ * ((n : ℝ) * ((n : ℝ) * (γ₁ * LW)))) 0
      (by
        refine haemul _ _ (hζm.pow_const 2) ?_
        have h1 : AEMeasurable (fun x => ∑ i, ∑ j, M x i j * Dg k x j * Dg k x i)
            (volume.restrict (tsupport ζ)) :=
          haesum _ fun i => haesum _ fun j =>
            haemul _ _ (haemul _ _ (hMm i j) (hDgcm j)) (hDgcm i)
        exact h1.congr (Filter.Eventually.of_forall fun x => (hQ0eq x).symm)) ?_
    filter_upwards [hMb] with x hMx
    have hin : ∀ i j : Fin n, |M x i j * Dg k x j * Dg k x i|
        ≤ γ₁ * LW * ‖Dg k x‖ * ‖Dg k x‖ :=
      fun i j => hmulb _ _ _ _ (hmulb _ _ _ _ (hMx i j) (hDgb x j)) (hDgb x i)
    have h3 : |∑ i, ∑ j, M x i j * Dg k x j * Dg k x i|
        ≤ (n : ℝ) * ((n : ℝ) * (γ₁ * LW * ‖Dg k x‖ * ‖Dg k x‖)) :=
      hsumbd _ _ fun i => hsumbd _ _ fun j => hin i j
    rw [hQ0eq x]
    calc |ζ x ^ 2 * ∑ i, ∑ j, M x i j * Dg k x j * Dg k x i|
        ≤ Lζ * ((n : ℝ) * ((n : ℝ) * (γ₁ * LW * ‖Dg k x‖ * ‖Dg k x‖))) :=
          hmulb _ _ _ _ (by rw [abs_of_nonneg (sq_nonneg _)]; exact hLζ x) h3
      _ = Lζ * ((n : ℝ) * ((n : ℝ) * (γ₁ * LW))) * ‖Dg k x‖ ^ 2 + 0 * v x ^ 2 := by
          ring
  have hP2int : IntegrableOn P2 (tsupport ζ) volume := by
    refine hdom _
      (Real.sqrt Lζ * ((n : ℝ) * ((n : ℝ) * (γ₁ * LW * Real.sqrt LDζ))))
      (Real.sqrt Lζ * ((n : ℝ) * ((n : ℝ) * (γ₁ * LW * Real.sqrt LDζ))))
      (by
        rw [hP2def]
        exact haemul _ _ (haemul _ _ (hvm.const_mul 2) hζm)
          (haesum _ fun i => haesum _ fun j =>
            haemul _ _ (haemul _ _ (hMm i j) (hDgcm j)) (hDζm i))) ?_
    filter_upwards [hMb] with x hMx
    have hin : ∀ i j : Fin n, |M x i j * Dg k x j
          * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
        ≤ γ₁ * LW * ‖Dg k x‖ * Real.sqrt LDζ :=
      fun i j => hmulb _ _ _ _ (hmulb _ _ _ _ (hMx i j) (hDgb x j)) (hDζb x i)
    have h3 : |∑ i, ∑ j, M x i j * Dg k x j
          * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
        ≤ (n : ℝ) * ((n : ℝ) * (γ₁ * LW * ‖Dg k x‖ * Real.sqrt LDζ)) :=
      hsumbd _ _ fun i => hsumbd _ _ fun j => hin i j
    have hpre : |2 * v x * ζ x| ≤ 2 * v x * Real.sqrt Lζ := by
      have h2v : (0 : ℝ) ≤ 2 * v x := by linarith [hv0 x]
      rw [abs_mul, abs_of_nonneg h2v]
      exact mul_le_mul_of_nonneg_left (hζb x) h2v
    have hvd : v x * ‖Dg k x‖ ≤ (v x ^ 2 + ‖Dg k x‖ ^ 2) / 2 := by
      have h1 := habs2 (v x) ‖Dg k x‖
      rwa [abs_of_nonneg (hv0 x), abs_of_nonneg (norm_nonneg _)] at h1
    have hcc : (0 : ℝ) ≤ Real.sqrt Lζ * ((n : ℝ) * ((n : ℝ)
        * (γ₁ * LW * Real.sqrt LDζ))) := by positivity
    rw [hP2eq x]
    calc |2 * v x * ζ x * ∑ i, ∑ j, M x i j * Dg k x j
            * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
        ≤ (2 * v x * Real.sqrt Lζ)
          * ((n : ℝ) * ((n : ℝ) * (γ₁ * LW * ‖Dg k x‖ * Real.sqrt LDζ))) :=
          hmulb _ _ _ _ hpre h3
      _ = (Real.sqrt Lζ * ((n : ℝ) * ((n : ℝ) * (γ₁ * LW * Real.sqrt LDζ))))
            * (2 * (v x * ‖Dg k x‖)) := by ring
      _ ≤ (Real.sqrt Lζ * ((n : ℝ) * ((n : ℝ) * (γ₁ * LW * Real.sqrt LDζ))))
            * (2 * ((v x ^ 2 + ‖Dg k x‖ ^ 2) / 2)) :=
          mul_le_mul_of_nonneg_left (by linarith [hvd]) hcc
      _ = Real.sqrt Lζ * ((n : ℝ) * ((n : ℝ) * (γ₁ * LW * Real.sqrt LDζ)))
            * ‖Dg k x‖ ^ 2
          + Real.sqrt Lζ * ((n : ℝ) * ((n : ℝ) * (γ₁ * LW * Real.sqrt LDζ)))
            * v x ^ 2 := by ring
  have hXint : IntegrableOn (fun x => W x * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
      (tsupport ζ) volume := by
    refine hdom _ (LW * Lζ) 0
      (haemul _ _ (haemul _ _ hWm hDgnm) (hζm.pow_const 2)) ?_
    filter_upwards [hLW] with x hWx
    have hW0 : (0 : ℝ) ≤ W x := (hWpos x).le
    calc |W x * ‖Dg k x‖ ^ 2 * ζ x ^ 2|
        = W x * ‖Dg k x‖ ^ 2 * ζ x ^ 2 := abs_of_nonneg (by positivity)
      _ ≤ LW * ‖Dg k x‖ ^ 2 * Lζ := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hWx (sq_nonneg _))
            (hLζ x) (sq_nonneg _) (by positivity)
      _ = LW * Lζ * ‖Dg k x‖ ^ 2 + 0 * v x ^ 2 := by ring
  have hYint : IntegrableOn (fun x => W x * v x ^ 2
      * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2)
      (tsupport ζ) volume := by
    refine hdom _ 0 (LW * LDζ)
      (haemul _ _ (haemul _ _ hWm (hvm.pow_const 2))
        (haesum _ fun i => (hDζm i).pow_const 2)) ?_
    filter_upwards [hLW] with x hWx
    have hW0 : (0 : ℝ) ≤ W x := (hWpos x).le
    have hB0 : (0 : ℝ) ≤ ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    calc |W x * v x ^ 2 * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2|
        = W x * v x ^ 2 * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 :=
          abs_of_nonneg (by positivity)
      _ ≤ LW * v x ^ 2 * LDζ := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hWx (sq_nonneg _))
            (hLDζ x) hB0 (by positivity)
      _ = 0 * ‖Dg k x‖ ^ 2 + LW * LDζ * v x ^ 2 := by ring
  -- the four integrands vanish off the support, so everything lifts to `Ω`
  have hvanP1 : ∀ x, x ∉ tsupport ζ → P1 x = 0 := fun x hx => by
    rw [hP1eq x, hζ0 x hx]; ring
  have hvanP2 : ∀ x, x ∉ tsupport ζ → P2 x = 0 := fun x hx => by
    rw [hP2eq x, hζ0 x hx]; ring
  have hvanX : ∀ x, x ∉ tsupport ζ → W x * ‖Dg k x‖ ^ 2 * ζ x ^ 2 = 0 := fun x hx => by
    rw [hζ0 x hx]; ring
  have hvanQ0 : ∀ x, x ∉ tsupport ζ → ζ x ^ 2 * Q0 x = 0 := fun x hx => by
    rw [hζ0 x hx]; ring
  have hvanY : ∀ x, x ∉ tsupport ζ → W x * v x ^ 2
      * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 = 0 := by
    intro x hx
    have hz : ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hDζ0 x hx i]; ring
    rw [hz, mul_zero]
  have hP1Ω : IntegrableOn P1 Ω volume := hextend _ hvanP1 hP1int
  have hP2Ω : IntegrableOn P2 Ω volume := hextend _ hvanP2 hP2int
  have hXΩ : IntegrableOn (fun x => W x * ‖Dg k x‖ ^ 2 * ζ x ^ 2) Ω volume :=
    hextend _ hvanX hXint
  have hQ0Ω : IntegrableOn (fun x => ζ x ^ 2 * Q0 x) Ω volume :=
    hextend _ hvanQ0 hQ0int
  have hYΩ : IntegrableOn (fun x => W x * v x ^ 2
      * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) Ω volume :=
    hextend _ hvanY hYint
  exact ⟨hvm, hP1Ω, hP2Ω, hXΩ, hQ0Ω, hYΩ⟩
