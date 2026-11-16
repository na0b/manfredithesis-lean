import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
set_option maxHeartbeats 1600000
open MeasureTheory

/-- Integrability on `supp ζ` of the three terms of the power-weighted weak
form and of the `n` test-field pairings: with `w = ε + ‖g‖²`,
`Dw_i = 2∑_k g_kDg^k_i` and `a_{ij}(x) = ∂A_i/∂h_j(g(x))`, each of
`ζ²w^{t/2}∑_k∑_i∑_ja_{ij}Dg^k_jDg^k_i`,
`ζ²w^{t/2-1}∑_i∑_ja_{ij}Dw_jDw_i`,
`ζw^{t/2}∑_i∑_ja_{ij}Dw_j∂_iζ` and, for each `k`,
`∑_i∑_ja_{ij}Dg^k_j(gφ^k)_i` is integrable on `supp ζ`.

Conventions, restated here because a helper inherits none of its parent's.
`supp ζ` means `tsupport ζ`, the CLOSED support; `g` plays the role of `∇u` and
`Dg k` of `∇D_ku`, with `(Dg^k)_j` the index placement pm-0017 records as load
bearing; `∂_iζ` is `fderiv ℝ ζ x (EuclideanSpace.single i 1)`.  Every power of
a positive real is the real power, and the exponent `t` is an arbitrary real,
so `w^{t/2}` and `w^{t/2-1}` are `rpow` and need no sign hypothesis beyond
`w > 0` — this is pm-0024(1)'s convention, kept exactly as printed.  The
continuous representative `w'` of `w` is carried separately, because the
local sup bounds for the powers of the weight are available for `w'` and
transfer to `w` only almost everywhere.  `gφ` is carried as an abstract field
with its pointwise formula as a hypothesis, which is all the pairing term uses.

The route.  `supp ζ` is compact and contained in `Ω`, so the hypothesis on
`w'` supplies finite constants `L_{p/2-1}`, `L_{t/2}`, `L_{t/2-1}` bounding the
three powers of the weight on it, and `(Q2)` bounds `|a_{ij}| ≤ γ₁w^{p/2-1}`
almost everywhere there, hence `|a_{ij}| ≤ γ₁L_{p/2-1}`.  With `ζ² ≤ L_ζ`,
`|∇ζ|² ≤ L_{∇ζ}` and `w' ≤ L_{w}` on `supp ζ`, each of the four integrands is
dominated almost everywhere on `supp ζ` by a CONSTANT multiple of
`∑_m‖Dg^m‖²`: the double and triple sums are controlled by `|∑| ≤ n·max`
applied once per index, the products of two gradient components by
`|ab| ≤ (a² + b²)/2`, and the factor `Dw` by the hypothesis
`∑_i(Dw_i)² ≤ 4w∑_k‖Dg^k‖²`, which is Cauchy--Schwarz for `Dw = 2∑_kg_kDg^k`
and replaces every occurrence of `Dw` by `2\sqrt{w}\bigl(∑_k‖Dg^k‖²\bigr)^{1/2}`
up to constants.  Since `∑_m‖Dg^m‖²` is integrable on `supp ζ` and every
integrand is measurable there — being built from the measurable factors `w^σ`,
`g_k`, `Dg^k_i`, `Dw_i`, `a_{ij}`, `ζ` and `∂_iζ` by products and finite sums —
domination gives integrability (Preamble) for all four. -/
theorem PowerWeightIntegrandIntegrability :
    ∀ (n : ℕ) (p ε γ₀ γ₁ t Lζ Lw1 LDζ : ℝ)
      (Ω : Set (EuclideanSpace ℝ (Fin n)))
      (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (ζ w w' : EuclideanSpace ℝ (Fin n) → ℝ)
      (Dw : EuclideanSpace ℝ (Fin n) → Fin n → ℝ)
      (aij : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
      (gφ : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      0 < ε → 0 < γ₀ → γ₀ ≤ γ₁ →
      EllipticStructureQ12 n p ε γ₀ γ₁ Ω (fun _ _ h => A h) →
      HasCompactSupport ζ → tsupport ζ ⊆ Ω →
      (∀ x, w x = ε + ‖g x‖ ^ 2) → (∀ x, 0 < w x) →
      (∀ x i j, aij x i j
        = (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i) →
      (∀ᵐ x ∂(volume.restrict Ω), w x = w' x) →
      (∀ (σ : ℝ) (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K → K ⊆ Ω →
        ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, w' x ^ σ ≤ L) →
      (∀ x, w' x ^ (1 : ℝ) = w' x) →
      (∀ x, (∑ i, (Dw x i) ^ 2) ≤ 4 * w x * ∑ k, ‖Dg k x‖ ^ 2) →
      IsCompact (tsupport ζ) → MeasurableSet (tsupport ζ) →
      IntegrableOn (fun x => ∑ k, ‖Dg k x‖ ^ 2) (tsupport ζ) volume →
      0 ≤ Lζ → (∀ x, ζ x ^ 2 ≤ Lζ) →
      (∀ x ∈ tsupport ζ, w' x ^ (1 : ℝ) ≤ Lw1) →
      (∀ x, ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 ≤ LDζ) →
      (∀ σ : ℝ, AEMeasurable (fun x => w x ^ σ) (volume.restrict (tsupport ζ))) →
      (∀ k : Fin n, AEMeasurable (fun x => g x k) (volume.restrict (tsupport ζ))) →
      (∀ k i : Fin n, AEMeasurable (fun x => Dg k x i)
        (volume.restrict (tsupport ζ))) →
      (∀ i : Fin n, AEMeasurable (fun x => Dw x i)
        (volume.restrict (tsupport ζ))) →
      (∀ k x i, gφ k x i
        = ζ x ^ 2 * (w x ^ (t / 2) * Dg k x i
            + (t / 2) * g x k * w x ^ (t / 2 - 1) * Dw x i)
          + (g x k * w x ^ (t / 2)) * (2 * ζ x
            * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)))) →
      (∀ i j : Fin n, AEMeasurable (fun x => aij x i j)
        (volume.restrict (tsupport ζ))) →
      (∀ f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ i, AEMeasurable (f i) (volume.restrict (tsupport ζ))) →
        AEMeasurable (fun x => ∑ i, f i x) (volume.restrict (tsupport ζ))) →
      AEMeasurable ζ (volume.restrict (tsupport ζ)) →
      (∀ i : Fin n, AEMeasurable
        (fun x => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)))
        (volume.restrict (tsupport ζ))) →
      IntegrableOn (fun x => ζ x ^ 2 * w x ^ (t / 2)
          * ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i) (tsupport ζ) volume
      ∧ IntegrableOn (fun x => ζ x ^ 2 * w x ^ (t / 2 - 1)
          * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i) (tsupport ζ) volume
      ∧ IntegrableOn (fun x => ζ x * w x ^ (t / 2)
          * ∑ i, ∑ j, aij x i j * Dw x j
            * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)))
          (tsupport ζ) volume
      ∧ (∀ k : Fin n, IntegrableOn
          (fun x => ∑ i, ∑ j, aij x i j * Dg k x j * gφ k x i)
          (tsupport ζ) volume) := by
  intro n p ε γ₀ γ₁ t Lζ Lw1 LDζ Ω A g Dg ζ w w' Dw aij gφ hε hγ₀ hγ hQ hζcs hζΩ hweq
    hwpos haijeq hwae hwpowbd hwrpow1 hCS2 hKcpt hKmeas hMint hLζ0 hLζ hLw1 hLDζ
    hrpowm hgcm hDgcm hDwm hgφeq haijm haesum hζm hDζm
  have hsumbd : ∀ (f : Fin n → ℝ) (M : ℝ), (∀ i, |f i| ≤ M) →
      |∑ i, f i| ≤ (n : ℝ) * M := by
    intro f M hM
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ i, |f i| ≤ ∑ _i : Fin n, M := Finset.sum_le_sum fun i _ => hM i
      _ = (n : ℝ) * M := by simp [mul_comm]
  have haemul : ∀ f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ,
      AEMeasurable f₁ (volume.restrict (tsupport ζ)) →
      AEMeasurable f₂ (volume.restrict (tsupport ζ)) →
      AEMeasurable (fun x => f₁ x * f₂ x) (volume.restrict (tsupport ζ)) := by
    intro f₁ f₂ h1 h2
    exact (h1.mul h2).congr (Filter.Eventually.of_forall fun x => by simp)
  have haeadd : ∀ f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ,
      AEMeasurable f₁ (volume.restrict (tsupport ζ)) →
      AEMeasurable f₂ (volume.restrict (tsupport ζ)) →
      AEMeasurable (fun x => f₁ x + f₂ x) (volume.restrict (tsupport ζ)) := by
    intro f₁ f₂ h1 h2
    exact (h1.add h2).congr (Filter.Eventually.of_forall fun x => by simp)
  -- the bounded factors on the support
  obtain ⟨Lp2, hLp20, hLp2⟩ := hwpowbd (p / 2 - 1) (tsupport ζ) hζcs hζΩ
  obtain ⟨Lt2, hLt20, hLt2⟩ := hwpowbd (t / 2) (tsupport ζ) hζcs hζΩ
  obtain ⟨Lt21, hLt210, hLt21⟩ := hwpowbd (t / 2 - 1) (tsupport ζ) hζcs hζΩ
  have hγ₁p : (0 : ℝ) < γ₁ := lt_of_lt_of_le hγ₀ hγ
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
  have hDgb : ∀ (x : EuclideanSpace ℝ (Fin n)) (k j : Fin n),
      |Dg k x j| ≤ ‖Dg k x‖ := by
    intro x k j
    have hns : ∑ m, (Dg k x m) ^ 2 = ‖Dg k x‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      exact (Finset.sum_congr rfl fun m _ => by rw [Real.norm_eq_abs, sq_abs]).symm
    have h1 : (Dg k x j) ^ 2 ≤ ‖Dg k x‖ ^ 2 := by
      rw [← hns]
      exact Finset.single_le_sum (f := fun m => (Dg k x m) ^ 2)
        (fun m _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg _)] at h2
  have hSk : ∀ (x : EuclideanSpace ℝ (Fin n)) (k : Fin n),
      ‖Dg k x‖ ^ 2 ≤ ∑ m, ‖Dg m x‖ ^ 2 := fun x k =>
    Finset.single_le_sum (f := fun m => ‖Dg m x‖ ^ 2)
      (fun m _ => sq_nonneg _) (Finset.mem_univ k)
  -- the a.e. bounds used by every integrand of Step 5
  have haeb : ∀ᵐ x ∂(volume.restrict (tsupport ζ)),
      (∀ i j, |aij x i j| ≤ γ₁ * Lp2)
      ∧ (∀ k, |g x k| ≤ Real.sqrt Lw1)
      ∧ (w x ^ (t / 2) ≤ Lt2 ∧ (0 : ℝ) ≤ w x ^ (t / 2))
      ∧ (w x ^ (t / 2 - 1) ≤ Lt21 ∧ (0 : ℝ) ≤ w x ^ (t / 2 - 1))
      ∧ (∑ i, (Dw x i) ^ 2) ≤ 4 * Lw1 * ∑ m, ‖Dg m x‖ ^ 2 := by
    filter_upwards [ae_restrict_mem hKmeas,
      ae_restrict_of_ae_restrict_of_subset hζΩ hwae,
      ae_restrict_of_ae hQ.Q2] with x hxK hxw hxQ2
    have hxΩ : x ∈ Ω := hζΩ hxK
    have hwne : ε + ‖g x‖ ^ 2 ≠ 0 := by
      have h1 : (0 : ℝ) ≤ ‖g x‖ ^ 2 := sq_nonneg _
      exact ne_of_gt (by linarith)
    refine ⟨fun i j => ?_, fun k => ?_, ⟨by rw [hxw]; exact hLt2 x hxK,
      le_of_lt (Real.rpow_pos_of_pos (hwpos x) _)⟩,
      ⟨by rw [hxw]; exact hLt21 x hxK,
      le_of_lt (Real.rpow_pos_of_pos (hwpos x) _)⟩, ?_⟩
    · have h1 := hxQ2 hxΩ 0 (g x) i j hwne
      rw [← haijeq x i j] at h1
      refine le_trans h1 ?_
      have h2 : ε + ‖g x‖ ^ 2 = w x := (hweq x).symm
      rw [h2, hxw]
      exact mul_le_mul_of_nonneg_left (hLp2 x hxK) hγ₁p.le
    · have hns : ∑ m, (g x m) ^ 2 = ‖g x‖ ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
        exact (Finset.sum_congr rfl fun m _ => by rw [Real.norm_eq_abs, sq_abs]).symm
      have hgk2 : (g x k) ^ 2 ≤ ‖g x‖ ^ 2 := by
        rw [← hns]
        exact Finset.single_le_sum (f := fun m => (g x m) ^ 2)
          (fun m _ => sq_nonneg _) (Finset.mem_univ k)
      have h1 : ‖g x‖ ^ 2 ≤ Lw1 := by
        have h2 : ‖g x‖ ^ 2 ≤ w x := by rw [hweq x]; linarith
        rw [hxw] at h2
        exact le_trans h2 (by rw [← hwrpow1 x]; exact hLw1 x hxK)
      have h3 := Real.sqrt_le_sqrt (le_trans hgk2 h1)
      rwa [Real.sqrt_sq_eq_abs] at h3
    · refine le_trans (hCS2 x) ?_
      have hS0 : (0 : ℝ) ≤ ∑ m, ‖Dg m x‖ ^ 2 := Finset.sum_nonneg fun m _ => sq_nonneg _
      have hw1 : w x ≤ Lw1 := by
        rw [hxw, ← hwrpow1 x]
        exact hLw1 x hxK
      exact mul_le_mul_of_nonneg_right (by linarith) hS0
  -- the single dominating function of Step 5
  have hdom : ∀ (F : EuclideanSpace ℝ (Fin n) → ℝ) (C₁ C₂ : ℝ),
      AEMeasurable F (volume.restrict (tsupport ζ)) →
      (∀ᵐ x ∂(volume.restrict (tsupport ζ)),
        |F x| ≤ C₁ + C₂ * ∑ m, ‖Dg m x‖ ^ 2) →
      IntegrableOn F (tsupport ζ) volume := by
    intro F C₁ C₂ hFm hFb
    have hD : IntegrableOn (fun x => C₁ + C₂ * ∑ m, ‖Dg m x‖ ^ 2)
        (tsupport ζ) volume :=
      (integrableOn_const (μ := volume) (C := C₁) hKcpt.measure_lt_top.ne).add
        (hMint.const_mul C₂)
    refine Integrable.mono' hD hFm.aestronglyMeasurable ?_
    filter_upwards [hFb] with x hx
    rwa [Real.norm_eq_abs]
  have habs1 : ∀ a : ℝ, |a| ≤ 1 + a ^ 2 := by
    intro a
    have h1 : (0 : ℝ) ≤ (|a| - 1) ^ 2 := sq_nonneg _
    have h2 : (|a| - 1) ^ 2 = a ^ 2 - 2 * |a| + 1 := by rw [sub_sq, sq_abs]; ring
    linarith [h1, h2, sq_nonneg a]
  have habs2 : ∀ a b : ℝ, |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    intro a b
    have h1 : (0 : ℝ) ≤ (|a| - |b|) ^ 2 := sq_nonneg _
    have h2 : (|a| - |b|) ^ 2 = a ^ 2 - 2 * (|a| * |b|) + b ^ 2 := by
      rw [sub_sq, sq_abs, sq_abs]; ring
    linarith [h1, h2]
  have hC0 : (0 : ℝ) ≤ γ₁ * Lp2 := mul_nonneg hγ₁p.le hLp20
  have hsL : (0 : ℝ) ≤ Real.sqrt Lζ := Real.sqrt_nonneg _
  have hsD : (0 : ℝ) ≤ Real.sqrt LDζ := Real.sqrt_nonneg _
  -- integrability of the three integrands of (5)
  have hT1int : IntegrableOn (fun x => ζ x ^ 2 * w x ^ (t / 2)
      * ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i) (tsupport ζ) volume := by
    refine hdom _ 0 (Lζ * Lt2 * ((n : ℝ) * ((n : ℝ) * ((n : ℝ) * (γ₁ * Lp2)))))
      (haemul _ _ (haemul _ _ (hζm.pow_const 2) (hrpowm _))
        (haesum _ fun k => haesum _ fun i => haesum _ fun j =>
          haemul _ _ (haemul _ _ (haijm i j) (hDgcm k j)) (hDgcm k i))) ?_
    filter_upwards [haeb] with x hx
    obtain ⟨hA, -, ⟨hwt2, hwt20⟩, -, -⟩ := hx
    have hinner : ∀ k i j : Fin n,
        |aij x i j * Dg k x j * Dg k x i| ≤ γ₁ * Lp2 * ∑ m, ‖Dg m x‖ ^ 2 := by
      intro k i j
      calc |aij x i j * Dg k x j * Dg k x i|
          = |aij x i j| * |Dg k x j| * |Dg k x i| := by rw [abs_mul, abs_mul]
        _ ≤ γ₁ * Lp2 * ‖Dg k x‖ * ‖Dg k x‖ :=
            mul_le_mul (mul_le_mul (hA i j) (hDgb x k j) (abs_nonneg _) hC0)
              (hDgb x k i) (abs_nonneg _) (mul_nonneg hC0 (norm_nonneg _))
        _ = γ₁ * Lp2 * ‖Dg k x‖ ^ 2 := by ring
        _ ≤ γ₁ * Lp2 * ∑ m, ‖Dg m x‖ ^ 2 := mul_le_mul_of_nonneg_left (hSk x k) hC0
    have h3 : |∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i|
        ≤ (n : ℝ) * ((n : ℝ) * ((n : ℝ) * (γ₁ * Lp2 * ∑ m, ‖Dg m x‖ ^ 2))) :=
      hsumbd _ _ fun k => hsumbd _ _ fun i => hsumbd _ _ fun j => hinner k i j
    have hpre : |ζ x ^ 2 * w x ^ (t / 2)| ≤ Lζ * Lt2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hwt20]
      exact mul_le_mul (hLζ x) hwt2 hwt20 hLζ0
    calc |ζ x ^ 2 * w x ^ (t / 2) * ∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i|
        = |ζ x ^ 2 * w x ^ (t / 2)|
          * |∑ k, ∑ i, ∑ j, aij x i j * Dg k x j * Dg k x i| := abs_mul _ _
      _ ≤ Lζ * Lt2
          * ((n : ℝ) * ((n : ℝ) * ((n : ℝ) * (γ₁ * Lp2 * ∑ m, ‖Dg m x‖ ^ 2)))) :=
          mul_le_mul hpre h3 (abs_nonneg _) (mul_nonneg hLζ0 hLt20)
      _ = 0 + Lζ * Lt2 * ((n : ℝ) * ((n : ℝ) * ((n : ℝ) * (γ₁ * Lp2))))
          * ∑ m, ‖Dg m x‖ ^ 2 := by ring
  have hT2int : IntegrableOn (fun x => ζ x ^ 2 * w x ^ (t / 2 - 1)
      * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i) (tsupport ζ) volume := by
    refine hdom _ 0 (Lζ * Lt21 * ((n : ℝ) * ((n : ℝ) * (γ₁ * Lp2 * (4 * Lw1)))))
      (haemul _ _ (haemul _ _ (hζm.pow_const 2) (hrpowm _))
        (haesum _ fun i => haesum _ fun j =>
          haemul _ _ (haemul _ _ (haijm i j) (hDwm j)) (hDwm i))) ?_
    filter_upwards [haeb] with x hx
    obtain ⟨hA, -, -, ⟨hwt21, hwt210⟩, hDwS⟩ := hx
    have hinner : ∀ i j : Fin n, |aij x i j * Dw x j * Dw x i|
        ≤ γ₁ * Lp2 * (4 * Lw1 * ∑ m, ‖Dg m x‖ ^ 2) := by
      intro i j
      have hab : |Dw x j| * |Dw x i| ≤ ∑ m, (Dw x m) ^ 2 := by
        have h1 : (Dw x j) ^ 2 ≤ ∑ m, (Dw x m) ^ 2 :=
          Finset.single_le_sum (f := fun m => (Dw x m) ^ 2)
            (fun m _ => sq_nonneg _) (Finset.mem_univ j)
        have h2 : (Dw x i) ^ 2 ≤ ∑ m, (Dw x m) ^ 2 :=
          Finset.single_le_sum (f := fun m => (Dw x m) ^ 2)
            (fun m _ => sq_nonneg _) (Finset.mem_univ i)
        linarith [habs2 (Dw x j) (Dw x i)]
      calc |aij x i j * Dw x j * Dw x i|
          = |aij x i j| * (|Dw x j| * |Dw x i|) := by rw [abs_mul, abs_mul, mul_assoc]
        _ ≤ γ₁ * Lp2 * (4 * Lw1 * ∑ m, ‖Dg m x‖ ^ 2) :=
            mul_le_mul (hA i j) (le_trans hab hDwS)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hC0
    have h3 : |∑ i, ∑ j, aij x i j * Dw x j * Dw x i|
        ≤ (n : ℝ) * ((n : ℝ) * (γ₁ * Lp2 * (4 * Lw1 * ∑ m, ‖Dg m x‖ ^ 2))) :=
      hsumbd _ _ fun i => hsumbd _ _ fun j => hinner i j
    have hpre : |ζ x ^ 2 * w x ^ (t / 2 - 1)| ≤ Lζ * Lt21 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hwt210]
      exact mul_le_mul (hLζ x) hwt21 hwt210 hLζ0
    calc |ζ x ^ 2 * w x ^ (t / 2 - 1) * ∑ i, ∑ j, aij x i j * Dw x j * Dw x i|
        = |ζ x ^ 2 * w x ^ (t / 2 - 1)|
          * |∑ i, ∑ j, aij x i j * Dw x j * Dw x i| := abs_mul _ _
      _ ≤ Lζ * Lt21
          * ((n : ℝ) * ((n : ℝ) * (γ₁ * Lp2 * (4 * Lw1 * ∑ m, ‖Dg m x‖ ^ 2)))) :=
          mul_le_mul hpre h3 (abs_nonneg _) (mul_nonneg hLζ0 hLt210)
      _ = 0 + Lζ * Lt21 * ((n : ℝ) * ((n : ℝ) * (γ₁ * Lp2 * (4 * Lw1))))
          * ∑ m, ‖Dg m x‖ ^ 2 := by ring
  have hT3int : IntegrableOn (fun x => ζ x * w x ^ (t / 2)
      * ∑ i, ∑ j, aij x i j * Dw x j
        * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) (tsupport ζ) volume := by
    refine hdom _
      (Real.sqrt Lζ * Lt2 * ((n : ℝ) * ((n : ℝ) * (γ₁ * Lp2 * Real.sqrt LDζ))))
      (Real.sqrt Lζ * Lt2
        * ((n : ℝ) * ((n : ℝ) * (γ₁ * Lp2 * Real.sqrt LDζ * (4 * Lw1)))))
      (haemul _ _ (haemul _ _ hζm (hrpowm _))
        (haesum _ fun i => haesum _ fun j =>
          haemul _ _ (haemul _ _ (haijm i j) (hDwm j)) (hDζm i))) ?_
    filter_upwards [haeb] with x hx
    obtain ⟨hA, -, ⟨hwt2, hwt20⟩, -, hDwS⟩ := hx
    have hS0 : (0 : ℝ) ≤ ∑ m, ‖Dg m x‖ ^ 2 :=
      Finset.sum_nonneg fun m _ => sq_nonneg _
    have hinner : ∀ i j : Fin n,
        |aij x i j * Dw x j * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
          ≤ γ₁ * Lp2 * Real.sqrt LDζ * (1 + 4 * Lw1 * ∑ m, ‖Dg m x‖ ^ 2) := by
      intro i j
      have hDwj : |Dw x j| ≤ 1 + 4 * Lw1 * ∑ m, ‖Dg m x‖ ^ 2 := by
        have h1 : (Dw x j) ^ 2 ≤ ∑ m, (Dw x m) ^ 2 :=
          Finset.single_le_sum (f := fun m => (Dw x m) ^ 2)
            (fun m _ => sq_nonneg _) (Finset.mem_univ j)
        linarith [habs1 (Dw x j), h1, hDwS]
      calc |aij x i j * Dw x j * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
          = |aij x i j| * |Dw x j|
            * |fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))| := by
            rw [abs_mul, abs_mul]
        _ ≤ γ₁ * Lp2 * (1 + 4 * Lw1 * ∑ m, ‖Dg m x‖ ^ 2) * Real.sqrt LDζ :=
            mul_le_mul (mul_le_mul (hA i j) hDwj (abs_nonneg _) hC0)
              (hDζb x i) (abs_nonneg _)
              (mul_nonneg hC0 (le_trans (abs_nonneg _) hDwj))
        _ = γ₁ * Lp2 * Real.sqrt LDζ * (1 + 4 * Lw1 * ∑ m, ‖Dg m x‖ ^ 2) := by ring
    have h3 : |∑ i, ∑ j, aij x i j * Dw x j
          * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
        ≤ (n : ℝ) * ((n : ℝ) * (γ₁ * Lp2 * Real.sqrt LDζ
            * (1 + 4 * Lw1 * ∑ m, ‖Dg m x‖ ^ 2))) :=
      hsumbd _ _ fun i => hsumbd _ _ fun j => hinner i j
    have hpre : |ζ x * w x ^ (t / 2)| ≤ Real.sqrt Lζ * Lt2 := by
      rw [abs_mul, abs_of_nonneg hwt20]
      exact mul_le_mul (hζb x) hwt2 hwt20 hsL
    calc |ζ x * w x ^ (t / 2) * ∑ i, ∑ j, aij x i j * Dw x j
            * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
        = |ζ x * w x ^ (t / 2)|
          * |∑ i, ∑ j, aij x i j * Dw x j
              * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))| := abs_mul _ _
      _ ≤ Real.sqrt Lζ * Lt2 * ((n : ℝ) * ((n : ℝ) * (γ₁ * Lp2 * Real.sqrt LDζ
            * (1 + 4 * Lw1 * ∑ m, ‖Dg m x‖ ^ 2)))) :=
          mul_le_mul hpre h3 (abs_nonneg _) (mul_nonneg hsL hLt20)
      _ = Real.sqrt Lζ * Lt2 * ((n : ℝ) * ((n : ℝ) * (γ₁ * Lp2 * Real.sqrt LDζ)))
          + Real.sqrt Lζ * Lt2
            * ((n : ℝ) * ((n : ℝ) * (γ₁ * Lp2 * Real.sqrt LDζ * (4 * Lw1))))
            * ∑ m, ‖Dg m x‖ ^ 2 := by ring
  have hmulb : ∀ a b Ma Mb : ℝ, |a| ≤ Ma → |b| ≤ Mb → |a * b| ≤ Ma * Mb := by
    intro a b Ma Mb ha hb
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)
  have haddb : ∀ a b Ma Mb : ℝ, |a| ≤ Ma → |b| ≤ Mb → |a + b| ≤ Ma + Mb :=
    fun a b Ma Mb ha hb => le_trans (abs_add_le a b) (add_le_add ha hb)
  have hgφm : ∀ k i : Fin n, AEMeasurable (fun x => gφ k x i)
      (volume.restrict (tsupport ζ)) := by
    intro k i
    have h1 : AEMeasurable (fun x => ζ x ^ 2 * (w x ^ (t / 2) * Dg k x i
        + (t / 2) * g x k * w x ^ (t / 2 - 1) * Dw x i)
        + (g x k * w x ^ (t / 2)) * (2 * ζ x
          * fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))))
        (volume.restrict (tsupport ζ)) :=
      haeadd _ _
        (haemul _ _ (hζm.pow_const 2)
          (haeadd _ _ (haemul _ _ (hrpowm _) (hDgcm k i))
            (haemul _ _ (haemul _ _ ((hgcm k).const_mul (t / 2)) (hrpowm _))
              (hDwm i))))
        (haemul _ _ (haemul _ _ (hgcm k) (hrpowm _))
          (haemul _ _ (hζm.const_mul 2) (hDζm i)))
    exact h1.congr (Filter.Eventually.of_forall fun x => (hgφeq k x i).symm)
  have hIkint : ∀ k : Fin n, IntegrableOn
      (fun x => ∑ i, ∑ j, aij x i j * Dg k x j * gφ k x i)
      (tsupport ζ) volume := by
    intro k
    refine hdom _
      ((n : ℝ) * ((n : ℝ) *
        (γ₁ * Lp2 * Real.sqrt Lw1 * Lt2 * 2 * Real.sqrt Lζ * Real.sqrt LDζ)))
      ((n : ℝ) * ((n : ℝ) *
        (γ₁ * Lp2 * Lζ * Lt2
          + γ₁ * Lp2 * Lζ * (|t| / 2) * Real.sqrt Lw1 * Lt21 * ((1 + 4 * Lw1) / 2)
          + γ₁ * Lp2 * Real.sqrt Lw1 * Lt2 * 2 * Real.sqrt Lζ * Real.sqrt LDζ)))
      (haesum _ fun i => haesum _ fun j =>
        haemul _ _ (haemul _ _ (haijm i j) (hDgcm k j)) (hgφm k i)) ?_
    filter_upwards [haeb] with x hx
    obtain ⟨hA, hg, ⟨hwt2, hwt20⟩, ⟨hwt21, hwt210⟩, hDwS⟩ := hx
    have hq1 : (0 : ℝ) ≤ γ₁ * Lp2 * Lζ * Lt2 :=
      mul_nonneg (mul_nonneg hC0 hLζ0) hLt20
    have hq2 : (0 : ℝ) ≤ γ₁ * Lp2 * Lζ * (|t| / 2) * Real.sqrt Lw1 * Lt21 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hLζ0)
        (by positivity)) (Real.sqrt_nonneg _)) hLt210
    have hq3 : (0 : ℝ)
        ≤ γ₁ * Lp2 * Real.sqrt Lw1 * Lt2 * 2 * Real.sqrt Lζ * Real.sqrt LDζ :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0
        (Real.sqrt_nonneg _)) hLt20) (by norm_num)) hsL) hsD
    have hgφb : ∀ k' i : Fin n, |gφ k' x i|
        ≤ Lζ * (Lt2 * ‖Dg k' x‖ + |t| / 2 * Real.sqrt Lw1 * Lt21 * |Dw x i|)
          + Real.sqrt Lw1 * Lt2 * (2 * Real.sqrt Lζ * Real.sqrt LDζ) := by
      intro k' i
      rw [hgφeq k' x i]
      refine haddb _ _ _ _
        (hmulb _ _ _ _ (by rw [abs_of_nonneg (sq_nonneg _)]; exact hLζ x)
          (haddb _ _ _ _
            (hmulb _ _ _ _ (by rw [abs_of_nonneg hwt20]; exact hwt2) (hDgb x k' i))
            (hmulb _ _ _ _
              (hmulb _ _ _ _
                (hmulb _ _ _ _ (le_of_eq (by rw [abs_div]; norm_num)) (hg k'))
                (by rw [abs_of_nonneg hwt210]; exact hwt21))
              (le_refl |Dw x i|))))
        (hmulb _ _ _ _
          (hmulb _ _ _ _ (hg k') (by rw [abs_of_nonneg hwt20]; exact hwt2))
          (hmulb _ _ _ _
            (hmulb _ _ _ _ (le_of_eq (abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)))
              (hζb x))
            (hDζb x i)))
    have hinner : ∀ i j : Fin n, |aij x i j * Dg k x j * gφ k x i|
        ≤ γ₁ * Lp2 * Real.sqrt Lw1 * Lt2 * 2 * Real.sqrt Lζ * Real.sqrt LDζ
          + (γ₁ * Lp2 * Lζ * Lt2
            + γ₁ * Lp2 * Lζ * (|t| / 2) * Real.sqrt Lw1 * Lt21 * ((1 + 4 * Lw1) / 2)
            + γ₁ * Lp2 * Real.sqrt Lw1 * Lt2 * 2 * Real.sqrt Lζ * Real.sqrt LDζ)
            * ∑ m, ‖Dg m x‖ ^ 2 := by
      intro i j
      have hbd1 : ‖Dg k x‖ ^ 2 ≤ ∑ m, ‖Dg m x‖ ^ 2 := hSk x k
      have hbd2 : ‖Dg k x‖ * |Dw x i|
          ≤ (1 + 4 * Lw1) / 2 * ∑ m, ‖Dg m x‖ ^ 2 := by
        have h1 := habs2 ‖Dg k x‖ (Dw x i)
        rw [abs_of_nonneg (norm_nonneg _)] at h1
        have h2 : (Dw x i) ^ 2 ≤ ∑ m, (Dw x m) ^ 2 :=
          Finset.single_le_sum (f := fun m => (Dw x m) ^ 2)
            (fun m _ => sq_nonneg _) (Finset.mem_univ i)
        linarith [h1, h2, hbd1, hDwS]
      have hbd3 : ‖Dg k x‖ ≤ 1 + ∑ m, ‖Dg m x‖ ^ 2 := by
        have h1 := habs1 ‖Dg k x‖
        rw [abs_of_nonneg (norm_nonneg _)] at h1
        linarith [h1, hbd1]
      calc |aij x i j * Dg k x j * gφ k x i|
          = |aij x i j * Dg k x j| * |gφ k x i| := abs_mul _ _
        _ ≤ (γ₁ * Lp2 * ‖Dg k x‖)
            * (Lζ * (Lt2 * ‖Dg k x‖ + |t| / 2 * Real.sqrt Lw1 * Lt21 * |Dw x i|)
              + Real.sqrt Lw1 * Lt2 * (2 * Real.sqrt Lζ * Real.sqrt LDζ)) :=
            mul_le_mul (hmulb _ _ _ _ (hA i j) (hDgb x k j)) (hgφb k i)
              (abs_nonneg _) (mul_nonneg hC0 (norm_nonneg _))
        _ = γ₁ * Lp2 * Lζ * Lt2 * ‖Dg k x‖ ^ 2
            + γ₁ * Lp2 * Lζ * (|t| / 2) * Real.sqrt Lw1 * Lt21
                * (‖Dg k x‖ * |Dw x i|)
            + γ₁ * Lp2 * Real.sqrt Lw1 * Lt2 * 2 * Real.sqrt Lζ * Real.sqrt LDζ
                * ‖Dg k x‖ := by ring
        _ ≤ γ₁ * Lp2 * Lζ * Lt2 * ∑ m, ‖Dg m x‖ ^ 2
            + γ₁ * Lp2 * Lζ * (|t| / 2) * Real.sqrt Lw1 * Lt21
                * ((1 + 4 * Lw1) / 2 * ∑ m, ‖Dg m x‖ ^ 2)
            + γ₁ * Lp2 * Real.sqrt Lw1 * Lt2 * 2 * Real.sqrt Lζ * Real.sqrt LDζ
                * (1 + ∑ m, ‖Dg m x‖ ^ 2) :=
            add_le_add (add_le_add (mul_le_mul_of_nonneg_left hbd1 hq1)
              (mul_le_mul_of_nonneg_left hbd2 hq2))
              (mul_le_mul_of_nonneg_left hbd3 hq3)
        _ = γ₁ * Lp2 * Real.sqrt Lw1 * Lt2 * 2 * Real.sqrt Lζ * Real.sqrt LDζ
            + (γ₁ * Lp2 * Lζ * Lt2
              + γ₁ * Lp2 * Lζ * (|t| / 2) * Real.sqrt Lw1 * Lt21
                  * ((1 + 4 * Lw1) / 2)
              + γ₁ * Lp2 * Real.sqrt Lw1 * Lt2 * 2 * Real.sqrt Lζ * Real.sqrt LDζ)
              * ∑ m, ‖Dg m x‖ ^ 2 := by ring
    have h3 := hsumbd _ _ fun i => hsumbd _ _ fun j => hinner i j
    calc |∑ i, ∑ j, aij x i j * Dg k x j * gφ k x i|
        ≤ (n : ℝ) * ((n : ℝ) *
          (γ₁ * Lp2 * Real.sqrt Lw1 * Lt2 * 2 * Real.sqrt Lζ * Real.sqrt LDζ
            + (γ₁ * Lp2 * Lζ * Lt2
              + γ₁ * Lp2 * Lζ * (|t| / 2) * Real.sqrt Lw1 * Lt21
                  * ((1 + 4 * Lw1) / 2)
              + γ₁ * Lp2 * Real.sqrt Lw1 * Lt2 * 2 * Real.sqrt Lζ * Real.sqrt LDζ)
              * ∑ m, ‖Dg m x‖ ^ 2)) := h3
      _ = (n : ℝ) * ((n : ℝ) *
            (γ₁ * Lp2 * Real.sqrt Lw1 * Lt2 * 2 * Real.sqrt Lζ * Real.sqrt LDζ))
          + (n : ℝ) * ((n : ℝ) *
            (γ₁ * Lp2 * Lζ * Lt2
              + γ₁ * Lp2 * Lζ * (|t| / 2) * Real.sqrt Lw1 * Lt21
                  * ((1 + 4 * Lw1) / 2)
              + γ₁ * Lp2 * Real.sqrt Lw1 * Lt2 * 2 * Real.sqrt Lζ * Real.sqrt LDζ))
            * ∑ m, ‖Dg m x‖ ^ 2 := by ring
  exact ⟨hT1int, hT2int, hT3int, hIkint⟩
