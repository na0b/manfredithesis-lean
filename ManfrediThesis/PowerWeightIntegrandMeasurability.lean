import ManfrediThesis.Preamble
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pLocOn
set_option maxHeartbeats 1200000
open MeasureTheory

/-- Measurability on `supp ζ` of every factor of the power-weighted
Caccioppoli argument, and integrability on `Ω` of its two integrands: the
weight powers `w^σ`, the coordinates `g_k`, `(Dg^k)_i` and `Dw_i`, the cut-off
`ζ` and its derivatives `∂_iζ` are all measurable there, finite sums and
products of functions measurable there are measurable there, and both
`w^{\frac{p+t}2-2}\bigl(∑_i(Dw_i)^2\bigr)ζ^2` and
`w^{\frac{p+t}2}|∇ζ|^2` are integrable on `Ω`.

Conventions, restated here because a helper inherits none of its parent's.
`supp ζ` means `tsupport ζ`, the CLOSED support, and `|∇ζ|²` abbreviates
`∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i 1))²`; `g` plays the role of `∇u`
and `Dg k` of `∇D_ku`, with `Dw_i = 2∑_kg_kDg^k_i` the weak derivative of
`w = ε + ‖g‖²`.  Every power of a positive real is the real power with an
arbitrary real exponent, which is pm-0024(1)'s convention and is why the
measurability clause is stated for ALL `σ` at once rather than for the two
exponents the consumer happens to need.  `w'` is a continuous representative of
`w` on `Ω`, agreeing with it almost everywhere, and the local sup bounds for
the powers of the weight are available for `w'`; those bounds, the extension
principle and the integrability of `∑_k‖Dg^k‖²` on `supp ζ` are taken as
hypotheses, so the lemma states exactly what it consumes.

The route.  `g` is almost everywhere strongly measurable on the compact
`supp ζ ⊆ Ω` because `u` is a weak solution with `∇u = g`, so each coordinate
`g_k` is measurable there, and so is `w = ε + ‖g‖²`; composing with the
continuous real power gives every `w^σ` measurable, the base being positive.
Each `(Dg^k)_i` is measurable because `g_k ∈ W^{1,2}_loc(Ω)` with weak gradient
`Dg^k`, and `Dw_i` is then measurable as a constant multiple of a finite sum of
products.  `ζ` and each `∂_iζ` are continuous, hence measurable.  Products and
finite sums of functions measurable on `supp ζ` are measurable there, which is
the pair of closure clauses.  For the two integrands, each is dominated almost
everywhere on `supp ζ` by a constant multiple of `∑_k‖Dg^k‖²` or of a constant:
the first by `L_{w,2}L_ζ·4L_{w,1}` times that sum, using
`∑_i(Dw_i)^2 ≤ 4w∑_k‖Dg^k‖²` and the sup bounds on `w^{\frac{p+t}2-2}`, `ζ²`
and `w`; the second by `L_{w,J}L_{∇ζ}`.  Domination by an integrable function
gives integrability on `supp ζ` (Preamble), and the extension principle carries
both to `Ω`, each integrand carrying a factor `ζ²` or `∇ζ` that vanishes off
`supp ζ`. -/
theorem PowerWeightIntegrandMeasurability :
    ∀ (n : ℕ) (p ε t Lζ Lw2 Lw1 LwJ LDζ : ℝ)
      (Ω : Set (EuclideanSpace ℝ (Fin n)))
      (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (u : EuclideanSpace ℝ (Fin n) → ℝ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (ζ w w' : EuclideanSpace ℝ (Fin n) → ℝ)
      (Dw : EuclideanSpace ℝ (Fin n) → Fin n → ℝ),
      IsWeakSolutionOn n p Ω (fun _ _ h => A h) (fun _ _ _ => 0) u g →
      (∀ i : Fin n, MemW1pLocOn n 2 Ω (fun x => g x i) (Dg i)) →
      ContDiff ℝ (⊤ : ℕ∞) ζ → tsupport ζ ⊆ Ω →
      (∀ x, w x = ε + ‖g x‖ ^ 2) → (∀ x, 0 < w x) →
      (∀ x i, Dw x i = 2 * ∑ k, g x k * Dg k x i) →
      (∀ᵐ x ∂(volume.restrict Ω), w x = w' x) →
      (∀ x, (∑ i, (Dw x i) ^ 2) ≤ 4 * w x * ∑ k, ‖Dg k x‖ ^ 2) →
      IsCompact (tsupport ζ) → MeasurableSet (tsupport ζ) →
      (∀ x, x ∉ tsupport ζ → ζ x = 0) →
      (∀ x, x ∉ tsupport ζ → ∀ i : Fin n,
        fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)) = 0) →
      (∀ F : EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ x, x ∉ tsupport ζ → F x = 0) →
        IntegrableOn F (tsupport ζ) volume → IntegrableOn F Ω volume) →
      IntegrableOn (fun x => ∑ k, ‖Dg k x‖ ^ 2) (tsupport ζ) volume →
      (∀ x, ζ x ^ 2 ≤ Lζ) →
      0 ≤ Lw2 → (∀ x ∈ tsupport ζ, w' x ^ ((p + t) / 2 - 2) ≤ Lw2) →
      0 ≤ Lw1 → (∀ x ∈ tsupport ζ, w' x ^ (1 : ℝ) ≤ Lw1) →
      0 ≤ LwJ → (∀ x ∈ tsupport ζ, w' x ^ ((p + t) / 2) ≤ LwJ) →
      (∀ x, w' x ^ (1 : ℝ) = w' x) →
      (∀ x, ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 ≤ LDζ) →
      AEStronglyMeasurable g (volume.restrict (tsupport ζ))
      ∧ AEMeasurable w (volume.restrict (tsupport ζ))
      ∧ (∀ σ : ℝ, AEMeasurable (fun x => w x ^ σ)
          (volume.restrict (tsupport ζ)))
      ∧ (∀ k : Fin n, AEMeasurable (fun x => g x k)
          (volume.restrict (tsupport ζ)))
      ∧ (∀ k i : Fin n, AEMeasurable (fun x => Dg k x i)
          (volume.restrict (tsupport ζ)))
      ∧ (∀ i : Fin n, AEMeasurable (fun x => Dw x i)
          (volume.restrict (tsupport ζ)))
      ∧ IntegrableOn (fun x =>
          w x ^ ((p + t) / 2 - 2) * (∑ i, (Dw x i) ^ 2) * ζ x ^ 2) Ω volume
      ∧ IntegrableOn (fun x => w x ^ ((p + t) / 2)
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) Ω volume
      ∧ (∀ f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ,
          (∀ i, AEMeasurable (f i) (volume.restrict (tsupport ζ))) →
          AEMeasurable (fun x => ∑ i, f i x) (volume.restrict (tsupport ζ)))
      ∧ AEMeasurable ζ (volume.restrict (tsupport ζ))
      ∧ (∀ i : Fin n, AEMeasurable
          (fun x => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)))
          (volume.restrict (tsupport ζ)))
      ∧ (∀ f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ,
          AEMeasurable f₁ (volume.restrict (tsupport ζ)) →
          AEMeasurable f₂ (volume.restrict (tsupport ζ)) →
          AEMeasurable (fun x => f₁ x * f₂ x) (volume.restrict (tsupport ζ))) := by
  intro n p ε t Lζ Lw2 Lw1 LwJ LDζ Ω A u g Dg ζ w w' Dw hsol hDg hζsm hζΩ hweq hwpos
    hDweq hwae hCS2 hKcpt hKmeas hζ0 hDζ0 hextend hMint hLζ hLw20 hLw2 hLw10 hLw1 hLwJ0
    hLwJ hwrpow1 hLDζ
  have hgK : AEStronglyMeasurable g (volume.restrict (tsupport ζ)) :=
    (hsol.1.2 (tsupport ζ) hKcpt hζΩ).2.1
  have hwm : AEMeasurable w (volume.restrict (tsupport ζ)) := by
    have h1 : AEMeasurable (fun x => ε + ‖g x‖ ^ 2)
        (volume.restrict (tsupport ζ)) :=
      (hgK.aemeasurable.norm.pow_const 2).const_add ε
    exact h1.congr (Filter.Eventually.of_forall fun x => (hweq x).symm)
  have hrpowm : ∀ σ : ℝ, AEMeasurable (fun x => w x ^ σ)
      (volume.restrict (tsupport ζ)) := by
    intro σ
    have heq : ∀ x, w x ^ σ = Real.exp (Real.log (w x) * σ) :=
      fun x => Real.rpow_def_of_pos (hwpos x) σ
    simp only [heq]
    exact (hwm.log.mul_const σ).exp
  have hgcm : ∀ k : Fin n, AEMeasurable (fun x => g x k)
      (volume.restrict (tsupport ζ)) := fun k =>
    ((hDg k).2 (tsupport ζ) hKcpt hζΩ).1.1.aemeasurable
  have hDgcm : ∀ k i : Fin n, AEMeasurable (fun x => Dg k x i)
      (volume.restrict (tsupport ζ)) := by
    intro k i
    have h1 := ((hDg k).2 (tsupport ζ) hKcpt hζΩ).2.1.aemeasurable
    exact ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable).comp_aemeasurable h1
  have hDwm : ∀ i : Fin n, AEMeasurable (fun x => Dw x i)
      (volume.restrict (tsupport ζ)) := by
    intro i
    have hs : AEMeasurable (fun x => ∑ k, g x k * Dg k x i)
        (volume.restrict (tsupport ζ)) := by
      have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin n))
        (fun k (_ : k ∈ Finset.univ) => (hgcm k).mul (hDgcm k i))
      exact h.congr (Filter.Eventually.of_forall fun x => by simp)
    have h1 : AEMeasurable (fun x => 2 * ∑ k, g x k * Dg k x i)
        (volume.restrict (tsupport ζ)) := hs.const_mul 2
    exact h1.congr (Filter.Eventually.of_forall fun x => (hDweq x i).symm)
  have hIint : IntegrableOn (fun x =>
      w x ^ ((p + t) / 2 - 2) * (∑ i, (Dw x i) ^ 2) * ζ x ^ 2) Ω volume := by
    refine hextend _ (fun x hx => by rw [hζ0 x hx]; ring) ?_
    have hsumDw : AEMeasurable (fun x => ∑ i, (Dw x i) ^ 2)
        (volume.restrict (tsupport ζ)) := by
      have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin n))
        (fun i (_ : i ∈ Finset.univ) => (hDwm i).pow_const 2)
      exact h.congr (Filter.Eventually.of_forall fun x => by simp)
    have hIm : AEMeasurable (fun x =>
        w x ^ ((p + t) / 2 - 2) * (∑ i, (Dw x i) ^ 2) * ζ x ^ 2)
        (volume.restrict (tsupport ζ)) := by
      have h1 := ((hrpowm ((p + t) / 2 - 2)).mul hsumDw).mul
        ((hζsm.continuous.measurable.pow_const 2).aemeasurable)
      exact h1.congr (Filter.Eventually.of_forall fun x => by simp)
    refine Integrable.mono' (hMint.const_mul (4 * Lw2 * Lw1 * Lζ))
      hIm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hKmeas,
      ae_restrict_of_ae_restrict_of_subset hζΩ hwae] with x hxK hxw
    have hS0 : (0 : ℝ) ≤ ∑ k, ‖Dg k x‖ ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    have ha0 : (0 : ℝ) ≤ w x ^ ((p + t) / 2 - 2) :=
      le_of_lt (Real.rpow_pos_of_pos (hwpos x) _)
    have ha : w x ^ ((p + t) / 2 - 2) ≤ Lw2 := by rw [hxw]; exact hLw2 x hxK
    have hw1 : w x ≤ Lw1 := by
      rw [hxw, ← hwrpow1 x]
      exact hLw1 x hxK
    have hb0 : (0 : ℝ) ≤ ∑ i, (Dw x i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hb : (∑ i, (Dw x i) ^ 2) ≤ 4 * Lw1 * ∑ k, ‖Dg k x‖ ^ 2 := by
      refine (hCS2 x).trans ?_
      have h1 : 4 * w x ≤ 4 * Lw1 := by linarith
      exact mul_le_mul_of_nonneg_right h1 hS0
    have hc0 : (0 : ℝ) ≤ ζ x ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc w x ^ ((p + t) / 2 - 2) * (∑ i, (Dw x i) ^ 2) * ζ x ^ 2
        ≤ Lw2 * (4 * Lw1 * ∑ k, ‖Dg k x‖ ^ 2) * Lζ := by
          refine mul_le_mul (mul_le_mul ha hb hb0 hLw20) (hLζ x) hc0 ?_
          exact mul_nonneg hLw20 (mul_nonneg (by linarith) hS0)
      _ = 4 * Lw2 * Lw1 * Lζ * ∑ k, ‖Dg k x‖ ^ 2 := by ring
  have hJint : IntegrableOn (fun x => w x ^ ((p + t) / 2)
      * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) Ω volume := by
    refine hextend _ (fun x hx => ?_) ?_
    · have hz : ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hDζ0 x hx i]; ring
      rw [hz, mul_zero]
    · have hJm : AEMeasurable (fun x => w x ^ ((p + t) / 2)
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2)
          (volume.restrict (tsupport ζ)) := by
        have hsD : AEMeasurable (fun x =>
            ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2)
            (volume.restrict (tsupport ζ)) := by
          have h : Measurable (fun x =>
              ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) := by
            refine Finset.measurable_sum _ fun i _ => ?_
            exact (((hζsm.continuous_fderiv (by simp)).clm_apply
              continuous_const).measurable).pow_const 2
          exact h.aemeasurable
        have h1 := (hrpowm ((p + t) / 2)).mul hsD
        exact h1.congr (Filter.Eventually.of_forall fun x => by simp)
      refine Integrable.mono' (integrableOn_const (μ := volume)
        (C := LwJ * LDζ) hKcpt.measure_lt_top.ne) hJm.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem hKmeas,
        ae_restrict_of_ae_restrict_of_subset hζΩ hwae] with x hxK hxw
      have ha0 : (0 : ℝ) ≤ w x ^ ((p + t) / 2) :=
        le_of_lt (Real.rpow_pos_of_pos (hwpos x) _)
      have ha : w x ^ ((p + t) / 2) ≤ LwJ := by rw [hxw]; exact hLwJ x hxK
      have hb0 : (0 : ℝ) ≤ ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul ha (hLDζ x) hb0 hLwJ0
  -- Steps 3-5: substitution into (3.2) and summation over `k`
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
  have haemul : ∀ f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ,
      AEMeasurable f₁ (volume.restrict (tsupport ζ)) →
      AEMeasurable f₂ (volume.restrict (tsupport ζ)) →
      AEMeasurable (fun x => f₁ x * f₂ x) (volume.restrict (tsupport ζ)) := by
    intro f₁ f₂ h1 h2
    exact (h1.mul h2).congr (Filter.Eventually.of_forall fun x => by simp)
  exact ⟨hgK, hwm, hrpowm, hgcm, hDgcm, hDwm, hIint, hJint, haesum, hζm, hDζm,
    haemul⟩
