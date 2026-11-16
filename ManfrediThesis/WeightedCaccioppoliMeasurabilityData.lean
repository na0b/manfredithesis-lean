import ManfrediThesis.Preamble
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pLocOn
set_option maxHeartbeats 800000
open MeasureTheory

/-- The measurability and boundedness data of the weighted Caccioppoli
argument, gathered on the compact set `supp ζ`: the weight `W`, the coefficient
entries `M x i j`, the components `(Dg^k)_j` of the second gradient, the
cut-off `ζ` and its derivatives `∂_iζ` are all almost-everywhere measurable
there; products and finite sums of functions measurable there are measurable
there; `‖Dg^k‖²` is integrable there; and `ζ²`, `|∇ζ|²` and `W` each admit a
nonnegative upper bound on that set, the last one almost everywhere.

Conventions, restated here because a helper inherits none of its parent's.
`supp ζ` means `tsupport ζ`, the CLOSED support, and `|∇ζ|²` abbreviates
`∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i 1))²`; `g` plays the role of `∇u`
and `Dg k` of `∇D_ku`, with `(Dg^k)_j` the index placement pm-0017 records as
load bearing.  `w = ε + ‖g‖²` and `W = w^{p/2-1}` are carried as function
variables with their defining equations, and per pm-0024(1) the weight is the
printed real power, so `W` is `rpow` with an arbitrary real exponent `p/2 - 1`.
`w'` is a continuous representative of `w` on `Ω`: `W = w'^{p/2-1}` almost
everywhere there, and the local sup bounds for powers of the weight are
available for `w'`, which is the only way a bound for `W` on a compact subset
is obtained.  `M x i j = ∂A_i/∂h_j(g x)` is the coefficient matrix of the
differentiated equation.

The route.  Being a weak solution with `∇u = g`, `u` has `g` almost everywhere
strongly measurable on every compact subset of `Ω`, and `supp ζ` is such a
subset; so each `g_k` is measurable there, hence so are `w = ε + ‖g‖²` and,
composing with the continuous real power on `(0, ∞)`, the weight `W`.  The
entries `M x i j` are measurable because `A` is `C¹`, so `x ↦ fderiv ℝ A (g x)`
is continuous in `g x` and measurable in `x`.  Each `(Dg^k)_j` is measurable
because `g_k ∈ W^{1,2}_loc(Ω)` with weak gradient `Dg^k`, and the same
membership gives `‖Dg^k‖² ∈ L¹(supp ζ)`.  `ζ` and each `∂_iζ` are continuous,
hence measurable, and the two closure clauses are the standard stability of
measurability under products and finite sums.  For the three bounds: `ζ²` and
`|∇ζ|²` are continuous and vanish off the compact `supp ζ`, so each attains a
finite maximum there and the maximum with `0` is a nonnegative bound valid
everywhere; and `W ≤ L_W` almost everywhere on `supp ζ` follows from the sup
bound for `w'^{p/2-1}` on that compact set together with `W = w'^{p/2-1}`
almost everywhere on `Ω`. -/
theorem WeightedCaccioppoliMeasurabilityData :
    ∀ (n : ℕ) (p ε : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
      (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (u : EuclideanSpace ℝ (Fin n) → ℝ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (ζ : EuclideanSpace ℝ (Fin n) → ℝ) (k : Fin n)
      (w w' W : EuclideanSpace ℝ (Fin n) → ℝ)
      (M : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ),
      IsWeakSolutionOn n p Ω (fun _ _ h => A h) (fun _ _ _ => 0) u g →
      (∀ i : Fin n, MemW1pLocOn n 2 Ω (fun x => g x i) (Dg i)) →
      ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
      (∀ x, w x = ε + ‖g x‖ ^ 2) → (∀ x, 0 < w x) →
      (∀ x, W x = w x ^ (p / 2 - 1)) →
      (∀ᵐ x ∂(volume.restrict Ω), W x = w' x ^ (p / 2 - 1)) →
      (∀ (σ : ℝ) (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K → K ⊆ Ω →
        ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, w' x ^ σ ≤ L) →
      (∀ x i j, M x i j
        = (fderiv ℝ A (g x) (EuclideanSpace.single j (1 : ℝ))) i) →
      ContDiff ℝ 1 (fun h : EuclideanSpace ℝ (Fin n) => A h) →
      (∀ x, x ∉ tsupport ζ → ζ x = 0) →
      (∀ x, x ∉ tsupport ζ → ∀ i : Fin n,
        fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)) = 0) →
      AEMeasurable W (volume.restrict (tsupport ζ))
      ∧ (∀ i j : Fin n, AEMeasurable (fun x => M x i j)
          (volume.restrict (tsupport ζ)))
      ∧ (∀ j : Fin n, AEMeasurable (fun x => Dg k x j)
          (volume.restrict (tsupport ζ)))
      ∧ AEMeasurable ζ (volume.restrict (tsupport ζ))
      ∧ (∀ i : Fin n, AEMeasurable
          (fun x => fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ)))
          (volume.restrict (tsupport ζ)))
      ∧ (∀ f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ,
          AEMeasurable f₁ (volume.restrict (tsupport ζ)) →
          AEMeasurable f₂ (volume.restrict (tsupport ζ)) →
          AEMeasurable (fun x => f₁ x * f₂ x) (volume.restrict (tsupport ζ)))
      ∧ (∀ f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ,
          (∀ i, AEMeasurable (f i) (volume.restrict (tsupport ζ))) →
          AEMeasurable (fun x => ∑ i, f i x) (volume.restrict (tsupport ζ)))
      ∧ IntegrableOn (fun x => ‖Dg k x‖ ^ 2) (tsupport ζ) volume
      ∧ (∃ L : ℝ, 0 ≤ L ∧ ∀ x, ζ x ^ 2 ≤ L)
      ∧ (∃ L : ℝ, 0 ≤ L ∧ ∀ x,
          ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 ≤ L)
      ∧ (∃ L : ℝ, 0 ≤ L
          ∧ ∀ᵐ x ∂(volume.restrict (tsupport ζ)), W x ≤ L) := by
  intro n p ε Ω A u g Dg ζ k w w' W M hsol hDg hζsm hζcs hζΩ hweq hwpos hWeq hWae
    hwpowbd hMeq hAcd hζ0 hDζ0
  have hKcpt : IsCompact (tsupport ζ) := hζcs
  have hKmeas : MeasurableSet (tsupport ζ) := hKcpt.measurableSet
  have hgK : AEStronglyMeasurable g (volume.restrict (tsupport ζ)) :=
    (hsol.1.2 (tsupport ζ) hKcpt hζΩ).2.1
  have hwm : AEMeasurable w (volume.restrict (tsupport ζ)) := by
    have h1 : AEMeasurable (fun x => ε + ‖g x‖ ^ 2) (volume.restrict (tsupport ζ)) :=
      (hgK.aemeasurable.norm.pow_const 2).const_add ε
    exact h1.congr (Filter.Eventually.of_forall fun x => (hweq x).symm)
  have hWm : AEMeasurable W (volume.restrict (tsupport ζ)) := by
    have heq : ∀ x, W x = Real.exp (Real.log (w x) * (p / 2 - 1)) := by
      intro x
      rw [hWeq x]
      exact Real.rpow_def_of_pos (hwpos x) _
    have h1 : AEMeasurable (fun x => Real.exp (Real.log (w x) * (p / 2 - 1)))
        (volume.restrict (tsupport ζ)) := (hwm.log.mul_const _).exp
    exact h1.congr (Filter.Eventually.of_forall fun x => (heq x).symm)
  have hMm : ∀ i j : Fin n, AEMeasurable (fun x => M x i j)
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
      (Filter.Eventually.of_forall fun x => (hMeq x i j).symm)
  have hDgcm : ∀ j : Fin n, AEMeasurable (fun x => Dg k x j)
      (volume.restrict (tsupport ζ)) := by
    intro j
    have h1 := ((hDg k).2 (tsupport ζ) hKcpt hζΩ).2.1.aemeasurable
    exact ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable).comp_aemeasurable h1
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
  have haeadd : ∀ f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ,
      AEMeasurable f₁ (volume.restrict (tsupport ζ)) →
      AEMeasurable f₂ (volume.restrict (tsupport ζ)) →
      AEMeasurable (fun x => f₁ x + f₂ x) (volume.restrict (tsupport ζ)) := by
    intro f₁ f₂ h1 h2
    exact (h1.add h2).congr (Filter.Eventually.of_forall fun x => by simp)
  have haesum : ∀ f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ i, AEMeasurable (f i) (volume.restrict (tsupport ζ))) →
      AEMeasurable (fun x => ∑ i, f i x) (volume.restrict (tsupport ζ)) := by
    intro f hf
    have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin n))
      (fun i (_ : i ∈ Finset.univ) => hf i)
    exact h.congr (Filter.Eventually.of_forall fun x => by simp)
  have hMint : IntegrableOn (fun x => ‖Dg k x‖ ^ 2) (tsupport ζ) volume := by
    have hmem := ((hDg k).2 (tsupport ζ) hKcpt hζΩ).2
    have h1 : Integrable (fun x => ‖Dg k x‖ ^ (ENNReal.ofReal 2).toReal)
        (volume.restrict (tsupport ζ)) :=
      hmem.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp] at h1
    refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
    show ‖Dg k x‖ ^ (2 : ℝ) = ‖Dg k x‖ ^ 2
    rw [← Real.rpow_natCast ‖Dg k x‖ 2]
    norm_num
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
  obtain ⟨LW, hLW0, hLW'⟩ := hwpowbd (p / 2 - 1) (tsupport ζ) hζcs hζΩ
  have hLW : ∀ᵐ x ∂(volume.restrict (tsupport ζ)), W x ≤ LW := by
    filter_upwards [ae_restrict_mem hKmeas,
      ae_restrict_of_ae_restrict_of_subset hζΩ hWae] with x hxK hxW
    rw [hxW]
    exact hLW' x hxK
  exact ⟨hWm, hMm, hDgcm, hζm, hDζm, haemul, haesum, hMint, ⟨Lζ, hLζ0, hLζ⟩,
    ⟨LDζ, hLDζ0, hLDζ⟩, ⟨LW, hLW0, hLW⟩⟩
