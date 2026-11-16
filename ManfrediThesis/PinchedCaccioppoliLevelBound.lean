import ManfrediThesis.Preamble
import ManfrediThesis.WeightedCaccioppoliToDeGiorgiLevelBound
import ManfrediThesis.StandardRadialCutoff
import ManfrediThesis.DeGiorgiLevelBound
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.WeakGradientLinear
open MeasureTheory
set_option maxHeartbeats 600000

/-- From a weighted Caccioppoli inequality whose weight `w` is pinched between
two constants of bounded ratio `K` on the set of integration, an instance of the
De Giorgi condition (2.1) with the weight removed.  The constant is
`γ = c * K^(2|s|) * (1 + Λ²)` with `Λ` the gradient constant of the standard
cut-off, so it depends on `n`, `s`, `K` and `c` alone; the pinch constants `κ₁`,
`κ₂` cancel exactly and are bound after it.  The two sign cases are stated as
SEPARATE implications, each carrying its own pinch and its own Caccioppoli
inequality on the set its own conclusion integrates over, because the two sets
`{f > l}` and `{f < l}` are disjoint and a consumer may have the pinch on only
one of them at a given level. -/
theorem PinchedCaccioppoliLevelBound :
    ∀ (n : ℕ) (s K c : ℝ), 1 ≤ n → 1 ≤ K → 0 < c →
      ∃ γ : ℝ, 0 < γ ∧
        ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R Θ l κ₁ κ₂ : ℝ)
          (f : EuclideanSpace ℝ (Fin n) → ℝ)
          (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (w : EuclideanSpace ℝ (Fin n) → ℝ),
          0 < R → 0 < κ₁ → κ₂ ≤ K * κ₁ → Measurable w →
          MemW1pLocOn n 2 (Metric.ball x₀ R) f G →
          (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), |f x| ≤ Θ) →
          ∀ ρ₀ ρ₁ : ℝ, 0 < ρ₀ → ρ₀ < ρ₁ → ρ₁ < R →
            ((∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R ∩ {y | l < f y})),
                κ₁ ≤ w x ∧ w x ≤ κ₂) →
              (∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
                ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
                tsupport ζ ⊆ Metric.ball x₀ R →
                (∫ x in Metric.ball x₀ R ∩ {y | l < f y},
                    w x ^ s * ‖G x‖ ^ 2 * ζ x ^ 2)
                  ≤ c * ∫ x in Metric.ball x₀ R, w x ^ s * max (f x - l) 0 ^ 2
                      * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) →
              DeGiorgiLevelBound n γ f G x₀ l ρ₀ ρ₁)
            ∧ ((∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R ∩ {y | f y < l})),
                κ₁ ≤ w x ∧ w x ≤ κ₂) →
              (∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
                ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
                tsupport ζ ⊆ Metric.ball x₀ R →
                (∫ x in Metric.ball x₀ R ∩ {y | f y < l},
                    w x ^ s * ‖G x‖ ^ 2 * ζ x ^ 2)
                  ≤ c * ∫ x in Metric.ball x₀ R, w x ^ s * max (l - f x) 0 ^ 2
                      * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) →
              DeGiorgiLevelBound n γ (fun x => -f x) (fun x => -G x) x₀ (-l)
                ρ₀ ρ₁) := by
  intro n s K c hn hK hc
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le one_pos hK
  obtain ⟨L, hL0, hSRC⟩ := StandardRadialCutoff n hn
  -- Step 3: the constant
  obtain ⟨γ, hγdef⟩ : ∃ t : ℝ, t = c * K ^ (2 * |s|) * (1 + L) := ⟨_, rfl⟩
  have hKabs : (0:ℝ) < K ^ (2 * |s|) := Real.rpow_pos_of_pos hK0 _
  have hγ0 : 0 < γ := by
    rw [hγdef]
    have h1 : (0:ℝ) < 1 + L := by linarith [hL0]
    exact mul_pos (mul_pos hc hKabs) h1
  refine ⟨γ, hγ0, ?_⟩
  intro x₀ R Θ l κ₁ κ₂ f G w hR hκ₁ hκ₂ hwm hW hΘ ρ₀ ρ₁ hρ₀ hρ01 hρ1R
  have hρ₁ : (0:ℝ) < ρ₁ := lt_trans hρ₀ hρ01
  have hdpos : (0:ℝ) < ρ₁ - ρ₀ := by linarith
  obtain ⟨ζ, hζsm, hζcs, hζts, hζnn, hζle1, hζone, hζgrad⟩ :=
    hSRC x₀ ρ₀ ρ₁ hρ₀ hρ01
  -- Step 2: the pinch
  have hratio : ∀ a b : ℝ, 0 < a → 0 < b → a ≤ K * b → b ≤ K * a →
      a ^ s ≤ K ^ |s| * b ^ s := by
    intro a b ha hb hab hba
    rcases le_or_gt 0 s with hs | hs
    · have h1 : a ^ s ≤ (K * b) ^ s := Real.rpow_le_rpow ha.le hab hs
      rw [Real.mul_rpow hK0.le hb.le] at h1
      rwa [abs_of_nonneg hs]
    · have hbk : b / K ≤ a := by
        rw [div_le_iff₀ hK0]
        linarith [hba]
      have h1 : a ^ s ≤ (b / K) ^ s :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hbk hs.le
      rw [Real.div_rpow hb.le hK0.le] at h1
      have h2 : b ^ s / K ^ s = K ^ |s| * b ^ s := by
        rw [abs_of_neg hs, Real.rpow_neg hK0.le]
        field_simp
      rwa [h2] at h1
  -- Step 4: the `+` implication, for an arbitrary admissible `(F, Γ, ℓ)`
  have step4 : ∀ (F : EuclideanSpace ℝ (Fin n) → ℝ)
      (Γ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (ℓ : ℝ),
      MemW1pLocOn n 2 (Metric.ball x₀ R) F Γ →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), |F x| ≤ Θ) →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R ∩ {y | ℓ < F y})),
          κ₁ ≤ w x ∧ w x ≤ κ₂) →
      (∀ ζ' : EuclideanSpace ℝ (Fin n) → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) ζ' → HasCompactSupport ζ' →
          tsupport ζ' ⊆ Metric.ball x₀ R →
          (∫ x in Metric.ball x₀ R ∩ {y | ℓ < F y},
              w x ^ s * ‖Γ x‖ ^ 2 * ζ' x ^ 2)
            ≤ c * ∫ x in Metric.ball x₀ R, w x ^ s * max (F x - ℓ) 0 ^ 2
                * ∑ i, (fderiv ℝ ζ' x (EuclideanSpace.single i (1 : ℝ))) ^ 2) →
      DeGiorgiLevelBound n γ F Γ x₀ ℓ ρ₀ ρ₁ :=
    WeightedCaccioppoliToDeGiorgiLevelBound n s K c L γ R Θ κ₁ κ₂ ρ₀ ρ₁ x₀ w ζ hc
      hK0 hL0 hR hκ₁ hκ₂ hwm hγdef hKabs hρ01 hρ1R hρ₁ hdpos hratio hζsm hζcs hζts
      hζnn hζle1 hζone hζgrad
  constructor
  · intro h3 h4
    exact step4 f G l hW hΘ h3 h4
  · intro h3 h4
    have hset : {y : EuclideanSpace ℝ (Fin n) | -l < -f y} = {y | f y < l} := by
      ext y; simp only [Set.mem_ofPred_eq, neg_lt_neg_iff]
    refine step4 (fun x => -f x) (fun x => -G x) (-l) ?_ ?_ ?_ ?_
    · have hlin := (WeakGradientLinear n 2 hn (by norm_num) (Metric.ball x₀ R)
        f f G G (-1) 0 0 Metric.isOpen_ball).1 hW hW
      have e1 : (fun x => (-1:ℝ) * f x + (0:ℝ) * f x) = fun x => -f x := by
        funext x; ring
      have e2 : (fun x => (-1:ℝ) • G x + (0:ℝ) • G x) = fun x => -G x := by
        funext x; simp
      rw [e1, e2] at hlin
      exact hlin
    · filter_upwards [hΘ] with x hx
      rwa [abs_neg]
    · rw [hset]
      exact h3
    · intro ζ' hζ'1 hζ'2 hζ'3
      have := h4 ζ' hζ'1 hζ'2 hζ'3
      rw [hset]
      refine le_trans (le_of_eq ?_) (le_trans this (le_of_eq ?_))
      · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show w x ^ s * ‖-G x‖ ^ 2 * ζ' x ^ 2 = w x ^ s * ‖G x‖ ^ 2 * ζ' x ^ 2
        rw [norm_neg]
      · refine congrArg (fun t => c * t) ?_
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show w x ^ s * max (l - f x) 0 ^ 2
            * ∑ i, (fderiv ℝ ζ' x (EuclideanSpace.single i (1:ℝ))) ^ 2
          = w x ^ s * max (-f x - -l) 0 ^ 2
            * ∑ i, (fderiv ℝ ζ' x (EuclideanSpace.single i (1:ℝ))) ^ 2
        congr 2
        ring_nf
