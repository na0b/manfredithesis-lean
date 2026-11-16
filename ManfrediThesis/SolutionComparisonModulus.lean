import ManfrediThesis.Preamble
open MeasureTheory

/-- The two moduli of §5, built from the modulus `σ` of (Q6) and the Hölder
datum `(α, C₁)`.  These are the thesis' own explicit formulas at l. 1524-1528,
with its `C(p)` and `γ₀` absorbed into the single factor `K = 1/(γ₀ C_M)` and
with the `γ₄` term carrying the constant `4` that §5's Step 5 derives:
`σ₀(t) = K((p-1)/p · σ(t + C₁ t^α) + 4 γ₄ C₁ t^α)` and
`σ₁(t) = K(1/p · σ(t + C₁ t^α))`.

The content is that these are **moduli of continuity on all of `ℝ`**:
nonnegative, bounded, continuous, nondecreasing and vanishing at `0`.  That is
what Lemma 5.1's `σ₂` is required to be, and it is what the absorption step
consumes.  The closed forms are asserted on `(0, 1]` only: off that interval the
functions are extended by `0` below and held at their value at `1` above, which
is what makes them bounded and nondecreasing on all of `ℝ` while changing
nothing below, since only `t ≤ R₁ ≤ 1` is ever used.

This is **not** `FrozenFreezingErrorBound`.  That node is the §4 branch: its
moduli are `K(σ(t + C₁t^α) + C₂σ(t + 2C₁t^α))` and `K(C₂σ(t + 2C₁t^α))`, both
built from `σ` alone, and it is stated together with a variational comparison
whose conclusion is (4.8).  The present node produces different functions --
note the term `4 γ₄ C₁ t^α`, which is *polynomial* in `t` and has no `σ` in it
at all -- and produces nothing else.  That term is the contribution of the
right-hand side `B` through (Q5), and the §4 branch has no right-hand side, so
it has no such term and no `γ₄`. -/
theorem SolutionComparisonModulus :
    ∀ (p α C₁ K γ₄ Cσ : ℝ) (σ : ℝ → ℝ),
      1 < p → 0 < α → α ≤ 1 → 0 ≤ C₁ → 0 < K → 0 < γ₄ →
      Continuous σ → Monotone σ → σ 0 = 0 → (∀ t : ℝ, σ t ≤ Cσ) →
      ∃ σ₀ σ₁ : ℝ → ℝ,
        (∀ t : ℝ, 0 < t → t ≤ 1 →
            σ₀ t = K * ((p - 1) / p * σ (t + C₁ * t ^ α)
              + 4 * γ₄ * C₁ * t ^ α)) ∧
        (∀ t : ℝ, 0 < t → t ≤ 1 → σ₁ t = K * (1 / p * σ (t + C₁ * t ^ α))) ∧
        (∀ t : ℝ, 0 ≤ σ₀ t) ∧ (∀ t : ℝ, 0 ≤ σ₁ t) ∧
        (∃ C : ℝ, ∀ t : ℝ, σ₀ t ≤ C ∧ σ₁ t ≤ C) ∧
        Continuous σ₀ ∧ Continuous σ₁ ∧ Monotone σ₀ ∧ Monotone σ₁ ∧
        σ₀ 0 = 0 ∧ σ₁ 0 = 0 := by
  intro p α C₁ K γ₄ Cσ σ hp hα0 hα1 hC₁ hK hγ₄ hσc hσm hσ0 hσb
  have hp0 : (0:ℝ) < p := by linarith
  have hc0nn : (0:ℝ) ≤ (p - 1) / p := by positivity
  have hc1nn : (0:ℝ) ≤ 1 / p := by positivity
  have hE0 : (0:ℝ) ≤ 4 * γ₄ * C₁ := by positivity
  -- the clamp and the inner argument
  set θ : ℝ → ℝ := fun t => min (max t 0) 1 with hθdef
  have hθ0 : ∀ t, (0:ℝ) ≤ θ t := fun t => le_min (le_max_right _ _) zero_le_one
  have hθ1 : ∀ t, θ t ≤ 1 := fun t => min_le_right _ _
  have hθc : Continuous θ := (continuous_id.max continuous_const).min continuous_const
  have hθm : Monotone θ := fun a b hab => min_le_min (max_le_max hab le_rfl) le_rfl
  have hθid : ∀ t : ℝ, 0 < t → t ≤ 1 → θ t = t := by
    intro t ht ht1
    rw [hθdef]
    simp only
    rw [max_eq_left ht.le, min_eq_left ht1]
  have hθz : θ 0 = 0 := by rw [hθdef]; simp
  -- the α-power of the clamp
  have hpa0 : ∀ t, (0:ℝ) ≤ θ t ^ α := fun t => Real.rpow_nonneg (hθ0 t) _
  have hpac : Continuous fun t => θ t ^ α :=
    hθc.rpow_const fun _ => Or.inr hα0.le
  have hpam : Monotone fun t => θ t ^ α := fun a b hab =>
    Real.rpow_le_rpow (hθ0 a) (hθm hab) hα0.le
  have hpa1 : ∀ t, θ t ^ α ≤ 1 := by
    intro t
    have h := Real.rpow_le_rpow (hθ0 t) (hθ1 t) hα0.le
    rwa [Real.one_rpow] at h
  have hpaz : θ 0 ^ α = 0 := by rw [hθz]; exact Real.zero_rpow (ne_of_gt hα0)
  -- the argument of σ
  set Ψ : ℝ → ℝ := fun t => θ t + C₁ * θ t ^ α with hΨdef
  have hΨ0 : ∀ t, (0:ℝ) ≤ Ψ t := by
    intro t; rw [hΨdef]; simp only; positivity
  have hΨc : Continuous Ψ := hθc.add (hpac.const_mul C₁)
  have hΨm : Monotone Ψ := fun a b hab => by
    rw [hΨdef]; simp only
    exact add_le_add (hθm hab) (mul_le_mul_of_nonneg_left (hpam hab) hC₁)
  have hΨ1 : ∀ t, Ψ t ≤ 1 + C₁ := by
    intro t
    rw [hΨdef]; simp only
    nlinarith [hθ1 t, hpa1 t, hC₁]
  have hΨz : Ψ 0 = 0 := by
    rw [hΨdef]; simp only
    rw [hθz, Real.zero_rpow (ne_of_gt hα0)]
    ring
  -- σ along Ψ
  have hσΨ0 : ∀ t, (0:ℝ) ≤ σ (Ψ t) := by
    intro t
    have := hσm (hΨ0 t)
    rwa [hσ0] at this
  have hσΨc : Continuous fun t => σ (Ψ t) := hσc.comp hΨc
  have hσΨm : Monotone fun t => σ (Ψ t) := fun a b hab => hσm (hΨm hab)
  have hσΨ1 : ∀ t, σ (Ψ t) ≤ σ (1 + C₁) := fun t => hσm (hΨ1 t)
  refine ⟨fun t => K * ((p - 1) / p * σ (Ψ t) + 4 * γ₄ * C₁ * θ t ^ α),
    fun t => K * (1 / p * σ (Ψ t)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht ht1
    have h1 : θ t = t := hθid t ht ht1
    simp only [hΨdef, h1]
  · intro t ht ht1
    have h1 : θ t = t := hθid t ht ht1
    simp only [hΨdef, h1]
  · intro t
    simp only
    have := hσΨ0 t
    have := hpa0 t
    positivity
  · intro t
    simp only
    have := hσΨ0 t
    positivity
  · refine ⟨max (K * ((p - 1) / p * σ (1 + C₁) + 4 * γ₄ * C₁))
      (K * (1 / p * σ (1 + C₁))), fun t => ⟨?_, ?_⟩⟩
    · refine le_trans ?_ (le_max_left _ _)
      refine mul_le_mul_of_nonneg_left ?_ hK.le
      have e1 : (p - 1) / p * σ (Ψ t) ≤ (p - 1) / p * σ (1 + C₁) :=
        mul_le_mul_of_nonneg_left (hσΨ1 t) hc0nn
      have e2 : 4 * γ₄ * C₁ * θ t ^ α ≤ 4 * γ₄ * C₁ :=
        le_trans (mul_le_mul_of_nonneg_left (hpa1 t) hE0) (by linarith)
      linarith
    · refine le_trans ?_ (le_max_right _ _)
      refine mul_le_mul_of_nonneg_left ?_ hK.le
      exact mul_le_mul_of_nonneg_left (hσΨ1 t) hc1nn
  · exact ((hσΨc.const_mul _).add (hpac.const_mul _)).const_mul K
  · exact (hσΨc.const_mul _).const_mul K
  · intro a b hab
    simp only
    refine mul_le_mul_of_nonneg_left ?_ hK.le
    exact add_le_add (mul_le_mul_of_nonneg_left (hσΨm hab) hc0nn)
      (mul_le_mul_of_nonneg_left (hpam hab) hE0)
  · intro a b hab
    simp only
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hσΨm hab) hc1nn) hK.le
  · simp only [hΨz, hσ0, hθz, Real.zero_rpow (ne_of_gt hα0)]
    ring
  · simp only [hΨz, hσ0]
    ring
