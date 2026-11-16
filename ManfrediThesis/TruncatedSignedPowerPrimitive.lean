import ManfrediThesis.Preamble
set_option maxHeartbeats 800000
open MeasureTheory

/-- The truncated primitive of the signed power: for `p ≥ 2` and `μ > 0` there
is a `C¹` function `F : ℝ → ℝ` with a GLOBALLY bounded derivative,
`|F'| ≤ \tfrac p2μ^{\frac p2-1}` everywhere, which agrees with the signed power
`φ(s) = |s|^{\frac p2-1}s` on `[-μ, μ]` and whose derivative there is
`\tfrac p2|s|^{\frac p2-1}`.

Conventions, restated here because a helper inherits none of its parent's.
`φ` is carried as a function variable with its defining equation, in the form
the consumer holds it; every power of a nonnegative real is the real power, and
the exponent `p/2 - 1` is assumed NONNEGATIVE, which is what makes the
truncated integrand continuous at `0`.  Everything is one-dimensional: no
domain, no Sobolev space and no reference to the equation appears.

Why the truncation is needed, and what it is for.  The signed power itself has
an UNBOUNDED derivative, so it is not an admissible outer function for the
scalar chain rule \noderef{WeakGradientC1Comp}, which requires a globally
`C¹` function with a global bound on its derivative.  Truncating at the level
`μ` repairs exactly that, and the agreement clauses are what let the consumer
transport the conclusion back to the untruncated function on the set where
`|g^k| ≤ μ`.  This is the composition that node DOES handle --- one scalar
`W^{1,q}` function against a map `ℝ → ℝ` --- so pm-0013, which refutes using it
for a vector field, does not bite here.

The route.  Put `ψ_μ(t) = \tfrac p2\bigl(\min(|t|, μ)\bigr)^{\frac p2-1}` and
`F(s) = ∫_0^sψ_μ`.  Then `ψ_μ` is continuous, being a constant times the real
power --- with nonnegative exponent --- of the continuous nonnegative
`\min(|t|, μ)`; it is even, since `|{-t}| = |t|`; and it is bounded by
`\tfrac p2μ^{\frac p2-1}`, because `\min(|t|, μ) ≤ μ` and the power is
increasing for a nonnegative exponent.  The fundamental theorem of calculus
(Preamble) therefore makes `F` differentiable with `F' = ψ_μ`, hence `C¹` since
`ψ_μ` is continuous, and the bound on `ψ_μ` is the asserted global bound on
`F'`.  On `[-μ, μ]` one has `\min(|s|, μ) = |s|`, so `F'(s) = \tfrac p2|s|^{\frac p2-1}`
there, which is the fourth clause.  For the third, `F` is odd --- the integral
of an even function from `0` --- and `φ` is odd as well, so it suffices to
compare them on `[0, μ]`: there both vanish at `0` and have the same
derivative, `\tfrac p2 s^{\frac p2-1}`, as `φ(s) = s^{p/2}` for `s > 0`, so they
agree by uniqueness of antiderivatives with a common value at a point. -/
theorem TruncatedSignedPowerPrimitive :
    ∀ (p μ : ℝ) (φ : ℝ → ℝ), 1 < p → 0 < μ → (0:ℝ) ≤ p / 2 - 1 →
      φ 0 = 0 → (∀ s : ℝ, φ (-s) = -φ s) →
      (∀ s : ℝ, 0 < s → φ s = s ^ (p / 2)) →
      ∃ F : ℝ → ℝ,
        ContDiff ℝ 1 F
        ∧ (∀ t : ℝ, |deriv F t| ≤ p / 2 * μ ^ (p / 2 - 1))
        ∧ (∀ s : ℝ, |s| ≤ μ → F s = φ s)
        ∧ (∀ s : ℝ, |s| ≤ μ → deriv F s = p / 2 * |s| ^ (p / 2 - 1)) := by
  intro p μ φ hp hμ hexp0 hφ0 hφneg hφpos
  obtain ⟨ψμ, hψμdef⟩ : ∃ f : ℝ → ℝ,
    f = fun t => p / 2 * (min |t| μ) ^ (p / 2 - 1) := ⟨_, rfl⟩
  have hψμcont : Continuous ψμ := by
    rw [hψμdef]
    exact continuous_const.mul
      ((continuous_abs.min continuous_const).rpow_const fun x => Or.inr hexp0)
  have hψμeven : ∀ t : ℝ, ψμ (-t) = ψμ t := by
    intro t; rw [hψμdef]; simp [abs_neg]
  have hψμbd : ∀ t : ℝ, |ψμ t| ≤ p / 2 * μ ^ (p / 2 - 1) := by
    intro t
    rw [hψμdef]
    have h1 : (0:ℝ) ≤ min |t| μ := le_min (abs_nonneg t) hμ.le
    have h2 : min |t| μ ≤ μ := min_le_right _ _
    have h3 : (min |t| μ) ^ (p / 2 - 1) ≤ μ ^ (p / 2 - 1) :=
      Real.rpow_le_rpow h1 h2 hexp0
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  obtain ⟨F, hFdef⟩ : ∃ f : ℝ → ℝ, f = fun s => ∫ t in (0:ℝ)..s, ψμ t := ⟨_, rfl⟩
  have hFhas : ∀ s : ℝ, HasDerivAt F (ψμ s) s := by
    intro s
    rw [hFdef]
    exact (hψμcont.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hFderiv : deriv F = ψμ := by
    funext s; exact (hFhas s).deriv
  have hFC1 : ContDiff ℝ 1 F :=
    contDiff_one_iff_deriv.2 ⟨fun s => (hFhas s).differentiableAt, by
      rw [hFderiv]; exact hψμcont⟩
  have hFbd : ∀ t : ℝ, |deriv F t| ≤ p / 2 * μ ^ (p / 2 - 1) := by
    intro t; rw [hFderiv]; exact hψμbd t
  -- `F` agrees with `φ` on `[-μ, μ]`
  have hFnn : ∀ s : ℝ, 0 ≤ s → s ≤ μ → F s = φ s := by
    intro s hs0 hsμ
    rcases eq_or_lt_of_le hs0 with hs | hs
    · rw [← hs, hFdef, hφ0]
      simp
    · have hcong : ∀ t ∈ Set.uIcc (0:ℝ) s, ψμ t = p / 2 * t ^ (p / 2 - 1) := by
        intro t ht
        rw [Set.uIcc_of_le hs0] at ht
        rw [hψμdef]
        show p / 2 * (min |t| μ) ^ (p / 2 - 1) = p / 2 * t ^ (p / 2 - 1)
        congr 2
        rw [abs_of_nonneg ht.1]
        exact min_eq_left (le_trans ht.2 hsμ)
      rw [hFdef]
      simp only
      rw [intervalIntegral.integral_congr hcong,
        intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by linarith))]
      rw [show p / 2 - 1 + 1 = p / 2 by ring, Real.zero_rpow (by linarith),
        hφpos s hs]
      field_simp
      ring
  have hFodd : ∀ s : ℝ, F (-s) = -F s := by
    intro s
    rw [hFdef]
    simp only
    have e1 : (∫ t in (0:ℝ)..(-s), ψμ t) = ∫ t in (0:ℝ)..(-s), ψμ (-t) := by
      refine intervalIntegral.integral_congr ?_
      intro t _
      show ψμ t = ψμ (-t)
      rw [hψμeven]
    rw [e1, intervalIntegral.integral_comp_neg (fun t => ψμ t)]
    simp only [neg_neg, neg_zero]
    exact intervalIntegral.integral_symm 0 s
  have hFeq : ∀ s : ℝ, |s| ≤ μ → F s = φ s := by
    intro s hs
    rcases le_or_gt 0 s with h | h
    · exact hFnn s h (le_trans (le_abs_self s) hs |>.trans_eq rfl)
    · have h1 : F (-s) = φ (-s) := by
        refine hFnn (-s) (by linarith) ?_
        rw [abs_of_neg h] at hs
        linarith
      rw [hFodd, hφneg] at h1
      linarith
  have hderivFeq : ∀ s : ℝ, |s| ≤ μ → deriv F s = p / 2 * |s| ^ (p / 2 - 1) := by
    intro s hs
    rw [hFderiv, hψμdef]
    simp only
    rw [min_eq_left hs]
  exact ⟨F, hFC1, hFbd, hFeq, hderivFeq⟩
