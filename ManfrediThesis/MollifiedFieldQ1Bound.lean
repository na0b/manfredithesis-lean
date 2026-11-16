import ManfrediThesis.Preamble
import ManfrediThesis.MollifiedFieldDifferenceQuotientLowerBound
import ManfrediThesis.EllipticStructureQ12
set_option maxHeartbeats 400000
open MeasureTheory

/-- The condition (Q1) for the mollified field at the nondegenerate parameter.

Conventions, restated here because a helper inherits none of its parent's.
`ρ` is the mollifying kernel: smooth, nonnegative, supported in the closed unit
ball and of unit mass, `supp ρ` meaning its CLOSED support.  For `e > 0` the
mollified field is
`A_e(h) = ∫ ρ(z) A(h + √e z) dz − ∫ ρ(z) A(√e z) dz`,
the subtracted constant being the normalisation `A_e(0) = 0`; this is the live
route to the structure conditions at `ε = e`, and it is *not* the perturbation
`A(h) + e^{p/2-1}h`, which does not preserve `γ₀, γ₁`.  Every weight is the
`Real.rpow` power `(e + ‖h‖²)^{p/2-1}`, written exactly as (Q1)/(Q2) print it
and never rewritten as an integer power.  `c₁ ≤ C₂` are the two constants of the
weight sandwich for the scalar kernel
`K(h,e) = ∫ (‖h + √e z‖²)^{p/2-1} ρ(z) dz`, taken here as a hypothesis; `C_M`
is the constant of the monotonicity bound for `A` itself, also a hypothesis, in
the almost-every-`x` form the producing node states it in; `c₄` is the constant
of the two (Q1) cases, constrained only by `c₄ ≤ 2^{p/2-1}c₁` and
`c₄ ≤ 4^{p/2-1}`; and `γ₀' = C_M c₄ γ₀` is the (Q1) constant the parent chooses
for `A_e`.

The conclusion is the (Q1) field of `EllipticStructureQ12 n p e γ₀' γ₁' univ A_e`
verbatim, and in particular it is an almost-everywhere statement in `x`: (Q1)
and (Q2) are a.e.-`x` clauses while the continuity and `C¹` clauses are
everywhere-`x`, and that distinction is load-bearing.  Here `A_e` does not
depend on `x` at all, so the a.e. quantifier is discharged by
`Filter.Eventually.of_forall`; it is kept in the statement so that the parent
can supply this lemma as that field without reshaping it.

The route is the paper's monotonicity argument, run on symmetric difference
quotients.  (Q1) for `A` has been integrated along segments once and for all
into the monotonicity bound
`C_Mγ₀(|a|²+|b|²)^{p/2-1}|a−b|² ≤ (A(a)−A(b),a−b)`,
which is read here at one witness point, legitimate because the field does not
depend on `x`.  Taking `a = h + tξ + √e z` and `b = h − tξ + √e z`, so that
`a − b = 2tξ`, and integrating against `ρ(z)dz` bounds
`4t²C_Mγ₀|ξ|² ∫ρ(z)(|a|²+|b|²)^{p/2-1}dz` by
`2t(A_e(h+tξ)−A_e(h−tξ),ξ)`.  The symmetric quotient on the right converges to
`(dA_e(h)ξ,ξ)` as `t ↓ 0` because `A_e` is differentiable (a hypothesis here,
since it is proved once in the parent for both arms), so it remains to bound the
left-hand integral from below by a multiple of `(e+|h|²)^{p/2-1}`, uniformly for
small `t`.  Two cases do that, and they are where `c₄` comes from: for
`t|ξ| ≤ √(e+|h|²)` the two norms are comparable to `|h|` and the weight
sandwich at `h` gives the factor `2^{p/2-1}c₁` after discarding the smaller of
`|a|,|b|`; otherwise `t|ξ|` dominates and the elementary bound
`|a|²+|b|² ≤ 4(e+|h|²)+2t²|ξ|²` gives the factor `4^{p/2-1}`, the unit mass of
`ρ` turning the integral into that constant.  Passing to the limit in whichever
case is active yields the asserted bound. -/
theorem MollifiedFieldQ1Bound :
    ∀ (n : ℕ) (p : ℝ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ), 2 ≤ n →
      ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) →
      tsupport ρ ⊆ Metric.closedBall 0 1 → (∫ z, ρ z) = 1 →
      ∀ c₁ C₂ : ℝ,
        (∀ (h : EuclideanSpace ℝ (Fin n)) (e : ℝ), 0 < e →
          c₁ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)
              ≤ ∫ z, (‖h + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ρ z
            ∧ (∫ z, (‖h + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ρ z)
              ≤ C₂ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)) →
      ∀ (γ₀ γ₁ : ℝ) (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀ →
        EllipticStructureQ12 n p 0 γ₀ γ₁ Set.univ (fun _ _ h => A h) →
      ∀ CM : ℝ, 0 < CM →
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) →
            ∀ (zz : ℝ) (a b : EuclideanSpace ℝ (Fin n)),
              CM * γ₀ * (0 + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2
                ≤ ∑ i, (A a i - A b i) * (a i - b i)) →
      ∀ c₄ : ℝ, c₄ ≤ (2 : ℝ) ^ (p / 2 - 1) * c₁ → c₄ ≤ (4 : ℝ) ^ (p / 2 - 1) →
      ∀ e : ℝ, 0 < e →
        ContDiff ℝ (⊤ : ℕ∞) (fun h : EuclideanSpace ℝ (Fin n) =>
          (∫ z, ρ z • A (h + Real.sqrt e • z))
            - ∫ z, ρ z • A (Real.sqrt e • z)) →
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) →
            ∀ (zz : ℝ) (h ξ : EuclideanSpace ℝ (Fin n)), e + ‖h‖ ^ 2 ≠ 0 →
              CM * c₄ * γ₀ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖ξ‖ ^ 2
                ≤ ∑ i, (fderiv ℝ (fun h' : EuclideanSpace ℝ (Fin n) =>
                    (∫ z, ρ z • A (h' + Real.sqrt e • z))
                      - ∫ z, ρ z • A (Real.sqrt e • z)) h ξ) i * ξ i := by
  intro n p ρ hn hρsm hρ0 hρsupp hρint c₁ C₂ hsw γ₀ γ₁ A hγ₀ hQ CM hCM0 hmono c₄
    hc₄a hc₄b e he0 hsmooth
  have hAcont : Continuous A := hQ.hcont 0 (Set.mem_univ 0) 0
  have hρcs : HasCompactSupport ρ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 1) isClosed_closure hρsupp
  have hρintble : Integrable ρ volume :=
    hρsm.continuous.integrable_of_hasCompactSupport hρcs
  have hquot : ∀ (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ (⊤ : ℕ∞) G → ∀ h' ξ' : EuclideanSpace ℝ (Fin n),
      Filter.Tendsto (fun t : ℝ => (2 * t)⁻¹ • (G (h' + t • ξ') - G (h' - t • ξ')))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (fderiv ℝ G h' ξ')) := by
    intro G hG h' ξ'
    have hd : HasFDerivAt G (fderiv ℝ G h') h' :=
      (hG.differentiable (by simp)).differentiableAt.hasFDerivAt
    have hγ : HasDerivAt (fun t : ℝ => h' + t • ξ') ξ' (0 : ℝ) := by
      have h1 : HasDerivAt (fun t : ℝ => t • ξ') ξ' (0 : ℝ) := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const ξ'
      simpa using h1.const_add h'
    have hd' : HasFDerivAt G (fderiv ℝ G h') ((fun t : ℝ => h' + t • ξ') 0) := by
      simpa using hd
    have hg1 : HasDerivAt (fun t : ℝ => G (h' + t • ξ')) (fderiv ℝ G h' ξ') (0 : ℝ) :=
      hd'.comp_hasDerivAt 0 hγ
    have hS : Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (G (h' + t • ξ') - G (h' + (0 : ℝ) • ξ')))
        (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (fderiv ℝ G h' ξ')) := by
      have h0 := hasDerivAt_iff_tendsto_slope.1 hg1
      refine h0.congr fun t => ?_
      rw [slope_def_module]
      simp
    have hsub : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
      nhdsWithin_mono _ (fun y hy => ne_of_gt hy)
    have hA := hS.mono_left hsub
    have hnegmap : Filter.Tendsto (fun t : ℝ => -t) (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hc : Filter.Tendsto (fun t : ℝ => -t) (nhds 0) (nhds (-(0 : ℝ))) :=
          continuous_neg.tendsto (0 : ℝ)
        rw [neg_zero] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact fun hc => absurd (neg_eq_zero.1 hc) (ne_of_gt ht)
    have hB := hS.comp hnegmap
    have hsum := (hA.add hB).const_smul ((2 : ℝ)⁻¹)
    rw [show ((2 : ℝ)⁻¹ • (fderiv ℝ G h' ξ' + fderiv ℝ G h' ξ')) = fderiv ℝ G h' ξ' by
      rw [← two_smul ℝ (fderiv ℝ G h' ξ'), smul_smul]; norm_num] at hsum
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htne : t ≠ 0 := ne_of_gt ht
    show (2 : ℝ)⁻¹ • (t⁻¹ • (G (h' + t • ξ') - G (h' + (0 : ℝ) • ξ'))
        + (-t)⁻¹ • (G (h' + (-t) • ξ') - G (h' + (0 : ℝ) • ξ')))
      = (2 * t)⁻¹ • (G (h' + t • ξ') - G (h' - t • ξ'))
    have hz : h' + (0 : ℝ) • ξ' = h' := by simp
    have hnn : h' + (-t) • ξ' = h' - t • ξ' := by rw [neg_smul, ← sub_eq_add_neg]
    rw [hz, hnn, inv_neg, neg_smul, ← smul_neg, ← smul_add,
      show (G (h' + t • ξ') - G h') + -(G (h' - t • ξ') - G h')
        = G (h' + t • ξ') - G (h' - t • ξ') from by abel,
      smul_smul, mul_inv]
  refine Filter.Eventually.of_forall (fun x _ zz h ξ _ => ?_)
  show CM * c₄ * γ₀ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖ξ‖ ^ 2
    ≤ ∑ i, (fderiv ℝ (fun h' : EuclideanSpace ℝ (Fin n) =>
        (∫ z, ρ z • A (h' + Real.sqrt e • z))
          - ∫ z, ρ z • A (Real.sqrt e • z)) h ξ) i * ξ i
  rcases eq_or_ne ξ 0 with hξ0 | hξ0
  · subst hξ0
    simp
  have hξn : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.2 hξ0
  have hW0 : (0 : ℝ) < e + ‖h‖ ^ 2 := by nlinarith [sq_nonneg ‖h‖]
  have hWq : (0 : ℝ) < (e + ‖h‖ ^ 2) ^ (p / 2 - 1) := Real.rpow_pos_of_pos hW0 _
  have hIP : ∀ v : EuclideanSpace ℝ (Fin n), (∑ i, v i * ξ i) = (innerSL ℝ ξ) v := by
    intro v
    show (∑ i, v i * ξ i) = inner ℝ ξ v
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  rw [hIP]
  -- (MA): the monotonicity bound of `A`, read at every pair
  have hneb : Filter.NeBot (ae (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    refine ae_neBot.2 (fun hc => ?_)
    have hpos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))) Set.univ :=
      isOpen_univ.measure_pos volume ⟨0, trivial⟩
    rw [hc] at hpos
    simp at hpos
  obtain ⟨x₀, hx₀⟩ :=
    hmono.exists
  have hMA : ∀ a b : EuclideanSpace ℝ (Fin n),
      CM * γ₀ * (0 + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2
        ≤ ∑ i, (A a i - A b i) * (a i - b i) := hx₀ (Set.mem_univ x₀) 0
  -- integrability of the two families of integrands
  have hAint : ∀ h' : EuclideanSpace ℝ (Fin n),
      Integrable (fun z => ρ z • A (h' + Real.sqrt e • z)) volume := by
    intro h'
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hρsm.continuous.smul (hAcont.comp (by fun_prop))
    · refine hρcs.mono (fun z hz => ?_)
      simp only [Function.mem_support, ne_eq] at hz ⊢
      intro hc
      exact hz (by rw [hc, zero_smul])
  have hbasepos : ∀ (t : ℝ), 0 < t → ∀ z : EuclideanSpace ℝ (Fin n),
      0 < 2 * ‖h + Real.sqrt e • z‖ ^ 2 + 2 * t ^ 2 * ‖ξ‖ ^ 2 := by
    intro t ht z
    have h1 : (0 : ℝ) ≤ ‖h + Real.sqrt e • z‖ ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) < 2 * t ^ 2 * ‖ξ‖ ^ 2 := by positivity
    linarith
  have hLint : ∀ t : ℝ, 0 < t →
      Integrable (fun z => (2 * ‖h + Real.sqrt e • z‖ ^ 2
        + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) * ρ z) volume := by
    intro t ht
    have hbasec : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
        2 * ‖h + Real.sqrt e • z‖ ^ 2 + 2 * t ^ 2 * ‖ξ‖ ^ 2) := by fun_prop
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (hbasec.rpow_const
        (fun z => Or.inl (ne_of_gt (hbasepos t ht z)))).mul hρsm.continuous
    · refine hρcs.mono (fun z hz => ?_)
      simp only [Function.mem_support, ne_eq] at hz ⊢
      intro hc
      exact hz (by rw [hc, mul_zero])
  have hRint : ∀ t : ℝ,
      Integrable (fun z => ((innerSL ℝ ξ)
        (A (h + t • ξ + Real.sqrt e • z) - A (h - t • ξ + Real.sqrt e • z)))
          * ρ z) volume := by
    intro t
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · refine Continuous.mul ?_ hρsm.continuous
      exact (innerSL ℝ ξ).continuous.comp
        (((hAcont.comp (by fun_prop)).sub (hAcont.comp (by fun_prop))))
    · refine hρcs.mono (fun z hz => ?_)
      simp only [Function.mem_support, ne_eq] at hz ⊢
      intro hc
      exact hz (by rw [hc, mul_zero])
  -- the inequality of (Q1-t), for every `t ∈ (0,1]`
  have hkey : ∀ t : ℝ, 0 < t →
      CM * γ₀ * ‖ξ‖ ^ 2 * (∫ z, (2 * ‖h + Real.sqrt e • z‖ ^ 2
          + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) * ρ z)
        ≤ (2 * t)⁻¹ * (innerSL ℝ ξ)
            ((fun h' : EuclideanSpace ℝ (Fin n) =>
                (∫ z, ρ z • A (h' + Real.sqrt e • z))
                  - ∫ z, ρ z • A (Real.sqrt e • z)) (h + t • ξ)
              - (fun h' : EuclideanSpace ℝ (Fin n) =>
                (∫ z, ρ z • A (h' + Real.sqrt e • z))
                  - ∫ z, ρ z • A (Real.sqrt e • z)) (h - t • ξ)) :=
    MollifiedFieldDifferenceQuotientLowerBound n p CM γ₀ e ρ A h ξ hρ0 hIP hMA
      hAint hLint hRint
  -- the limit `t ↓ 0`
  have hvec := hquot _ hsmooth h ξ
  have hD : Filter.Tendsto (fun t : ℝ => (2 * t)⁻¹ * (innerSL ℝ ξ)
        ((fun h' : EuclideanSpace ℝ (Fin n) =>
            (∫ z, ρ z • A (h' + Real.sqrt e • z))
              - ∫ z, ρ z • A (Real.sqrt e • z)) (h + t • ξ)
          - (fun h' : EuclideanSpace ℝ (Fin n) =>
            (∫ z, ρ z • A (h' + Real.sqrt e • z))
              - ∫ z, ρ z • A (Real.sqrt e • z)) (h - t • ξ)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((innerSL ℝ ξ) (fderiv ℝ (fun h' : EuclideanSpace ℝ (Fin n) =>
        (∫ z, ρ z • A (h' + Real.sqrt e • z))
          - ∫ z, ρ z • A (Real.sqrt e • z)) h ξ))) := by
    have h1 := ((innerSL ℝ ξ).continuous.tendsto _).comp hvec
    refine h1.congr fun t => ?_
    simp only [Function.comp_apply, map_smul, smul_eq_mul]
  have hcoef0 : (0 : ℝ) ≤ CM * γ₀ * ‖ξ‖ ^ 2 :=
    mul_nonneg (mul_nonneg hCM0.le hγ₀.le) (sq_nonneg _)
  rcases le_or_gt 0 (p / 2 - 1) with hq | hq
  · -- `p ≥ 2`: the sandwich bounds `L(t)` below uniformly in `t`
    have hKint : Integrable
        (fun z => (‖h + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ρ z) volume := by
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · have hbc : Continuous
            (fun z : EuclideanSpace ℝ (Fin n) => ‖h + Real.sqrt e • z‖ ^ 2) := by
          fun_prop
        exact (hbc.rpow_const (fun z => Or.inr hq)).mul hρsm.continuous
      · refine hρcs.mono (fun z hz => ?_)
        simp only [Function.mem_support, ne_eq] at hz ⊢
        intro hc
        exact hz (by rw [hc, mul_zero])
    have hlow : ∀ t : ℝ, 0 < t →
        c₄ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)
          ≤ ∫ z, (2 * ‖h + Real.sqrt e • z‖ ^ 2
            + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) * ρ z := by
      intro t ht
      have hptw2 : ∀ z : EuclideanSpace ℝ (Fin n),
          (2 : ℝ) ^ (p / 2 - 1)
              * ((‖h + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ρ z)
            ≤ (2 * ‖h + Real.sqrt e • z‖ ^ 2
              + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) * ρ z := by
        intro z
        have hb1 : (2 * ‖h + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)
            ≤ (2 * ‖h + Real.sqrt e • z‖ ^ 2
              + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) := by
          refine Real.rpow_le_rpow (by positivity) ?_ hq
          nlinarith [sq_nonneg t, sq_nonneg ‖ξ‖]
        have hb2 : (2 * ‖h + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)
            = (2 : ℝ) ^ (p / 2 - 1)
              * (‖h + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) :=
          Real.mul_rpow (by norm_num) (sq_nonneg _)
        rw [← mul_assoc, ← hb2]
        exact mul_le_mul_of_nonneg_right hb1 (hρ0 z)
      have hint2 := integral_mono (hKint.const_mul ((2 : ℝ) ^ (p / 2 - 1)))
        (hLint t ht) hptw2
      rw [integral_const_mul] at hint2
      obtain ⟨hsw1, -⟩ := hsw h e he0
      calc c₄ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)
          ≤ ((2 : ℝ) ^ (p / 2 - 1) * c₁) * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) :=
            mul_le_mul_of_nonneg_right hc₄a hWq.le
        _ = (2 : ℝ) ^ (p / 2 - 1) * (c₁ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)) := by ring
        _ ≤ (2 : ℝ) ^ (p / 2 - 1)
            * ∫ z, (‖h + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ρ z :=
            mul_le_mul_of_nonneg_left hsw1 (Real.rpow_nonneg (by norm_num) _)
        _ ≤ _ := hint2
    refine ge_of_tendsto hD ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    calc CM * c₄ * γ₀ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖ξ‖ ^ 2
        = CM * γ₀ * ‖ξ‖ ^ 2 * (c₄ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)) := by ring
      _ ≤ CM * γ₀ * ‖ξ‖ ^ 2
          * ∫ z, (2 * ‖h + Real.sqrt e • z‖ ^ 2
            + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) * ρ z :=
          mul_le_mul_of_nonneg_left (hlow t ht') hcoef0
      _ ≤ _ := hkey t ht'
  · -- `1 < p < 2`: the trivial bound, with a limit in `t`
    have hzb : ∀ z : EuclideanSpace ℝ (Fin n), ρ z ≠ 0 →
        ‖h + Real.sqrt e • z‖ ^ 2 ≤ 2 * (e + ‖h‖ ^ 2) := by
      intro z hz
      have hmem : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
        hρsupp (subset_tsupport _ (by simpa [Function.mem_support] using hz))
      rw [Metric.mem_closedBall, dist_zero_right] at hmem
      have ht0 : 0 < Real.sqrt e := Real.sqrt_pos.2 he0
      have hsq : Real.sqrt e ^ 2 = e := Real.sq_sqrt he0.le
      have h1 : ‖h + Real.sqrt e • z‖ ≤ ‖h‖ + Real.sqrt e := by
        calc ‖h + Real.sqrt e • z‖ ≤ ‖h‖ + ‖Real.sqrt e • z‖ := norm_add_le _ _
          _ ≤ ‖h‖ + Real.sqrt e := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
              nlinarith [ht0.le, norm_nonneg z]
      have h2 : ‖h + Real.sqrt e • z‖ ^ 2 ≤ (‖h‖ + Real.sqrt e) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [h2, sq_nonneg (‖h‖ - Real.sqrt e), hsq]
    have hlow : ∀ t : ℝ, 0 < t →
        (4 * (e + ‖h‖ ^ 2) + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1)
          ≤ ∫ z, (2 * ‖h + Real.sqrt e • z‖ ^ 2
            + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) * ρ z := by
      intro t ht
      have hptw2 : ∀ z : EuclideanSpace ℝ (Fin n),
          (4 * (e + ‖h‖ ^ 2) + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) * ρ z
            ≤ (2 * ‖h + Real.sqrt e • z‖ ^ 2
              + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) * ρ z := by
        intro z
        by_cases hz : ρ z = 0
        · rw [hz, mul_zero, mul_zero]
        · refine mul_le_mul_of_nonneg_right ?_ (hρ0 z)
          refine Real.rpow_le_rpow_of_nonpos (hbasepos t ht z) ?_ hq.le
          have hzz := hzb z hz
          linarith
      have hint2 := integral_mono
        (hρintble.const_mul ((4 * (e + ‖h‖ ^ 2) + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1)))
        (hLint t ht) hptw2
      rw [integral_const_mul, hρint, mul_one] at hint2
      exact hint2
    have hΦ : Filter.Tendsto (fun t : ℝ => CM * γ₀ * ‖ξ‖ ^ 2
          * (4 * (e + ‖h‖ ^ 2) + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (CM * γ₀ * ‖ξ‖ ^ 2 * (4 * (e + ‖h‖ ^ 2)) ^ (p / 2 - 1))) := by
      have hbc : Continuous (fun t : ℝ =>
          (4 * (e + ‖h‖ ^ 2) + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1)) := by
        refine Continuous.rpow_const (by fun_prop) (fun t => Or.inl (ne_of_gt ?_))
        nlinarith [sq_nonneg t, sq_nonneg ‖ξ‖, hW0]
      have h2 := (hbc.tendsto 0).mono_left
        (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
      rw [show (4 * (e + ‖h‖ ^ 2) + 2 * (0 : ℝ) ^ 2 * ‖ξ‖ ^ 2)
        = 4 * (e + ‖h‖ ^ 2) from by ring] at h2
      exact h2.const_mul _
    have hfin : CM * γ₀ * ‖ξ‖ ^ 2 * (4 * (e + ‖h‖ ^ 2)) ^ (p / 2 - 1)
        ≤ (innerSL ℝ ξ) (fderiv ℝ (fun h' : EuclideanSpace ℝ (Fin n) =>
          (∫ z, ρ z • A (h' + Real.sqrt e • z))
            - ∫ z, ρ z • A (Real.sqrt e • z)) h ξ) := by
      refine le_of_tendsto_of_tendsto hΦ hD ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0 : ℝ) < t := ht
      calc CM * γ₀ * ‖ξ‖ ^ 2
            * (4 * (e + ‖h‖ ^ 2) + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1)
          ≤ CM * γ₀ * ‖ξ‖ ^ 2
            * ∫ z, (2 * ‖h + Real.sqrt e • z‖ ^ 2
              + 2 * t ^ 2 * ‖ξ‖ ^ 2) ^ (p / 2 - 1) * ρ z :=
            mul_le_mul_of_nonneg_left (hlow t ht') hcoef0
        _ ≤ _ := hkey t ht'
    have h4 : (4 * (e + ‖h‖ ^ 2)) ^ (p / 2 - 1)
        = (4 : ℝ) ^ (p / 2 - 1) * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) :=
      Real.mul_rpow (by norm_num) hW0.le
    calc CM * c₄ * γ₀ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖ξ‖ ^ 2
        = CM * γ₀ * ‖ξ‖ ^ 2 * (c₄ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)) := by ring
      _ ≤ CM * γ₀ * ‖ξ‖ ^ 2
          * ((4 : ℝ) ^ (p / 2 - 1) * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hc₄b hWq.le) hcoef0
      _ = CM * γ₀ * ‖ξ‖ ^ 2 * (4 * (e + ‖h‖ ^ 2)) ^ (p / 2 - 1) := by rw [h4]
      _ ≤ _ := hfin
