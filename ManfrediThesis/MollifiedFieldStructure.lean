import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.MollifiedFieldQ1Bound
import ManfrediThesis.MollifiedFieldQ2Bound
import ManfrediThesis.StructureMonotonicityBound
import ManfrediThesis.SegmentWeightIntegrable
import ManfrediThesis.WeightSandwich
open MeasureTheory
set_option maxHeartbeats 200000

/-- Mollification transfers the structure conditions from the degenerate
parameter `ε = 0` to the nondegenerate parameter `ε = e`, with a bounded ratio:
if `A` satisfies (Q1)--(Q2) at `ε = 0` with `γ₁ ≤ r γ₀`, then the mollified
field `h ↦ ∫ ρ(z) A(h + √e z) dz − ∫ ρ(z) A(√e z) dz` satisfies (Q1)--(Q2) at
`ε = e` with constants whose ratio is at most a number `r'` chosen before the
field and the parameter. -/
theorem MollifiedFieldStructure :
    ∀ (n : ℕ) (p r : ℝ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ),
      2 ≤ n → 1 < p → 0 < r →
      ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) →
      tsupport ρ ⊆ Metric.closedBall 0 1 →
      (∫ z, ρ z) = 1 →
      (∃ κ : ℝ, 0 < κ ∧
        ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (7 / 8), κ ≤ ρ z) →
      ∃ r' : ℝ, 0 < r' ∧
        ∀ (γ₀ γ₁ : ℝ) (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 < γ₀ → γ₁ ≤ r * γ₀ →
          EllipticStructureQ12 n p 0 γ₀ γ₁ Set.univ (fun _ _ h => A h) →
          ∀ e : ℝ, 0 < e → e ≤ 1 →
            ∃ γ₀' γ₁' : ℝ, 0 < γ₀' ∧ γ₁' ≤ r' * γ₀' ∧
              EllipticStructureQ12 n p e γ₀' γ₁' Set.univ
                (fun _ _ h => (∫ z, ρ z • A (h + Real.sqrt e • z))
                  - ∫ z, ρ z • A (Real.sqrt e • z)) := by
  intro n p r ρ hn hp hr hρsm hρ0 hρsupp hρint hκ
  -- the constant of the monotonicity bound, from `n`, `p` and `r` alone
  obtain ⟨CM, hCM0, hCM⟩ := StructureMonotonicityBound n p r hn hp hr
  -- the two constants of the weight sandwich, from `n`, `p` and `ρ` alone
  obtain ⟨c₁, C₂, hc₁0, hc₁C₂, hsw⟩ :=
    WeightSandwich n p ρ hn hp hρsm hρ0 hρsupp hρint hκ
  have hC₂0 : (0 : ℝ) < C₂ := lt_of_lt_of_le hc₁0 hc₁C₂
  -- the constant `c₄` of the two (Q1) cases, and `c₀ = C_M c₄`
  obtain ⟨c₄, hc₄0, hc₄a, hc₄b⟩ : ∃ c₄ : ℝ, 0 < c₄ ∧
      c₄ ≤ (2 : ℝ) ^ (p / 2 - 1) * c₁ ∧ c₄ ≤ (4 : ℝ) ^ (p / 2 - 1) := by
    refine ⟨min ((2 : ℝ) ^ (p / 2 - 1) * c₁) ((4 : ℝ) ^ (p / 2 - 1)),
      lt_min (by positivity) (Real.rpow_pos_of_pos (by norm_num) _),
      min_le_left _ _, min_le_right _ _⟩
  have hc₀0 : (0 : ℝ) < CM * c₄ := by positivity
  refine ⟨C₂ * r / (CM * c₄), by positivity, ?_⟩
  intro γ₀ γ₁ A hγ₀ hγ₁r hQ e he0 he1
  refine ⟨CM * c₄ * γ₀, C₂ * γ₁, by positivity, ?_, ?_⟩
  · -- the ratio bound: `γ₁^{(e)} ≤ r' γ₀^{(e)}`
    have hrw : C₂ * r / (CM * c₄) * (CM * c₄ * γ₀) = C₂ * (r * γ₀) := by
      field_simp
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hγ₁r hC₂0.le
  · -- the `EllipticStructureQ12` bundle for `A_e` at `ε = e`
    -- The convolution paragraph of the `.tex`: `A_e = A * σ − (A * σ)(0)` with
    -- `σ(w) = e^{-n/2} ρ(−w/√e)`, so `A_e` is `C^∞` by the Preamble item on
    -- convolution with a smooth compactly supported kernel, applied to each
    -- component with `w = A^i`, which is in `L^1_loc(ℝⁿ)` because `A` is
    -- continuous (clause `hcont` of `hQ`).  Hypotheses available at this hole:
    -- `hQ` (the bundle for `A` at `ε = 0`), `hρsm`, `hρ0`, `hρsupp`, `hρint`,
    -- `he0 : 0 < e`, `he1 : e ≤ 1`, and the defining formula in the goal.
    have hAcont : Continuous A := hQ.hcont 0 (Set.mem_univ 0) 0
    have ht : 0 < Real.sqrt e := Real.sqrt_pos.2 he0
    have hρcs : HasCompactSupport ρ :=
      IsCompact.of_isClosed_subset (isCompact_closedBall 0 1) isClosed_closure hρsupp
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun h : EuclideanSpace ℝ (Fin n) =>
          (∫ z, ρ z • A (h + Real.sqrt e • z))
            - ∫ z, ρ z • A (Real.sqrt e • z)) := by
      have hρ'sm : ContDiff ℝ (⊤ : ℕ∞) (fun z : EuclideanSpace ℝ (Fin n) => ρ (-z)) :=
        hρsm.comp contDiff_neg
      have hρ'cs : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin n) => ρ (-z)) :=
        hρcs.comp_homeomorph (Homeomorph.neg (EuclideanSpace ℝ (Fin n)))
      have hBcont : Continuous
          (fun y : EuclideanSpace ℝ (Fin n) => A (Real.sqrt e • y)) :=
        hAcont.comp (continuous_const_smul _)
      have hBloc : LocallyIntegrable
          (fun y : EuclideanSpace ℝ (Fin n) => A (Real.sqrt e • y)) volume :=
        hBcont.locallyIntegrable
      have hconv : ContDiff ℝ (⊤ : ℕ∞)
          (convolution (fun z : EuclideanSpace ℝ (Fin n) => ρ (-z))
            (fun y : EuclideanSpace ℝ (Fin n) => A (Real.sqrt e • y))
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
        hρ'cs.contDiff_convolution_left _ hρ'sm hBloc
      have hid : ∀ h : EuclideanSpace ℝ (Fin n),
          (∫ z, ρ z • A (h + Real.sqrt e • z))
            = convolution (fun z : EuclideanSpace ℝ (Fin n) => ρ (-z))
                (fun y : EuclideanSpace ℝ (Fin n) => A (Real.sqrt e • y))
                (ContinuousLinearMap.lsmul ℝ ℝ) volume ((Real.sqrt e)⁻¹ • h) := by
        intro h
        show (∫ z, ρ z • A (h + Real.sqrt e • z))
          = ∫ z, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ (-z))
              (A (Real.sqrt e • ((Real.sqrt e)⁻¹ • h - z)))
        rw [← integral_neg_eq_self
          (fun z : EuclideanSpace ℝ (Fin n) => (ContinuousLinearMap.lsmul ℝ ℝ) (ρ (-z))
            (A (Real.sqrt e • ((Real.sqrt e)⁻¹ • h - z)))) volume]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        show ρ z • A (h + Real.sqrt e • z)
          = (ContinuousLinearMap.lsmul ℝ ℝ) (ρ (- -z))
              (A (Real.sqrt e • ((Real.sqrt e)⁻¹ • h - -z)))
        rw [neg_neg, sub_neg_eq_add, smul_add, smul_inv_smul₀ (ne_of_gt ht)]
        rfl
      have hcomp : ContDiff ℝ (⊤ : ℕ∞)
          (fun h : EuclideanSpace ℝ (Fin n) => ∫ z, ρ z • A (h + Real.sqrt e • z)) := by
        have hlin : ContDiff ℝ (⊤ : ℕ∞)
            (fun h : EuclideanSpace ℝ (Fin n) => (Real.sqrt e)⁻¹ • h) :=
          contDiff_const_smul _
        have heq : (fun h : EuclideanSpace ℝ (Fin n) =>
              ∫ z, ρ z • A (h + Real.sqrt e • z))
            = (convolution (fun z : EuclideanSpace ℝ (Fin n) => ρ (-z))
                (fun y : EuclideanSpace ℝ (Fin n) => A (Real.sqrt e • y))
                (ContinuousLinearMap.lsmul ℝ ℝ) volume)
              ∘ (fun h : EuclideanSpace ℝ (Fin n) => (Real.sqrt e)⁻¹ • h) := funext hid
        rw [heq]
        exact hconv.comp hlin
      exact hcomp.sub contDiff_const
    refine ⟨fun z h => measurable_const,
      fun x => hsmooth.continuous.comp continuous_snd,
      fun x _ z => hsmooth.continuous,
      fun x _ z => (hsmooth.of_le (by simp)).contDiffOn, ?_, ?_⟩
    · -- (Q1) for `A_e`, from the monotonicity of `A`
      exact MollifiedFieldQ1Bound n p ρ hn hρsm hρ0 hρsupp hρint c₁ C₂ hsw γ₀ γ₁ A
        hγ₀ hQ CM hCM0
        (hCM 0 γ₀ γ₁ Set.univ (fun _ _ h => A h) le_rfl hγ₀ hγ₁r hQ)
        c₄ hc₄a hc₄b e he0 hsmooth
    · -- (Q2) for `A_e`, from segment increments of `A`
      exact MollifiedFieldQ2Bound n p ρ hn hρsm hρ0 hρcs c₁ C₂ hc₁0 hC₂0 hsw γ₀ γ₁
        A hQ e he0 hsmooth
