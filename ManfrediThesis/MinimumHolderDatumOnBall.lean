import ManfrediThesis.Preamble
import ManfrediThesis.EssOscOn
import ManfrediThesis.VariationalGrowthF1
import ManfrediThesis.IsLocalMinimumOn
import ManfrediThesis.CitedHolderOscillationMinimum
import ManfrediThesis.ContinuousRepHolderDatumFromEssOsc
open MeasureTheory

/-- The Hölder datum the comparison scheme needs at a single ball: from the
cited oscillation estimate (C4)(a) and the uniform bound `|u| ≤ M`, a continuous
representative `U` of a bounded local minimum satisfies
`|U x - U x₀| ≤ C₁ R^α` on `closedBall x₀ R` for every small `R`, with
`α`, `R₀` and `C₁` depending only on `n, p, λ, Λ, a, M` and the domain distance
`d` -- bound before `ε` and before all the data, which is what makes them
ε-uniform.  This is thesis l. 1128-1136. -/
theorem MinimumHolderDatumOnBall :
    ∀ (n : ℕ) (p lam Lam a M d : ℝ), 1 ≤ n → 1 < p →
      0 < lam → lam ≤ Lam → 0 < a → 0 ≤ M → 0 < d →
      CitedHolderOscillationMinimum n p →
      ∃ α R₀ C₁ : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < R₀ ∧ 0 ≤ C₁ ∧
        ∀ (ε : ℝ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
          (fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
          (u U : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ),
          0 ≤ ε → ε ≤ 1 → IsOpen Ω →
          (∀ x ∈ Ω', ∀ y, y ∉ Ω → d ≤ dist x y) → x₀ ∈ Ω' →
          VariationalGrowthF1 n p ε lam Lam a Ω fdens →
          IsLocalMinimumOn n p Ω fdens u g →
          (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
          0 < R → R ≤ R₀ →
          ContinuousOn U (Metric.closedBall x₀ R) →
          (∀ x ∈ Metric.ball x₀ R, U x = u x) →
          ∀ x ∈ Metric.closedBall x₀ R, |U x - U x₀| ≤ C₁ * R ^ α := by
  intro n p lam Lam a M d hn hp hlam hlamLam ha hM hd hC4
  obtain ⟨α, dst, hα0, hα1, hdst0, hC4'⟩ := hC4 lam Lam a M hlam hlamLam ha hM
  have h4α : (0:ℝ) < (4:ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
  have h2dα : (0:ℝ) < (2/d) ^ α := Real.rpow_pos_of_pos (by positivity) _
  have hmax0 : (0:ℝ) ≤ max (2 * M) (dst * (d/2)) :=
    le_trans (by linarith) (le_max_left _ _)
  refine ⟨α, min (d/2) 1,
    (4:ℝ) ^ α * max (2 * M) (dst * (d/2)) * (2/d) ^ α,
    hα0, hα1, lt_min (by linarith) one_pos,
    mul_nonneg (mul_nonneg h4α.le hmax0) h2dα.le, ?_⟩
  intro ε Ω Ω' fdens u U g x₀ R hε hε1 hΩ hsep hx₀ hF1 hmin hMu hR hRR₀ hUc hUu
  have hRd2 : R ≤ d/2 := le_trans hRR₀ (min_le_left _ _)
  -- the closed ball of radius `d/2` sits inside `Ω`
  have hcb : Metric.closedBall x₀ (d/2) ⊆ Ω := by
    intro y hy
    by_contra hc
    have h1 := hsep x₀ hx₀ y hc
    rw [Metric.mem_closedBall, dist_comm] at hy
    linarith
  have hC4R := hC4' ε hε hε1 Ω fdens u g x₀ (d/2) R hΩ hF1 hmin hMu hcb hR hRd2
  exact ContinuousRepHolderDatumFromEssOsc n α dst M d (by linarith) Ω u U x₀ R hR
    hRd2 hcb hMu hUc hUu hC4R
