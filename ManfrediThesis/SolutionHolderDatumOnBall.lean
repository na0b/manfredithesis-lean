import ManfrediThesis.Preamble
import ManfrediThesis.EssOscOn
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.EllipticStructureQ345
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.CitedHolderOscillationSolution
import ManfrediThesis.ContinuousRepHolderDatumFromEssOsc
open MeasureTheory

/-- The Hölder datum at a single ball on the **equation** side: from the cited
oscillation estimate (C4)(b) and the uniform bound `|u| ≤ M`, a continuous
representative `U` of a bounded weak solution of (1.1) satisfies
`|U x - U x₀| ≤ C₁ R^α` on `closedBall x₀ R` for every small `R`, with `α`,
`R₀` and `C₁` depending only on `n, p, μ, γ₀, …, γ₄, M` and the domain distance
`d` -- bound before `ε` and before all the data, which is what makes them
ε-uniform.  This is thesis l. 1535-1539.

This is **not** `MinimumHolderDatumOnBall`.  That node is the §4 branch: its
hypotheses are `VariationalGrowthF1` on an integrand `fdens`,
`IsLocalMinimumOn` and `CitedHolderOscillationMinimum`, which is part (a) of
(C4).  The present node is the §5 branch: its hypotheses are
`EllipticStructureQ12` and `EllipticStructureQ345` on a field `A` with a
right-hand side `B`, `IsWeakSolutionOn`, and `CitedHolderOscillationSolution`,
which is part (b).  The two halves of (C4) are separate predicates (the paper
labels them (a) and (b) at l. 263), neither implies the other, and neither set
of structure hypotheses is available on the other side: this is pm-0092's
frozen-operator exception, which leaves the equation side without a twin. -/
theorem SolutionHolderDatumOnBall :
    ∀ (n : ℕ) (p μ γ₀ γ₁ γ₂ γ₃ γ₄ M d : ℝ), 1 ≤ n → 1 < p →
      0 < μ → 0 < γ₀ → γ₀ ≤ γ₁ → 0 < γ₂ → 0 < γ₃ → 0 < γ₄ → 0 ≤ M → 0 < d →
      CitedHolderOscillationSolution n p →
      ∃ α R₀ C₁ : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < R₀ ∧ 0 ≤ C₁ ∧
        ∀ (ε : ℝ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
          (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
            EuclideanSpace ℝ (Fin n))
          (B : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
          (u U : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ),
          0 ≤ ε → ε ≤ 1 → IsOpen Ω →
          (∀ x ∈ Ω', ∀ y, y ∉ Ω → d ≤ dist x y) → x₀ ∈ Ω' →
          EllipticStructureQ12 n p ε γ₀ γ₁ Ω A →
          EllipticStructureQ345 n p ε μ γ₂ γ₃ γ₄ Ω A B →
          IsWeakSolutionOn n p Ω A B u g →
          (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
          0 < R → R ≤ R₀ →
          ContinuousOn U (Metric.closedBall x₀ R) →
          (∀ x ∈ Metric.ball x₀ R, U x = u x) →
          ∀ x ∈ Metric.closedBall x₀ R, |U x - U x₀| ≤ C₁ * R ^ α := by
  intro n p μ γ₀ γ₁ γ₂ γ₃ γ₄ M d hn hp hμ hγ₀ hγ₀γ₁ hγ₂ hγ₃ hγ₄ hM hd hC4
  have hγ₁0 : 0 < γ₁ := lt_of_lt_of_le hγ₀ hγ₀γ₁
  obtain ⟨α, dst, hα0, hα1, hdst0, hC4'⟩ :=
    hC4 μ γ₀ γ₁ γ₂ γ₃ γ₄ M hγ₀ hγ₁0 hγ₂ hγ₃ hγ₄ hμ hM
  have h4α : (0:ℝ) < (4:ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
  have h2dα : (0:ℝ) < (2/d) ^ α := Real.rpow_pos_of_pos (by positivity) _
  have hmax0 : (0:ℝ) ≤ max (2 * M) (dst * (d/2)) :=
    le_trans (by linarith) (le_max_left _ _)
  refine ⟨α, min (d/2) 1,
    (4:ℝ) ^ α * max (2 * M) (dst * (d/2)) * (2/d) ^ α,
    hα0, hα1, lt_min (by linarith) one_pos,
    mul_nonneg (mul_nonneg h4α.le hmax0) h2dα.le, ?_⟩
  intro ε Ω Ω' A B u U g x₀ R hε hε1 hΩ hsep hx₀ hQ12 hQ345 hsol hMu hR hRR₀ hUc hUu
  have hRd2 : R ≤ d/2 := le_trans hRR₀ (min_le_left _ _)
  -- the closed ball of radius `d/2` sits inside `Ω`
  have hcb : Metric.closedBall x₀ (d/2) ⊆ Ω := by
    intro y hy
    by_contra hc
    have h1 := hsep x₀ hx₀ y hc
    rw [Metric.mem_closedBall, dist_comm] at hy
    linarith
  have hC4R := hC4' ε hε hε1 Ω A B u g x₀ (d/2) R hΩ hQ12 hQ345 hsol hMu hcb hR hRd2
  exact ContinuousRepHolderDatumFromEssOsc n α dst M d (by linarith) Ω u U x₀ R hR
    hRd2 hcb hMu hUc hUu hC4R
