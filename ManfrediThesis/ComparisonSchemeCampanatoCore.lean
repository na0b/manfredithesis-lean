import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pOn
import ManfrediThesis.CampanatoDecayFromBundle
import ManfrediThesis.WeakGradientRestrict
import ManfrediThesis.WeakGradientCompactSupportIntegral
import ManfrediThesis.CampanatoIterationLemma
import ManfrediThesis.MemHolderOn
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.FrozenComparisonOn
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.CitedDirichletW1p
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.CitedDirichletHolder
import ManfrediThesis.FrozenComparisonDecay
import ManfrediThesis.GradientSupEstimate
import ManfrediThesis.GradientOscillationEstimate
open MeasureTheory
-- `maxHeartbeats` sized by bisection: the default 200000 fails, 250000 succeeds.
set_option maxHeartbeats 250000

/-- The abstract comparison scheme behind Theorems 4 and 6, in two clauses.
Clause (A): from the Morrey bound (4.15), the oscillation estimate (4.16) for
the comparison maps and the Hölder smallness (4.17) of the remainder, the
Campanato decay (4.19) for `∇u`.  Clause (B) takes the producer-side data
instead of the bundle -- the frozen family with its (Q1)-(Q2), the `C^α` datum
for the continuous representative, and (4.17) quantified over bundles -- and
builds the comparison map and (4.16) itself from Theorems 1 and 2, so that a
consumer never has to assemble the bundle.  Its oscillation exponent `α₂` is
Theorem 2's, produced here rather than received, and the Morrey data `τ`, `c₁`
are bound after it, which is the order the paper's proof of Theorem 4 uses. -/
theorem ComparisonSchemeCampanatoCore :
    ∀ (n : ℕ) (p α δ' τ c₁ c₃ : ℝ), 2 ≤ n → 1 < p → 0 < α → α ≤ 1 → 0 < δ' →
      0 < c₁ → 0 < c₃ → 0 < τ → τ < p * α * δ' / ((n : ℝ) + p * α) →
      (∃ lam₀ c₁₀ R₂ : ℝ, 0 < lam₀ ∧ lam₀ < p ∧ 0 < c₁₀ ∧ 0 < R₂ ∧ R₂ ≤ 1 ∧
        ∀ (ε : ℝ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (R₁ : ℝ),
          0 ≤ ε → ε ≤ 1 → IsOpen Ω → IsOpen Ω' → closure Ω' ⊆ Ω → 0 < R₁ →
          MemW1pOn n p Ω u g →
          (∀ x₀ ∈ Ω', ∀ R : ℝ, 0 < R → R ≤ R₁ →
            R ^ (-(n : ℝ)) * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2)
              ≤ c₁ * R ^ (-τ)) →
          (∀ x₀ ∈ Ω', ∀ R : ℝ, 0 < R → R ≤ R₁ → Metric.closedBall x₀ R ⊆ Ω →
            ∃ (v : EuclideanSpace ℝ (Fin n) → ℝ)
              (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
              MemW1pOn n p (Metric.ball x₀ R) v gv ∧
              (∀ ρ : ℝ, 0 < ρ → ρ ≤ R / 2 →
                (∫ x in Metric.ball x₀ ρ,
                    ‖gv x - (volume (Metric.ball x₀ ρ)).toReal⁻¹
                      • ∫ y in Metric.ball x₀ ρ, gv y‖ ^ p)
                  ≤ c₃ * (ρ / R) ^ (p * α) * ρ ^ (n : ℝ)
                    * (R ^ (-(n : ℝ))
                      * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2))) ∧
              (∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p)
                ≤ R ^ (δ' + (n : ℝ))
                  * (R ^ (-(n : ℝ))
                    * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2))) →
          ∀ x₀ ∈ Ω', ∀ R ρ : ℝ, 0 < R → R ≤ min R₁ R₂ →
            Metric.closedBall x₀ R ⊆ Ω → 0 < ρ →
            2 * ρ ≤ R ^ (1 + δ' / ((n : ℝ) + p * α)) →
            (∫ x in Metric.ball x₀ ρ,
                ‖g x - (volume (Metric.ball x₀ ρ)).toReal⁻¹
                  • ∫ y in Metric.ball x₀ ρ, g y‖ ^ p)
              ≤ c₁₀ * ρ ^ ((n : ℝ) + lam₀))
      ∧ (∀ r αH : ℝ, 0 < r → 0 < αH → αH ≤ 1 →
          CitedSobolevPoincareBall n →
          (∀ (ε' γ₀' γ₁' : ℝ)
            (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
            0 < γ₀' → 0 < γ₁' → CitedDirichletW1p n p ε' γ₀' γ₁' A') →
          (∀ (ε' γ₀' γ₁' : ℝ) (Ω₀ : Set (EuclideanSpace ℝ (Fin n)))
            (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
            0 < γ₀' → 0 < γ₁' → IsOpen Ω₀ →
            CitedRegularityEpsPos n p ε' γ₀' γ₁' Ω₀ A') →
          (∀ (ε' γ₀' γ₁' : ℝ)
            (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
            0 < γ₀' → 0 < γ₁' → CitedDirichletHolder n p ε' γ₀' γ₁' A') →
          ∃ α₂ : ℝ, 0 < α₂ ∧ α₂ ≤ 1 ∧
            ∀ δ₂ τ₂ : ℝ, 0 < δ₂ → 0 < τ₂ →
              τ₂ < p * α₂ * δ₂ / ((n : ℝ) + p * α₂) →
              ∃ lam₂ R₃ : ℝ, 0 < lam₂ ∧ lam₂ < p ∧ 0 < R₃ ∧ R₃ ≤ 1 ∧
                ∀ c₂ : ℝ, 0 < c₂ →
                  ∃ c₂₀ : ℝ, 0 < c₂₀ ∧
                    ∀ (ε γ₀ γ₁ : ℝ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
                      (𝒜 : EuclideanSpace ℝ (Fin n) → ℝ →
                        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
                      (u U : EuclideanSpace ℝ (Fin n) → ℝ)
                      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
                      (R₁ : ℝ),
                      0 ≤ ε → ε ≤ 1 → 0 < γ₀ → 0 < γ₁ → γ₁ ≤ r * γ₀ →
                      IsOpen Ω → IsOpen Ω' → closure Ω' ⊆ Ω → 0 < R₁ →
                      MemW1pOn n p Ω u g → MemW1pOn n p Ω U g →
                      (∀ x₀ ∈ Ω', ∀ R : ℝ, 0 < R → R ≤ R₁ →
                        Metric.closedBall x₀ R ⊆ Ω) →
                      (∀ x₀ ∈ Ω', EllipticStructureQ12 n p ε γ₀ γ₁ Set.univ
                        (fun _ _ h => 𝒜 x₀ (U x₀) h - 𝒜 x₀ (U x₀) 0)) →
                      (∀ x₀ ∈ Ω', MemHolderOn n αH (Metric.closedBall x₀ R₁) U) →
                      (∀ x₀ ∈ Ω', ∀ R : ℝ, 0 < R → R ≤ R₁ →
                        R ^ (-(n : ℝ))
                            * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2)
                          ≤ c₂ * R ^ (-τ₂)) →
                      (∀ x₀ ∈ Ω', ∀ R : ℝ, 0 < R → R ≤ R₁ →
                        ∀ (v V : EuclideanSpace ℝ (Fin n) → ℝ)
                          (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
                          FrozenComparisonOn n p x₀ R (𝒜 x₀ (U x₀)) U U g v V gv →
                          (∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p)
                            ≤ R ^ (δ₂ + (n : ℝ))
                              * (R ^ (-(n : ℝ))
                                * ∫ x in Metric.ball x₀ R,
                                    (1 + ‖g x‖ ^ 2) ^ (p / 2))) →
                      ∀ x₀ ∈ Ω', ∀ R ρ : ℝ, 0 < R → R ≤ min R₁ R₃ →
                        0 < ρ →
                        2 * ρ ≤ R ^ (1 + δ₂ / ((n : ℝ) + p * α₂)) →
                        (∫ x in Metric.ball x₀ ρ,
                            ‖g x - (volume (Metric.ball x₀ ρ)).toReal⁻¹
                              • ∫ y in Metric.ball x₀ ρ, g y‖ ^ p)
                          ≤ c₂₀ * ρ ^ ((n : ℝ) + lam₂)) := by
  intro n p α δ' τ c₁ c₃ hn hp hα hα1 hδ' hc₁ hc₃ hτ hadm
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  have hp2 : (0:ℝ) < p / 2 := by linarith
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hntriv : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, hnpos⟩ (1 : ℝ), ?_⟩⟩
    intro hcon
    have h := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w ⟨0, hnpos⟩) hcon
    simp at h
  constructor
  · -- Clause (A): a direct application of the peeled node.
    obtain ⟨lam₀, R₂, hlam₀, hlam₀p, hR₂, hR₂1, hrest⟩ :=
      CampanatoDecayFromBundle n p α δ' τ hn hp hα hα1 hδ' hτ hadm
    obtain ⟨c₁₀, hc₁₀, hconc⟩ := hrest c₁ c₃ hc₁ hc₃
    refine ⟨lam₀, c₁₀, R₂, hlam₀, hlam₀p, hc₁₀, hR₂, hR₂1, ?_⟩
    intro ε Ω Ω' u g R₁ hε0 hε1 hΩ hΩ' hcl hR₁ hu hM hB
    refine hconc ε Ω Ω' u g R₁ hε0 hε1 hΩ hΩ' hcl hR₁ hu hM ?_
    intro y hy S hS hSR₁ hballS
    obtain ⟨v, gv, hvW, h416, h417⟩ := hB y hy S hS hSR₁ hballS
    exact ⟨v, gv, hvW, fun r hr hr4 => h416 r hr (by linarith), h417⟩
  · -- Clause (B): the bundle is produced here, then clause (A)'s node is applied.
    intro r αH hr hαH hαH1 hSP hC2 hC1 hC3
    -- Step B1: the constants.
    obtain ⟨C₂, α₂, hC₂pos, hα₂, hα₂1, hosc⟩ :=
      GradientOscillationEstimate n p r hn hp hr hSP hC2 hC1
    obtain ⟨Cs, hCs, hsup⟩ := GradientSupEstimate n p r hn hp hr hSP hC2 hC1
    obtain ⟨c₀, hc₀, hdec⟩ := FrozenComparisonDecay n p r hn hp hr hSP hC2 hC1 hC3
    refine ⟨α₂, hα₂, hα₂1, ?_⟩
    intro δ₂ τ₂ hδ₂ hτ₂ hadm₂
    obtain ⟨lam₂, R₃, hlam₂, hlam₂p, hR₃, hR₃1, hrest⟩ :=
      CampanatoDecayFromBundle n p α₂ δ₂ τ₂ hn hp hα₂ hα₂1 hδ₂ hτ₂ hadm₂
    refine ⟨lam₂, R₃, hlam₂, hlam₂p, hR₃, hR₃1, ?_⟩
    intro c₂ hc₂
    have hqsub : ∀ q X Y : ℝ, 0 < q → 0 ≤ X → 0 ≤ Y →
        (X + Y) ^ q ≤ max 1 (2 ^ (q-1)) * (X ^ q + Y ^ q) := by
      intro q X Y hq hX hY
      have hsum : (0:ℝ) ≤ X ^ q + Y ^ q :=
        add_nonneg (Real.rpow_nonneg hX _) (Real.rpow_nonneg hY _)
      rcases le_or_gt q 1 with h1 | h1
      · have hbase : (X + Y) ^ q ≤ X ^ q + Y ^ q := by
          have h := NNReal.rpow_add_le_add_rpow X.toNNReal Y.toNNReal hq.le h1
          have h2 := (NNReal.coe_le_coe (r₁ := (X.toNNReal + Y.toNNReal) ^ q)
            (r₂ := X.toNNReal ^ q + Y.toNNReal ^ q)).2 h
          push_cast [Real.coe_toNNReal _ hX, Real.coe_toNNReal _ hY] at h2
          exact h2
        nlinarith [le_max_left (1:ℝ) ((2:ℝ) ^ (q-1)), hsum]
      · have hbase : (X + Y) ^ q ≤ 2 ^ (q-1) * (X ^ q + Y ^ q) := by
          have h := NNReal.rpow_add_le_mul_rpow_add_rpow X.toNNReal Y.toNNReal h1.le
          have h2 := (NNReal.coe_le_coe (r₁ := (X.toNNReal + Y.toNNReal) ^ q)
            (r₂ := 2 ^ (q-1) * (X.toNNReal ^ q + Y.toNNReal ^ q))).2 h
          push_cast [Real.coe_toNNReal _ hX, Real.coe_toNNReal _ hY] at h2
          exact h2
        nlinarith [le_max_right (1:ℝ) ((2:ℝ) ^ (q-1)), hsum]
    have hsq : ∀ t : ℝ, 0 ≤ t → (t ^ 2) ^ (p/2) = t ^ p := by
      intro t ht
      rw [show (t:ℝ) ^ 2 = t ^ ((2:ℕ):ℝ) from by rw [Real.rpow_natCast], ← Real.rpow_mul ht]
      congr 1
      push_cast
      ring
    set ωn : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal with hωdef
    have hω : 0 < ωn := by
      rw [hωdef]
      refine ENNReal.toReal_pos (ne_of_gt ?_) measure_ball_lt_top.ne
      exact Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self one_pos⟩
    have hballvol : ∀ (y : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 ≤ t →
        (volume (Metric.ball y t)).toReal = ωn * t ^ ((n:ℝ)) := by
      intro y t ht
      rw [Measure.addHaar_ball volume y ht, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg ht _),
        show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n by simp, ← hωdef,
        ← Real.rpow_natCast t n]
      ring
    set κ : ℝ := max (2 ^ (p/2)) (2 ^ (p-1)) with hκdef
    have hκ : 0 < κ := lt_of_lt_of_le (Real.rpow_pos_of_pos two_pos _) (le_max_left _ _)
    set c₃s : ℝ := 4 ^ p * ωn * C₂ ^ p * (2 ^ ((n:ℝ)) * Cs * c₀ * κ) with hc₃sdef
    have hc₃s : 0 < c₃s := by
      rw [hc₃sdef]
      have h4 : (0:ℝ) < 4 ^ p := Real.rpow_pos_of_pos (by norm_num) _
      have hC2p : (0:ℝ) < C₂ ^ p := Real.rpow_pos_of_pos hC₂pos _
      have h2n : (0:ℝ) < 2 ^ ((n:ℝ)) := Real.rpow_pos_of_pos two_pos _
      positivity
    obtain ⟨c₂₀, hc₂₀, hconc⟩ := hrest c₂ c₃s hc₂ hc₃s
    refine ⟨c₂₀, hc₂₀, ?_⟩
    intro ε γ₀ γ₁ Ω Ω' 𝒜 u U g R₁ hε0 hε1 hγ₀ hγ₁ hγr hΩ hΩ' hcl hR₁ hu hU hballs hQ12 hHol
      hMor h417
    have hR₁f : (0:ℝ) < min R₁ 1 := lt_min hR₁ one_pos
    have hmor : ∀ x₀ ∈ Ω', ∀ R : ℝ, 0 < R → R ≤ min R₁ 1 →
        R ^ (-(n : ℝ)) * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2)
          ≤ c₂ * R ^ (-τ₂) :=
      fun x₀ hx₀ R hR hRm => hMor x₀ hx₀ R hR (le_trans hRm (min_le_left _ _))
    have hbundle : ∀ x₀ ∈ Ω', ∀ R : ℝ, 0 < R → R ≤ min R₁ 1 →
        Metric.closedBall x₀ R ⊆ Ω →
        ∃ (v : EuclideanSpace ℝ (Fin n) → ℝ)
          (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          MemW1pOn n p (Metric.ball x₀ R) v gv ∧
          (∀ ρ : ℝ, 0 < ρ → ρ ≤ R / 4 →
            (∫ x in Metric.ball x₀ ρ,
                ‖gv x - (volume (Metric.ball x₀ ρ)).toReal⁻¹
                  • ∫ y in Metric.ball x₀ ρ, gv y‖ ^ p)
              ≤ c₃s * (ρ / R) ^ (p * α₂) * ρ ^ (n : ℝ)
                * (R ^ (-(n : ℝ))
                  * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2))) ∧
          (∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p)
            ≤ R ^ (δ₂ + (n : ℝ))
              * (R ^ (-(n : ℝ))
                * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2)) := by
      intro x₀ hx₀ R hR hRm hballR
      have hRR₁ : R ≤ R₁ := le_trans hRm (min_le_left _ _)
      have hR1 : R ≤ 1 := le_trans hRm (min_le_right _ _)
      have hballsub : Metric.ball x₀ R ⊆ Ω :=
        subset_trans Metric.ball_subset_closedBall hballR
      -- (B2a) the comparison map
      have hUball : MemW1pOn n p (Metric.ball x₀ R) U g :=
        (WeakGradientRestrict n p hn1 hp.le Ω (Metric.ball x₀ R) U g hΩ
          Metric.isOpen_ball hballsub).1 hU
      have hHolR : MemHolderOn n αH (Metric.closedBall x₀ R) U := by
        obtain ⟨hcont, C, hC0, hC⟩ := hHol x₀ hx₀
        exact ⟨hcont.mono (Metric.closedBall_subset_closedBall hRR₁), C, hC0,
          fun x hx y hy => hC x (Metric.closedBall_subset_closedBall hRR₁ hx)
            y (Metric.closedBall_subset_closedBall hRR₁ hy)⟩
      obtain ⟨v, V, gv, hFC, h411⟩ :=
        hdec ε αH γ₀ γ₁ (𝒜 x₀ (U x₀)) x₀ R U g hε0 hε1 hαH hαH1 hγ₀ hγ₁ hγr hR
          (hQ12 x₀ hx₀) hUball hHolR
      have hvW : MemW1pOn n p (Metric.ball x₀ R) v gv := hFC.2.1
      refine ⟨v, gv, hvW, ?_, h417 x₀ hx₀ R hR hRR₁ v V gv hFC⟩
      -- the operator shift: `v` solves for the normalised field `A⁰ - A⁰ 0`
      have hsolT : IsWeakSolutionOn n p (Metric.ball x₀ R)
          (fun _ _ h => 𝒜 x₀ (U x₀) h - 𝒜 x₀ (U x₀) 0) (fun _ _ _ => 0) v gv := by
        refine ⟨hFC.1.1, ?_⟩
        intro φ gφ hφW hφc hφs
        obtain ⟨hint0, hid0⟩ := hFC.1.2 φ gφ hφW hφc hφs
        have hzero := WeakGradientCompactSupportIntegral n p hn1 hp.le x₀ R φ gφ hR hφW hφc hφs
        set D : EuclideanSpace ℝ (Fin n) → ℝ :=
          fun x => ∑ i, (𝒜 x₀ (U x₀) 0) i * gφ x i with hDdef
        have hDint : IntegrableOn D (Metric.ball x₀ R) volume := by
          rw [hDdef]
          exact integrable_finsetSum _ fun i _ => ((hzero i).1.const_mul _)
        have hDzero : (∫ x in Metric.ball x₀ R, D x) = 0 := by
          rw [hDdef, integral_finsetSum _ fun i _ => ((hzero i).1.const_mul _)]
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [integral_const_mul, (hzero i).2, mul_zero]
        have hEq : ∀ x : EuclideanSpace ℝ (Fin n),
            (∑ i, ((𝒜 x₀ (U x₀) (gv x) - 𝒜 x₀ (U x₀) 0) i) * gφ x i) + (0:ℝ) * φ x
              = ((∑ i, (𝒜 x₀ (U x₀) (gv x)) i * gφ x i) + (0:ℝ) * φ x) - D x := by
          intro x
          simp only [hDdef, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
          ring
        constructor
        · refine (hint0.sub hDint).congr_fun (fun x _ => ?_) measurableSet_ball
          simp only [Pi.sub_apply]
          exact (hEq x).symm
        · rw [setIntegral_congr_fun measurableSet_ball (fun x _ => hEq x),
            integral_sub hint0 hDint, hid0, hDzero, sub_zero]
      -- (B2b) the sup bound
      have hκid : (2:ℝ) ^ (p/2) * max 1 (2 ^ (p/2-1)) = κ := by
        rw [hκdef, mul_max_of_nonneg _ _ (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _), mul_one,
          ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 2
        ring
      have hQball : EllipticStructureQ12 n p ε γ₀ γ₁ (Metric.ball x₀ R)
          (fun _ _ h => 𝒜 x₀ (U x₀) h - 𝒜 x₀ (U x₀) 0) := by
        obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hQ12 x₀ hx₀
        exact ⟨m1, m2, fun x _ => m3 x (Set.mem_univ x), fun x _ => m4 x (Set.mem_univ x),
          m5.mono fun x hx _ => hx (Set.mem_univ x),
          m6.mono fun x hx _ => hx (Set.mem_univ x)⟩
      have hcb2 : Metric.closedBall x₀ (R/2) ⊆ Metric.ball x₀ R := fun y hy =>
        Metric.mem_ball.2 (by have := Metric.mem_closedBall.1 hy; linarith)
      have hsupR := hsup ε γ₀ γ₁ (Metric.ball x₀ R)
        (fun h => 𝒜 x₀ (U x₀) h - 𝒜 x₀ (U x₀) 0) v gv x₀ (R/2)
        hε0 hγ₀ hγr Metric.isOpen_ball (by linarith) (sub_self _) hQball hsolT hcb2
      -- integrability on B_R
      have hgR : MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) :=
        (hu.2.2).mono_measure (Measure.restrict_mono hballsub le_rfl)
      have hgvR : MemLp gv (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) := hvW.2.2
      have hpne0 : (ENNReal.ofReal p) ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
      have hpnet : (ENNReal.ofReal p) ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
      have htoR : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
      have hfinR : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
      have hcontrp : Continuous fun s : ℝ => s ^ (p/2) :=
        continuous_iff_continuousAt.mpr fun s =>
          Real.continuousAt_rpow_const s (p/2) (Or.inr hp2.le)
      have hggvp : IntegrableOn (fun x => ‖g x - gv x‖ ^ p) (Metric.ball x₀ R) volume := by
        have h := ((hgR.sub hgvR).integrable_norm_rpow hpne0 hpnet)
        rwa [htoR] at h
      have hgp : IntegrableOn (fun x => ‖g x‖ ^ p) (Metric.ball x₀ R) volume := by
        have h := (hgR.integrable_norm_rpow hpne0 hpnet)
        rwa [htoR] at h
      have hΛmeas : AEStronglyMeasurable (fun x => (1 + ‖g x‖ ^ 2) ^ (p/2))
          (volume.restrict (Metric.ball x₀ R)) :=
        (hcontrp.comp ((continuous_const.add (continuous_pow 2)) :
            Continuous fun t : ℝ => 1 + t ^ 2)).comp_aestronglyMeasurable
          hgR.aestronglyMeasurable.norm
      have hΛint : IntegrableOn (fun x => (1 + ‖g x‖ ^ 2) ^ (p/2)) (Metric.ball x₀ R) volume := by
        refine Integrable.mono' (g := fun x => max 1 (2 ^ (p/2-1)) * (1 + ‖g x‖ ^ p))
          (((integrable_const (1:ℝ)).add hgp).const_mul _) hΛmeas
          (Filter.Eventually.of_forall fun x => ?_)
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
        have h := hqsub (p/2) 1 (‖g x‖ ^ 2) hp2 zero_le_one (by positivity)
        rwa [Real.one_rpow, hsq (‖g x‖) (norm_nonneg _)] at h
      set IG : ℝ := ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p/2) with hIGdef
      have hIG0 : 0 ≤ IG := integral_nonneg fun x => Real.rpow_nonneg (by positivity) _
      -- the κ comparison of g_v with ∇u
      have hκpt : ∀ x : EuclideanSpace ℝ (Fin n), (ε + ‖gv x‖ ^ 2) ^ (p/2)
          ≤ κ * ((1 + ‖g x‖ ^ 2) ^ (p/2) + ‖g x - gv x‖ ^ p) := by
        intro x
        have hgvle : ‖gv x‖ ≤ ‖g x‖ + ‖g x - gv x‖ := by
          have h0 := norm_sub_le (g x) (g x - gv x)
          rwa [show g x - (g x - gv x) = gv x from by abel] at h0
        have hsqle : ‖gv x‖ ^ 2 ≤ (‖g x‖ + ‖g x - gv x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hgvle 2
        have hb : ε + ‖gv x‖ ^ 2 ≤ 2 * ((1 + ‖g x‖ ^ 2) + ‖g x - gv x‖ ^ 2) := by
          nlinarith [hsqle, hε1, sq_nonneg (‖g x‖ - ‖g x - gv x‖)]
        calc (ε + ‖gv x‖ ^ 2) ^ (p/2)
            ≤ (2 * ((1 + ‖g x‖ ^ 2) + ‖g x - gv x‖ ^ 2)) ^ (p/2) :=
              Real.rpow_le_rpow (add_nonneg hε0 (sq_nonneg _)) hb hp2.le
          _ = 2 ^ (p/2) * ((1 + ‖g x‖ ^ 2) + ‖g x - gv x‖ ^ 2) ^ (p/2) :=
              Real.mul_rpow (by norm_num) (by positivity)
          _ ≤ 2 ^ (p/2) * (max 1 (2 ^ (p/2-1))
                * ((1 + ‖g x‖ ^ 2) ^ (p/2) + (‖g x - gv x‖ ^ 2) ^ (p/2))) :=
              mul_le_mul_of_nonneg_left
                (hqsub (p/2) _ _ hp2 (by positivity) (by positivity))
                (Real.rpow_nonneg (by norm_num) _)
          _ = κ * ((1 + ‖g x‖ ^ 2) ^ (p/2) + ‖g x - gv x‖ ^ p) := by
              rw [hsq (‖g x - gv x‖) (norm_nonneg _), ← mul_assoc, hκid]
      have h417R := h417 x₀ hx₀ R hR hRR₁ v V gv hFC
      have hggvIG : (∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p) ≤ IG := by
        refine le_trans h417R ?_
        rw [show R ^ (δ₂ + (n:ℝ)) * (R ^ (-(n:ℝ)) * IG)
              = (R ^ (δ₂ + (n:ℝ)) * R ^ (-(n:ℝ))) * IG from by ring,
          ← Real.rpow_add hR, show δ₂ + (n:ℝ) + -(n:ℝ) = δ₂ from by ring]
        calc R ^ δ₂ * IG ≤ 1 * IG :=
              mul_le_mul_of_nonneg_right (Real.rpow_le_one hR.le hR1 hδ₂.le) hIG0
          _ = IG := one_mul IG
      have hIgv : (∫ x in Metric.ball x₀ R, (ε + ‖gv x‖ ^ 2) ^ (p/2)) ≤ 2 * κ * IG := by
        have hdom : IntegrableOn
            (fun x => κ * ((1 + ‖g x‖ ^ 2) ^ (p/2) + ‖g x - gv x‖ ^ p))
            (Metric.ball x₀ R) volume := (hΛint.add hggvp).const_mul _
        have h1 := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x =>
            Real.rpow_nonneg (add_nonneg hε0 (sq_nonneg _)) (p/2))
          hdom (Filter.Eventually.of_forall hκpt)
        rw [integral_const_mul] at h1
        rw [integral_add hΛint hggvp] at h1
        calc (∫ x in Metric.ball x₀ R, (ε + ‖gv x‖ ^ 2) ^ (p/2))
            ≤ κ * (IG + ∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p) := h1
          _ ≤ κ * (IG + IG) := by
              refine mul_le_mul_of_nonneg_left ?_ hκ.le
              linarith [hggvIG]
          _ = 2 * κ * IG := by ring
      -- the sup bound constant S
      have hnR1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      have h2n0 : (0:ℝ) < 2 ^ ((n:ℝ)) := Real.rpow_pos_of_pos two_pos _
      set Λv : ℝ := R ^ (-(n:ℝ)) * IG with hΛvdef
      have hΛv0 : 0 ≤ Λv := mul_nonneg (Real.rpow_pos_of_pos hR _).le hIG0
      set Sp : ℝ := 2 ^ ((n:ℝ)) * Cs * c₀ * κ * Λv with hSpdef
      have hprodnn : (0:ℝ) ≤ Cs * c₀ * κ * Λv :=
        mul_nonneg (mul_nonneg (mul_nonneg hCs.le hc₀.le) hκ.le) hΛv0
      have hSp0 : 0 ≤ Sp := by
        rw [hSpdef]
        calc (0:ℝ) ≤ 2 ^ ((n:ℝ)) * (Cs * c₀ * κ * Λv) := mul_nonneg h2n0.le hprodnn
          _ = 2 ^ ((n:ℝ)) * Cs * c₀ * κ * Λv := by ring
      set S : ℝ := Sp ^ (1/p) with hSdef
      have hS0 : 0 ≤ S := Real.rpow_nonneg hSp0 _
      have hSpow : S ^ p = Sp := by
        rw [hSdef, ← Real.rpow_mul hSp0, one_div, inv_mul_cancel₀ (ne_of_gt hp0), Real.rpow_one]
      have hhalf : (0:ℝ) < (1/2 : ℝ) ^ ((n:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
      have hsplit : (R/2 : ℝ) ^ ((n:ℝ)) = R ^ ((n:ℝ)) * (1/2 : ℝ) ^ ((n:ℝ)) := by
        rw [show (R/2 : ℝ) = R * (1/2) from by ring, Real.mul_rpow hR.le (by norm_num)]
      have hIgv2 : (∫ y in Metric.ball x₀ (R/2), (ε + ‖gv y‖ ^ 2) ^ (p/2))
          ≤ c₀ * (1/2 : ℝ) ^ ((n:ℝ)) * (2 * κ * IG) := by
        refine le_trans (h411 (R/2) (by linarith) (by linarith)) ?_
        rw [show (R/2)/R = (1/2 : ℝ) from by field_simp]
        exact mul_le_mul_of_nonneg_left hIgv (mul_nonneg hc₀.le hhalf.le)
      have h2le : (2:ℝ) ≤ 2 ^ ((n:ℝ)) := by
        calc (2:ℝ) = 2 ^ (1:ℝ) := (Real.rpow_one 2).symm
          _ ≤ 2 ^ ((n:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hnR1
      have hsupbd : Cs / (R/2) ^ ((n:ℝ))
            * (∫ y in Metric.ball x₀ (R/2), (ε + ‖gv y‖ ^ 2) ^ (p/2)) ≤ Sp := by
        have hcoef : (0:ℝ) < Cs / (R/2) ^ ((n:ℝ)) := by
          refine div_pos hCs ?_
          rw [hsplit]
          exact mul_pos (Real.rpow_pos_of_pos hR _) hhalf
        have hkey : Cs / (R/2) ^ ((n:ℝ)) * (c₀ * (1/2:ℝ) ^ ((n:ℝ)) * (2 * κ * IG))
            = 2 * (Cs * c₀ * κ * Λv) := by
          rw [hsplit, hΛvdef, Real.rpow_neg hR.le]
          field_simp
        calc Cs / (R/2) ^ ((n:ℝ))
              * (∫ y in Metric.ball x₀ (R/2), (ε + ‖gv y‖ ^ 2) ^ (p/2))
            ≤ Cs / (R/2) ^ ((n:ℝ)) * (c₀ * (1/2:ℝ) ^ ((n:ℝ)) * (2 * κ * IG)) :=
              mul_le_mul_of_nonneg_left hIgv2 hcoef.le
          _ = 2 * (Cs * c₀ * κ * Λv) := hkey
          _ ≤ 2 ^ ((n:ℝ)) * (Cs * c₀ * κ * Λv) := mul_le_mul_of_nonneg_right h2le hprodnn
          _ = Sp := by rw [hSpdef]; ring
      have hae : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R/4))), ‖gv x‖ ≤ S := by
        have h := hsupR
        rw [show R/2/2 = R/4 from by ring] at h
        filter_upwards [h] with x hx
        have h1 : (ε + ‖gv x‖ ^ 2) ^ (p/2) ≤ S ^ p := by
          rw [hSpow]; exact le_trans hx hsupbd
        have h2 : ε + ‖gv x‖ ^ 2 ≤ S ^ 2 := by
          have h3 := Real.rpow_le_rpow
            (Real.rpow_nonneg (add_nonneg hε0 (sq_nonneg _)) _) h1 (div_pos two_pos hp0).le
          rw [← Real.rpow_mul (add_nonneg hε0 (sq_nonneg _)), ← Real.rpow_mul hS0,
            show p/2 * (2/p) = 1 from by field_simp, show p * (2/p) = 2 from by field_simp,
            Real.rpow_one, show ((2:ℝ)) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast] at h3
          exact h3
        have h4 : ‖gv x‖ ^ 2 ≤ S ^ 2 := by linarith
        exact le_of_pow_le_pow_left₀ (by norm_num) hS0 h4
      -- (B2c) the oscillation estimate (4.16)
      intro ρ hρ hρ4
      have hρR : ρ ≤ R := by linarith
      have hρR0 : (0:ℝ) ≤ ρ / R := div_nonneg hρ.le hR.le
      have hρR40 : (0:ℝ) ≤ ρ / (R/4) := div_nonneg hρ.le (by linarith)
      have hcb4 : Metric.closedBall x₀ (R/4) ⊆ Metric.ball x₀ R := fun y hy =>
        Metric.mem_ball.2 (by have := Metric.mem_closedBall.1 hy; linarith)
      have hoscR := hosc ε γ₀ γ₁ S (Metric.ball x₀ R)
        (fun h => 𝒜 x₀ (U x₀) h - 𝒜 x₀ (U x₀) 0) v gv x₀ (R/4) ρ
        hε0 hγ₀ hγr Metric.isOpen_ball hρ hρ4 hQball hsolT hcb4 hae
      have hVolρ : (0:ℝ) < (volume (Metric.ball x₀ ρ)).toReal := by
        rw [hballvol x₀ ρ hρ.le]
        exact mul_pos hω (Real.rpow_pos_of_pos hρ _)
      have hbρ : Metric.ball x₀ ρ ⊆ Metric.ball x₀ R := Metric.ball_subset_ball hρR
      have hfinρ : IsFiniteMeasure (volume.restrict (Metric.ball x₀ ρ)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
      have hgvρ : MemLp gv (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ ρ)) :=
        hgvR.mono_measure (Measure.restrict_mono hbρ le_rfl)
      have hp1E : (1 : ENNReal) ≤ ENNReal.ofReal p := by
        rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
        exact ENNReal.ofReal_le_ofReal hp.le
      have hgvint : IntegrableOn gv (Metric.ball x₀ ρ) volume := hgvρ.integrable hp1E
      set T : ℝ := C₂ * S * (ρ / (R/4)) ^ α₂ with hTdef
      have hT0 : 0 ≤ T := by
        rw [hTdef]
        exact mul_nonneg (mul_nonneg hC₂pos.le hS0) (Real.rpow_nonneg hρR40 _)
      have hmeanbd : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ)),
          ‖gv x - (volume (Metric.ball x₀ ρ)).toReal⁻¹
            • ∫ y in Metric.ball x₀ ρ, gv y‖ ≤ T := by
        filter_upwards [hoscR] with x hx
        have he : (volume (Metric.ball x₀ ρ)).toReal⁻¹
              • (∫ y in Metric.ball x₀ ρ, (gv x - gv y))
            = gv x - (volume (Metric.ball x₀ ρ)).toReal⁻¹
              • ∫ y in Metric.ball x₀ ρ, gv y := by
          rw [integral_sub (integrable_const (gv x)) hgvint, setIntegral_const,
            Measure.real_def, smul_sub, smul_smul,
            inv_mul_cancel₀ (ne_of_gt hVolρ), one_smul]
        rw [← he, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hVolρ]
        have hb1 : ‖∫ y in Metric.ball x₀ ρ, (gv x - gv y)‖
            ≤ ∫ y in Metric.ball x₀ ρ, ‖gv x - gv y‖ := norm_integral_le_integral_norm _
        have hb2 : (∫ y in Metric.ball x₀ ρ, ‖gv x - gv y‖)
            ≤ (volume (Metric.ball x₀ ρ)).toReal * T := by
          have h := integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun y => norm_nonneg _) (integrable_const T) hx
          rwa [setIntegral_const, Measure.real_def, smul_eq_mul] at h
        calc (volume (Metric.ball x₀ ρ)).toReal⁻¹
              * ‖∫ y in Metric.ball x₀ ρ, (gv x - gv y)‖
            ≤ (volume (Metric.ball x₀ ρ)).toReal⁻¹
                * ((volume (Metric.ball x₀ ρ)).toReal * T) :=
              mul_le_mul_of_nonneg_left (le_trans hb1 hb2) (inv_nonneg.2 hVolρ.le)
          _ = T := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hVolρ), one_mul]
      have hstep : (∫ x in Metric.ball x₀ ρ,
            ‖gv x - (volume (Metric.ball x₀ ρ)).toReal⁻¹
              • ∫ y in Metric.ball x₀ ρ, gv y‖ ^ p)
          ≤ (volume (Metric.ball x₀ ρ)).toReal * T ^ p := by
        have h := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)
          (integrable_const (T ^ p))
          (hmeanbd.mono fun x hx => Real.rpow_le_rpow (norm_nonneg _) hx hp0.le)
        rwa [setIntegral_const, Measure.real_def, smul_eq_mul] at h
      -- the algebra
      have hTp : T ^ p ≤ C₂ ^ p * Sp * (4 ^ p * (ρ / R) ^ (p * α₂)) := by
        have hr4 : ρ / (R/4) = 4 * (ρ / R) := by
          rw [div_div_eq_mul_div, mul_comm ρ (4:ℝ), mul_div_assoc]
        rw [hTdef, Real.mul_rpow (mul_nonneg hC₂pos.le hS0)
            (Real.rpow_nonneg hρR40 _),
          Real.mul_rpow hC₂pos.le hS0, hSpow, hr4,
          ← Real.rpow_mul (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hρR0),
          Real.mul_rpow (by norm_num) hρR0]
        have hexp : α₂ * p ≤ p := by
          calc α₂ * p ≤ 1 * p := mul_le_mul_of_nonneg_right hα₂1 hp0.le
            _ = p := one_mul p
        have h4 : (4:ℝ) ^ (α₂ * p) ≤ 4 ^ p :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        have hcomm : (ρ / R) ^ (α₂ * p) = (ρ / R) ^ (p * α₂) := by rw [mul_comm α₂ p]
        rw [hcomm]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Real.rpow_nonneg hC₂pos.le _) hSp0)
        exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hρR0 _)
      refine le_trans hstep ?_
      rw [hballvol x₀ ρ hρ.le]
      have hnn : (0:ℝ) ≤ ωn * ρ ^ ((n:ℝ)) := mul_nonneg hω.le (Real.rpow_nonneg hρ.le _)
      calc ωn * ρ ^ ((n:ℝ)) * T ^ p
          ≤ ωn * ρ ^ ((n:ℝ)) * (C₂ ^ p * Sp * (4 ^ p * (ρ / R) ^ (p * α₂))) :=
            mul_le_mul_of_nonneg_left hTp hnn
        _ = c₃s * (ρ / R) ^ (p * α₂) * ρ ^ ((n:ℝ)) * Λv := by
            rw [hc₃sdef, hSpdef]; ring
    have hmain := hconc ε Ω Ω' u g (min R₁ 1) hε0 hε1 hΩ hΩ' hcl hR₁f hu hmor hbundle
    intro x₀ hx₀ R ρ hR hRmin hρ hρR
    have hRR₁ : R ≤ R₁ := le_trans hRmin (min_le_left _ _)
    have hRR₃ : R ≤ R₃ := le_trans hRmin (min_le_right _ _)
    have hR1 : R ≤ 1 := le_trans hRR₃ hR₃1
    exact hmain x₀ hx₀ R ρ hR (le_min (le_min hRR₁ hR1) hRR₃)
      (hballs x₀ hx₀ R hR hRR₁) hρ hρR
