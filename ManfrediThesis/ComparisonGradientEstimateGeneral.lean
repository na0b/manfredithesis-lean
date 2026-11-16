import ManfrediThesis.Preamble
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.CitedDirichletHolder
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.EllipticStructureQ345
import ManfrediThesis.EllipticStructureQ6
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.FrozenComparisonOn
import ManfrediThesis.CitedHolderOscillationSolution
import ManfrediThesis.DirichletProblemRestricted
import ManfrediThesis.FrozenSolutionStructureQ12
import ManfrediThesis.FrozenFieldDualMemLp
import ManfrediThesis.SolutionWeakFormDualData
import ManfrediThesis.SolutionFrozenTestIdentity
import ManfrediThesis.SolutionFrozenMonotonicityIntegral
import ManfrediThesis.SolutionFreezingErrorBound
import ManfrediThesis.SolutionRightHandSideBound
import ManfrediThesis.SolutionHolderDatumOnBall
import ManfrediThesis.BallSolutionConstantBounds
import ManfrediThesis.SolutionComparisonModulus
import ManfrediThesis.ModulusPowerDecayTransfer
import ManfrediThesis.WeightedRemainderAbsorption
open MeasureTheory

/-- Lemma 5.1 (clause (A)) together with the §5 analogue of the paper's (4.17)
(clause (B)).  Clause (A) is the paper's lemma verbatim: `σ₂` and `R₁` are bound
after `M`, `d` and `σ` and the Hölder parameters `α, δ` are nowhere in its
scope, because Lemma 5.1 assumes no rate for the modulus of (Q6).  Clause (B)
carries its own `α, δ` prefix; its rate exponent `δ'` is bound after
`n, p, μ, γ₀, …, γ₄, α, δ` and before `M`, `d`, `σ`, `cσ` and `C₁`, and its
radius threshold `R₁'` carries those constants. -/
theorem ComparisonGradientEstimateGeneral :
    ∀ (n : ℕ) (p μ γ₀ γ₁ γ₂ γ₃ γ₄ : ℝ),
      2 ≤ n → 1 < p → 0 < μ → 0 < γ₀ → γ₀ ≤ γ₁ → 0 < γ₂ → 0 < γ₃ → 0 < γ₄ →
      CitedSobolevPoincareBall n →
      (∀ (ε' γ₀' γ₁' : ℝ)
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → CitedDirichletHolder n p ε' γ₀' γ₁' A') →
      (∀ (M d : ℝ) (σ : ℝ → ℝ), 0 ≤ M → 0 < d →
        ∃ (σ₂ : ℝ → ℝ) (R₁ : ℝ), 0 < R₁ ∧ (∃ C : ℝ, ∀ t : ℝ, σ₂ t ≤ C) ∧
          Continuous σ₂ ∧ Monotone σ₂ ∧ σ₂ 0 = 0 ∧ (∀ t : ℝ, 0 ≤ σ₂ t) ∧
          ∀ (ε : ℝ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
            (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
              EuclideanSpace ℝ (Fin n))
            (B : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
            (u U : EuclideanSpace ℝ (Fin n) → ℝ)
            (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
            (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
            (v V : EuclideanSpace ℝ (Fin n) → ℝ)
            (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
            0 ≤ ε → ε ≤ 1 → IsOpen Ω → IsOpen Ω' → Bornology.IsBounded Ω' →
            closure Ω' ⊆ Ω → (∀ x ∈ Ω', ∀ y, y ∉ Ω → d ≤ dist x y) →
            EllipticStructureQ12 n p ε γ₀ γ₁ Ω A →
            EllipticStructureQ345 n p ε μ γ₂ γ₃ γ₄ Ω A B →
            EllipticStructureQ6 n p Ω A σ →
            CitedHolderOscillationSolution n p →
            MemW1pOn n p Ω u g → (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
            IsWeakSolutionOn n p Ω A B u g →
            x₀ ∈ Ω' → 0 < R → R ≤ R₁ → Metric.closedBall x₀ R ⊆ Ω →
            FrozenComparisonOn n p x₀ R (fun h => A x₀ (U x₀) h) u U g v V gv →
            (∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p)
              ≤ σ₂ R * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2))
      ∧ (∀ α δ : ℝ, 0 < α → α ≤ 1 → 0 < δ →
          ∃ δ' : ℝ, 0 < δ' ∧
            ∀ (M d : ℝ) (σ : ℝ → ℝ), 0 ≤ M → 0 < d →
              ∀ cσ C₁ : ℝ, 0 < cσ → 0 ≤ C₁ →
                (∀ t : ℝ, 0 ≤ t → σ t ≤ cσ * t ^ δ) →
                ∃ R₁' : ℝ, 0 < R₁' ∧
                  ∀ (ε : ℝ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
                    (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
                      EuclideanSpace ℝ (Fin n))
                    (B : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
                    (u U : EuclideanSpace ℝ (Fin n) → ℝ)
                    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
                    (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
                    (v V : EuclideanSpace ℝ (Fin n) → ℝ)
                    (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
                    0 ≤ ε → ε ≤ 1 → IsOpen Ω → IsOpen Ω' → Bornology.IsBounded Ω' →
                    closure Ω' ⊆ Ω → (∀ x ∈ Ω', ∀ y, y ∉ Ω → d ≤ dist x y) →
                    EllipticStructureQ12 n p ε γ₀ γ₁ Ω A →
                    EllipticStructureQ345 n p ε μ γ₂ γ₃ γ₄ Ω A B →
                    EllipticStructureQ6 n p Ω A σ →
                    CitedHolderOscillationSolution n p →
                    MemW1pOn n p Ω u g → (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
                    IsWeakSolutionOn n p Ω A B u g →
                    x₀ ∈ Ω' → 0 < R → R ≤ R₁' → Metric.closedBall x₀ R ⊆ Ω →
                    FrozenComparisonOn n p x₀ R (fun h => A x₀ (U x₀) h) u U g v V gv →
                    (∀ x ∈ Metric.closedBall x₀ R, ∀ y ∈ Metric.closedBall x₀ R,
                      |U x - U y| ≤ C₁ * dist x y ^ α) →
                    (∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p)
                      ≤ R ^ δ' * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2)) := by
  intro n p μ γ₀ γ₁ γ₂ γ₃ γ₄ hn hp hμ hγ₀ hγ₀γ₁ hγ₂ hγ₃ hγ₄ hSP _hDH
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hp0 : (0:ℝ) < p := by linarith
  have hγ₁0 : (0:ℝ) < γ₁ := lt_of_lt_of_le hγ₀ hγ₀γ₁
  obtain ⟨CM, hCM0, hMono⟩ :=
    SolutionFrozenMonotonicityIntegral n p (γ₁/γ₀) hn hp (div_pos hγ₁0 hγ₀)
  obtain ⟨b₀, cA, hb₀, hcA, habs⟩ := WeightedRemainderAbsorption p hp
  have hK0 : (0:ℝ) < 1 / (γ₀ * CM) := by positivity
  -- the σ₂ package, from σ₀ and σ₁
  have hsig2 : ∀ σ₀ σ₁ : ℝ → ℝ,
      (∀ t : ℝ, 0 ≤ σ₀ t) → (∀ t : ℝ, 0 ≤ σ₁ t) →
      (∃ C : ℝ, ∀ t : ℝ, σ₀ t ≤ C ∧ σ₁ t ≤ C) →
      Continuous σ₀ → Continuous σ₁ → Monotone σ₀ → Monotone σ₁ →
      σ₀ 0 = 0 → σ₁ 0 = 0 →
      (∃ C : ℝ, ∀ t : ℝ,
          cA * (σ₀ t + σ₀ t ^ (p/2) + σ₁ t ^ (p/2)) ≤ C)
        ∧ Continuous (fun t => cA * (σ₀ t + σ₀ t ^ (p/2) + σ₁ t ^ (p/2)))
        ∧ Monotone (fun t => cA * (σ₀ t + σ₀ t ^ (p/2) + σ₁ t ^ (p/2)))
        ∧ cA * (σ₀ 0 + σ₀ 0 ^ (p/2) + σ₁ 0 ^ (p/2)) = 0
        ∧ ∀ t : ℝ, 0 ≤ cA * (σ₀ t + σ₀ t ^ (p/2) + σ₁ t ^ (p/2)) := by
    intro σ₀ σ₁ h0nn h1nn hbd h0c h1c h0m h1m h00 h10
    obtain ⟨Cb, hCb⟩ := hbd
    have hCb0 : (0:ℝ) ≤ Cb := by have := (hCb 0).1; rw [h00] at this; exact this
    have hrp : ∀ (f : ℝ → ℝ), Continuous f → (∀ t, 0 ≤ f t) →
        Continuous (fun t => f t ^ (p/2)) := by
      intro f hf _
      exact hf.rpow_const fun t => Or.inr (by positivity)
    have hA : Continuous fun t : ℝ => σ₀ t := h0c
    have hB : Continuous fun t : ℝ => σ₀ t ^ (p/2) := hrp σ₀ h0c h0nn
    have hD : Continuous fun t : ℝ => σ₁ t ^ (p/2) := hrp σ₁ h1c h1nn
    refine ⟨⟨cA * (Cb + Cb ^ (p/2) + Cb ^ (p/2)), fun t => ?_⟩,
      ((hA.add hB).add hD).const_mul cA, ?_, ?_, fun t => ?_⟩
    · have e1 : σ₀ t ^ (p/2) ≤ Cb ^ (p/2) :=
        Real.rpow_le_rpow (h0nn t) (hCb t).1 (by positivity)
      have e2 : σ₁ t ^ (p/2) ≤ Cb ^ (p/2) :=
        Real.rpow_le_rpow (h1nn t) (hCb t).2 (by positivity)
      have e3 := (hCb t).1
      nlinarith [hcA]
    · intro s t hst
      have e1 : σ₀ s ^ (p/2) ≤ σ₀ t ^ (p/2) :=
        Real.rpow_le_rpow (h0nn s) (h0m hst) (by positivity)
      have e2 : σ₁ s ^ (p/2) ≤ σ₁ t ^ (p/2) :=
        Real.rpow_le_rpow (h1nn s) (h1m hst) (by positivity)
      have e3 := h0m hst
      nlinarith [hcA]
    · rw [h00, h10, Real.zero_rpow (by positivity : p/2 ≠ 0)]
      ring
    · have e1 : (0:ℝ) ≤ σ₀ t ^ (p/2) := Real.rpow_nonneg (h0nn t) _
      have e2 : (0:ℝ) ≤ σ₁ t ^ (p/2) := Real.rpow_nonneg (h1nn t) _
      have e3 := h0nn t
      positivity
  -- the shared core: (5.9) from a Hölder datum
  have hcore : ∀ (σ : ℝ → ℝ) (Cs α C₁ : ℝ),
      Continuous σ → Monotone σ → σ 0 = 0 → (∀ t : ℝ, σ t ≤ Cs) →
      0 < α → α ≤ 1 → 0 ≤ C₁ →
      ∃ σ₀ σ₁ : ℝ → ℝ,
        (∀ t : ℝ, 0 ≤ σ₀ t) ∧ (∀ t : ℝ, 0 ≤ σ₁ t) ∧
        (∃ C : ℝ, ∀ t : ℝ, σ₀ t ≤ C ∧ σ₁ t ≤ C) ∧
        Continuous σ₀ ∧ Continuous σ₁ ∧ Monotone σ₀ ∧ Monotone σ₁ ∧
        σ₀ 0 = 0 ∧ σ₁ 0 = 0 ∧
        (∀ t : ℝ, 0 < t → t ≤ 1 →
            σ₀ t = (1/(γ₀*CM)) * ((p - 1) / p * σ (t + C₁ * t ^ α)
              + 4 * γ₄ * C₁ * t ^ α)) ∧
        (∀ t : ℝ, 0 < t → t ≤ 1 →
            σ₁ t = (1/(γ₀*CM)) * (1 / p * σ (t + C₁ * t ^ α))) ∧
        ∀ (ε : ℝ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
          (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
            EuclideanSpace ℝ (Fin n))
          (Bf : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
          (u U : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
          (v V : EuclideanSpace ℝ (Fin n) → ℝ)
          (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 ≤ ε → ε ≤ 1 → IsOpen Ω →
          EllipticStructureQ12 n p ε γ₀ γ₁ Ω A →
          EllipticStructureQ345 n p ε μ γ₂ γ₃ γ₄ Ω A Bf →
          EllipticStructureQ6 n p Ω A σ →
          MemW1pOn n p Ω u g →
          IsWeakSolutionOn n p Ω A Bf u g →
          0 < R → R ≤ 1 → Metric.closedBall x₀ R ⊆ Ω →
          FrozenComparisonOn n p x₀ R (fun h => A x₀ (U x₀) h) u U g v V gv →
          (∀ x ∈ Metric.closedBall x₀ R, |U x - U x₀| ≤ C₁ * R ^ α) →
          (∫ x in Metric.ball x₀ R,
              (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2)
            ≤ σ₀ R * (∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2))
              + σ₁ R * ∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p := by
    intro σ Cs α C₁ hσc hσm hσ0 hσb hα0 hα1 hC₁
    obtain ⟨σ₀, σ₁, hf0, hf1, hnn0, hnn1, hbd, hc0, hc1, hm0, hm1, hz0, hz1⟩ :=
      SolutionComparisonModulus p α C₁ (1/(γ₀*CM)) γ₄ Cs σ hp hα0 hα1 hC₁ hK0 hγ₄
        hσc hσm hσ0 hσb
    refine ⟨σ₀, σ₁, hnn0, hnn1, hbd, hc0, hc1, hm0, hm1, hz0, hz1, hf0, hf1, ?_⟩
    intro ε Ω Ω' A Bf u U g x₀ R v V gv hε hε1 hΩ hQ12 hQ345 hQ6 huW hsol hR hR1
      hcb hfc hHolR
    obtain ⟨hsol0, hvW, hzeroW, hUc, hUu, hVc, hVv, hVU⟩ := hfc
    have hBsub : Metric.ball x₀ R ⊆ Ω := Metric.ball_subset_closedBall.trans hcb
    have hx₀Ω : x₀ ∈ Ω := hcb (Metric.mem_closedBall_self hR.le)
    have hBfin : volume (Metric.ball x₀ R) ≠ ⊤ := measure_ball_lt_top.ne
    have hCR0 : (0:ℝ) ≤ C₁ * R ^ α := by positivity
    -- the Lebesgue data on the ball
    have hgB : MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) :=
      huW.2.2.mono_measure (Measure.restrict_mono hBsub le_rfl)
    have huB : MemLp u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) :=
      huW.2.1.mono_measure (Measure.restrict_mono hBsub le_rfl)
    have hgvB : MemLp gv (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ R)) := hvW.2.2
    have hdiffB := hgB.sub hgvB
    -- Step 1: the frozen field, before and after normalisation
    have hQ12f := FrozenSolutionStructureQ12 n p ε γ₀ γ₁ hn hp hε hγ₀ hγ₁0 Ω A σ
      x₀ (U x₀) hΩ hx₀Ω hQ12 hQ6
    obtain ⟨hAu, hBfint⟩ := SolutionWeakFormDualData n p ε μ γ₀ γ₁ γ₂ γ₃ γ₄ hn hp
      hε hε1 hγ₀ hγ₁0 hγ₃ hγ₄ Ω A Bf u g (Metric.ball x₀ R) hQ12 hQ345
      measurableSet_ball hBsub hBfin huB hgB
    have hA0g := FrozenFieldDualMemLp n p ε γ₀ γ₁ hn hp hε hε1 hγ₀ hγ₁0
      (fun h => A x₀ (U x₀) h) hQ12f.2 (Metric.ball x₀ R) g hBfin hgB
    have hA0gv := FrozenFieldDualMemLp n p ε γ₀ γ₁ hn hp hε hε1 hγ₀ hγ₁0
      (fun h => A x₀ (U x₀) h) hQ12f.2 (Metric.ball x₀ R) gv hBfin hgvB
    -- the Hölder pairing is integrable
    have hIP : ∀ a b : EuclideanSpace ℝ (Fin n),
        (∑ i, a i * b i) = (innerSL ℝ b) a := by
      intro a b
      show (∑ i, a i * b i) = inner ℝ b a
      rw [PiLp.inner_apply]
      exact Finset.sum_congr rfl fun i _ => by simp
    have hCS : ∀ a b : EuclideanSpace ℝ (Fin n), |∑ i, a i * b i| ≤ ‖a‖ * ‖b‖ := by
      intro a b
      rw [hIP a b, mul_comm ‖a‖ ‖b‖]
      exact abs_real_inner_le_norm b a
    have hconj : Real.HolderConjugate p (p / (p - 1)) :=
      (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
    have hHT : ENNReal.HolderTriple (ENNReal.ofReal (p / (p - 1)))
        (ENNReal.ofReal p) 1 :=
      ⟨by rw [inv_one]; exact hconj.symm.inv_add_inv_ennreal⟩
    have hpair : ∀ F H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        MemLp F (ENNReal.ofReal (p / (p - 1)))
            (volume.restrict (Metric.ball x₀ R)) →
        MemLp H (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) →
        IntegrableOn (fun x => ∑ i, F x i * H x i) (Metric.ball x₀ R) volume := by
      intro F H hF hH
      have hprod : Integrable (fun x => ‖F x‖ * ‖H x‖)
          (volume.restrict (Metric.ball x₀ R)) := hF.norm.integrable_mul hH.norm
      have hmeas : AEStronglyMeasurable (fun x => ∑ i, F x i * H x i)
          (volume.restrict (Metric.ball x₀ R)) := by
        have hinner : AEStronglyMeasurable (fun x => (inner ℝ (H x) (F x) : ℝ))
            (volume.restrict (Metric.ball x₀ R)) :=
          (continuous_inner (𝕜 := ℝ)
            (E := EuclideanSpace ℝ (Fin n))).comp_aestronglyMeasurable
            (hH.aestronglyMeasurable.prodMk hF.aestronglyMeasurable)
        exact hinner.congr (Filter.Eventually.of_forall fun x => (hIP (F x) (H x)).symm)
      refine hprod.mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs]
      exact hCS _ _
    -- (6b): the comparison bound for v against the two constants
    have hsphere : ∀ x ∈ Metric.sphere x₀ R,
        U x₀ - C₁ * R ^ α ≤ V x ∧ V x ≤ U x₀ + C₁ * R ^ α := by
      intro x hx
      have h1 := hHolR x (Metric.sphere_subset_closedBall hx)
      have h2 := abs_le.1 h1
      rw [hVU x hx]
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    have hvbd := BallSolutionConstantBounds n p ε γ₀ γ₁ hn hp hε hγ₀ hγ₀γ₁ hSP
      (fun h => A x₀ (U x₀) h) x₀ R v V gv (U x₀ - C₁ * R ^ α) (U x₀ + C₁ * R ^ α)
      hR hQ12f.2 hsol0 hvW hVc hVv hsphere
    have huv : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
        |u x - v x| ≤ 4 * C₁ * R ^ α := by
      filter_upwards [hvbd, ae_restrict_mem measurableSet_ball] with x hv hx
      have h1 : |u x - U x₀| ≤ C₁ * R ^ α := by
        rw [← hUu x hx]
        exact hHolR x (Metric.ball_subset_closedBall hx)
      have h2 := abs_le.1 h1
      rw [abs_le]
      exact ⟨by linarith [hv.2], by linarith [hv.1]⟩
    -- (5.4)
    have h54 := SolutionFrozenTestIdentity n p hn1 hp Ω A Bf u U g x₀ R
      (4 * C₁ * R ^ α) v V gv hΩ hR hBsub hsol
      ⟨hsol0, hvW, hzeroW, hUc, hUu, hVc, hVv, hVU⟩ hAu hA0g hA0gv hdiffB hBfint
      (by positivity) huv
    -- (5.5)
    have hI1int : IntegrableOn
        (fun x => ∑ i, (A x₀ (U x₀) (g x) - A x₀ (U x₀) (gv x)) i * (g x - gv x) i)
        (Metric.ball x₀ R) volume :=
      hpair (fun x => A x₀ (U x₀) (g x) - A x₀ (U x₀) (gv x))
        (fun x => g x - gv x) (hA0g.sub hA0gv) hdiffB
    have hγ₀ne : γ₀ ≠ 0 := ne_of_gt hγ₀
    have hγratio : γ₁ ≤ γ₁ / γ₀ * γ₀ := by
      rw [div_mul_cancel₀ _ hγ₀ne]
    have h55 := hMono ε γ₀ γ₁ (fun h => A x₀ (U x₀) h) x₀ R g gv hε hγ₀ hγratio hR
      hQ12f.1 hgB hgvB hdiffB hI1int
    -- (5.7)
    have hu0 : ∀ x ∈ Metric.ball x₀ R, |u x - U x₀| ≤ C₁ * R ^ α := by
      intro x hx
      rw [← hUu x hx]
      exact hHolR x (Metric.ball_subset_closedBall hx)
    have h57 := SolutionFreezingErrorBound n p hn1 hp Ω A σ u g gv x₀ (U x₀) R α C₁
      hQ6 hx₀Ω hR hBsub hα0 hC₁ hu0 hgB hdiffB hAu hA0g
    -- (5.8)
    have h58 := SolutionRightHandSideBound n p ε μ γ₂ γ₃ γ₄ hn1 hp hγ₄ Ω A Bf u v g
      x₀ R α C₁ hR hBsub hα0 hC₁ hQ345 hgB huB.aestronglyMeasurable
      hvW.2.1.aestronglyMeasurable hBfint huv
    -- (5.9)
    rw [hf0 R hR hR1, hf1 R hR hR1]
    have hγ₀' : γ₀ ≠ 0 := ne_of_gt hγ₀
    have hCM' : CM ≠ 0 := ne_of_gt hCM0
    have key : CM * γ₀ * (∫ x in Metric.ball x₀ R,
          (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2)
        ≤ ((p - 1) / p * σ (R + C₁ * R ^ α) + 4 * γ₄ * C₁ * R ^ α)
            * (∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2))
          + 1 / p * σ (R + C₁ * R ^ α)
            * ∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p := by
      nlinarith [h55, h54, h57, h58]
    calc (∫ x in Metric.ball x₀ R,
            (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2)
        = 1 / (γ₀ * CM) * (CM * γ₀ * ∫ x in Metric.ball x₀ R,
            (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2) := by
          field_simp
      _ ≤ 1 / (γ₀ * CM)
            * (((p - 1) / p * σ (R + C₁ * R ^ α) + 4 * γ₄ * C₁ * R ^ α)
                * (∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2))
              + 1 / p * σ (R + C₁ * R ^ α)
                * ∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = 1 / (γ₀ * CM) * ((p - 1) / p * σ (R + C₁ * R ^ α)
              + 4 * γ₄ * C₁ * R ^ α)
            * (∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2))
          + 1 / (γ₀ * CM) * (1 / p * σ (R + C₁ * R ^ α))
            * ∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p := by ring
  refine ⟨?_, ?_⟩
  · -- clause (A)
    intro M d σ hM hd
    by_cases hdec : ((∃ C : ℝ, ∀ t : ℝ, σ t ≤ C) ∧ Continuous σ ∧ Monotone σ
        ∧ σ 0 = 0) ∧ CitedHolderOscillationSolution n p
    · -- the four σ-clauses and the cited oscillation estimate hold
      obtain ⟨⟨⟨Cs, hCs⟩, hσc, hσm, hσ0⟩, hC4⟩ := hdec
      obtain ⟨α, R₀, C₁, hα0, hα1, hR₀0, hC₁, hHol⟩ :=
        SolutionHolderDatumOnBall n p μ γ₀ γ₁ γ₂ γ₃ γ₄ M d hn1 hp hμ hγ₀ hγ₀γ₁
          hγ₂ hγ₃ hγ₄ hM hd hC4
      obtain ⟨σ₀, σ₁, hnn0, hnn1, hbd, hc0, hc1, hm0, hm1, hz0, hz1, hf0, hf1,
        hmain⟩ := hcore σ Cs α C₁ hσc hσm hσ0 hCs hα0 hα1 hC₁
      obtain ⟨hs2bd, hs2c, hs2m, hs2z, hs2nn⟩ :=
        hsig2 σ₀ σ₁ hnn0 hnn1 hbd hc0 hc1 hm0 hm1 hz0 hz1
      have hthr : ∃ ρ : ℝ, 0 < ρ ∧ σ₁ ρ ≤ b₀ := by
        have h1 : σ₁ 0 < b₀ := by rw [hz1]; exact hb₀
        have hca : ContinuousAt σ₁ (0:ℝ) := hc1.continuousAt
        rw [Metric.continuousAt_iff] at hca
        obtain ⟨ρ, hρ0, hρ⟩ := hca (b₀ - σ₁ 0) (by linarith)
        refine ⟨ρ/2, by positivity, ?_⟩
        have h2 : dist (ρ/2) (0:ℝ) < ρ := by
          rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
        have h3 := hρ h2
        rw [Real.dist_eq] at h3
        have h4 := abs_lt.1 h3
        linarith [h4.2]
      obtain ⟨ρ, hρ0, hρ⟩ := hthr
      refine ⟨fun t => cA * (σ₀ t + σ₀ t ^ (p/2) + σ₁ t ^ (p/2)),
        min (min R₀ 1) ρ, lt_min (lt_min hR₀0 one_pos) hρ0, hs2bd, hs2c, hs2m,
        hs2z, hs2nn, ?_⟩
      intro ε Ω Ω' A Bf u U g x₀ R v V gv hε hε1 hΩ hΩ' hΩ'b hclΩ hsep hQ12 hQ345
        hQ6 _hC4' huW huM hsol hx₀ hR hRR₁ hcb hfc
      have hR1 : R ≤ 1 :=
        le_trans hRR₁ (le_trans (min_le_left _ _) (min_le_right _ _))
      have hRR₀ : R ≤ R₀ :=
        le_trans hRR₁ (le_trans (min_le_left _ _) (min_le_left _ _))
      have hRρ : R ≤ ρ := le_trans hRR₁ (min_le_right _ _)
      obtain ⟨hsol0, hvW, hzeroW, hUc, hUu, hVc, hVv, hVU⟩ := hfc
      have hHolR := hHol ε Ω Ω' A Bf u U g x₀ R hε hε1 hΩ hsep hx₀ hQ12 hQ345
        hsol huM hR hRR₀ hUc hUu
      have h59 := hmain ε Ω Ω' A Bf u U g x₀ R v V gv hε hε1 hΩ hQ12 hQ345 hQ6
        huW hsol hR hR1 hcb ⟨hsol0, hvW, hzeroW, hUc, hUu, hVc, hVv, hVU⟩ hHolR
      have hBsub : Metric.ball x₀ R ⊆ Ω := Metric.ball_subset_closedBall.trans hcb
      have hgB : MemLp g (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R)) :=
        huW.2.2.mono_measure (Measure.restrict_mono hBsub le_rfl)
      exact habs n ε (σ₀ R) (σ₁ R) (Metric.ball x₀ R) g gv hε hε1
        (hnn0 R) (hnn1 R) (le_trans (hm1 hRρ) hρ) measurableSet_ball
        measure_ball_lt_top.ne hgB hvW.2.2 (hgB.sub hvW.2.2) h59
    · refine ⟨fun _ => 0, 1, one_pos, ⟨0, fun _ => le_rfl⟩, continuous_const,
        monotone_const, rfl, fun _ => le_rfl, ?_⟩
      intro ε Ω Ω' A Bf u U g x₀ R v V gv _ _ _ _ _ _ _ _ _ hQ6 hC4 _ _ _ _ _ _ _ _
      exact absurd ⟨⟨hQ6.σ_bdd, hQ6.σ_cont, hQ6.σ_mono, hQ6.σ_zero⟩, hC4⟩ hdec
  · -- clause (B)
    intro α δ hα0 hα1 hδ0
    obtain ⟨δ', hδ'0, htrans⟩ := ModulusPowerDecayTransfer p α δ hp hα0 hα1 hδ0
    refine ⟨δ', hδ'0, ?_⟩
    intro M d σ hM hd cσ C₁ hcσ hC₁ hrate
    by_cases hdec : (∃ C : ℝ, ∀ t : ℝ, σ t ≤ C) ∧ Continuous σ ∧ Monotone σ
        ∧ σ 0 = 0
    · -- the four σ-clauses hold
      obtain ⟨⟨Cs, hCs⟩, hσc, hσm, hσ0⟩ := hdec
      obtain ⟨σ₀, σ₁, hnn0, hnn1, hbd, hc0, hc1, hm0, hm1, hz0, hz1, hf0, hf1,
        hmain⟩ := hcore σ Cs α C₁ hσc hσm hσ0 hCs hα0 hα1 hC₁
      obtain ⟨R₂, hR₂0, hR₂1, hR₂⟩ :=
        htrans cσ C₁ (1/(γ₀*CM)) γ₄ cA σ σ₀ σ₁ hcσ hC₁ hK0 hγ₄ hcA hrate hf0 hf1
          hnn0 hnn1
      have hthr : ∃ ρ : ℝ, 0 < ρ ∧ σ₁ ρ ≤ b₀ := by
        have h1 : σ₁ 0 < b₀ := by rw [hz1]; exact hb₀
        have hca : ContinuousAt σ₁ (0:ℝ) := hc1.continuousAt
        rw [Metric.continuousAt_iff] at hca
        obtain ⟨ρ, hρ0, hρ⟩ := hca (b₀ - σ₁ 0) (by linarith)
        refine ⟨ρ/2, by positivity, ?_⟩
        have h2 : dist (ρ/2) (0:ℝ) < ρ := by
          rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
        have h3 := hρ h2
        rw [Real.dist_eq] at h3
        have h4 := abs_lt.1 h3
        linarith [h4.2]
      obtain ⟨ρ, hρ0, hρ⟩ := hthr
      refine ⟨min R₂ ρ, lt_min hR₂0 hρ0, ?_⟩
      intro ε Ω Ω' A Bf u U g x₀ R v V gv hε hε1 hΩ hΩ' hΩ'b hclΩ hsep hQ12 hQ345
        hQ6 _hC4' huW huM hsol hx₀ hR hRR₁ hcb hfc hHol2
      have hRR₂ : R ≤ R₂ := le_trans hRR₁ (min_le_left _ _)
      have hR1 : R ≤ 1 := le_trans hRR₂ hR₂1
      have hRρ : R ≤ ρ := le_trans hRR₁ (min_le_right _ _)
      obtain ⟨hsol0, hvW, hzeroW, hUc, hUu, hVc, hVv, hVU⟩ := hfc
      have hHolR : ∀ x ∈ Metric.closedBall x₀ R, |U x - U x₀| ≤ C₁ * R ^ α := by
        intro x hx
        have h1 := hHol2 x hx x₀ (Metric.mem_closedBall_self hR.le)
        have h2 : dist x x₀ ≤ R := Metric.mem_closedBall.1 hx
        have h3 : dist x x₀ ^ α ≤ R ^ α :=
          Real.rpow_le_rpow dist_nonneg h2 hα0.le
        nlinarith [hC₁, h1, h3]
      have h59 := hmain ε Ω Ω' A Bf u U g x₀ R v V gv hε hε1 hΩ hQ12 hQ345 hQ6
        huW hsol hR hR1 hcb ⟨hsol0, hvW, hzeroW, hUc, hUu, hVc, hVv, hVU⟩ hHolR
      have hBsub : Metric.ball x₀ R ⊆ Ω := Metric.ball_subset_closedBall.trans hcb
      have hgB : MemLp g (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R)) :=
        huW.2.2.mono_measure (Measure.restrict_mono hBsub le_rfl)
      have habsR := habs n ε (σ₀ R) (σ₁ R) (Metric.ball x₀ R) g gv hε hε1
        (hnn0 R) (hnn1 R) (le_trans (hm1 hRρ) hρ) measurableSet_ball
        measure_ball_lt_top.ne hgB hvW.2.2 (hgB.sub hvW.2.2) h59
      have hJ0 : (0:ℝ) ≤ ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2) :=
        setIntegral_nonneg measurableSet_ball fun x _ => by positivity
      exact le_trans habsR
        (mul_le_mul_of_nonneg_right (hR₂ R hR hRR₂) hJ0)
    · refine ⟨1, one_pos, ?_⟩
      intro ε Ω Ω' A Bf u U g x₀ R v V gv _ _ _ _ _ _ _ _ _ hQ6 _ _ _ _ _ _ _ _ _ _
      exact absurd ⟨hQ6.σ_bdd, hQ6.σ_cont, hQ6.σ_mono, hQ6.σ_zero⟩ hdec
