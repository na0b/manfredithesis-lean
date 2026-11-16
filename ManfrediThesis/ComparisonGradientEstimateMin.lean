import ManfrediThesis.Preamble
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.CitedDirichletHolder
import ManfrediThesis.FrozenOperatorStructureQ12
import ManfrediThesis.VariationalStructureF123
import ManfrediThesis.IsLocalMinimumOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.FrozenComparisonOn
import ManfrediThesis.FrozenGradientOperator
import ManfrediThesis.MidpointGradientWeightBound
import ManfrediThesis.SegmentSecondOrderIdentity
import ManfrediThesis.FrozenFieldDualMemLp
import ManfrediThesis.WeakSolutionZeroTest
import ManfrediThesis.LocalMinimumZeroTest
import ManfrediThesis.BallSolutionConstantBounds
import ManfrediThesis.BallComparisonPrinciple
import ManfrediThesis.MinimumHolderDatumOnBall
import ManfrediThesis.VariationalGrowthF1
import ManfrediThesis.FrozenFreezingErrorBound
import ManfrediThesis.WeightedRemainderAbsorption
import ManfrediThesis.DirichletProblemRestricted
import ManfrediThesis.CitedHolderOscillationMinimum
open MeasureTheory
set_option maxHeartbeats 600000

/-- Lemma 4.1 (clause (A)) together with the paper's (4.17) (clause (B)).
Clause (A) is the paper's lemma verbatim: `σ₂` and `R₁` are bound after
`M`, `d` and `σ` and the Hölder parameters `α, δ` are nowhere in its scope,
because Lemma 4.1 does not assume (F4).  Clause (B) carries its own `α, δ`
prefix; its rate exponent `δ'` is bound after `n, p, λ, Λ, a, ν₀, ν₁, α, δ`
and before `M`, `d`, `σ`, `cσ` and `C₁`, which is the dependence the paper
records at l. 1359-1362, and its radius threshold `R₁'` carries those
constants. -/
theorem ComparisonGradientEstimateMin :
    ∀ (n : ℕ) (p lam Lam a ν₀ ν₁ : ℝ),
      2 ≤ n → 1 < p → 0 < lam → lam ≤ Lam → 0 < a → 0 < ν₀ → ν₀ < ν₁ →
      CitedSobolevPoincareBall n →
      (∀ (ε' γ₀' γ₁' : ℝ)
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → CitedDirichletHolder n p ε' γ₀' γ₁' A') →
      (∀ (M d : ℝ) (σ : ℝ → ℝ), 0 ≤ M → 0 < d →
        ∃ (σ₂ : ℝ → ℝ) (R₁ : ℝ), 0 < R₁ ∧ (∃ C : ℝ, ∀ t : ℝ, σ₂ t ≤ C) ∧
          Continuous σ₂ ∧ Monotone σ₂ ∧ σ₂ 0 = 0 ∧ (∀ t : ℝ, 0 ≤ σ₂ t) ∧
          ∀ (ε : ℝ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
            (fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
            (u U : EuclideanSpace ℝ (Fin n) → ℝ)
            (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
            (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
            (v V : EuclideanSpace ℝ (Fin n) → ℝ)
            (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
            0 ≤ ε → ε ≤ 1 → IsOpen Ω → IsOpen Ω' → Bornology.IsBounded Ω' →
            closure Ω' ⊆ Ω → (∀ x ∈ Ω', ∀ y, y ∉ Ω → d ≤ dist x y) →
            VariationalStructureF123 n p ε lam Lam a ν₀ ν₁ Ω fdens σ →
            CitedHolderOscillationMinimum n p →
            MemW1pOn n p Ω u g → (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
            IsLocalMinimumOn n p Ω fdens u g →
            x₀ ∈ Ω' → 0 < R → R ≤ R₁ → Metric.closedBall x₀ R ⊆ Ω →
            FrozenComparisonOn n p x₀ R
              (FrozenGradientOperator n fdens x₀ (U x₀)) u U g v V gv →
            (∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p)
              ≤ σ₂ R * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2))
      ∧ (∀ α δ : ℝ, 0 < α → α ≤ 1 → 0 < δ →
          ∃ δ' : ℝ, 0 < δ' ∧
            ∀ (M d : ℝ) (σ : ℝ → ℝ), 0 ≤ M → 0 < d →
              ∀ cσ C₁ : ℝ, 0 < cσ → 0 ≤ C₁ →
                (∀ t : ℝ, 0 ≤ t → σ t ≤ cσ * t ^ δ) →
                ∃ R₁' : ℝ, 0 < R₁' ∧
                  ∀ (ε : ℝ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
                    (fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
                    (u U : EuclideanSpace ℝ (Fin n) → ℝ)
                    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
                    (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
                    (v V : EuclideanSpace ℝ (Fin n) → ℝ)
                    (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
                    0 ≤ ε → ε ≤ 1 → IsOpen Ω → IsOpen Ω' → Bornology.IsBounded Ω' →
                    closure Ω' ⊆ Ω → (∀ x ∈ Ω', ∀ y, y ∉ Ω → d ≤ dist x y) →
                    VariationalStructureF123 n p ε lam Lam a ν₀ ν₁ Ω fdens σ →
                    CitedHolderOscillationMinimum n p →
                    MemW1pOn n p Ω u g → (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
                    IsLocalMinimumOn n p Ω fdens u g →
                    x₀ ∈ Ω' → 0 < R → R ≤ R₁' → Metric.closedBall x₀ R ⊆ Ω →
                    FrozenComparisonOn n p x₀ R
                      (FrozenGradientOperator n fdens x₀ (U x₀)) u U g v V gv →
                    (∀ x ∈ Metric.closedBall x₀ R, ∀ y ∈ Metric.closedBall x₀ R,
                      |U x - U y| ≤ C₁ * dist x y ^ α) →
                    (∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p)
                      ≤ R ^ δ' * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2)) := by
  intro n p lam Lam a ν₀ ν₁ hn hp hlam hlamLam ha hν₀ hν₁ hSP hC3
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hp0 : (0:ℝ) < p := by linarith
  have hν₁0 : 0 < ν₁ := lt_trans hν₀ hν₁
  have hLam0 : (0:ℝ) ≤ Lam := le_trans hlam.le hlamLam
  obtain ⟨Cm, hCm0, hCm⟩ := MidpointGradientWeightBound p hp
  obtain ⟨b₀, cA, hb₀, hcA, habs⟩ := WeightedRemainderAbsorption p hp
  have hKpos : (0:ℝ) < 1 / (ν₀ * Cm) := by positivity
  -- the σ₂ built from σ₀ and σ₁, and its five properties
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
      ((hA.add hB).add hD).const_mul cA,
      ?_, ?_, fun t => ?_⟩
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
  -- the shared core: (4.8) from a Hölder datum
  have hcore : ∀ (σ : ℝ → ℝ) (Cs α C₁ : ℝ),
      Continuous σ → Monotone σ → σ 0 = 0 → (∀ t : ℝ, σ t ≤ Cs) →
      0 < α → α ≤ 1 → 0 ≤ C₁ →
      ∃ (C₂ : ℝ) (σ₀ σ₁ : ℝ → ℝ), 0 < C₂ ∧
        (∀ t : ℝ, 0 < t →
          σ₀ t = (1/(ν₀*Cm)) * (σ (t + C₁ * t ^ α) + C₂ * σ (t + 2*C₁ * t ^ α))) ∧
        (∀ t : ℝ, 0 < t → σ₁ t = (1/(ν₀*Cm)) * (C₂ * σ (t + 2*C₁ * t ^ α))) ∧
        (∀ t : ℝ, 0 ≤ σ₀ t) ∧ (∀ t : ℝ, 0 ≤ σ₁ t) ∧
        (∃ C : ℝ, ∀ t : ℝ, σ₀ t ≤ C ∧ σ₁ t ≤ C) ∧
        Continuous σ₀ ∧ Continuous σ₁ ∧ Monotone σ₀ ∧ Monotone σ₁ ∧
        σ₀ 0 = 0 ∧ σ₁ 0 = 0 ∧
        ∀ (ε : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
          (fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
          (u U : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
          (v V : EuclideanSpace ℝ (Fin n) → ℝ)
          (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 ≤ ε → ε ≤ 1 → IsOpen Ω →
          VariationalStructureF123 n p ε lam Lam a ν₀ ν₁ Ω fdens σ →
          MemW1pOn n p Ω u g → IsLocalMinimumOn n p Ω fdens u g →
          0 < R → Metric.closedBall x₀ R ⊆ Ω →
          FrozenComparisonOn n p x₀ R
            (FrozenGradientOperator n fdens x₀ (U x₀)) u U g v V gv →
          (∀ x ∈ Metric.closedBall x₀ R, |U x - U x₀| ≤ C₁ * R ^ α) →
          (∫ x in Metric.ball x₀ R,
              (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2)
            ≤ σ₀ R * (∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2))
              + σ₁ R * ∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p := by
    intro σ Cs α C₁ hσc hσm hσ0 hσb hα0 hα1 hC₁
    obtain ⟨C₂, σ₀, σ₁, hC₂0, hσ₀eq, hσ₁eq, hσ₀nn, hσ₁nn, hbd, hσ₀c, hσ₁c,
      hσ₀m, hσ₁m, hσ₀0, hσ₁0, hFFE⟩ :=
      FrozenFreezingErrorBound n p α C₁ (1/(ν₀*Cm)) Cs σ hn1 hp hα0 hα1 hC₁ hKpos
        hσc hσm hσ0 hσb
    refine ⟨C₂, σ₀, σ₁, hC₂0, hσ₀eq, hσ₁eq, hσ₀nn, hσ₁nn, hbd, hσ₀c, hσ₁c,
      hσ₀m, hσ₁m, hσ₀0, hσ₁0, ?_⟩
    intro ε Ω fdens u U g x₀ R v V gv hε hε1 hΩ hF hu hmin hR hcb hfc hHol
    obtain ⟨hsol, hvW, hzeroW, hUc, hUu, hVc, hVv, hVU⟩ := hfc
    set B : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball x₀ R with hBdef
    have hBmeas : MeasurableSet B := measurableSet_ball
    have hBfin : volume B ≠ ⊤ := measure_ball_lt_top.ne
    have hfinB : IsFiniteMeasure (volume.restrict B) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have hBsub : B ⊆ Ω := Metric.ball_subset_closedBall.trans hcb
    have hx₀Ω : x₀ ∈ Ω := hcb (Metric.mem_closedBall_self hR.le)
    -- Step 1
    set f0 : EuclideanSpace ℝ (Fin n) → ℝ := fdens x₀ (U x₀) with hf0def
    set A0 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
      FrozenGradientOperator n fdens x₀ (U x₀) with hA0def
    have hf1 : ContDiff ℝ 1 f0 := hF.F2_diff x₀ hx₀Ω (U x₀)
    have hDopen : IsOpen {h : EuclideanSpace ℝ (Fin n) | ε + ‖h‖ ^ 2 ≠ 0} := by
      have hc : Continuous fun h : EuclideanSpace ℝ (Fin n) => ε + ‖h‖ ^ 2 :=
        continuous_const.add (continuous_norm.pow 2)
      exact isOpen_ne.preimage hc
    have hf2 : ContDiffOn ℝ 2 f0 {h : EuclideanSpace ℝ (Fin n) | ε + ‖h‖ ^ 2 ≠ 0} :=
      hF.F2_diff2 x₀ hx₀Ω (U x₀)
    have hTcont : Continuous (fderiv ℝ f0) := hf1.continuous_fderiv (by norm_num)
    have hA0cont : Continuous A0 := by
      rw [hA0def]
      show Continuous fun h : EuclideanSpace ℝ (Fin n) =>
        (WithLp.toLp 2 fun i => fderiv ℝ (fdens x₀ (U x₀)) h (EuclideanSpace.single i (1:ℝ)) :
          EuclideanSpace ℝ (Fin n))
      exact (PiLp.continuous_toLp 2 _).comp
        (continuous_pi fun _ => hTcont.clm_apply continuous_const)
    have hbasis : ∀ ζ : EuclideanSpace ℝ (Fin n),
        (∑ i, ζ i • EuclideanSpace.single i (1:ℝ)) = ζ := by
      intro ζ
      ext j
      simp [Finset.sum_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq]
    have hfA : ∀ h ζ : EuclideanSpace ℝ (Fin n),
        fderiv ℝ f0 h ζ = ∑ i, A0 h i * ζ i := by
      intro h ζ
      conv_lhs => rw [← hbasis ζ]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul]
      show ζ i * fderiv ℝ f0 h (EuclideanSpace.single i (1:ℝ))
        = fderiv ℝ f0 h (EuclideanSpace.single i (1:ℝ)) * ζ i
      ring
    have hfd : ∀ h : EuclideanSpace ℝ (Fin n), DifferentiableAt ℝ f0 h :=
      fun h => (hf1.differentiable (by norm_num)) h
    have hf0cont : Continuous f0 := hf1.continuous
    have hQ12 : EllipticStructureQ12 n p ε ν₀ ν₁ Set.univ
        (fun _ _ h => A0 h - A0 0) :=
      FrozenOperatorStructureQ12 n p ε lam Lam a ν₀ ν₁ hn hp hε hε1 hlam hlamLam ha
        hν₀ hν₁ Ω fdens σ x₀ (U x₀) hΩ hx₀Ω hF
    -- the L^p data on the ball
    have hgLp : MemLp g (ENNReal.ofReal p) (volume.restrict B) :=
      MeasureTheory.MemLp.mono_measure (Measure.restrict_mono hBsub le_rfl) hu.2.2
    have huLp : MemLp u (ENNReal.ofReal p) (volume.restrict B) :=
      MeasureTheory.MemLp.mono_measure (Measure.restrict_mono hBsub le_rfl) hu.2.1
    have hgvLp : MemLp gv (ENNReal.ofReal p) (volume.restrict B) := hvW.2.2
    have hvLp : MemLp v (ENNReal.ofReal p) (volume.restrict B) := hvW.2.1
    have hdiffLp : MemLp (fun x => g x - gv x) (ENNReal.ofReal p)
        (volume.restrict B) := hgLp.sub hgvLp
    -- the Hölder pairing of an `L^{p'}` field against an `L^p` field
    have hconj : Real.HolderConjugate (p / (p - 1)) p := by
      have h : Real.HolderConjugate p (p / (p - 1)) :=
        (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
      exact h.symm
    have hIP : ∀ aa bb : EuclideanSpace ℝ (Fin n), (∑ i, aa i * bb i) = inner ℝ bb aa := by
      intro aa bb
      rw [PiLp.inner_apply]
      exact Finset.sum_congr rfl fun i _ => by simp
    have hCS : ∀ aa bb : EuclideanSpace ℝ (Fin n), |∑ i, aa i * bb i| ≤ ‖aa‖ * ‖bb‖ := by
      intro aa bb
      rw [hIP aa bb, mul_comm ‖aa‖ ‖bb‖]
      exact abs_real_inner_le_norm bb aa
    have hHT : ENNReal.HolderTriple (ENNReal.ofReal (p / (p - 1))) (ENNReal.ofReal p) 1 :=
      ⟨by rw [inv_one]; exact hconj.inv_add_inv_ennreal⟩
    have hpair : ∀ F H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        MemLp F (ENNReal.ofReal (p / (p - 1))) (volume.restrict B) →
        MemLp H (ENNReal.ofReal p) (volume.restrict B) →
        IntegrableOn (fun x => ∑ i, F x i * H x i) B volume := by
      intro F H hFm hHm
      have hprod : Integrable (fun x => ‖F x‖ * ‖H x‖) (volume.restrict B) :=
        hFm.norm.integrable_mul hHm.norm
      have hmeas : AEStronglyMeasurable (fun x => ∑ i, F x i * H x i)
          (volume.restrict B) := by
        have hinner : AEStronglyMeasurable
            (fun x => (inner ℝ (H x) (F x) : ℝ)) (volume.restrict B) :=
          (continuous_inner (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))).comp_aestronglyMeasurable
            (hHm.aestronglyMeasurable.prodMk hFm.aestronglyMeasurable)
        exact hinner.congr (Filter.Eventually.of_forall fun x => (hIP (F x) (H x)).symm)
      refine hprod.mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs]
      exact hCS _ _
    -- the `(1 + |·|²)^{p/2}` weight is integrable along an `L^p` field
    have hwle : ∀ s : ℝ, 0 ≤ s → (1 + s ^ 2) ^ (p/2) ≤ (1 + s) ^ p := by
      intro s hs
      have h1 : (1 : ℝ) + s ^ 2 ≤ (1 + s) ^ 2 := by nlinarith
      have h2 : ((1:ℝ) + s ^ 2) ^ (p/2) ≤ ((1 + s) ^ 2) ^ (p/2) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
      have h3 : (((1:ℝ) + s) ^ 2) ^ (p/2) = (1 + s) ^ p := by
        rw [show ((1 + s : ℝ)) ^ 2 = (1 + s) ^ (2:ℝ) by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]]
        rw [← Real.rpow_mul (by linarith)]
        congr 1
        ring
      rwa [h3] at h2
    have hwint : ∀ h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        MemLp h (ENNReal.ofReal p) (volume.restrict B) →
        IntegrableOn (fun x => (1 + ‖h x‖ ^ 2) ^ (p/2)) B volume := by
      intro h hh
      have hone : MemLp (fun x => (1:ℝ) + ‖h x‖) (ENNReal.ofReal p)
          (volume.restrict B) := (memLp_const (1:ℝ)).add hh.norm
      have hpow := hone.norm_rpow_div (ENNReal.ofReal p)
      rw [ENNReal.toReal_ofReal hp0.le,
        ENNReal.div_self (ne_of_gt (ENNReal.ofReal_pos.2 hp0)) ENNReal.ofReal_ne_top] at hpow
      have hint1 : Integrable (fun x => ((1:ℝ) + ‖h x‖) ^ p) (volume.restrict B) := by
        have hh2 := memLp_one_iff_integrable.1 hpow
        refine hh2.congr ?_
        filter_upwards with x
        rw [Real.norm_of_nonneg (by positivity)]
      have hmeasw : AEStronglyMeasurable (fun x => (1 + ‖h x‖ ^ 2) ^ (p/2))
          (volume.restrict B) := by
        have hc : Continuous fun z : ℝ => (1 + z ^ 2) ^ (p/2) := by
          have h1 : Continuous fun z : ℝ => 1 + z ^ 2 := by fun_prop
          exact h1.rpow_const fun z => Or.inr (by positivity)
        exact hc.comp_aestronglyMeasurable hh.norm.aestronglyMeasurable
      refine hint1.mono' hmeasw ?_
      filter_upwards with x
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact hwle ‖h x‖ (norm_nonneg _)
    -- the F1 majorant, and the integrability of the frozen and the true integrand
    have hmaj : ∀ h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        MemLp h (ENNReal.ofReal p) (volume.restrict B) →
        IntegrableOn (fun x => Lam * (1 + ‖h x‖ ^ 2) ^ (p/2) + a) B volume :=
      fun h hh => ((hwint h hh).const_mul Lam).add (integrable_const a)
    have hF1abs : ∀ (x : EuclideanSpace ℝ (Fin n)), x ∈ Ω → ∀ (z : ℝ)
        (h : EuclideanSpace ℝ (Fin n)),
        |fdens x z h| ≤ Lam * (1 + ‖h‖ ^ 2) ^ (p/2) + a := by
      intro x hx z h
      have h1 := hF.F1 x hx z h
      have hmono : (ε + ‖h‖ ^ 2) ^ (p/2) ≤ (1 + ‖h‖ ^ 2) ^ (p/2) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      have hw1 : (0:ℝ) ≤ (ε + ‖h‖ ^ 2) ^ (p/2) := Real.rpow_nonneg (by positivity) _
      rw [abs_le]
      constructor
      · nlinarith [h1.1, hw1, hmono]
      · nlinarith [h1.2, hmono, hw1]
    have hf0int : ∀ h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        MemLp h (ENNReal.ofReal p) (volume.restrict B) →
        IntegrableOn (fun x => f0 (h x)) B volume := by
      intro h hh
      refine Integrable.mono' (hmaj h hh)
        (hf0cont.comp_aestronglyMeasurable hh.aestronglyMeasurable) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs]
      exact hF1abs x₀ hx₀Ω (U x₀) (h x)
    have hCara : ∀ (w : EuclideanSpace ℝ (Fin n) → ℝ)
        (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        AEStronglyMeasurable w (volume.restrict B) →
        AEStronglyMeasurable h (volume.restrict B) →
        AEStronglyMeasurable (fun x => fdens x (w x) (h x)) (volume.restrict B) := by
      have hU : Measurable (Function.uncurry
          (fun (q : ℝ × EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) =>
            fdens x q.1 q.2)) :=
        measurable_uncurry_of_continuous_of_measurable
          (fun x => hF.cont_zh x) (fun q => hF.meas_x q.1 q.2)
      intro w h hw hh
      obtain ⟨w', hw'm, hw'e⟩ := hw
      obtain ⟨h', hh'm, hh'e⟩ := hh
      refine ⟨fun x => fdens x (w' x) (h' x), ?_, ?_⟩
      · exact Measurable.stronglyMeasurable
          (hU.comp ((hw'm.measurable.prodMk hh'm.measurable).prodMk measurable_id))
      · filter_upwards [hw'e, hh'e] with x h1 h2
        rw [h1, h2]
    have hfdint : ∀ (w : EuclideanSpace ℝ (Fin n) → ℝ)
        (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        AEStronglyMeasurable w (volume.restrict B) →
        MemLp h (ENNReal.ofReal p) (volume.restrict B) →
        IntegrableOn (fun x => fdens x (w x) (h x)) B volume := by
      intro w h hw hh
      refine Integrable.mono' (hmaj h hh) (hCara w h hw hh.1) ?_
      filter_upwards [ae_restrict_mem hBmeas] with x hx
      rw [Real.norm_eq_abs]
      exact hF1abs x (hBsub hx) (w x) (h x)
    -- Step 3: the first-order term vanishes
    have hA0Lp : MemLp (fun x => A0 (gv x)) (ENNReal.ofReal (p / (p - 1)))
        (volume.restrict B) :=
      FrozenFieldDualMemLp n p ε ν₀ ν₁ hn hp hε hε1 hν₀ hν₁0 A0 hQ12 B gv hBfin hgvLp
    have hstep3 : (∫ x in B, ∑ i, A0 (gv x) i * (gv x - g x) i) = 0 :=
      WeakSolutionZeroTest n p hn1 hp B (fun _ _ h => A0 h) v gv
        (fun x => v x - u x) (fun x => gv x - g x) Metric.isOpen_ball hsol hA0Lp hzeroW
    -- Step 4: the pointwise second-order bound
    have hptw4 : ∀ Aa Bb : EuclideanSpace ℝ (Fin n),
        ν₀ * Cm * (ε + ‖Aa‖ ^ 2 + ‖Bb‖ ^ 2) ^ (p / 2 - 1) * ‖Aa - Bb‖ ^ 2
          ≤ f0 Aa - f0 Bb - ∑ i, A0 Bb i * (Aa - Bb) i := by
      intro Aa Bb
      by_cases hab : Aa = Bb
      · rw [hab]
        simp
      set ζ : EuclideanSpace ℝ (Fin n) := Aa - Bb with hζdef
      set ξ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => t • Aa + (1 - t) • Bb with hξdef
      set q : ℝ → ℝ := fun t =>
        if ε + ‖ξ t‖ ^ 2 = 0 then 0
        else fderiv ℝ (fun h' => fderiv ℝ f0 h' ζ) (ξ t) ζ with hqdef
      -- hypothesis (i)
      have hC1 : ContDiffOn ℝ 1 (fderiv ℝ f0) {h : EuclideanSpace ℝ (Fin n) | ε + ‖h‖ ^ 2 ≠ 0} := by
        refine (hf2.fderivWithin (m := 1) hDopen.uniqueDiffOn (by norm_num)).congr
          (fun x hx => ?_)
        exact (fderivWithin_of_isOpen hDopen hx).symm
      have hξd : ∀ t : ℝ,
          HasDerivAt (fun s : ℝ => s • Aa + (1 - s) • Bb) (Aa - Bb) t := by
        intro t
        have h1 : HasDerivAt (fun s : ℝ => s • Aa) Aa t := by
          simpa using (hasDerivAt_id t).smul_const Aa
        have h2 : HasDerivAt (fun s : ℝ => (1 - s) • Bb) (-Bb) t := by
          have h := ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).smul_const Bb
          simpa using h
        have h3 : HasDerivAt (fun s : ℝ => s • Aa + (1 - s) • Bb) (Aa + -Bb) t := h1.add h2
        rwa [← sub_eq_add_neg] at h3
      have hqd : ∀ t : ℝ, ε + ‖t • Aa + (1 - t) • Bb‖ ^ 2 ≠ 0 →
          HasDerivAt (fun s : ℝ => ∑ i, A0 (s • Aa + (1 - s) • Bb) i * (Aa - Bb) i) (q t) t := by
        intro t ht
        have hfun : (fun s : ℝ => ∑ i, A0 (s • Aa + (1 - s) • Bb) i * (Aa - Bb) i)
            = fun s : ℝ => fderiv ℝ f0 (s • Aa + (1 - s) • Bb) ζ := by
          funext s
          rw [hζdef, hfA]
        rw [hfun]
        have hmem : (t • Aa + (1 - t) • Bb) ∈
            {h : EuclideanSpace ℝ (Fin n) | ε + ‖h‖ ^ 2 ≠ 0} := ht
        have hdiff : DifferentiableAt ℝ (fderiv ℝ f0) (t • Aa + (1 - t) • Bb) :=
          ((hC1.differentiableOn (by norm_num)).differentiableAt (hDopen.mem_nhds hmem))
        have hdiffat : DifferentiableAt ℝ
            (fun h' : EuclideanSpace ℝ (Fin n) => fderiv ℝ f0 h' ζ)
            (t • Aa + (1 - t) • Bb) := hdiff.clm_apply (differentiableAt_const ζ)
        have h := hdiffat.hasFDerivAt.comp_hasDerivAt t (hξd t)
        have hq : q t = fderiv ℝ (fun h' => fderiv ℝ f0 h' ζ) (t • Aa + (1 - t) • Bb) ζ := by
          rw [hqdef]
          simp only
          rw [if_neg (by rw [hξdef]; exact ht)]
        rw [hq]
        exact h
      -- hypothesis (ii)
      have hqb : ∀ t : ℝ, ε + ‖t • Aa + (1 - t) • Bb‖ ^ 2 ≠ 0 →
          |q t| ≤ ν₁ * (ε + ‖t • Aa + (1 - t) • Bb‖ ^ 2) ^ (p / 2 - 1) * ‖Aa - Bb‖ ^ 2 := by
        intro t ht
        rw [hqdef]
        simp only
        rw [if_neg ht]
        have h := hF.F2 x₀ hx₀Ω (U x₀) (ξ t) ζ (by rw [hξdef]; exact ht)
        have hw : (0:ℝ) ≤ ν₀ * (ε + ‖ξ t‖ ^ 2) ^ (p / 2 - 1) * ‖ζ‖ ^ 2 := by
          have := Real.rpow_nonneg (le_trans hε (by nlinarith [sq_nonneg ‖ξ t‖]) : (0:ℝ) ≤ ε + ‖ξ t‖ ^ 2) (p/2-1)
          positivity
        rw [abs_le]
        constructor
        · have := h.1
          nlinarith [h.1, hw]
        · exact h.2
      -- hypothesis (iii)
      have hq0 : ∀ t : ℝ, ε + ‖t • Aa + (1 - t) • Bb‖ ^ 2 = 0 → q t = 0 := by
        intro t ht
        rw [hqdef]
        simp only
        rw [if_pos (by rw [hξdef]; exact ht)]
      obtain ⟨hqint, hid⟩ := SegmentSecondOrderIdentity n p ε ν₁ hp hε hν₁0.le f0 A0
        hfd hfA hA0cont Aa Bb q hqd hqb hq0
      -- the lower bound on the remainder
      have hwint : IntervalIntegrable
          (fun t : ℝ => ((1 - t) * (ν₀ * ‖ζ‖ ^ 2))
            * (ε + ‖t • Aa + (1 - t) • Bb‖ ^ 2) ^ (p / 2 - 1)) volume 0 1 :=
        (SegmentWeightIntegrable n p hp ε Aa Bb hε).continuousOn_mul (by fun_prop)
      have hptw : ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
          ((1 - t) * (ν₀ * ‖ζ‖ ^ 2))
              * (ε + ‖t • Aa + (1 - t) • Bb‖ ^ 2) ^ (p / 2 - 1)
            ≤ (1 - t) * q t := by
        have hTnull : volume {t : ℝ | ε + ‖t • Aa + (1 - t) • Bb‖ ^ 2 = 0} = 0 := by
          have hz : ∀ s : ℝ, ε + ‖s • Aa + (1 - s) • Bb‖ ^ 2 = 0 →
              s • Aa + (1 - s) • Bb = 0 := by
            intro s hs
            have h1 : ‖s • Aa + (1 - s) • Bb‖ ^ 2 = 0 := by
              have h2 := sq_nonneg ‖s • Aa + (1 - s) • Bb‖
              linarith
            exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
          have hζ0 : Aa - Bb ≠ 0 := sub_ne_zero.2 hab
          rcases Set.eq_empty_or_nonempty
              {t : ℝ | ε + ‖t • Aa + (1 - t) • Bb‖ ^ 2 = 0} with he | ⟨t₀, ht₀⟩
          · rw [he]; exact measure_empty
          · refine measure_mono_null (fun t ht => ?_) (measure_singleton t₀)
            have e1 := hz t ht
            have e2 := hz t₀ ht₀
            have e0 : (t • Aa + (1 - t) • Bb) - (t₀ • Aa + (1 - t₀) • Bb)
                = (t - t₀) • (Aa - Bb) := by module
            have e3 : (t - t₀) • (Aa - Bb) = 0 := by rw [← e0, e1, e2, sub_zero]
            rcases smul_eq_zero.1 e3 with h5 | h5
            · exact sub_eq_zero.mp h5
            · exact absurd h5 hζ0
        have hae : ∀ᵐ t ∂(volume : Measure ℝ),
            ε + ‖t • Aa + (1 - t) • Bb‖ ^ 2 ≠ 0 := by
          rw [Filter.eventually_iff, mem_ae_iff]
          refine measure_mono_null (fun t ht => ?_) hTnull
          simpa using ht
        filter_upwards [hae.filter_mono (ae_mono Measure.restrict_le_self),
          ae_restrict_mem measurableSet_Icc] with t ht htI
        have h1 := hF.F2 x₀ hx₀Ω (U x₀) (t • Aa + (1 - t) • Bb) ζ ht
        have hq : q t = fderiv ℝ (fun h' => fderiv ℝ f0 h' ζ) (t • Aa + (1 - t) • Bb) ζ := by
          rw [hqdef]
          simp only
          rw [if_neg (by rw [hξdef]; exact ht)]
        have h1t : (0:ℝ) ≤ 1 - t := by
          have := htI.2
          linarith
        rw [hq]
        have hlb : ν₀ * (ε + ‖t • Aa + (1 - t) • Bb‖ ^ 2) ^ (p / 2 - 1) * ‖ζ‖ ^ 2
            ≤ fderiv ℝ (fun h' => fderiv ℝ f0 h' ζ) (t • Aa + (1 - t) • Bb) ζ := h1.1
        nlinarith [hlb, h1t]
      have hlow : (∫ t in (0:ℝ)..1, ((1 - t) * (ν₀ * ‖ζ‖ ^ 2))
            * (ε + ‖t • Aa + (1 - t) • Bb‖ ^ 2) ^ (p / 2 - 1))
          ≤ ∫ t in (0:ℝ)..1, (1 - t) * q t :=
        intervalIntegral.integral_mono_ae_restrict (by norm_num) hwint hqint hptw
      have hmid := hCm n ε Aa Bb hn1 hε
      have hfactor : (∫ t in (0:ℝ)..1, ((1 - t) * (ν₀ * ‖ζ‖ ^ 2))
            * (ε + ‖t • Aa + (1 - t) • Bb‖ ^ 2) ^ (p / 2 - 1))
          = ν₀ * ‖ζ‖ ^ 2 * ∫ t in (0:ℝ)..1,
            (1 - t) * (ε + ‖t • Aa + (1 - t) • Bb‖ ^ 2) ^ (p / 2 - 1) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun t _ => ?_
        ring
      rw [hfactor] at hlow
      have hζ0 : (0:ℝ) ≤ ν₀ * ‖ζ‖ ^ 2 := by positivity
      have hstep : ν₀ * ‖ζ‖ ^ 2 * (Cm * (ε + ‖Aa‖ ^ 2 + ‖Bb‖ ^ 2) ^ (p / 2 - 1))
          ≤ ν₀ * ‖ζ‖ ^ 2 * ∫ t in (0:ℝ)..1,
            (1 - t) * (ε + ‖t • Aa + (1 - t) • Bb‖ ^ 2) ^ (p / 2 - 1) :=
        mul_le_mul_of_nonneg_left hmid hζ0
      have hfin : ν₀ * Cm * (ε + ‖Aa‖ ^ 2 + ‖Bb‖ ^ 2) ^ (p / 2 - 1) * ‖Aa - Bb‖ ^ 2
          ≤ ∫ t in (0:ℝ)..1, (1 - t) * q t := by
        have he : ν₀ * Cm * (ε + ‖Aa‖ ^ 2 + ‖Bb‖ ^ 2) ^ (p / 2 - 1) * ‖Aa - Bb‖ ^ 2
            = ν₀ * ‖ζ‖ ^ 2 * (Cm * (ε + ‖Aa‖ ^ 2 + ‖Bb‖ ^ 2) ^ (p / 2 - 1)) := by
          rw [hζdef]; ring
        rw [he]
        linarith
      have hid2 : f0 Aa - f0 Bb - ∑ i, A0 Bb i * (Aa - Bb) i
          = ∫ t in (0:ℝ)..1, (1 - t) * q t := by
        rw [hid]; ring
      rw [hid2]
      exact hfin
    -- Step 4: (4.3)
    have hpairint : IntegrableOn (fun x => ∑ i, A0 (gv x) i * (g x - gv x) i) B volume :=
      hpair (fun x => A0 (gv x)) (fun x => g x - gv x) hA0Lp hdiffLp
    have hi1 : IntegrableOn (fun x => f0 (g x)) B volume := hf0int g hgLp
    have hi2 : IntegrableOn (fun x => f0 (gv x)) B volume := hf0int gv hgvLp
    have hi12 : IntegrableOn (fun x => f0 (g x) - f0 (gv x)) B volume := hi1.sub hi2
    have hrhsint : IntegrableOn
        (fun x => f0 (g x) - f0 (gv x) - ∑ i, A0 (gv x) i * (g x - gv x) i) B volume :=
      hi12.sub hpairint
    have hWmeas : AEStronglyMeasurable
        (fun x => (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2)
        (volume.restrict B) := by
      have hb : AEStronglyMeasurable (fun x => ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2)
          (volume.restrict B) :=
        (aestronglyMeasurable_const.add (hgLp.aestronglyMeasurable.norm.pow 2)).add
          (hgvLp.aestronglyMeasurable.norm.pow 2)
      have hr : AEStronglyMeasurable
          (fun x => (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1)) (volume.restrict B) :=
        (hb.aemeasurable.pow_const (p / 2 - 1)).aestronglyMeasurable
      exact hr.mul (hdiffLp.aestronglyMeasurable.norm.pow 2)
    have hlhsint : IntegrableOn
        (fun x => (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2)
        B volume := by
      refine Integrable.mono' (hrhsint.const_mul (1 / (ν₀ * Cm))) hWmeas ?_
      filter_upwards with x
      have h1 := hptw4 (g x) (gv x)
      have h2 : (0:ℝ) ≤ (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2 := by
        have := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) (p/2-1)
        positivity
      rw [Real.norm_of_nonneg h2]
      have hK0 : (0:ℝ) < 1 / (ν₀ * Cm) := by positivity
      have h3 := mul_le_mul_of_nonneg_left h1 hK0.le
      calc (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2
          = (1 / (ν₀ * Cm)) * (ν₀ * Cm * (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1)
              * ‖g x - gv x‖ ^ 2) := by
            field_simp
        _ ≤ (1 / (ν₀ * Cm))
              * (f0 (g x) - f0 (gv x) - ∑ i, A0 (gv x) i * (g x - gv x) i) := h3
    have h43 : (∫ x in B,
          (ε + ‖g x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1) * ‖g x - gv x‖ ^ 2)
        ≤ (1 / (ν₀ * Cm)) * ((∫ x in B, f0 (g x)) - ∫ x in B, f0 (gv x)) := by
      have hmono := integral_mono (hlhsint.const_mul (ν₀ * Cm)) hrhsint
        (fun x => by
          have h1 := hptw4 (g x) (gv x)
          nlinarith [h1])
      rw [integral_const_mul] at hmono
      have hsplit : (∫ x in B,
            (f0 (g x) - f0 (gv x) - ∑ i, A0 (gv x) i * (g x - gv x) i))
          = (∫ x in B, f0 (g x)) - (∫ x in B, f0 (gv x))
            - ∫ x in B, ∑ i, A0 (gv x) i * (g x - gv x) i := by
        rw [integral_sub hi12 hpairint, integral_sub hi1 hi2]
      have hneg : (∫ x in B, ∑ i, A0 (gv x) i * (g x - gv x) i) = 0 := by
        have he : (fun x => ∑ i, A0 (gv x) i * (g x - gv x) i)
            = fun x => -(∑ i, A0 (gv x) i * (gv x - g x) i) := by
          funext x
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          show A0 (gv x) i * (g x - gv x) i = -(A0 (gv x) i * (gv x - g x) i)
          show A0 (gv x) i * (g x i - gv x i) = -(A0 (gv x) i * (gv x i - g x i))
          ring
        rw [he, integral_neg, hstep3, neg_zero]
      rw [hsplit, hneg, sub_zero] at hmono
      rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      linarith [hmono]
    -- Step 5: minimality
    have h51 : (∫ x in B, fdens x (u x) (g x)) ≤ ∫ x in B, fdens x (v x) (gv x) :=
      LocalMinimumZeroTest n p ε lam Lam a ν₀ ν₁ hn1 hp hε hε1 hlam hlamLam Ω B fdens σ
        u v g gv hΩ Metric.isOpen_ball hBsub hBfin hF huLp hgLp hmin hzeroW
    -- (6d): the comparison bound for `v`
    have hsphere : ∀ x ∈ Metric.sphere x₀ R,
        U x₀ - C₁ * R ^ α ≤ V x ∧ V x ≤ U x₀ + C₁ * R ^ α := by
      intro x hx
      have hxc : x ∈ Metric.closedBall x₀ R := by
        rw [Metric.mem_sphere] at hx
        rw [Metric.mem_closedBall, hx]
      have h1 := hHol x hxc
      rw [hVU x hx]
      rw [abs_le] at h1
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have h6d : ∀ᵐ x ∂(volume.restrict B),
        U x₀ - C₁ * R ^ α ≤ v x ∧ v x ≤ U x₀ + C₁ * R ^ α :=
      BallSolutionConstantBounds n p ε ν₀ ν₁ hn hp hε hν₀ hν₁.le hSP A0 x₀ R v V gv
        (U x₀ - C₁ * R ^ α) (U x₀ + C₁ * R ^ α) hR hQ12 hsol hvW hVc hVv hsphere
    have hvbd : ∀ᵐ x ∂(volume.restrict B), |v x - U x₀| ≤ C₁ * R ^ α := by
      filter_upwards [h6d] with x hx
      rw [abs_le]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hubd : ∀ᵐ x ∂(volume.restrict B), |u x - U x₀| ≤ C₁ * R ^ α := by
      filter_upwards [ae_restrict_mem hBmeas] with x hx
      have h1 := hHol x (Metric.ball_subset_closedBall hx)
      rwa [hUu x hx] at h1
    -- (6e)
    have hF3 : ∀ x ∈ B, ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)),
        |fdens x z h - f0 h| ≤ (1 + ‖h‖ ^ 2) ^ (p / 2) * σ (dist x x₀ + |z - U x₀|) :=
      fun x hx z h => hF.F3 x (hBsub hx) x₀ hx₀Ω z (U x₀) h
    exact hFFE ε (U x₀) R x₀ fdens f0 u v g gv hR hgLp hgvLp
      (hf0int g hgLp) (hf0int gv hgvLp)
      (hfdint u g huLp.aestronglyMeasurable hgLp)
      (hfdint v gv hvLp.aestronglyMeasurable hgvLp)
      hF3 hubd hvbd h51 h43
  refine ⟨?_, ?_⟩
  · -- clause (A)
    intro M d σ hM hd
    by_cases hsplit : (Continuous σ ∧ Monotone σ ∧ σ 0 = 0 ∧ (∃ Cs : ℝ, ∀ t : ℝ, σ t ≤ Cs))
        ∧ CitedHolderOscillationMinimum n p
    · obtain ⟨⟨hσc, hσm, hσ0, Cs, hσb⟩, hC4⟩ := hsplit
      obtain ⟨α, R₀, C₁, hα0, hα1, hR₀, hC₁, hHolD⟩ :=
        MinimumHolderDatumOnBall n p lam Lam a M d hn1 hp hlam hlamLam ha hM hd hC4
      obtain ⟨C₂, σ₀, σ₁, hC₂0, hσ₀eq, hσ₁eq, hσ₀nn, hσ₁nn, hbd, hσ₀c, hσ₁c,
        hσ₀m, hσ₁m, hσ₀0, hσ₁0, hFFE⟩ := hcore σ Cs α C₁ hσc hσm hσ0 hσb hα0 hα1 hC₁
      obtain ⟨η, hη0, hησ⟩ : ∃ η : ℝ, 0 < η ∧ σ₁ η ≤ b₀ := by
        have h1 : Filter.Tendsto σ₁ (nhds 0) (nhds (σ₁ 0)) := hσ₁c.tendsto 0
        rw [hσ₁0] at h1
        have h2 : ∀ᶠ t in nhds (0:ℝ), σ₁ t < b₀ := h1.eventually (gt_mem_nhds hb₀)
        have h3 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), σ₁ t < b₀ :=
          h2.filter_mono nhdsWithin_le_nhds
        obtain ⟨η, hη1, hη2⟩ := (h3.and self_mem_nhdsWithin).exists
        exact ⟨η, hη2, hη1.le⟩
      obtain ⟨hσ2bd, hσ2c, hσ2m, hσ20, hσ2nn⟩ :=
        hsig2 σ₀ σ₁ hσ₀nn hσ₁nn hbd hσ₀c hσ₁c hσ₀m hσ₁m hσ₀0 hσ₁0
      refine ⟨fun t => cA * (σ₀ t + σ₀ t ^ (p/2) + σ₁ t ^ (p/2)), min R₀ η,
        lt_min hR₀ hη0, hσ2bd, hσ2c, hσ2m, hσ20, hσ2nn, ?_⟩
      intro ε Ω Ω' fdens u U g x₀ R v V gv hε hε1 hΩ hΩ' hbdd hcl hsep hF hC4' hu hMb
        hmin hx₀ hR hRR₁ hcb hfc
      have hBsub : Metric.ball x₀ R ⊆ Ω := Metric.ball_subset_closedBall.trans hcb
      have hgLp : MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) :=
        MeasureTheory.MemLp.mono_measure (Measure.restrict_mono hBsub le_rfl) hu.2.2
      have hgvLp : MemLp gv (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ R)) := hfc.2.1.2.2
      have hHol : ∀ x ∈ Metric.closedBall x₀ R, |U x - U x₀| ≤ C₁ * R ^ α :=
        hHolD ε Ω Ω' fdens u U g x₀ R hε hε1 hΩ hsep hx₀
          ⟨hF.meas_x, hF.cont_zh, hF.F1⟩ hmin hMb hR (le_trans hRR₁ (min_le_left _ _))
          hfc.2.2.2.1 hfc.2.2.2.2.1
      have h48 := hFFE ε Ω fdens u U g x₀ R v V gv hε hε1 hΩ hF hu hmin hR hcb hfc hHol
      have hσ1R : σ₁ R ≤ b₀ := le_trans (hσ₁m (le_trans hRR₁ (min_le_right _ _))) hησ
      exact habs n ε (σ₀ R) (σ₁ R) (Metric.ball x₀ R) g gv hε hε1 (hσ₀nn R) (hσ₁nn R)
        hσ1R measurableSet_ball measure_ball_lt_top.ne hgLp hgvLp (hgLp.sub hgvLp) h48
    · refine ⟨fun _ => 0, 1, one_pos, ⟨0, fun t => le_refl 0⟩, continuous_const,
        monotone_const, rfl, fun t => le_refl 0, ?_⟩
      intro ε Ω Ω' fdens u U g x₀ R v V gv hε hε1 hΩ hΩ' hbdd hcl hsep hF hC4' hu hMb
        hmin hx₀ hR hRR₁ hcb hfc
      exact absurd ⟨⟨hF.σ_cont, hF.σ_mono, hF.σ_zero, hF.σ_bdd⟩, hC4'⟩ hsplit
  · -- clause (B)
    intro α δ hα0 hα1 hδ0
    set θ : ℝ := min (α*δ) (α*δ*(p/2)) with hθdef
    have hθ0 : 0 < θ := by
      rw [hθdef]
      exact lt_min (by positivity) (by positivity)
    refine ⟨θ/2, by positivity, ?_⟩
    intro M d σ hM hd cσ C₁ hcσ hC₁ hσdec
    by_cases hsplit : Continuous σ ∧ Monotone σ ∧ σ 0 = 0 ∧ (∃ Cs : ℝ, ∀ t : ℝ, σ t ≤ Cs)
    · obtain ⟨hσc, hσm, hσ0, Cs, hσb⟩ := hsplit
      obtain ⟨C₂, σ₀, σ₁, hC₂0, hσ₀eq, hσ₁eq, hσ₀nn, hσ₁nn, hbd, hσ₀c, hσ₁c,
        hσ₀m, hσ₁m, hσ₀0, hσ₁0, hFFE⟩ := hcore σ Cs α C₁ hσc hσm hσ0 hσb hα0 hα1 hC₁
      set K₀ : ℝ := (1/(ν₀*Cm)) * ((1 + C₂) * (cσ * (1 + 2*C₁) ^ δ)) with hK₀def
      have hK₀0 : 0 ≤ K₀ := by
        rw [hK₀def]
        have h1 : (0:ℝ) < (1 + 2*C₁) ^ δ := Real.rpow_pos_of_pos (by linarith) _
        positivity
      set Kt : ℝ := cA * K₀ + 2 * cA * K₀ ^ (p/2) with hKtdef
      have hKt0 : 0 ≤ Kt := by
        rw [hKtdef]
        have h1 : (0:ℝ) ≤ K₀ ^ (p/2) := Real.rpow_nonneg hK₀0 _
        positivity
      -- the decay of the two moduli
      have hdecay : ∀ r : ℝ, 0 < r → r ≤ 1 →
          σ₀ r ≤ K₀ * r ^ (α*δ) ∧ σ₁ r ≤ K₀ * r ^ (α*δ) := by
        intro r hr hr1
        have hrα : r ≤ r ^ α := by
          have h := Real.rpow_le_rpow_of_exponent_ge hr hr1 hα1
          rwa [Real.rpow_one] at h
        have hrαnn : (0:ℝ) ≤ r ^ α := Real.rpow_nonneg hr.le _
        have harg : ∀ c : ℝ, 0 ≤ c → c ≤ 2*C₁ →
            σ (r + c * r ^ α) ≤ cσ * ((1 + 2*C₁) ^ δ * r ^ (α*δ)) := by
          intro c hc hc2
          have h1 : r + c * r ^ α ≤ (1 + 2*C₁) * r ^ α := by nlinarith
          have h2 : (0:ℝ) ≤ r + c * r ^ α := by positivity
          have h3 : σ (r + c * r ^ α) ≤ cσ * (r + c * r ^ α) ^ δ := hσdec _ h2
          have h4 : (r + c * r ^ α) ^ δ ≤ ((1 + 2*C₁) * r ^ α) ^ δ :=
            Real.rpow_le_rpow h2 h1 hδ0.le
          have h5 : ((1 + 2*C₁) * r ^ α) ^ δ = (1 + 2*C₁) ^ δ * r ^ (α*δ) := by
            rw [Real.mul_rpow (by linarith) hrαnn, ← Real.rpow_mul hr.le]
          rw [h5] at h4
          nlinarith [h3, h4, hcσ]
        have hA := harg C₁ hC₁ (by linarith)
        have hBb := harg (2*C₁) (by linarith) le_rfl
        have hKeq : K₀ * r ^ (α*δ)
            = (1/(ν₀*Cm)) * ((1 + C₂) * (cσ * ((1 + 2*C₁) ^ δ * r ^ (α*δ)))) := by
          rw [hK₀def]; ring
        have h7 : (0:ℝ) ≤ cσ * ((1 + 2*C₁) ^ δ * r ^ (α*δ)) := by
          have h1 : (0:ℝ) < (1 + 2*C₁) ^ δ := Real.rpow_pos_of_pos (by linarith) _
          positivity
        have h8 : C₂ * σ (r + 2*C₁ * r ^ α)
            ≤ C₂ * (cσ * ((1 + 2*C₁) ^ δ * r ^ (α*δ))) :=
          mul_le_mul_of_nonneg_left hBb hC₂0.le
        constructor
        · rw [hσ₀eq r hr, hKeq]
          refine mul_le_mul_of_nonneg_left ?_ hKpos.le
          calc σ (r + C₁ * r ^ α) + C₂ * σ (r + 2*C₁ * r ^ α)
              ≤ cσ * ((1 + 2*C₁) ^ δ * r ^ (α*δ))
                + C₂ * (cσ * ((1 + 2*C₁) ^ δ * r ^ (α*δ))) := by linarith [hA, h8]
            _ = (1 + C₂) * (cσ * ((1 + 2*C₁) ^ δ * r ^ (α*δ))) := by ring
        · rw [hσ₁eq r hr, hKeq]
          refine mul_le_mul_of_nonneg_left ?_ hKpos.le
          calc C₂ * σ (r + 2*C₁ * r ^ α)
              ≤ C₂ * (cσ * ((1 + 2*C₁) ^ δ * r ^ (α*δ))) := h8
            _ ≤ (1 + C₂) * (cσ * ((1 + 2*C₁) ^ δ * r ^ (α*δ))) := by nlinarith [h7]
      -- the radius threshold
      obtain ⟨η, hη0, hησ⟩ : ∃ η : ℝ, 0 < η ∧ σ₁ η ≤ b₀ := by
        have h1 : Filter.Tendsto σ₁ (nhds 0) (nhds (σ₁ 0)) := hσ₁c.tendsto 0
        rw [hσ₁0] at h1
        have h2 : ∀ᶠ t in nhds (0:ℝ), σ₁ t < b₀ := h1.eventually (gt_mem_nhds hb₀)
        have h3 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), σ₁ t < b₀ :=
          h2.filter_mono nhdsWithin_le_nhds
        obtain ⟨t, ht1, ht2⟩ := (h3.and self_mem_nhdsWithin).exists
        exact ⟨t, ht2, ht1.le⟩
      obtain ⟨r₀, hr₀0, hr₀⟩ : ∃ r₀ : ℝ, 0 < r₀ ∧ Kt * r₀ ^ (θ/2) ≤ 1 := by
        have hc : Continuous fun t : ℝ => Kt * t ^ (θ/2) := by
          have h1 : Continuous fun t : ℝ => t ^ (θ/2) :=
            continuous_iff_continuousAt.mpr fun t =>
              Real.continuousAt_rpow_const t (θ/2) (Or.inr (by positivity))
          exact h1.const_mul Kt
        have h1 : Filter.Tendsto (fun t : ℝ => Kt * t ^ (θ/2)) (nhds 0)
            (nhds (Kt * (0:ℝ) ^ (θ/2))) := hc.tendsto 0
        rw [Real.zero_rpow (by positivity : θ/2 ≠ 0), mul_zero] at h1
        have h2 : ∀ᶠ t in nhds (0:ℝ), Kt * t ^ (θ/2) < 1 :=
          h1.eventually (gt_mem_nhds one_pos)
        have h3 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), Kt * t ^ (θ/2) < 1 :=
          h2.filter_mono nhdsWithin_le_nhds
        obtain ⟨t, ht1, ht2⟩ := (h3.and self_mem_nhdsWithin).exists
        exact ⟨t, ht2, ht1.le⟩
      refine ⟨min 1 (min η r₀), lt_min one_pos (lt_min hη0 hr₀0), ?_⟩
      intro ε Ω Ω' fdens u U g x₀ R v V gv hε hε1 hΩ hΩ' hbdd hcl hsep hF hC4' hu hMb
        hmin hx₀ hR hRR₁ hcb hfc hHolB
      have hR1 : R ≤ 1 := le_trans hRR₁ (min_le_left _ _)
      have hRη : R ≤ η := le_trans hRR₁ (le_trans (min_le_right _ _) (min_le_left _ _))
      have hRr₀ : R ≤ r₀ := le_trans hRR₁ (le_trans (min_le_right _ _) (min_le_right _ _))
      have hBsub : Metric.ball x₀ R ⊆ Ω := Metric.ball_subset_closedBall.trans hcb
      have hgLp : MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) :=
        MeasureTheory.MemLp.mono_measure (Measure.restrict_mono hBsub le_rfl) hu.2.2
      have hgvLp : MemLp gv (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ R)) := hfc.2.1.2.2
      have hHol : ∀ x ∈ Metric.closedBall x₀ R, |U x - U x₀| ≤ C₁ * R ^ α := by
        intro x hx
        have h1 := hHolB x hx x₀ (Metric.mem_closedBall_self hR.le)
        have h2 : dist x x₀ ^ α ≤ R ^ α :=
          Real.rpow_le_rpow dist_nonneg (Metric.mem_closedBall.1 hx) hα0.le
        nlinarith [h1, h2, hC₁]
      have h48 := hFFE ε Ω fdens u U g x₀ R v V gv hε hε1 hΩ hF hu hmin hR hcb hfc hHol
      have hσ1R : σ₁ R ≤ b₀ := le_trans (hσ₁m hRη) hησ
      have habs' := habs n ε (σ₀ R) (σ₁ R) (Metric.ball x₀ R) g gv hε hε1 (hσ₀nn R)
        (hσ₁nn R) hσ1R measurableSet_ball measure_ball_lt_top.ne hgLp hgvLp
        (hgLp.sub hgvLp) h48
      -- the coefficient is at most `R ^ (θ/2)`
      have hIg0 : (0:ℝ) ≤ ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2) :=
        integral_nonneg fun x => Real.rpow_nonneg (by positivity) _
      have hcoef : cA * (σ₀ R + σ₀ R ^ (p/2) + σ₁ R ^ (p/2)) ≤ R ^ (θ/2) := by
        obtain ⟨hd0, hd1⟩ := hdecay R hR hR1
        have hS0 : (0:ℝ) ≤ K₀ * R ^ (α*δ) := by positivity
        have hexp1 : R ^ (α*δ) ≤ R ^ θ :=
          Real.rpow_le_rpow_of_exponent_ge hR hR1 (by rw [hθdef]; exact min_le_left _ _)
        have hexp2 : R ^ (α*δ*(p/2)) ≤ R ^ θ :=
          Real.rpow_le_rpow_of_exponent_ge hR hR1 (by rw [hθdef]; exact min_le_right _ _)
        have hRθ0 : (0:ℝ) ≤ R ^ θ := Real.rpow_nonneg hR.le _
        have hpow0 : σ₀ R ^ (p/2) ≤ (K₀ * R ^ (α*δ)) ^ (p/2) :=
          Real.rpow_le_rpow (hσ₀nn R) hd0 (by positivity)
        have hpow1 : σ₁ R ^ (p/2) ≤ (K₀ * R ^ (α*δ)) ^ (p/2) :=
          Real.rpow_le_rpow (hσ₁nn R) hd1 (by positivity)
        have hSp : (K₀ * R ^ (α*δ)) ^ (p/2) = K₀ ^ (p/2) * R ^ (α*δ*(p/2)) := by
          rw [Real.mul_rpow hK₀0 (Real.rpow_nonneg hR.le _), ← Real.rpow_mul hR.le]
        have hK₀p : (0:ℝ) ≤ K₀ ^ (p/2) := Real.rpow_nonneg hK₀0 _
        have hsum : cA * (σ₀ R + σ₀ R ^ (p/2) + σ₁ R ^ (p/2)) ≤ Kt * R ^ θ := by
          rw [hSp] at hpow0 hpow1
          have e1 : σ₀ R ≤ K₀ * R ^ θ :=
            le_trans hd0 (mul_le_mul_of_nonneg_left hexp1 hK₀0)
          have e2 : σ₀ R ^ (p/2) ≤ K₀ ^ (p/2) * R ^ θ :=
            le_trans hpow0 (mul_le_mul_of_nonneg_left hexp2 hK₀p)
          have e3 : σ₁ R ^ (p/2) ≤ K₀ ^ (p/2) * R ^ θ :=
            le_trans hpow1 (mul_le_mul_of_nonneg_left hexp2 hK₀p)
          have e4 : σ₀ R + σ₀ R ^ (p/2) + σ₁ R ^ (p/2)
              ≤ K₀ * R ^ θ + K₀ ^ (p/2) * R ^ θ + K₀ ^ (p/2) * R ^ θ := by linarith
          have e5 := mul_le_mul_of_nonneg_left e4 hcA.le
          rw [hKtdef]
          calc cA * (σ₀ R + σ₀ R ^ (p/2) + σ₁ R ^ (p/2))
              ≤ cA * (K₀ * R ^ θ + K₀ ^ (p/2) * R ^ θ + K₀ ^ (p/2) * R ^ θ) := e5
            _ = (cA * K₀ + 2 * cA * K₀ ^ (p/2)) * R ^ θ := by ring
        have hsplitR : R ^ θ = R ^ (θ/2) * R ^ (θ/2) := by
          rw [← Real.rpow_add hR]
          congr 1
          ring
        have hfac : Kt * R ^ (θ/2) ≤ 1 :=
          le_trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hR.le hRr₀ (by positivity)) hKt0) hr₀
        have hRh0 : (0:ℝ) ≤ R ^ (θ/2) := Real.rpow_nonneg hR.le _
        calc cA * (σ₀ R + σ₀ R ^ (p/2) + σ₁ R ^ (p/2)) ≤ Kt * R ^ θ := hsum
          _ = (Kt * R ^ (θ/2)) * R ^ (θ/2) := by rw [hsplitR]; ring
          _ ≤ 1 * R ^ (θ/2) := mul_le_mul_of_nonneg_right hfac hRh0
          _ = R ^ (θ/2) := one_mul _
      exact le_trans habs' (mul_le_mul_of_nonneg_right hcoef hIg0)
    · refine ⟨1, one_pos, ?_⟩
      intro ε Ω Ω' fdens u U g x₀ R v V gv hε hε1 hΩ hΩ' hbdd hcl hsep hF hC4' hu hMb
        hmin hx₀ hR hRR₁ hcb hfc hHolB
      exact absurd ⟨hF.σ_cont, hF.σ_mono, hF.σ_zero, hF.σ_bdd⟩ hsplit
