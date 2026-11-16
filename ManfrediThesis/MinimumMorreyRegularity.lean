import ManfrediThesis.Preamble
import ManfrediThesis.IsBoundedLipschitzDomain
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.VariationalStructureF123
import ManfrediThesis.ModelDensityStructureF123
import ManfrediThesis.IsLocalMinimumOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MorreyBoundOn
import ManfrediThesis.CampanatoBoundOn
import ManfrediThesis.MemHolderOn
import ManfrediThesis.ComparisonSchemeMorreyCore
import ManfrediThesis.FrozenComparisonDecay
import ManfrediThesis.InnerDomainRepresentative
import ManfrediThesis.ComparisonGradientEstimateMin
import ManfrediThesis.CitedHolderOscillationMinimum
import ManfrediThesis.CitedCampanatoEmbedding
import ManfrediThesis.FrozenComparisonOn
import ManfrediThesis.FrozenGradientOperator
import ManfrediThesis.FrozenOperatorStructureQ12
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.CitedDirichletW1p
import ManfrediThesis.CitedDirichletHolder
import ManfrediThesis.AEModificationInvariance
import ManfrediThesis.MemW1pZeroOn
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.EssOscOn
import ManfrediThesis.VariationalGrowthF1
import ManfrediThesis.WeakGradientRestrict
open MeasureTheory

/-- Theorem 3: Morrey, Campanato and Hölder regularity for local minima of `F`
under (F1), (F2), (F3). -/
theorem MinimumMorreyRegularity :
    ∀ (n : ℕ) (p τ lam Lam a ν₀ ν₁ d M Wn : ℝ) (σ : ℝ → ℝ),
      2 ≤ n → 1 < p → 0 < τ → τ < (n : ℝ) → 0 < lam → lam ≤ Lam → 0 < a →
      0 < ν₀ → ν₀ < ν₁ → 0 < d → 0 ≤ M → 0 ≤ Wn →
      CitedSobolevPoincareBall n →
      (∀ (ε' γ₀' γ₁' : ℝ) (Ω₀ : Set (EuclideanSpace ℝ (Fin n)))
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → IsOpen Ω₀ → CitedRegularityEpsPos n p ε' γ₀' γ₁' Ω₀ A') →
      (∀ (ε' γ₀' γ₁' : ℝ)
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → CitedDirichletW1p n p ε' γ₀' γ₁' A') →
      (∀ (ε' γ₀' γ₁' : ℝ)
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → CitedDirichletHolder n p ε' γ₀' γ₁' A') →
      ∃ N₁ N₂ : ℝ, 0 ≤ N₁ ∧ 0 ≤ N₂ ∧
        ∀ (ε : ℝ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
          (fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 ≤ ε → ε ≤ 1 → IsOpen Ω → IsOpen Ω' → Ω'.Nonempty →
          Bornology.IsBounded Ω' → closure Ω' ⊆ Ω →
          IsBoundedLipschitzDomain n Ω' →
          (∀ x ∈ Ω', ∀ y, y ∉ Ω → d ≤ dist x y) →
          CitedCampanatoEmbedding n ((n : ℝ) / ((n : ℝ) - 1)) Ω' →
          CitedHolderOscillationMinimum n p →
          VariationalStructureF123 n p ε lam Lam a ν₀ ν₁ Ω fdens σ →
          MemW1pOn n p Ω u g →
          (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
          ((∫ x in Ω, |u x| ^ p) + ∫ x in Ω, ‖g x‖ ^ p) ≤ Wn ^ p →
          IsLocalMinimumOn n p Ω fdens u g →
          MorreyBoundOn n p ((n : ℝ) - τ) Ω' (fun x => ‖g x‖) N₁
          ∧ CampanatoBoundOn n ((n : ℝ) / ((n : ℝ) - 1))
              ((n : ℝ) + (1 - τ / p) * ((n : ℝ) / ((n : ℝ) - 1))) Ω' u N₂
          ∧ (∀ η : ℝ, 0 ≤ η → η < 1 →
              ∃ w : EuclideanSpace ℝ (Fin n) → ℝ,
                (∀ᵐ x ∂(volume.restrict Ω'), u x = w x) ∧
                  MemHolderOn n η (closure Ω') w) := by
  intro n p τ lam Lam a ν₀ ν₁ d M Wn σ hn hp hτ0 hτn hlam hlamLam ha hν₀ hν₀ν₁ hd hM hWn
    hSP hC1 hC2 hC3
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hp1 : (1 : ℝ) ≤ p := le_of_lt hp
  have hν₁ : 0 < ν₁ := lt_trans hν₀ hν₀ν₁
  -- Step 1 (1a): the decay constant `c₀` of the comparison maps.
  obtain ⟨c₀, hc₀, hdecay⟩ :=
    FrozenComparisonDecay n p (ν₁ / ν₀) hn hp (div_pos hν₁ hν₀) hSP hC2 hC1 hC3
  -- Step 1 (1b): clause (A) of Lemma 4.1, read at `M`, at `d/2` and at `σ`.
  obtain ⟨hclauseA, -⟩ :=
    ComparisonGradientEstimateMin n p lam Lam a ν₀ ν₁ hn hp hlam hlamLam ha hν₀ hν₀ν₁ hSP
      hC3
  obtain ⟨σ₂, R₁, hR₁, -, hσ₂cont, hσ₂mono, hσ₂zero, hσ₂nn, hsmall⟩ :=
    hclauseA M (d / 2) σ hM (by linarith)
  -- Step 1 (1c): `R∗ = min {R₁, d/16}` and the two constants of the scheme.
  have hRs : (0 : ℝ) < min R₁ (d / 16) := lt_min hR₁ (by linarith)
  obtain ⟨N₁, N₂, hN₁, hN₂, hscheme⟩ :=
    ComparisonSchemeMorreyCore n p τ c₀ Wn M (d / 2) (min R₁ (d / 16)) σ₂ hn hp hτ0 hτn
      hc₀ hWn hM (by linarith) hRs hσ₂cont hσ₂mono hσ₂zero hσ₂nn hSP
  refine ⟨N₁, N₂, hN₁, hN₂, ?_⟩
  intro ε Ω Ω' fdens u g hε0 hε1 hΩ hΩ' hΩ'ne hΩ'bd hclΩ' hLip hsep hCamp hC4 hF hu hubd
    hWbd hmin
  -- Step 2: the oscillation decay, the inner domain and the continuous representative.
  obtain ⟨α, d₀, hα0, hα1, hd₀, hosc⟩ := hC4 lam Lam a M hlam hlamLam ha hM
  have hGrowth : VariationalGrowthF1 n p ε lam Lam a Ω fdens :=
    ⟨hF.meas_x, hF.cont_zh, hF.F1⟩
  have hoscu : ∀ (y : EuclideanSpace ℝ (Fin n)) (R₃ ρ : ℝ),
      Metric.closedBall y R₃ ⊆ Ω → 0 < ρ → ρ ≤ R₃ →
      EssOscOn n (Metric.ball y ρ) u
        ≤ (4 : ℝ) ^ α * max (EssOscOn n (Metric.ball y R₃) u) (d₀ * R₃)
          * (ρ / R₃) ^ α := by
    intro y R₃ ρ hsub hρ hρR
    exact hosc ε hε0 hε1 Ω fdens u g y R₃ ρ hΩ hGrowth hmin hubd hsub hρ hρR
  obtain ⟨Ω₁, U, hΩ₁, hΩ₁bd, hclΩ'Ω₁, hclΩ₁Ω, hsepA, hsepB, hballΩ, hUeq, hUW, hUcont,
      hUhol⟩ :=
    InnerDomainRepresentative n p α d₀ M d hn1 hp1 hα0 hα1 hd₀ hM hd Ω Ω' u g hΩ hΩ'ne
      hΩ'bd hsep hu hubd hoscu
  have hUbd : ∀ᵐ x ∂(volume.restrict Ω), |U x| ≤ M := by
    filter_upwards [hUeq, hubd] with x h1 h2
    rw [h1]
    exact h2
  have hUmin : IsLocalMinimumOn n p Ω fdens U g :=
    (AEModificationInvariance n p hn1 hp1 Ω u U g hΩ
      (hUeq.mono fun x hx => hx.symm)).2.2.2.2 fdens hmin
  -- Steps 3 and 4: the comparison map, the decay (4.11) and the smallness (⋆).
  have hbundle : ∀ x₁ ∈ Ω₁, ∀ R : ℝ, 0 < R → R ≤ min R₁ (d / 16) →
      Metric.closedBall x₁ R ⊆ Ω →
      ∃ (v : EuclideanSpace ℝ (Fin n) → ℝ)
        (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        MemW1pOn n p (Metric.ball x₁ R) v gv ∧
        (∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
          (∫ x in Metric.ball x₁ ρ, (ε + ‖gv x‖ ^ 2) ^ (p / 2))
            ≤ c₀ * (ρ / R) ^ (n : ℝ)
              * ∫ x in Metric.ball x₁ R, (ε + ‖gv x‖ ^ 2) ^ (p / 2)) ∧
        (∫ x in Metric.ball x₁ R, ‖g x - gv x‖ ^ p)
          ≤ σ₂ R * ∫ x in Metric.ball x₁ R, (1 + ‖g x‖ ^ 2) ^ (p / 2) := by
    intro x₁ hx₁ R hR0 hRle hRball
    have hx₁Ω : x₁ ∈ Ω := hclΩ₁Ω (subset_closure hx₁)
    -- the normalised frozen operator satisfies (Q1)-(Q2) on all of `ℝⁿ`
    have hQ12 := FrozenOperatorStructureQ12 n p ε lam Lam a ν₀ ν₁ hn hp hε0 hε1 hlam
      hlamLam ha hν₀ hν₀ν₁ Ω fdens σ x₁ (U x₁) hΩ hx₁Ω hF
    have hsubball : Metric.ball x₁ R ⊆ Ω := Metric.ball_subset_closedBall.trans hRball
    have hUWball : MemW1pOn n p (Metric.ball x₁ R) U g :=
      (WeakGradientRestrict n p hn1 hp1 Ω (Metric.ball x₁ R) U g hΩ Metric.isOpen_ball
        hsubball).1 hUW
    have hsub16 : Metric.closedBall x₁ R ⊆ Metric.closedBall x₁ (d / 16) :=
      Metric.closedBall_subset_closedBall (le_trans hRle (min_le_right _ _))
    have hUholR : MemHolderOn n α (Metric.closedBall x₁ R) U := by
      obtain ⟨hc, C, hC0, hCle⟩ := hUhol x₁ hx₁
      exact ⟨hc.mono hsub16, C, hC0, fun x hx y hy => hCle x (hsub16 hx) y (hsub16 hy)⟩
    obtain ⟨v, V, gv, hFC, hdec⟩ :=
      hdecay ε α ν₀ ν₁ (FrozenGradientOperator n fdens x₁ (U x₁)) x₁ R U g hε0 hε1 hα0
        hα1 hν₀ hν₁ (by field_simp; norm_num) hR0 hQ12 hUWball hUholR
    refine ⟨v, gv, hFC.2.1, hdec, ?_⟩
    exact hsmall ε Ω Ω₁ fdens U U g x₁ R v V gv hε0 hε1 hΩ hΩ₁ hΩ₁bd hclΩ₁Ω hsepB hF hC4
      hUW hUbd hUmin hx₁ hR0 (le_trans hRle (min_le_left _ _)) hRball hFC
  -- Step 5: the comparison scheme delivers the three conclusions.
  exact hscheme ε Ω Ω₁ Ω' u g hε0 hε1 hΩ hΩ₁ hΩ' hΩ'ne hΩ₁bd hclΩ'Ω₁ hclΩ₁Ω hsepA hsepB
    hLip hCamp hu hubd hWbd hbundle
