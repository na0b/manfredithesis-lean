import ManfrediThesis.Preamble
import ManfrediThesis.IsBoundedLipschitzDomain
import ManfrediThesis.BallIsLipschitzDomain
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.CitedDirichletW1p
import ManfrediThesis.CitedDirichletHolder
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.CitedHolderOscillationSolution
import ManfrediThesis.EllipticStructureQ345
import ManfrediThesis.EllipticStructureQ6
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.CampanatoBoundOn
import ManfrediThesis.MemC1HolderOn
import ManfrediThesis.ComparisonSchemeCampanatoCore
import ManfrediThesis.UniformHolderDatumOnBalls
import ManfrediThesis.GradientDecayToC1Holder
import ManfrediThesis.ComparisonGradientEstimateGeneral
import ManfrediThesis.SolutionMorreyRegularity
import ManfrediThesis.CitedCampanatoEmbedding
import ManfrediThesis.GradientSupEstimate
import ManfrediThesis.GradientOscillationEstimate
import ManfrediThesis.FrozenComparisonOn
open MeasureTheory

/-- Theorem 6: Campanato regularity of the gradient and `C^{1+β}` regularity of
a bounded weak solution, under the additional Hölder condition on `σ`. -/
theorem SolutionGradientHolder :
    ∀ (n : ℕ) (p μ γ₀ γ₁ γ₂ γ₃ γ₄ δ M : ℝ),
      2 ≤ n → 1 < p → 0 < μ → 0 < γ₀ → γ₀ ≤ γ₁ → 0 < γ₂ → 0 < γ₃ → 0 < γ₄ →
      0 < δ → 0 ≤ M →
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
      (∀ (y : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
        CitedCampanatoEmbedding n ((n : ℝ) / ((n : ℝ) - 1)) (Metric.ball y ρ)) →
      ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ p ∧
        ∀ (cσ d Wn : ℝ) (σ : ℝ → ℝ), 0 < cσ → 0 < d → 0 ≤ Wn →
          ∃ N : ℝ, 0 ≤ N ∧
            ∀ (ε : ℝ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
              (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
                EuclideanSpace ℝ (Fin n))
              (B : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
              (u : EuclideanSpace ℝ (Fin n) → ℝ)
              (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
              0 ≤ ε → ε ≤ 1 → IsOpen Ω → IsOpen Ω' → Ω'.Nonempty →
              Bornology.IsBounded Ω' → closure Ω' ⊆ Ω →
              IsBoundedLipschitzDomain n Ω' →
              (∀ x ∈ Ω', ∀ y, y ∉ Ω → d ≤ dist x y) →
              CitedCampanatoEmbedding n p Ω' →
              CitedCampanatoEmbedding n ((n : ℝ) / ((n : ℝ) - 1)) Ω' →
              CitedHolderOscillationSolution n p →
              EllipticStructureQ12 n p ε γ₀ γ₁ Ω A →
              EllipticStructureQ345 n p ε μ γ₂ γ₃ γ₄ Ω A B →
              EllipticStructureQ6 n p Ω A σ →
              (∀ t : ℝ, 0 ≤ t → σ t ≤ cσ * t ^ δ) →
              MemW1pOn n p Ω u g →
              (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
              ((∫ x in Ω, |u x| ^ p) + ∫ x in Ω, ‖g x‖ ^ p) ≤ Wn ^ p →
              IsWeakSolutionOn n p Ω A B u g →
              (∀ i : Fin n,
                  CampanatoBoundOn n p ((n : ℝ) + lam₀) Ω' (fun x => g x i) N)
                ∧ (∃ (w : EuclideanSpace ℝ (Fin n) → ℝ)
                    (gw : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
                    (∀ᵐ x ∂(volume.restrict Ω'), u x = w x) ∧
                      (∀ᵐ x ∂(volume.restrict Ω'), g x = gw x) ∧
                      MemC1HolderOn n (lam₀ / p) Ω' (closure Ω') w gw) := by
  intro n p μ γ₀ γ₁ γ₂ γ₃ γ₄ δ M hn hp hμ hγ₀ hγ₀γ₁ hγ₂ hγ₃ hγ₄ hδ hM hSP hC1 hC2
    hC3 hC5ball
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  have hγ₁0 : (0:ℝ) < γ₁ := lt_of_lt_of_le hγ₀ hγ₀γ₁
  have hp20 : (0:ℝ) ≤ p/2 := by linarith
  have h2p0 : (0:ℝ) < (2:ℝ) ^ (p/2) := Real.rpow_pos_of_pos two_pos _
  have hntriv : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ)
      (by rw [finrank_euclideanSpace_fin]; omega)
  set ωn : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal with hωndef
  have hωn0 : (0:ℝ) < ωn := by
    rw [hωndef]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne'
      measure_ball_lt_top.ne
  have hballvol : ∀ (y : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 ≤ t →
      (volume (Metric.ball y t)).toReal = ωn * t ^ ((n:ℝ)) := by
    intro y t ht
    rw [Measure.addHaar_ball volume y ht, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg ht _),
      (finrank_euclideanSpace_fin (n := n) (𝕜 := ℝ)), ← hωndef,
      ← Real.rpow_natCast t n]
    ring
  have hptw : ∀ t : ℝ, 0 ≤ t → (1 + t^2) ^ (p/2) ≤ 2 ^ (p/2) * (1 + t ^ p) := by
    intro t ht
    have ht2 : (t ^ (2:ℝ)) = t^2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num]; exact Real.rpow_natCast t 2
    have htp : (0:ℝ) ≤ t ^ p := Real.rpow_nonneg ht _
    rcases le_or_gt t 1 with h | h
    · have ht2le : t^2 ≤ 1 := pow_le_one₀ ht h
      have h2 : (1 + t^2) ^ (p/2) ≤ (2:ℝ) ^ (p/2) :=
        Real.rpow_le_rpow (by positivity) (by linarith) hp20
      exact h2.trans (le_mul_of_one_le_right h2p0.le (by linarith))
    · have ht21 : (1:ℝ) ≤ t^2 := one_le_pow₀ h.le
      have h2 : (1 + t^2) ^ (p/2) ≤ (2 * t^2 : ℝ) ^ (p/2) :=
        Real.rpow_le_rpow (by positivity) (by linarith) hp20
      have h4 : (2 * t^2 : ℝ) ^ (p/2) = 2 ^ (p/2) * t ^ p := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← ht2, ← Real.rpow_mul ht]
        congr 2
        ring
      rw [h4] at h2
      exact h2.trans (mul_le_mul_of_nonneg_left (by linarith) h2p0.le)
  have hcont1 : Continuous (fun t : ℝ => (1 + t^2) ^ (p/2)) := by
    have h1 : Continuous (fun t : ℝ => 1 + t^2) :=
      continuous_const.add (continuous_pow 2)
    exact h1.rpow_const (fun t => Or.inl (by positivity))
  -- (1a) the ratio
  have hr : (0:ℝ) < γ₁ / γ₀ := div_pos hγ₁0 hγ₀
  have hratio : γ₁ ≤ γ₁ / γ₀ * γ₀ := le_of_eq (by rw [div_mul_cancel₀ _ hγ₀.ne'])
  -- (1b) clause (B) of Lemma 5.1 at α = 1/2 and the present δ
  obtain ⟨-, hBsol⟩ := ComparisonGradientEstimateGeneral n p μ γ₀ γ₁ γ₂ γ₃ γ₄ hn hp hμ
    hγ₀ hγ₀γ₁ hγ₂ hγ₃ hγ₄ hSP hC3
  obtain ⟨δ', hδ'0, hsolB⟩ := hBsol (1/2) δ (by norm_num) (by norm_num) hδ
  -- (1c) τ♯ and the head of the comparison scheme
  have hden : (0:ℝ) < (n:ℝ) + p * (1/2) := by nlinarith
  have hQ : (0:ℝ) < p * (1/2) * δ' / ((n:ℝ) + p * (1/2)) := by positivity
  obtain ⟨-, hBcamp⟩ := ComparisonSchemeCampanatoCore n p (1/2) δ'
    ((1/2) * (p * (1/2) * δ' / ((n:ℝ) + p * (1/2)))) 1 1 hn hp (by norm_num)
    (by norm_num) hδ'0 one_pos one_pos (by positivity) (by linarith)
  -- (1d) clause (B) at r and αH = 1/2
  obtain ⟨α₂, hα₂0, hα₂1, hcampB⟩ :=
    hBcamp (γ₁/γ₀) (1/2) hr (by norm_num) (by norm_num) hSP hC2 hC1 hC3
  have hden2 : (0:ℝ) < (n:ℝ) + p * α₂ := by nlinarith
  set θ₂ : ℝ := δ' / ((n:ℝ) + p * α₂) with hθ₂def
  have hθ₂0 : (0:ℝ) < θ₂ := div_pos hδ'0 hden2
  have hpαθ : (0:ℝ) < p * α₂ * θ₂ := by positivity
  set τ₂ : ℝ := min (p * α₂ * θ₂ / 2) (min ((n:ℝ)/2) (p/2)) with hτ₂def
  have hτ₂0 : (0:ℝ) < τ₂ := by
    rw [hτ₂def]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hτ₂half : τ₂ ≤ p * α₂ * θ₂ / 2 := by rw [hτ₂def]; exact min_le_left _ _
  have hτ₂n2 : τ₂ ≤ (n:ℝ)/2 := by
    rw [hτ₂def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hτ₂p2 : τ₂ ≤ p/2 := by
    rw [hτ₂def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hτ₂n : τ₂ < (n:ℝ) := by linarith
  have hτ₂lt : τ₂ < p * α₂ * δ' / ((n:ℝ) + p * α₂) := by
    have h2 : p * α₂ * δ' / ((n:ℝ) + p * α₂) = p * α₂ * θ₂ := by rw [hθ₂def]; ring
    rw [h2]; linarith
  obtain ⟨lam₂, R₃, hlam₂0, hlam₂p, hR₃0, hR₃1, hc₂₀gen⟩ :=
    hcampB δ' τ₂ hδ'0 hτ₂0 hτ₂lt
  -- (1e)
  refine ⟨lam₂, hlam₂0, hlam₂p.le, ?_⟩
  intro cσ d Wn σ hcσ hd hWn
  -- Step 2: the case split on the (Q6) rate
  by_cases hrateσ : ∀ t : ℝ, 0 ≤ t → σ t ≤ cσ * t ^ δ
  case neg =>
    refine ⟨0, le_rfl, ?_⟩
    intro ε Ω Ω' A B u g _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hratedata _ _ _ _
    exact absurd hratedata hrateσ
  -- the surviving branch: the constant chain, all before the data
  obtain ⟨N₁, N₂, hN₁0, hN₂0, hthm5⟩ :=
    SolutionMorreyRegularity n p τ₂ μ γ₀ γ₁ γ₂ γ₃ γ₄ (d/4) M Wn σ hn hp hτ₂0 hτ₂n hμ
      hγ₀ hγ₀γ₁ hγ₂ hγ₃ hγ₄ (by linarith) hM hWn hSP hC1 hC2 hC3
  obtain ⟨C₁, hC₁0, hUH⟩ :=
    UniformHolderDatumOnBalls n p τ₂ d M N₂ hn hp hτ₂0 hτ₂p2 hd hM hN₂0
      (hC5ball 0 (d/4) (by linarith))
  obtain ⟨R₁', hR₁'0, hsmallB⟩ := hsolB M d σ hM hd cσ C₁ hcσ hC₁0 hrateσ
  set R₁ : ℝ := min (min (d/16) R₁') 1 with hR₁def
  have hR₁0 : (0:ℝ) < R₁ := by
    rw [hR₁def]; exact lt_min (lt_min (by linarith) hR₁'0) one_pos
  have hR₁d : R₁ ≤ d/16 := by
    rw [hR₁def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hR₁R' : R₁ ≤ R₁' := by
    rw [hR₁def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hR₁1 : R₁ ≤ 1 := by rw [hR₁def]; exact min_le_right _ _
  set c₂ : ℝ := 2 ^ (p/2) * (ωn + N₁ ^ p) with hc₂def
  have hc₂0 : (0:ℝ) < c₂ := by
    rw [hc₂def]
    have h1 : (0:ℝ) < 2 ^ (p/2) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0:ℝ) ≤ N₁ ^ p := Real.rpow_nonneg hN₁0 _
    positivity
  obtain ⟨c₂₀, hc₂₀0, hdecaygen⟩ := hc₂₀gen c₂ hc₂0
  set R : ℝ := min R₁ R₃ with hRdef
  have hR0 : (0:ℝ) < R := by rw [hRdef]; exact lt_min hR₁0 hR₃0
  have hRR₁ : R ≤ R₁ := by rw [hRdef]; exact min_le_left _ _
  have hRR₃ : R ≤ R₃ := by rw [hRdef]; exact min_le_right _ _
  have hR1 : R ≤ 1 := le_trans hRR₃ hR₃1
  set ρ₀ : ℝ := (1/2) * R ^ (1 + θ₂) with hρ₀def
  have hRpow : R ^ (1 + θ₂) ≤ R := by
    have h := Real.rpow_le_rpow_of_exponent_ge hR0 hR1
      (show (1:ℝ) ≤ 1 + θ₂ by linarith)
    rwa [Real.rpow_one] at h
  have hρ₀0 : (0:ℝ) < ρ₀ := by
    rw [hρ₀def]
    have := Real.rpow_pos_of_pos hR0 (1 + θ₂)
    linarith
  have hρ₀1 : ρ₀ ≤ 1 := by rw [hρ₀def]; linarith
  obtain ⟨N, hN0, hGD⟩ :=
    GradientDecayToC1Holder n p lam₂ c₂₀ ρ₀ Wn hn hp hlam₂0 hlam₂p hc₂₀0 hρ₀0 hρ₀1 hWn
  refine ⟨N, hN0, ?_⟩
  intro ε Ω Ω' A B u g hε0 hε1 hΩ hΩ' hΩ'ne hΩ'bd hclΩ' hLip hsep hCampp hCampq hC4
    hQ12 hQ345 hQ6 hrate' hu hubd hWbd hsol
  have hΩ'Ω : Ω' ⊆ Ω := subset_trans subset_closure hclΩ'
  -- the balls B_{d/4}(y₀), y₀ ∈ Ω', and their separation
  have hclball : ∀ y₀ ∈ Ω', Metric.closedBall y₀ (d/4) ⊆ Ω := by
    intro y₀ hy₀ z hz
    by_contra hzn
    have h1 := hsep y₀ hy₀ z hzn
    rw [Metric.mem_closedBall, dist_comm] at hz
    linarith
  have hsepball : ∀ y₀ ∈ Ω', ∀ x ∈ Metric.ball y₀ (d/4), ∀ y, y ∉ Ω →
      d/4 ≤ dist x y := by
    intro y₀ hy₀ x hx y hyn
    have h1 := hsep y₀ hy₀ y hyn
    rw [Metric.mem_ball] at hx
    have h2 : dist y₀ y ≤ dist y₀ x + dist x y := dist_triangle _ _ _
    rw [dist_comm y₀ x] at h2
    linarith
  -- (2a) the inner domain and the continuous representative
  obtain ⟨α₄, d₀, hα₄0, hα₄1, hd₀, hosc⟩ :=
    hC4 μ γ₀ γ₁ γ₂ γ₃ γ₄ M hγ₀ hγ₁0 hγ₂ hγ₃ hγ₄ hμ hM
  have hoscu : ∀ (y : EuclideanSpace ℝ (Fin n)) (Rb ρ : ℝ),
      Metric.closedBall y Rb ⊆ Ω → 0 < ρ → ρ ≤ Rb →
      EssOscOn n (Metric.ball y ρ) u
        ≤ (4:ℝ) ^ α₄ * max (EssOscOn n (Metric.ball y Rb) u) (d₀ * Rb)
          * (ρ / Rb) ^ α₄ := by
    intro y Rb ρ hsub hρ hρR
    exact hosc ε hε0 hε1 Ω A B u g y Rb ρ hΩ hQ12 hQ345 hsol hubd hsub hρ hρR
  obtain ⟨Ω₁, U, hΩ₁, hΩ₁bd, hclΩ'Ω₁, hclΩ₁Ω, hsepA, hsepB, hballΩ, hUeq, hUW,
      hUcont, hUhol⟩ :=
    InnerDomainRepresentative n p α₄ d₀ M d hn1 hp.le hα₄0 hα₄1 hd₀ hM hd Ω Ω' u g hΩ
      hΩ'ne hΩ'bd hsep hu hubd hoscu
  have hUbd : ∀ᵐ x ∂(volume.restrict Ω), |U x| ≤ M := by
    filter_upwards [hUeq, hubd] with x h1 h2
    rw [h1]
    exact h2
  have hUsol : IsWeakSolutionOn n p Ω A B U g :=
    (AEModificationInvariance n p hn1 hp.le Ω u U g hΩ
      (hUeq.mono fun x hx => hx.symm)).2.2.2.1 A B hsol
  have hball4Ω₁ : ∀ y₀ ∈ Ω', Metric.ball y₀ (d/4) ⊆ Ω₁ := by
    intro y₀ hy₀ z hz
    by_contra hzn
    have h1 := hsepA y₀ hy₀ z hzn
    rw [Metric.mem_ball, dist_comm] at hz
    linarith
  -- (2a′) Theorem 5 on each ball B_{d/4}(y₀), then the Hölder datum
  have hclball' : ∀ y₀ ∈ Ω', closure (Metric.ball y₀ (d/4)) ⊆ Ω := by
    intro y₀ hy₀
    have h := closure_mono (Metric.ball_subset_closedBall :
      Metric.ball y₀ (d/4) ⊆ Metric.closedBall y₀ (d/4))
    rw [Metric.isClosed_closedBall.closure_eq] at h
    exact h.trans (hclball y₀ hy₀)
  have hthm5ball : ∀ y₀ ∈ Ω',
      MorreyBoundOn n p ((n:ℝ) - τ₂) (Metric.ball y₀ (d/4)) (fun x => ‖g x‖) N₁
      ∧ CampanatoBoundOn n ((n:ℝ)/((n:ℝ)-1))
          ((n:ℝ) + (1 - τ₂/p) * ((n:ℝ)/((n:ℝ)-1))) (Metric.ball y₀ (d/4)) u N₂ := by
    intro y₀ hy₀
    obtain ⟨h1, h2, -⟩ := hthm5 ε Ω (Metric.ball y₀ (d/4)) A B u g hε0 hε1 hΩ
      Metric.isOpen_ball (Metric.nonempty_ball.2 (by linarith)) Metric.isBounded_ball
      (hclball' y₀ hy₀) (BallIsLipschitzDomain n hn1 y₀ (d/4) (by linarith))
      (hsepball y₀ hy₀) (hC5ball y₀ (d/4) (by linarith)) hC4 hQ12 hQ345 hQ6 hu hubd
      hWbd hsol
    exact ⟨h1, h2⟩
  have hUcontball : ∀ y₀ ∈ Ω', ContinuousOn U (Metric.ball y₀ (d/4)) :=
    fun y₀ hy₀ => hUcont.mono (hball4Ω₁ y₀ hy₀)
  have hdatum := hUH Ω Ω' u U hΩ hsep hubd hUeq hUcontball
    (fun y₀ hy₀ => (hthm5ball y₀ hy₀).2)
  -- (2b) the frozen family, from the equation-side frozen-structure node
  have hQ12f : ∀ x₀ ∈ Ω', EllipticStructureQ12 n p ε γ₀ γ₁ Set.univ
      (fun _ _ h => A x₀ (U x₀) h - A x₀ (U x₀) 0) := by
    intro x₀ hx₀
    exact (FrozenSolutionStructureQ12 n p ε γ₀ γ₁ hn hp hε0 hγ₀ hγ₁0 Ω A σ x₀ (U x₀)
      hΩ (hΩ'Ω hx₀) hQ12 hQ6).2
  -- (2c) the Morrey bound
  have hgΩ : MemLp g (ENNReal.ofReal p) (volume.restrict Ω) := hu.2.2
  have hofR0 : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero]; linarith
  have hofRtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoR : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hgnormint : ∀ S : Set (EuclideanSpace ℝ (Fin n)), S ⊆ Ω →
      IntegrableOn (fun y => ‖g y‖ ^ p) S := by
    intro S hS
    have h := (hgΩ.mono_measure
      (Measure.restrict_mono hS le_rfl)).integrable_norm_rpow hofR0 hofRtop
    rwa [htoR] at h
  have hclballR₁ : ∀ x₀ ∈ Ω', ∀ R' : ℝ, 0 < R' → R' ≤ R₁ →
      Metric.closedBall x₀ R' ⊆ Ω := by
    intro x₀ hx₀ R' _ hR'le
    exact (Metric.closedBall_subset_closedBall (by linarith)).trans (hclball x₀ hx₀)
  have hmorrey : ∀ x₀ ∈ Ω', ∀ R' : ℝ, 0 < R' → R' ≤ R₁ →
      R' ^ (-(n:ℝ)) * ∫ x in Metric.ball x₀ R', (1 + ‖g x‖ ^ 2) ^ (p/2)
        ≤ c₂ * R' ^ (-τ₂) := by
    intro x₀ hx₀ R' hR' hR'le
    have hR'd4 : R' ≤ d/4 := by linarith
    have hBΩ : Metric.ball x₀ R' ⊆ Ω :=
      Metric.ball_subset_closedBall.trans (hclballR₁ x₀ hx₀ R' hR' hR'le)
    have hdiam : Metric.diam (Metric.ball x₀ (d/4)) = 2 * (d/4) :=
      Metric.diam_ball_eq x₀ (by linarith)
    have hinter : Metric.ball x₀ (d/4) ∩ Metric.ball x₀ R' = Metric.ball x₀ R' :=
      Set.inter_eq_self_of_subset_right (Metric.ball_subset_ball hR'd4)
    have h415 : (∫ y in Metric.ball x₀ R', ‖g y‖ ^ p) ≤ N₁ ^ p * R' ^ ((n:ℝ) - τ₂) := by
      have h := (hthm5ball x₀ hx₀).1.2 x₀ (Metric.mem_ball_self (by linarith)) R' hR'
        (by rw [hdiam]; linarith)
      rw [hinter] at h
      simpa only [abs_norm] using h
    have : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R')) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have hmeas : AEStronglyMeasurable (fun x => (1 + ‖g x‖ ^ 2) ^ (p/2))
        (volume.restrict (Metric.ball x₀ R')) :=
      hcont1.comp_aestronglyMeasurable
        ((hgΩ.mono_measure (Measure.restrict_mono hBΩ le_rfl)).1).norm
    have hdomint : IntegrableOn (fun x => 2 ^ (p/2) * (1 + ‖g x‖ ^ p))
        (Metric.ball x₀ R') :=
      ((integrable_const (1:ℝ)).add (hgnormint _ hBΩ)).const_mul _
    have hLint : IntegrableOn (fun x => (1 + ‖g x‖ ^ 2) ^ (p/2)) (Metric.ball x₀ R') := by
      refine Integrable.mono' hdomint hmeas ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact hptw _ (norm_nonneg _)
    have hchain : (∫ x in Metric.ball x₀ R', (1 + ‖g x‖ ^ 2) ^ (p/2))
        ≤ 2 ^ (p/2) * (ωn * R' ^ ((n:ℝ))
          + ∫ x in Metric.ball x₀ R', ‖g x‖ ^ p) := by
      have h1 := integral_mono_ae hLint hdomint
        (Filter.Eventually.of_forall (fun x => hptw _ (norm_nonneg _)))
      rw [integral_const_mul, integral_add (integrable_const 1) (hgnormint _ hBΩ),
        integral_const, Measure.real_def, Measure.restrict_apply_univ, smul_eq_mul,
        mul_one, hballvol x₀ R' hR'.le] at h1
      exact h1
    have e1 : R' ^ (-(n:ℝ)) * R' ^ ((n:ℝ)) = 1 := by
      rw [← Real.rpow_add hR']; norm_num
    have e2 : R' ^ (-(n:ℝ)) * R' ^ ((n:ℝ) - τ₂) = R' ^ (-τ₂) := by
      rw [← Real.rpow_add hR']; congr 1; ring
    have e3 : (1:ℝ) ≤ R' ^ (-τ₂) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hR' (by linarith : R' ≤ 1)
        (by linarith : -τ₂ ≤ (0:ℝ))
      rwa [Real.rpow_zero] at h
    have hRn0 : (0:ℝ) < R' ^ (-(n:ℝ)) := Real.rpow_pos_of_pos hR' _
    have hN₁p : (0:ℝ) ≤ N₁ ^ p := Real.rpow_nonneg hN₁0 _
    rw [hc₂def]
    calc R' ^ (-(n:ℝ)) * (∫ x in Metric.ball x₀ R', (1 + ‖g x‖ ^ 2) ^ (p/2))
        ≤ R' ^ (-(n:ℝ)) * (2 ^ (p/2) * (ωn * R' ^ ((n:ℝ))
            + N₁ ^ p * R' ^ ((n:ℝ) - τ₂))) := by
          refine mul_le_mul_of_nonneg_left (le_trans hchain ?_) hRn0.le
          exact mul_le_mul_of_nonneg_left (by linarith) h2p0.le
      _ = 2 ^ (p/2) * (ωn * (R' ^ (-(n:ℝ)) * R' ^ ((n:ℝ)))
            + N₁ ^ p * (R' ^ (-(n:ℝ)) * R' ^ ((n:ℝ) - τ₂))) := by ring
      _ = 2 ^ (p/2) * (ωn + N₁ ^ p * R' ^ (-τ₂)) := by rw [e1, e2]; ring
      _ ≤ 2 ^ (p/2) * (ωn * R' ^ (-τ₂) + N₁ ^ p * R' ^ (-τ₂)) := by
          refine mul_le_mul_of_nonneg_left ?_ h2p0.le
          have h5 : ωn ≤ ωn * R' ^ (-τ₂) := by
            calc ωn = ωn * 1 := by ring
              _ ≤ ωn * R' ^ (-τ₂) := mul_le_mul_of_nonneg_left e3 hωn0.le
          linarith
      _ = 2 ^ (p/2) * (ωn + N₁ ^ p) * R' ^ (-τ₂) := by ring
  -- (2d) the smallness, in clause (B)'s normalised form
  have hsmall2 : ∀ x₀ ∈ Ω', ∀ R' : ℝ, 0 < R' → R' ≤ R₁ →
      ∀ (v V : EuclideanSpace ℝ (Fin n) → ℝ)
        (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        FrozenComparisonOn n p x₀ R' (fun h => A x₀ (U x₀) h) U U g v V gv →
        (∫ x in Metric.ball x₀ R', ‖g x - gv x‖ ^ p)
          ≤ R' ^ (δ' + (n:ℝ)) * (R' ^ (-(n:ℝ))
            * ∫ x in Metric.ball x₀ R', (1 + ‖g x‖ ^ 2) ^ (p/2)) := by
    intro x₀ hx₀ R' hR' hR'le v V gv hFC
    have h := hsmallB ε Ω Ω' A B U U g x₀ R' v V gv hε0 hε1 hΩ hΩ' hΩ'bd hclΩ' hsep
      hQ12 hQ345 hQ6 hC4 hUW hUbd hUsol hx₀ hR' (le_trans hR'le hR₁R')
      (hclballR₁ x₀ hx₀ R' hR' hR'le) hFC
      (fun x hx y hy => (hdatum x₀ hx₀ R' hR' (by linarith)).2 x hx y hy)
    have e : R' ^ (δ' + (n:ℝ)) * R' ^ (-(n:ℝ)) = R' ^ δ' := by
      rw [← Real.rpow_add hR']
      congr 1
      ring
    calc (∫ x in Metric.ball x₀ R', ‖g x - gv x‖ ^ p)
        ≤ R' ^ δ' * ∫ x in Metric.ball x₀ R', (1 + ‖g x‖ ^ 2) ^ (p/2) := h
      _ = R' ^ (δ' + (n:ℝ)) * (R' ^ (-(n:ℝ))
            * ∫ x in Metric.ball x₀ R', (1 + ‖g x‖ ^ 2) ^ (p/2)) := by
          rw [← mul_assoc, e]
  -- Step 3: the decay (4.19)
  have h419 := hdecaygen ε γ₀ γ₁ Ω Ω' (fun x z => A x z) u U g R₁
    hε0 hε1 hγ₀ hγ₁0 hratio hΩ hΩ' hclΩ' hR₁0 hu hUW hclballR₁ hQ12f
    (fun x₀ hx₀ => (hdatum x₀ hx₀ R₁ hR₁0 hR₁d).1) hmorrey hsmall2
  -- Step 4: the two conclusions
  have hballρ₀ : ∀ x₀ ∈ Ω', ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → Metric.ball x₀ ρ ⊆ Ω := by
    intro x₀ hx₀ ρ hρ hρle
    rw [hρ₀def] at hρle
    exact Metric.ball_subset_closedBall.trans
      (hclballR₁ x₀ hx₀ ρ hρ (by linarith))
  have hdecay4 : ∀ x₀ ∈ Ω', ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      (∫ x in Metric.ball x₀ ρ, ‖g x - (volume (Metric.ball x₀ ρ)).toReal⁻¹
          • ∫ y in Metric.ball x₀ ρ, g y‖ ^ p) ≤ c₂₀ * ρ ^ ((n:ℝ) + lam₂) := by
    intro x₀ hx₀ ρ hρ hρle
    refine h419 x₀ hx₀ R ρ hR0 (le_of_eq hRdef) hρ ?_
    rw [hρ₀def, hθ₂def] at hρle
    linarith
  have hWg : (∫ x in Ω, ‖g x‖ ^ p) ≤ Wn ^ p := by
    have h1 : (0:ℝ) ≤ ∫ x in Ω, |u x| ^ p :=
      integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _)
    linarith
  exact hGD Ω Ω' u g hΩ hΩ' hclΩ' hLip hCampp hu hWg hballρ₀ hdecay4
