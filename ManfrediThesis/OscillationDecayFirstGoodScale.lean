import ManfrediThesis.Preamble
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.EssOscOn
import ManfrediThesis.DeGiorgiLevelBound
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.WeakGradientRestrict
set_option maxHeartbeats 1600000
open MeasureTheory

/-- Case II of the oscillation decay estimate: the branch in which the
pinching hypothesis `H_m` holds at some scale.  Given the first such scale, the
oscillation of a partial derivative of the solution on `B_ρ(x₀)` is still at
most `16T(ρ/R₀)^α`.

Conventions, restated here because a helper inherits none of its parent's.
`B_σ(x₀)` is the open ball, `R_m = R₀/2^m` the dyadic radii, and
`μ(σ) = max_k \mathrm{ess\,sup}_{B_σ}|g^k|` the coordinate oscillation gauge,
all three carried as data with their defining properties as hypotheses rather
than as definitions, so that no form of them is assumed beyond what is listed.
`H : ℕ → Prop` is the pinching predicate, left OPAQUE: the branch uses only the
facts (H1)-(H6) about it listed below, never its definition, which is why it is
a bare `ℕ → Prop` here.  `EssOscOn` is the tablet's essential oscillation and
`DeGiorgiLevelBound` its De Giorgi level bound; `supp ζ` means the CLOSED
support of ζ wherever it occurs in the hypotheses, and all powers of positive
reals are `Real.rpow`, written exactly as the structure conditions print them,
including the weight `(ε + ‖g‖²)^{p/2-1}` of the Caccioppoli hypothesis.

The route is (B3)--(B7) of the parent's argument.  (B3) Let `m₀` be the least
`m` with `H_m`, which exists because `H` holds somewhere; below `m₀` the
predicate fails, so the chain hypothesis applies on `[0, m₀)` and gives the
decay of `μ` down to the scale `R_{m₀}`.  (B6) At the scale `m₀` itself the
pinching turns the Caccioppoli inequality into a De Giorgi level bound for a
coordinate `g^{k₀}` on the ball pair, which the oscillation decay lemma
converts into `osc_{B_{2R_{m₀}/3}}g^{k₀} ≤ δ·osc_{B_{R_{m₀}}}g^{k₀}`; with
`δ ≤ 2^{-α₂}` and `α ≤ α₂` that is decay at the exponent `α`.  (O) The gauge
`μ` is monotone, so these two regimes compose.  (B7) The assembly is three
cases on where `ρ` sits: `R_{m₀} ≤ ρ ≤ R₀`, `R_{m₀+1} ≤ ρ < R_{m₀}`, and
`ρ < R_{m₀+1}`; in each the bound `μ(ρ) ≤ 2(ρ/R₀)^α μ(R₀)` holds, and the
hypothesis relating `μ` to the oscillation finishes. -/
theorem OscillationDecayFirstGoodScale :
    ∀ (n : ℕ) (p r c₄ cp Kp γs δ ν α₂ α ε γ₀ γ₁ T : ℝ), 2 ≤ n → 1 < p → 0 < r →
      1 ≤ n → (2:ℝ) ≤ (n:ℝ) →
      0 < c₄ → 0 < cp → cp ≤ 1 / 16 → Kp = (1 / 4 + (n:ℝ)) / cp ^ 2 →
      0 < γs → δ ∈ Set.Ioo (0:ℝ) 1 →
      0 < α₂ → α₂ ≤ 1 → δ ≤ (2:ℝ) ^ (-α₂) →
      0 < α → α ≤ α₂ → α ≤ 1 →
      ∀ (Ω₀ : Set (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g g' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (x₀ : EuclideanSpace ℝ (Fin n)) (R₀ ρ : ℝ) (k : Fin n)
        (mu : ℝ → ℝ) (Rm : ℕ → ℝ) (Hm : ℕ → Prop),
        0 < ε → 0 < γ₀ → γ₁ ≤ r * γ₀ → 0 ≤ T → 0 < R₀ → 0 < ρ → ρ ≤ R₀ →
        0 < γ₁ →
        EllipticStructureQ12 n p ε γ₀ γ₁ Ω₀ (fun _ _ h => A h) →
        Metric.ball x₀ R₀ ⊆ Ω₀ →
        (∀ (ε' γ₀' γ₁' : ℝ) (Ω' : Set (EuclideanSpace ℝ (Fin n)))
          (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 < γ₀' → 0 < γ₁' → IsOpen Ω' →
          CitedRegularityEpsPos n p ε' γ₀' γ₁' Ω' A') →
        (∀ (ε γ₀ γ₁ : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (ζ : EuclideanSpace ℝ (Fin n) → ℝ) (k : Fin n) (l : ℝ),
        0 < ε → 0 < γ₀ → γ₁ ≤ r * γ₀ → IsOpen Ω →
        EllipticStructureQ12 n p ε γ₀ γ₁ Ω (fun _ _ h => A h) →
        CitedRegularityEpsPos n p ε γ₀ γ₁ Ω A →
        IsWeakSolutionOn n p Ω (fun _ _ h => A h) (fun _ _ _ => 0) u g →
        (∀ i : Fin n, MemW1pLocOn n 2 Ω (fun x => g x i) (Dg i)) →
        ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
        (∫ x in Ω ∩ {y | l < g y k},
        (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
        ≤ c₄ * ∫ x in Ω, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
        * max (g x k - l) 0 ^ 2
        * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2
        ∧ (∫ x in Ω ∩ {y | g y k < l},
        (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
        ≤ c₄ * ∫ x in Ω, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
        * max (l - g x k) 0 ^ 2
        * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) →
        (∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R Θ l κ₁ κ₂ : ℝ)
        (f : EuclideanSpace ℝ (Fin n) → ℝ)
        (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (w : EuclideanSpace ℝ (Fin n) → ℝ),
        0 < R → 0 < κ₁ → κ₂ ≤ Kp * κ₁ → Measurable w →
        MemW1pLocOn n 2 (Metric.ball x₀ R) f G →
        (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), |f x| ≤ Θ) →
        ∀ ρ₀ ρ₁ : ℝ, 0 < ρ₀ → ρ₀ < ρ₁ → ρ₁ < R →
        ((∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R ∩ {y | l < f y})),
        κ₁ ≤ w x ∧ w x ≤ κ₂) →
        (∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ Metric.ball x₀ R →
        (∫ x in Metric.ball x₀ R ∩ {y | l < f y},
        w x ^ (p / 2 - 1) * ‖G x‖ ^ 2 * ζ x ^ 2)
        ≤ c₄ * ∫ x in Metric.ball x₀ R, w x ^ (p / 2 - 1) * max (f x - l) 0 ^ 2
        * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) →
        DeGiorgiLevelBound n γs f G x₀ l ρ₀ ρ₁)
        ∧ ((∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R ∩ {y | f y < l})),
        κ₁ ≤ w x ∧ w x ≤ κ₂) →
        (∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ Metric.ball x₀ R →
        (∫ x in Metric.ball x₀ R ∩ {y | f y < l},
        w x ^ (p / 2 - 1) * ‖G x‖ ^ 2 * ζ x ^ 2)
        ≤ c₄ * ∫ x in Metric.ball x₀ R, w x ^ (p / 2 - 1) * max (l - f x) 0 ^ 2
        * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) →
        DeGiorgiLevelBound n γs (fun x => -f x) (fun x => -G x) x₀ (-l)
        ρ₀ ρ₁)) →
        (∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R m M : ℝ)
        (f : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < R → MemW1pOn n 2 (Metric.ball x₀ R) f g →
        (∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), |f x| ≤ C) →
        M = essSup f (volume.restrict (Metric.ball x₀ R)) →
        m = essInf f (volume.restrict (Metric.ball x₀ R)) →
        (∀ l ρ₀ ρ₁ : ℝ, l ∈ Set.Icc ((m + M) / 2) M →
        ρ₀ ∈ Set.Icc (2 / 3 * R) R → ρ₁ ∈ Set.Icc (2 / 3 * R) R → ρ₀ < ρ₁ →
        DeGiorgiLevelBound n γs f g x₀ l ρ₀ ρ₁) →
        (∀ l ρ₀ ρ₁ : ℝ, l ∈ Set.Icc m ((m + M) / 2) →
        ρ₀ ∈ Set.Icc (2 / 3 * R) R → ρ₁ ∈ Set.Icc (2 / 3 * R) R → ρ₀ < ρ₁ →
        DeGiorgiLevelBound n γs (fun x => -f x) (fun x => -g x) x₀ (-l) ρ₀ ρ₁) →
        EssOscOn n (Metric.ball x₀ (2 / 3 * R)) f
        ≤ δ * EssOscOn n (Metric.ball x₀ R) f) →
        (∀ σ : ℝ, 0 < σ → (ae (volume.restrict (Metric.ball x₀ σ))).NeBot) →
        (∀ {μm : Measure (EuclideanSpace ℝ (Fin n))}
        {v : EuclideanSpace ℝ (Fin n) → ℝ} {b : ℝ}, (ae μm).NeBot →
        (∀ᵐ x ∂μm, b ≤ v x) → Filter.IsCoboundedUnder (· ≤ ·) (ae μm) v) →
        (∀ {μm : Measure (EuclideanSpace ℝ (Fin n))}
        {v : EuclideanSpace ℝ (Fin n) → ℝ} {b : ℝ}, (ae μm).NeBot →
        (∀ᵐ x ∂μm, v x ≤ b) → Filter.IsCoboundedUnder (· ≥ ·) (ae μm) v) →
        (∀ (v : EuclideanSpace ℝ (Fin n)) (i : Fin n), |v i| ≤ ‖v‖) →
        (∀ (s t : Set (EuclideanSpace ℝ (Fin n))), t ⊆ s →
        EllipticStructureQ12 n p ε γ₀ γ₁ s (fun _ _ h => A h) →
        EllipticStructureQ12 n p ε γ₀ γ₁ t (fun _ _ h => A h)) →
        (∀ i : Fin n,
        MemW1pLocOn n 2 (Metric.ball x₀ R₀) (fun x => g x i) (Dg i)) →
        (∀ σ : ℝ, σ ≤ R₀ → ∀ k : Fin n,
        ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ σ)), |g x k| ≤ T) →
        (∀ σ : ℝ, 0 < σ → σ ≤ R₀ → ∀ k : Fin n,
        ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ σ)), |g x k| ≤ mu σ) →
        (∀ σ : ℝ, 0 < σ → σ ≤ R₀ → 0 ≤ mu σ) →
        (∀ σ : ℝ, 0 < σ → σ ≤ R₀ → mu σ ≤ T) →
        (∀ σ σ' : ℝ, 0 < σ → σ ≤ σ' → σ' ≤ R₀ → mu σ ≤ mu σ') →
        (∀ m : ℕ, 0 < Rm m) →
        (∀ m : ℕ, Rm m ≤ R₀) →
        (∀ m : ℕ, Rm (m + 1) = Rm m / 2) →
        (∀ m : ℕ, Metric.ball x₀ (Rm m) ⊆ Metric.ball x₀ R₀) →
        (∀ m : ℕ, IsWeakSolutionOn n p (Metric.ball x₀ (Rm m))
        (fun _ _ h => A h) (fun _ _ _ => 0) u g) →
        (∀ (m : ℕ) (i : Fin n),
        MemW1pLocOn n 2 (Metric.ball x₀ (Rm m)) (fun x => g x i) (Dg i)) →
        (∀ m : ℕ, Hm m → ∃ k₀ : Fin n,
        ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (Rm (m + 1)))),
        cp * mu (Rm m) ≤ |g x k₀|) →
        (∀ σ : ℝ, 0 < σ → σ ≤ R₀ → ∀ k : Fin n,
        EssOscOn n (Metric.ball x₀ σ) (fun x => g x k) ≤ 2 * mu σ) →
        (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ R₀ →
        ∃ m : ℕ, Rm (m + 1) < ρ' ∧ ρ' ≤ Rm m) →
        (∀ (m : ℕ) (ρ' : ℝ), 0 < ρ' → ρ' ≤ R₀ → Rm (m + 1) < ρ' → ρ' ≤ Rm m →
        mu (Rm m) ≤ ν ^ m * mu R₀ → mu ρ' ≤ 2 * (ρ' / R₀) ^ α * mu R₀) →
        (∀ m : ℕ, (∀ j : ℕ, j < m → ¬ Hm j) →
        mu (Rm m) ≤ ν ^ m * mu R₀) →
        (mu ρ ≤ 2 * (ρ / R₀) ^ α * mu R₀ →
        EssOscOn n (Metric.ball x₀ ρ) (fun x => g x k) ≤ 16 * T * (ρ / R₀) ^ α) →
        ContinuousOn g' (Metric.ball x₀ R₀) →
        (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R₀)), g x = g' x) →
        Rm = (fun m => R₀ / 2 ^ m) →
        (¬ ∀ m : ℕ, ¬ Hm m) →
        EssOscOn n (Metric.ball x₀ ρ) (fun x => g x k)
          ≤ 16 * T * (ρ / R₀) ^ α := by
  intro n p r c₄ cp Kp γs δ ν α₂ α ε γ₀ γ₁ T hn hp hr hn1 hnR hc₄0 hcp0 hcp16
    hKpdef hγs0 hδ hα₂0 hα₂1 hδα₂ hα0 hαα₂ hα1 Ω₀ A u g g' Dg x₀ R₀ ρ k mu Rm Hm
    hε hγ₀ hγ₁ hT0 hR₀ hρ hρR hγ₁0 hQ hballΩ hC1 hCLW hPCLB hODL hNBball hcobdd
    hcobddge hcoord hQrestrict hDg hgTk hmubnd hmu0 hmuT hmumono hRm0 hRmR
    hRmsucc hRmsub hsolBm hDgm hstep326 hoscmu hradius hdecay hchainmu hconclude
    hg'cont hg'ae hRmdef hCI
  classical
  have hex : ∃ m : ℕ, Hm m := by
    by_contra hc
    exact hCI (fun m hm => hc ⟨m, hm⟩)
  obtain ⟨m0, hm0def⟩ : ∃ m : ℕ, m = Nat.find hex := ⟨_, rfl⟩
  have hHm0 : Hm m0 := by rw [hm0def]; exact Nat.find_spec hex
  have hbelow : ∀ j : ℕ, j < m0 → ¬ Hm j := by
    intro j hj
    rw [hm0def] at hj
    exact Nat.find_min hex hj
  have hRsub1 : Metric.ball x₀ (Rm (m0 + 1)) ⊆ Metric.ball x₀ (Rm m0) :=
    Metric.ball_subset_ball (by rw [hRmsucc m0]; linarith [hRm0 m0])
  have hR1R : Rm (m0 + 1) ≤ R₀ := hRmR (m0 + 1)
  have hR10 : 0 < Rm (m0 + 1) := hRm0 (m0 + 1)
  -- (B4) the pinch on `𝓑 = B_{R_{m₀+1}}`
  have hnormsq : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (Rm (m0 + 1)))),
      ‖g x‖ ^ 2 ≤ (n:ℝ) * mu (Rm m0) ^ 2 := by
    have hall : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (Rm (m0 + 1)))),
        ∀ k : Fin n, |g x k| ≤ mu (Rm m0) := by
      rw [ae_all_iff]
      intro k
      exact ae_restrict_of_ae_restrict_of_subset hRsub1
        (hmubnd (Rm m0) (hRm0 m0) (hRmR m0) k)
    filter_upwards [hall] with x hx
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ k : Fin n, (g x k) ^ 2 ≤ ∑ _k : Fin n, mu (Rm m0) ^ 2 := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          have h1 := hx k
          nlinarith only [h1, abs_nonneg (g x k), sq_abs (g x k)]
      _ = (n:ℝ) * mu (Rm m0) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcp2 : cp ^ 2 ≤ 1 / 256 := by nlinarith only [hcp16, hcp0]
  obtain ⟨κ₁, κ₂, hκ₁0, hκ₂K, hpinch⟩ : ∃ κ₁ κ₂ : ℝ, 0 < κ₁ ∧ κ₂ ≤ Kp * κ₁ ∧
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (Rm (m0 + 1)))),
        κ₁ ≤ ε + ‖g x‖ ^ 2 ∧ ε + ‖g x‖ ^ 2 ≤ κ₂ := by
    rcases le_or_gt (mu (Rm m0) ^ 2 / 4) ε with hcase | hcase
    · -- `ε ≥ μ²/4`: the pinch is `ε ≤ w ≤ (1+4n)ε`
      refine ⟨ε, (1 + 4 * (n:ℝ)) * ε, hε, ?_, ?_⟩
      · have h1 : (1 + 4 * (n:ℝ)) ≤ Kp := by
          rw [hKpdef, le_div_iff₀ (by positivity)]
          nlinarith only [hcp2, hnR, hcp0]
        exact mul_le_mul_of_nonneg_right h1 hε.le
      · filter_upwards [hnormsq] with x hx
        refine ⟨by nlinarith only [sq_nonneg ‖g x‖], ?_⟩
        nlinarith only [hx, hcase, hnR]
    · -- `ε < μ²/4`: the pinch is `c_p²μ² ≤ w ≤ (1/4+n)μ²`
      obtain ⟨k₀, hk₀⟩ := hstep326 m0 hHm0
      have hμ2 : 0 < mu (Rm m0) ^ 2 := by nlinarith only [hcase, hε]
      refine ⟨cp ^ 2 * mu (Rm m0) ^ 2, (1 / 4 + (n:ℝ)) * mu (Rm m0) ^ 2,
        by positivity, ?_, ?_⟩
      · rw [hKpdef]
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        ring_nf
        nlinarith only [hμ2]
      · filter_upwards [hnormsq, hk₀] with x hx hxk
        refine ⟨?_, by nlinarith only [hx, hcase, hnR]⟩
        have h1 : cp * mu (Rm m0) ≤ |g x k₀| := hxk
        have h2 : |g x k₀| ≤ ‖g x‖ := hcoord (g x) k₀
        have h3 : (cp * mu (Rm m0)) ^ 2 ≤ ‖g x‖ ^ 2 := by
          have h4 : 0 ≤ cp * mu (Rm m0) := by
            have := hmu0 (Rm m0) (hRm0 m0) (hRmR m0)
            positivity
          nlinarith only [h1, h2, h4]
        nlinarith only [h3, hε]
  -- (B5) the weight, built from the continuous representative `g'`
  obtain ⟨wt, hwtdef⟩ : ∃ s : EuclideanSpace ℝ (Fin n) → ℝ,
      s = Set.piecewise (Metric.ball x₀ (Rm (m0 + 1)))
        (fun x => ε + ‖g' x‖ ^ 2) (fun _ => ε) := ⟨_, rfl⟩
  have hB1R0 : Metric.ball x₀ (Rm (m0 + 1)) ⊆ Metric.ball x₀ R₀ := hRmsub (m0 + 1)
  have hwtmeas : Measurable wt := by
    rw [hwtdef]
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const measurableSet_ball
    exact continuousOn_const.add (((hg'cont.mono hB1R0).norm).pow 2)
  have hwtae : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (Rm (m0 + 1)))),
      (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) = wt x ^ (p / 2 - 1) := by
    have hg'ae1 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (Rm (m0 + 1)))),
        g x = g' x := ae_restrict_of_ae_restrict_of_subset hB1R0 hg'ae
    filter_upwards [hg'ae1, ae_restrict_mem measurableSet_ball] with x hx hxB
    rw [hwtdef, Set.piecewise_eq_of_mem _ _ _ hxB, hx]
  have hpinchwt : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (Rm (m0 + 1)))),
      κ₁ ≤ wt x ∧ wt x ≤ κ₂ := by
    have hg'ae1 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (Rm (m0 + 1)))),
        g x = g' x := ae_restrict_of_ae_restrict_of_subset hB1R0 hg'ae
    filter_upwards [hpinch, hg'ae1, ae_restrict_mem measurableSet_ball]
      with x hx hgx hxB
    rw [hwtdef, Set.piecewise_eq_of_mem _ _ _ hxB, ← hgx]
    exact hx
  have hQ1 : EllipticStructureQ12 n p ε γ₀ γ₁ (Metric.ball x₀ (Rm (m0 + 1)))
      (fun _ _ h => A h) :=
    hQrestrict Ω₀ (Metric.ball x₀ (Rm (m0 + 1)))
      (subset_trans hB1R0 hballΩ) hQ
  -- THE HOIST: the (2.1) family on `𝓑`, once, for every component, level and
  -- pair of radii, consumed once per scale by (B6)
  have hDG : ∀ (kk : Fin n) (l ρ₀ ρ₁ : ℝ), 0 < ρ₀ → ρ₀ < ρ₁ → ρ₁ < Rm (m0 + 1) →
      DeGiorgiLevelBound n γs (fun x => g x kk) (Dg kk) x₀ l ρ₀ ρ₁ ∧
        DeGiorgiLevelBound n γs (fun x => -(g x kk)) (fun x => -(Dg kk x)) x₀ (-l)
          ρ₀ ρ₁ := by
    intro kk l ρ₀ ρ₁ hρ₀ hρ₀ρ₁ hρ₁
    have hbase := hPCLB x₀ (Rm (m0 + 1)) (mu (Rm (m0 + 1))) l κ₁ κ₂
      (fun x => g x kk) (Dg kk) wt hR10 hκ₁0 hκ₂K hwtmeas
      (hDgm (m0 + 1) kk) (hmubnd (Rm (m0 + 1)) hR10 hR1R kk) ρ₀ ρ₁ hρ₀ hρ₀ρ₁ hρ₁
    have hcaccz : ∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ Metric.ball x₀ (Rm (m0 + 1)) →
        ((∫ x in Metric.ball x₀ (Rm (m0 + 1)) ∩ {y | l < g y kk},
              wt x ^ (p / 2 - 1) * ‖Dg kk x‖ ^ 2 * ζ x ^ 2)
            ≤ c₄ * ∫ x in Metric.ball x₀ (Rm (m0 + 1)),
                wt x ^ (p / 2 - 1) * max (g x kk - l) 0 ^ 2
                  * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
          ∧ ((∫ x in Metric.ball x₀ (Rm (m0 + 1)) ∩ {y | g y kk < l},
              wt x ^ (p / 2 - 1) * ‖Dg kk x‖ ^ 2 * ζ x ^ 2)
            ≤ c₄ * ∫ x in Metric.ball x₀ (Rm (m0 + 1)),
                wt x ^ (p / 2 - 1) * max (l - g x kk) 0 ^ 2
                  * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2) := by
      intro ζ hζ1 hζ2 hζ3
      obtain ⟨hA, hBb⟩ :=
        hCLW ε γ₀ γ₁ (Metric.ball x₀ (Rm (m0 + 1))) A u g Dg ζ kk l
          hε hγ₀ hγ₁ Metric.isOpen_ball hQ1
          (hC1 ε γ₀ γ₁ (Metric.ball x₀ (Rm (m0 + 1))) A hγ₀ hγ₁0 Metric.isOpen_ball)
          (hsolBm (m0 + 1)) (hDgm (m0 + 1)) hζ1 hζ2 hζ3
      have hbig : (∫ x in Metric.ball x₀ (Rm (m0 + 1)),
            wt x ^ (p / 2 - 1) * max (g x kk - l) 0 ^ 2
              * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
          = ∫ x in Metric.ball x₀ (Rm (m0 + 1)),
            (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * max (g x kk - l) 0 ^ 2
              * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 := by
        refine integral_congr_ae ?_
        filter_upwards [hwtae] with x hx
        rw [hx]
      have hbig' : (∫ x in Metric.ball x₀ (Rm (m0 + 1)),
            wt x ^ (p / 2 - 1) * max (l - g x kk) 0 ^ 2
              * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
          = ∫ x in Metric.ball x₀ (Rm (m0 + 1)),
            (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * max (l - g x kk) 0 ^ 2
              * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 := by
        refine integral_congr_ae ?_
        filter_upwards [hwtae] with x hx
        rw [hx]
      refine ⟨?_, ?_⟩
      · have e1 : (∫ x in Metric.ball x₀ (Rm (m0 + 1)) ∩ {y | l < g y kk},
              wt x ^ (p / 2 - 1) * ‖Dg kk x‖ ^ 2 * ζ x ^ 2)
            = ∫ x in Metric.ball x₀ (Rm (m0 + 1)) ∩ {y | l < g y kk},
              (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg kk x‖ ^ 2 * ζ x ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards
            [ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hwtae] with x hx
          rw [hx]
        rw [e1, hbig]
        exact hA
      · have e2 : (∫ x in Metric.ball x₀ (Rm (m0 + 1)) ∩ {y | g y kk < l},
              wt x ^ (p / 2 - 1) * ‖Dg kk x‖ ^ 2 * ζ x ^ 2)
            = ∫ x in Metric.ball x₀ (Rm (m0 + 1)) ∩ {y | g y kk < l},
              (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg kk x‖ ^ 2 * ζ x ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards
            [ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hwtae] with x hx
          rw [hx]
        rw [e2, hbig']
        exact hBb
    exact ⟨hbase.1
        (ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hpinchwt)
        (fun ζ h1 h2 h3 => (hcaccz ζ h1 h2 h3).1),
      hbase.2
        (ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hpinchwt)
        (fun ζ h1 h2 h3 => (hcaccz ζ h1 h2 h3).2)⟩
  -- (O) the oscillation is monotone in the ball
  have hoscmono : ∀ (σ σ' : ℝ) (kk : Fin n), 0 < σ → σ ≤ σ' → σ' ≤ R₀ →
      EssOscOn n (Metric.ball x₀ σ) (fun x => g x kk)
        ≤ EssOscOn n (Metric.ball x₀ σ') (fun x => g x kk) := by
    intro σ σ' kk hσ hσσ' hσ'R
    have hσ'0 : 0 < σ' := lt_of_lt_of_le hσ hσσ'
    have hsub : Metric.ball x₀ σ ⊆ Metric.ball x₀ σ' := Metric.ball_subset_ball hσσ'
    have hNB := hNBball σ hσ
    have hb' := hmubnd σ' hσ'0 hσ'R kk
    have hhi' : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ σ')), g x kk ≤ mu σ' := by
      filter_upwards [hb'] with x hx
      exact le_trans (le_abs_self _) hx
    have hlo' : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ σ')), -(mu σ') ≤ g x kk := by
      filter_upwards [hb'] with x hx
      have h1 := neg_abs_le (g x kk)
      linarith
    have hS' : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ σ')),
        g x kk ≤ essSup (fun y => g y kk) (volume.restrict (Metric.ball x₀ σ')) :=
      ae_le_essSup ⟨mu σ', by rw [Filter.eventually_map]; exact hhi'⟩
    have hI' : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ σ')),
        essInf (fun y => g y kk) (volume.restrict (Metric.ball x₀ σ')) ≤ g x kk :=
      ae_essInf_le ⟨-(mu σ'), by rw [Filter.eventually_map]; exact hlo'⟩
    have hsuple : essSup (fun y => g y kk) (volume.restrict (Metric.ball x₀ σ))
        ≤ essSup (fun y => g y kk) (volume.restrict (Metric.ball x₀ σ')) :=
      essSup_le_of_ae_le _ (ae_restrict_of_ae_restrict_of_subset hsub hS')
        (hcobdd hNB (ae_restrict_of_ae_restrict_of_subset hsub hlo'))
    have hinfle : essInf (fun y => g y kk) (volume.restrict (Metric.ball x₀ σ'))
        ≤ essInf (fun y => g y kk) (volume.restrict (Metric.ball x₀ σ)) :=
      le_essInf_of_ae_le _ (ae_restrict_of_ae_restrict_of_subset hsub hI')
        (hcobddge hNB (ae_restrict_of_ae_restrict_of_subset hsub hhi'))
    rw [EssOscOn, EssOscOn]
    linarith
  -- the dyadic radii are antitone
  have hRmanti : ∀ a b : ℕ, a ≤ b → Rm b ≤ Rm a := by
    intro a b hab
    simp only [hRmdef]
    have h1 : (0:ℝ) < 2 ^ a := by positivity
    have h2 : (2:ℝ) ^ a ≤ 2 ^ b := by
      exact pow_le_pow_right₀ (by norm_num) hab
    rw [div_le_div_iff₀ (by positivity) h1]
    nlinarith only [h2, hR₀]
  -- (3.28)/(B.2): the geometric bound on `μ` for radii at or above `R_{m₀}`
  have hrange1 : ∀ ρ' : ℝ, Rm m0 ≤ ρ' → ρ' ≤ R₀ →
      mu ρ' ≤ 2 * (ρ' / R₀) ^ α * mu R₀ := by
    intro ρ' h1 h2
    have hρ'0 : 0 < ρ' := lt_of_lt_of_le (hRm0 m0) h1
    obtain ⟨m, hm1, hm2⟩ := hradius ρ' hρ'0 h2
    have hmle : m ≤ m0 := by
      by_contra hc
      have hc' : m0 + 1 ≤ m := by omega
      have h3 : Rm m ≤ Rm (m0 + 1) := hRmanti (m0 + 1) m hc'
      have h4 : Rm (m0 + 1) = Rm m0 / 2 := hRmsucc m0
      linarith [hRm0 m0]
    exact hdecay m ρ' hρ'0 h2 hm1 hm2
      (hchainmu m (fun j hj => hbelow j (lt_of_lt_of_le hj hmle)))
  -- (B6)/(3.27): the oscillation decays by `δ` at every scale past `m₀`
  have hstep327 : ∀ (m : ℕ) (kk : Fin n), m0 + 1 ≤ m →
      EssOscOn n (Metric.ball x₀ (Rm (m + 1))) (fun x => g x kk)
        ≤ δ * EssOscOn n (Metric.ball x₀ (Rm m)) (fun x => g x kk) := by
    intro m kk hm
    obtain ⟨Tm, hTmdef⟩ : ∃ s : ℝ, s = 3 / 4 * Rm m := ⟨_, rfl⟩
    have hTm0 : 0 < Tm := by rw [hTmdef]; linarith [hRm0 m]
    have hTmRm : Tm < Rm m := by rw [hTmdef]; linarith [hRm0 m]
    have hTmR0 : Tm ≤ R₀ := le_trans hTmRm.le (hRmR m)
    have hTmR1 : Tm < Rm (m0 + 1) := lt_of_lt_of_le hTmRm (hRmanti (m0 + 1) m hm)
    have hhalfT : 2 / 3 * Tm = Rm (m + 1) := by
      rw [hTmdef, hRmsucc m]; ring
    have hmem : MemW1pOn n 2 (Metric.ball x₀ Tm) (fun x => g x kk) (Dg kk) := by
      refine (WeakGradientRestrict n 2 hn1 (by norm_num) (Metric.ball x₀ R₀)
        (Metric.ball x₀ Tm) (fun x => g x kk) (Dg kk) Metric.isOpen_ball
        Metric.isOpen_ball (Metric.ball_subset_ball hTmR0)).2.2.2 (hDg kk) ?_ ?_
      · exact IsCompact.of_isClosed_subset (isCompact_closedBall x₀ Tm)
          isClosed_closure Metric.closure_ball_subset_closedBall
      · exact subset_trans Metric.closure_ball_subset_closedBall
          (Metric.closedBall_subset_ball (lt_of_lt_of_le hTmRm (hRmR m)))
    have hT23 : (0:ℝ) < 2 / 3 * Tm := by linarith
    have hconc := hODL x₀ Tm
      (essInf (fun x => g x kk) (volume.restrict (Metric.ball x₀ Tm)))
      (essSup (fun x => g x kk) (volume.restrict (Metric.ball x₀ Tm)))
      (fun x => g x kk) (Dg kk) hTm0 hmem ⟨T, hgTk Tm hTmR0 kk⟩ rfl rfl
      (fun l ρ₀ ρ₁ _ hρ₀ hρ₁ hlt =>
        (hDG kk l ρ₀ ρ₁ (lt_of_lt_of_le hT23 hρ₀.1) hlt
          (lt_of_le_of_lt hρ₁.2 hTmR1)).1)
      (fun l ρ₀ ρ₁ _ hρ₀ hρ₁ hlt =>
        (hDG kk l ρ₀ ρ₁ (lt_of_lt_of_le hT23 hρ₀.1) hlt
          (lt_of_le_of_lt hρ₁.2 hTmR1)).2)
    rw [hhalfT] at hconc
    have hmono := hoscmono Tm (Rm m) kk hTm0 hTmRm.le (hRmR m)
    have hδ0 : (0:ℝ) ≤ δ := hδ.1.le
    calc EssOscOn n (Metric.ball x₀ (Rm (m + 1))) (fun x => g x kk)
        ≤ δ * EssOscOn n (Metric.ball x₀ Tm) (fun x => g x kk) := hconc
      _ ≤ δ * EssOscOn n (Metric.ball x₀ (Rm m)) (fun x => g x kk) :=
          mul_le_mul_of_nonneg_left hmono hδ0
  -- the oscillation is nonnegative
  have hosc0 : ∀ (σ : ℝ) (kk : Fin n), 0 < σ → σ ≤ R₀ →
      0 ≤ EssOscOn n (Metric.ball x₀ σ) (fun x => g x kk) := by
    intro σ kk hσ hσR
    have hNB := hNBball σ hσ
    have hb := hmubnd σ hσ hσR kk
    have hhi : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ σ)), g x kk ≤ mu σ := by
      filter_upwards [hb] with x hx
      exact le_trans (le_abs_self _) hx
    have hlo : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ σ)), -(mu σ) ≤ g x kk := by
      filter_upwards [hb] with x hx
      have h1 := neg_abs_le (g x kk)
      linarith
    have hS : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ σ)),
        g x kk ≤ essSup (fun y => g y kk) (volume.restrict (Metric.ball x₀ σ)) :=
      ae_le_essSup ⟨mu σ, by rw [Filter.eventually_map]; exact hhi⟩
    have hI : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ σ)),
        essInf (fun y => g y kk) (volume.restrict (Metric.ball x₀ σ)) ≤ g x kk :=
      ae_essInf_le ⟨-(mu σ), by rw [Filter.eventually_map]; exact hlo⟩
    obtain ⟨x, hx1, hx2⟩ := (hS.and hI).exists
    rw [EssOscOn]
    linarith
  -- (B7) the assembly, in three ranges of `ρ`
  have hmuR0T : mu R₀ ≤ T := hmuT R₀ hR₀ le_rfl
  have hmuR00 : 0 ≤ mu R₀ := hmu0 R₀ hR₀ le_rfl
  have hdR0 : (0:ℝ) < ρ / R₀ := div_pos hρ hR₀
  have hpowρ : (0:ℝ) ≤ (ρ / R₀) ^ α := Real.rpow_nonneg hdR0.le _
  have htwoα : (2:ℝ) ^ α ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hα1
    rwa [Real.rpow_one] at h
  rcases le_or_gt (Rm m0) ρ with hr1 | hr1
  · -- range (i): `R_{m₀} ≤ ρ ≤ R₀`
    exact hconclude (hrange1 ρ hr1 hρR)
  rcases le_or_gt (Rm (m0 + 1)) ρ with hr2 | hr2
  · -- range (ii): `R_{m₀+1} ≤ ρ < R_{m₀}`
    have h1 : EssOscOn n (Metric.ball x₀ ρ) (fun x => g x k)
        ≤ EssOscOn n (Metric.ball x₀ (Rm m0)) (fun x => g x k) :=
      hoscmono ρ (Rm m0) k hρ hr1.le (hRmR m0)
    have h2 : EssOscOn n (Metric.ball x₀ (Rm m0)) (fun x => g x k)
        ≤ 2 * mu (Rm m0) := hoscmu (Rm m0) (hRm0 m0) (hRmR m0) k
    have h3 : mu (Rm m0) ≤ 2 * (Rm m0 / R₀) ^ α * mu R₀ :=
      hrange1 (Rm m0) le_rfl (hRmR m0)
    have hpow0 : (0:ℝ) ≤ (Rm m0 / R₀) ^ α :=
      Real.rpow_nonneg (le_of_lt (div_pos (hRm0 m0) hR₀)) _
    have h4 : Rm m0 / R₀ ≤ 2 * (ρ / R₀) := by
      have h5 : Rm m0 = 2 * Rm (m0 + 1) := by rw [hRmsucc m0]; ring
      rw [h5, div_le_iff₀ hR₀]
      have h6 : 2 * (ρ / R₀) * R₀ = 2 * ρ := by field_simp
      rw [h6]
      linarith
    have h7 : (Rm m0 / R₀) ^ α ≤ 2 * (ρ / R₀) ^ α := by
      have h8 : (Rm m0 / R₀) ^ α ≤ (2 * (ρ / R₀)) ^ α :=
        Real.rpow_le_rpow (le_of_lt (div_pos (hRm0 m0) hR₀)) h4 hα0.le
      rw [Real.mul_rpow (by norm_num) hdR0.le] at h8
      nlinarith only [h8, htwoα, hpowρ]
    have hprod1 : (Rm m0 / R₀) ^ α * mu R₀ ≤ 2 * (ρ / R₀) ^ α * mu R₀ :=
      mul_le_mul_of_nonneg_right h7 hmuR00
    have hprod2 : (0:ℝ) ≤ (ρ / R₀) ^ α * (T - mu R₀) :=
      mul_nonneg hpowρ (by linarith)
    have hprod3 : (0:ℝ) ≤ (ρ / R₀) ^ α * T := mul_nonneg hpowρ hT0
    linarith only [h1, h2, h3, hprod1, hprod2, hprod3]
  · -- range (iii): `0 < ρ < R_{m₀+1}`
    obtain ⟨m, hm1, hm2⟩ := hradius ρ hρ hρR
    have hmge : m0 + 1 ≤ m := by
      by_contra hc
      have hc' : m + 1 ≤ m0 + 1 := by omega
      have h1 : Rm (m0 + 1) ≤ Rm (m + 1) := hRmanti (m + 1) (m0 + 1) hc'
      linarith [hm1, hr2]
    obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = m - (m0 + 1) := ⟨_, rfl⟩
    have hmj : m0 + 1 + j = m := by rw [hjdef]; omega
    -- iterate (3.27) from `m₀+1` to `m`
    have hiter : ∀ i : ℕ,
        EssOscOn n (Metric.ball x₀ (Rm (m0 + 1 + i))) (fun x => g x k)
          ≤ δ ^ i * EssOscOn n (Metric.ball x₀ (Rm (m0 + 1))) (fun x => g x k) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have h1 : m0 + 1 ≤ m0 + 1 + i := by omega
        have h2 := hstep327 (m0 + 1 + i) k h1
        have h3 : m0 + 1 + (i + 1) = (m0 + 1 + i) + 1 := by omega
        rw [h3]
        calc EssOscOn n (Metric.ball x₀ (Rm (m0 + 1 + i + 1))) (fun x => g x k)
            ≤ δ * EssOscOn n (Metric.ball x₀ (Rm (m0 + 1 + i))) (fun x => g x k) := h2
          _ ≤ δ * (δ ^ i
              * EssOscOn n (Metric.ball x₀ (Rm (m0 + 1))) (fun x => g x k)) :=
              mul_le_mul_of_nonneg_left ih hδ.1.le
          _ = δ ^ (i + 1)
              * EssOscOn n (Metric.ball x₀ (Rm (m0 + 1))) (fun x => g x k) := by ring
    -- `δ^j ≤ 4 (ρ/R_{m₀})^α`
    have h2m : (2:ℝ) ^ m = 2 ^ (m0 + 1) * 2 ^ j := by rw [← hmj, pow_add]
    have hratio2 : Rm m / Rm (m0 + 1) = ((2:ℝ) ^ j)⁻¹ := by
      simp only [hRmdef]
      rw [h2m]
      field_simp
    have hA2 : δ ^ j ≤ (2:ℝ) ^ (-(α₂ * j)) := by
      have h1 : δ ^ j ≤ ((2:ℝ) ^ (-α₂)) ^ j := pow_le_pow_left₀ hδ.1.le hδα₂ j
      have h2 : ((2:ℝ) ^ (-α₂)) ^ j = (2:ℝ) ^ (-(α₂ * j)) := by
        rw [← Real.rpow_natCast ((2:ℝ) ^ (-α₂)) j, ← Real.rpow_mul (by norm_num)]
        congr 1
        ring
      linarith [h1, h2.le, h2.ge]
    have hB2 : (2:ℝ) ^ (-(α₂ * j)) = (Rm m / Rm (m0 + 1)) ^ α₂ := by
      rw [hratio2, show ((2:ℝ) ^ j)⁻¹ = (2:ℝ) ^ (-(j:ℝ)) by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast],
        ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    have hd1 : (0:ℝ) < ρ / Rm (m0 + 1) := div_pos hρ hR10
    have hd2 : ρ / Rm (m0 + 1) ≤ 1 := by rw [div_le_one hR10]; linarith [hr2]
    have hdm0 : (0:ℝ) < ρ / Rm m0 := div_pos hρ (hRm0 m0)
    have hC2 : (Rm m / Rm (m0 + 1)) ^ α₂ ≤ (2 * (ρ / Rm (m0 + 1))) ^ α₂ := by
      refine Real.rpow_le_rpow (le_of_lt (div_pos (hRm0 m) hR10)) ?_ hα₂0.le
      rw [div_le_iff₀ hR10]
      have h5 : Rm m = 2 * Rm (m + 1) := by rw [hRmsucc m]; ring
      have h6 : 2 * (ρ / Rm (m0 + 1)) * Rm (m0 + 1) = 2 * ρ := by field_simp
      rw [h5, h6]
      linarith [hm1]
    have hE2 : (2:ℝ) ^ α₂ ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hα₂1
      rwa [Real.rpow_one] at h
    have hF2 : (ρ / Rm (m0 + 1)) ^ α₂ ≤ (ρ / Rm (m0 + 1)) ^ α :=
      Real.rpow_le_rpow_of_exponent_ge hd1 hd2 hαα₂
    have hG2 : ρ / Rm (m0 + 1) = 2 * (ρ / Rm m0) := by
      rw [hRmsucc m0]; field_simp
    have hpowm0 : (0:ℝ) ≤ (ρ / Rm m0) ^ α := Real.rpow_nonneg hdm0.le _
    have hH2 : (ρ / Rm (m0 + 1)) ^ α ≤ 2 * (ρ / Rm m0) ^ α := by
      rw [hG2, Real.mul_rpow (by norm_num) hdm0.le]
      nlinarith only [htwoα, hpowm0]
    have hpa2 : (0:ℝ) ≤ (ρ / Rm (m0 + 1)) ^ α₂ := Real.rpow_nonneg hd1.le _
    have hδj : δ ^ j ≤ 4 * (ρ / Rm m0) ^ α :=
      calc δ ^ j ≤ (2:ℝ) ^ (-(α₂ * j)) := hA2
        _ = (Rm m / Rm (m0 + 1)) ^ α₂ := hB2
        _ ≤ (2 * (ρ / Rm (m0 + 1))) ^ α₂ := hC2
        _ = (2:ℝ) ^ α₂ * (ρ / Rm (m0 + 1)) ^ α₂ :=
            Real.mul_rpow (by norm_num) hd1.le
        _ ≤ 2 * (ρ / Rm (m0 + 1)) ^ α₂ := mul_le_mul_of_nonneg_right hE2 hpa2
        _ ≤ 2 * (ρ / Rm (m0 + 1)) ^ α := by linarith only [hF2]
        _ ≤ 2 * (2 * (ρ / Rm m0) ^ α) := by linarith only [hH2]
        _ = 4 * (ρ / Rm m0) ^ α := by ring
    -- the oscillation at the pivot scale
    have hoscB1 : EssOscOn n (Metric.ball x₀ (Rm (m0 + 1))) (fun x => g x k)
        ≤ 4 * (Rm m0 / R₀) ^ α * mu R₀ := by
      have t1 := hoscmu (Rm (m0 + 1)) hR10 hR1R k
      have t2 : mu (Rm (m0 + 1)) ≤ mu (Rm m0) :=
        hmumono (Rm (m0 + 1)) (Rm m0) hR10 (hRmanti m0 (m0 + 1) (by omega))
          (hRmR m0)
      have t3 : mu (Rm m0) ≤ 2 * (Rm m0 / R₀) ^ α * mu R₀ :=
        hrange1 (Rm m0) le_rfl (hRmR m0)
      linarith
    have hprodid : (ρ / Rm m0) ^ α * (Rm m0 / R₀) ^ α = (ρ / R₀) ^ α := by
      rw [← Real.mul_rpow hdm0.le (le_of_lt (div_pos (hRm0 m0) hR₀))]
      congr 1
      have hne1 : Rm m0 ≠ 0 := ne_of_gt (hRm0 m0)
      have hne2 : R₀ ≠ 0 := ne_of_gt hR₀
      field_simp
    have hstep1 : EssOscOn n (Metric.ball x₀ ρ) (fun x => g x k)
        ≤ δ ^ j * EssOscOn n (Metric.ball x₀ (Rm (m0 + 1))) (fun x => g x k) := by
      have t1 : EssOscOn n (Metric.ball x₀ ρ) (fun x => g x k)
          ≤ EssOscOn n (Metric.ball x₀ (Rm m)) (fun x => g x k) :=
        hoscmono ρ (Rm m) k hρ hm2 (hRmR m)
      have t2 := hiter j
      rw [hmj] at t2
      linarith
    have hoscB10 : (0:ℝ)
        ≤ EssOscOn n (Metric.ball x₀ (Rm (m0 + 1))) (fun x => g x k) :=
      hosc0 (Rm (m0 + 1)) k hR10 hR1R
    have hstep2 : δ ^ j * EssOscOn n (Metric.ball x₀ (Rm (m0 + 1))) (fun x => g x k)
        ≤ (4 * (ρ / Rm m0) ^ α) * (4 * (Rm m0 / R₀) ^ α * mu R₀) :=
      mul_le_mul hδj hoscB1 hoscB10 (by linarith only [hpowm0])
    have hstep3 : (4 * (ρ / Rm m0) ^ α) * (4 * (Rm m0 / R₀) ^ α * mu R₀)
        = 16 * ((ρ / R₀) ^ α * mu R₀) := by
      rw [← hprodid]; ring
    have hprod2 : (0:ℝ) ≤ (ρ / R₀) ^ α * (T - mu R₀) :=
      mul_nonneg hpowρ (by linarith)
    have hprod3 : (0:ℝ) ≤ (ρ / R₀) ^ α * T := mul_nonneg hpowρ hT0
    linarith only [hstep1, hstep2, hstep3.le, hstep3.ge, hprod2, hprod3]
