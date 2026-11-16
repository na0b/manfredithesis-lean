import ManfrediThesis.Preamble
import ManfrediThesis.OscillationDecayFirstGoodScale
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.IsWeakSolutionRestrict
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.EssOscOn
import ManfrediThesis.DeGiorgiLevelBound
import ManfrediThesis.WeakGradientRestrict
import ManfrediThesis.WeakGradientLinear
import ManfrediThesis.WeakGradientPositivePart
import ManfrediThesis.AEModificationInvariance
import ManfrediThesis.CaccioppoliLevelWeight
import ManfrediThesis.PinchedCaccioppoliLevelBound
import ManfrediThesis.DegenerateAlternative
import ManfrediThesis.OscillationDecayLemma
import ManfrediThesis.CitedRegularityEpsPos
open MeasureTheory

/-- The oscillation decay estimate of Theorem 2 in the nondegenerate case
`ε > 0`: each partial derivative of a solution of (3.1) has oscillation at most
`16 T (ρ/R)^α` on `B_ρ`, where `T` is any essential bound for `‖g‖` on `B_R`.
The hypothesis is the *open* ball `B_R ⊆ Ω`, which is what lets the consumer
apply the lemma with `Ω` itself a ball. -/
theorem GradientOscillationEstimateEpsPos :
    ∀ (n : ℕ) (p r : ℝ), 2 ≤ n → 1 < p → 0 < r →
      CitedSobolevPoincareBall n →
      (∀ (ε' γ₀' γ₁' : ℝ) (Ω' : Set (EuclideanSpace ℝ (Fin n)))
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → IsOpen Ω' → CitedRegularityEpsPos n p ε' γ₀' γ₁' Ω' A') →
      ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
        ∀ (ε γ₀ γ₁ T : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
          (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (x₀ : EuclideanSpace ℝ (Fin n)) (R ρ : ℝ) (k : Fin n),
          0 < ε → 0 < γ₀ → γ₁ ≤ r * γ₀ → 0 ≤ T → IsOpen Ω → 0 < R → 0 < ρ → ρ ≤ R →
          EllipticStructureQ12 n p ε γ₀ γ₁ Ω (fun _ _ h => A h) →
          IsWeakSolutionOn n p Ω (fun _ _ h => A h) (fun _ _ _ => 0) u g →
          Metric.ball x₀ R ⊆ Ω →
          (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), ‖g x‖ ≤ T) →
          EssOscOn n (Metric.ball x₀ ρ) (fun x => g x k) ≤ 16 * T * (ρ / R) ^ α := by
  intro n p r hn hp hr hSP hC1
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp
  have hp1 : (1:ℝ) ≤ p := le_of_lt hp
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the dyadic-exponent gadget: a contraction factor `t < 1` is `2^{-a}` for
  -- some `a ∈ (0,1]`.  Used once for `ν` in (S1) and once for `δ` in (S3).
  have hexp : ∀ t : ℝ, 0 < t → t < 1 →
      ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ t ≤ (2:ℝ) ^ (-a) := by
    intro t ht0 ht1
    obtain ⟨a, hadef⟩ : ∃ s : ℝ, s = min (Real.log (1 / t) / Real.log 2) 1 := ⟨_, rfl⟩
    have hlt : 1 < 1 / t := by rw [lt_div_iff₀ ht0]; linarith
    have hlogt : 0 < Real.log (1 / t) := Real.log_pos hlt
    refine ⟨a, ?_, ?_, ?_⟩
    · rw [hadef]; exact lt_min (div_pos hlogt hlog2) zero_lt_one
    · rw [hadef]; exact min_le_right _ _
    · have hale : a ≤ Real.log (1 / t) / Real.log 2 := by
        rw [hadef]; exact min_le_left _ _
      have h3 : a * Real.log 2 ≤ Real.log (1 / t) := by
        rw [← le_div_iff₀ hlog2]; exact hale
      have hpw : (0:ℝ) < (2:ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) _
      have h4 : (2:ℝ) ^ a ≤ 1 / t := by
        rw [← Real.log_le_log_iff hpw (by positivity), Real.log_rpow (by norm_num)]
        exact h3
      have h4' : (2:ℝ) ^ a * t ≤ 1 := (le_div_iff₀ ht0).1 h4
      rw [Real.rpow_neg (by norm_num), inv_eq_one_div, le_div_iff₀ hpw]
      linarith only [h4']
  -- (S1) the degenerate alternative and the exponent `α₁`
  obtain ⟨θ₂, ν, hθ₂, hν, hDA⟩ := DegenerateAlternative n p r hn hp hr hSP
  obtain ⟨α₁, hα₁0, hα₁1, hνα₁⟩ := hexp ν hν.1 hν.2
  -- (S2) the Caccioppoli constant, the pinch ratio and `γ♯`
  obtain ⟨c₄, hc₄0, hCLW⟩ := CaccioppoliLevelWeight n p r hn hp hr
  obtain ⟨cp, hcpdef⟩ : ∃ s : ℝ, s = min (1 / 16) ((2:ℝ) ^ (-1 - 4 / p)) := ⟨_, rfl⟩
  have hcp0 : 0 < cp := by
    rw [hcpdef]
    exact lt_min (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
  have hcp16 : cp ≤ 1 / 16 := by rw [hcpdef]; exact min_le_left _ _
  obtain ⟨Kp, hKpdef⟩ : ∃ s : ℝ, s = (1 / 4 + (n:ℝ)) / cp ^ 2 := ⟨_, rfl⟩
  have hKp1 : (1:ℝ) ≤ Kp := by
    rw [hKpdef, le_div_iff₀ (by positivity)]
    nlinarith only [hcp16, hcp0, hnR]
  obtain ⟨γs, hγs0, hPCLB⟩ :=
    PinchedCaccioppoliLevelBound n (p / 2 - 1) Kp c₄ hn1 hKp1 hc₄0
  -- (S3) the oscillation decay constant and the exponent `α`
  obtain ⟨δ, hδ, hODL⟩ :=
    OscillationDecayLemma n γs (2 / 3) hn hγs0 ⟨by norm_num, by norm_num⟩ hSP
  obtain ⟨α₂, hα₂0, hα₂1, hδα₂⟩ := hexp δ hδ.1 hδ.2
  obtain ⟨α, hαdef⟩ : ∃ s : ℝ, s = min α₁ α₂ := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hαdef]; exact lt_min hα₁0 hα₂0
  have hαα₁ : α ≤ α₁ := by rw [hαdef]; exact min_le_left _ _
  have hαα₂ : α ≤ α₂ := by rw [hαdef]; exact min_le_right _ _
  have hα1 : α ≤ 1 := le_trans hαα₁ hα₁1
  refine ⟨α, hα0, hα1, ?_⟩
  intro ε γ₀ γ₁ T Ω₀ A u g x₀ R₀ ρ k hε hγ₀ hγ₁ hT0 hΩ₀ hR₀ hρ hρR hQ hsol
    hballΩ hgT
  -- generic measure-theoretic toolkit
  have hNBball : ∀ σ : ℝ, 0 < σ → (ae (volume.restrict (Metric.ball x₀ σ))).NeBot := by
    intro σ hσ
    refine ⟨fun hb => ?_⟩
    rw [ae_eq_bot] at hb
    have h1 : volume (Metric.ball x₀ σ) = 0 := by
      simpa using congrArg (fun m => m (Metric.ball x₀ σ)) hb
    exact (Metric.measure_ball_pos volume x₀ hσ).ne' h1
  have hcobdd : ∀ {μm : Measure (EuclideanSpace ℝ (Fin n))}
      {v : EuclideanSpace ℝ (Fin n) → ℝ} {b : ℝ}, (ae μm).NeBot →
      (∀ᵐ x ∂μm, b ≤ v x) → Filter.IsCoboundedUnder (· ≤ ·) (ae μm) v := by
    intro μm v b hb hlo
    have hb' := hb
    refine ⟨b, fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨x, hax, hxb⟩ := (ha.and hlo).exists
    linarith
  have hcobddge : ∀ {μm : Measure (EuclideanSpace ℝ (Fin n))}
      {v : EuclideanSpace ℝ (Fin n) → ℝ} {b : ℝ}, (ae μm).NeBot →
      (∀ᵐ x ∂μm, v x ≤ b) → Filter.IsCoboundedUnder (· ≥ ·) (ae μm) v := by
    intro μm v b hb hhi
    have hb' := hb
    refine ⟨b, fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨x, hax, hxb⟩ := (ha.and hhi).exists
    linarith
  have hcoord : ∀ (v : EuclideanSpace ℝ (Fin n)) (i : Fin n), |v i| ≤ ‖v‖ := by
    intro v i
    have h1 : (v i) ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (f := fun m => (v m) ^ 2)
        (fun m _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith [abs_nonneg (v i), norm_nonneg v, sq_abs (v i)]
  -- the structure conditions restrict to any subset
  have hQrestrict : ∀ (s t : Set (EuclideanSpace ℝ (Fin n))), t ⊆ s →
      EllipticStructureQ12 n p ε γ₀ γ₁ s (fun _ _ h => A h) →
      EllipticStructureQ12 n p ε γ₀ γ₁ t (fun _ _ h => A h) := by
    intro s t hst hQs
    refine ⟨hQs.meas_x, hQs.cont_zh, fun x hx z => hQs.hcont x (hst hx) z,
      fun x hx z => hQs.hdiff x (hst hx) z, ?_, ?_⟩
    · filter_upwards [hQs.Q1] with x hx hxt
      exact hx (hst hxt)
    · filter_upwards [hQs.Q2] with x hx hxt
      exact hx (hst hxt)
  -- (S0) at the lemma's own data: the second structure constant is positive
  have hγ₁0 : 0 < γ₁ := by
    have hΩne : volume Ω₀ ≠ 0 := fun hc =>
      (Metric.measure_ball_pos volume x₀ hR₀).ne' (measure_mono_null hballΩ hc)
    have hNBΩ : (ae (volume.restrict Ω₀)).NeBot := by
      refine ⟨fun hb => ?_⟩
      rw [ae_eq_bot] at hb
      exact hΩne (by simpa using congrArg (fun m => m Ω₀) hb)
    obtain ⟨x, ⟨hxQ1, hxQ2⟩, hxΩ⟩ :=
      (((ae_restrict_of_ae hQ.Q1).and (ae_restrict_of_ae hQ.Q2)).and
        (ae_restrict_mem hΩ₀.measurableSet)).exists
    obtain ⟨i₀, hi₀⟩ : ∃ i : Fin n, True := ⟨⟨0, hnpos⟩, trivial⟩
    have hns : ‖(EuclideanSpace.single i₀ (1:ℝ))‖ = 1 := by
      rw [PiLp.norm_single]
      norm_num
    have hside : ε + ‖(EuclideanSpace.single i₀ (1:ℝ))‖ ^ 2 ≠ 0 := by
      rw [hns]; positivity
    have h1 := hxQ1 hxΩ 0 (EuclideanSpace.single i₀ (1:ℝ))
      (EuclideanSpace.single i₀ (1:ℝ)) hside
    have h2 := hxQ2 hxΩ 0 (EuclideanSpace.single i₀ (1:ℝ)) i₀ i₀ hside
    have hsum1 : ∀ v : EuclideanSpace ℝ (Fin n),
        ∑ i, v i * (EuclideanSpace.single i₀ (1:ℝ)) i = v i₀ := by
      intro v
      rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ _)]
      · simp
      · intro b _ hb
        simp [hb]
    rw [hns, hsum1] at h1
    rw [hns] at h2
    have hwpos : (0:ℝ) < (ε + 1 ^ 2) ^ (p / 2 - 1) := by
      refine Real.rpow_pos_of_pos ?_ _
      norm_num
      linarith
    have h3 := le_trans (le_abs_self _) h2
    have h4 : γ₀ * (ε + 1 ^ 2) ^ (p / 2 - 1) * 1 ^ 2
        ≤ γ₁ * (ε + 1 ^ 2) ^ (p / 2 - 1) := le_trans h1 h3
    nlinarith only [h4, hwpos, hγ₀]
  -- (B0r) the weak-solution property on the ball
  have hsolB : IsWeakSolutionOn n p (Metric.ball x₀ R₀) (fun _ _ h => A h)
      (fun _ _ _ => 0) u g :=
    IsWeakSolutionRestrict n p hn1 hp1 Ω₀ x₀ R₀ (fun _ _ h => A h)
      (fun _ _ _ => 0) u g hΩ₀ hR₀ hballΩ hsol
  have hQB : EllipticStructureQ12 n p ε γ₀ γ₁ (Metric.ball x₀ R₀)
      (fun _ _ h => A h) := hQrestrict Ω₀ (Metric.ball x₀ R₀) hballΩ hQ
  -- (B0) the second weak derivatives supplied by the cited regularity result
  obtain ⟨-, g', hg'cont, hg'ae, Dg, hDg'⟩ :=
    (hC1 ε γ₀ γ₁ (Metric.ball x₀ R₀) A hγ₀ hγ₁0 Metric.isOpen_ball) hε hQB u g hsolB
  have hDg : ∀ i : Fin n,
      MemW1pLocOn n 2 (Metric.ball x₀ R₀) (fun x => g x i) (Dg i) := by
    intro i
    refine (AEModificationInvariance n 2 hn1 (by norm_num) (Metric.ball x₀ R₀)
      (fun x => g' x i) (fun x => g x i) (Dg i) Metric.isOpen_ball ?_).2.2.1 (hDg' i)
    filter_upwards [hg'ae] with x hx
    rw [hx]
  -- the maximal partial derivative `μ(σ)` and its four properties
  have hFne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hnpos⟩, Finset.mem_univ _⟩
  obtain ⟨mu, hmudef⟩ : ∃ s : ℝ → ℝ, s = fun σ =>
      Finset.univ.sup' hFne
        (fun k => essSup (fun x => |g x k|)
          (volume.restrict (Metric.ball x₀ σ))) := ⟨_, rfl⟩
  have hgTk : ∀ σ : ℝ, σ ≤ R₀ → ∀ k : Fin n,
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ σ)), |g x k| ≤ T := by
    intro σ hσ k
    have hsub : Metric.ball x₀ σ ⊆ Metric.ball x₀ R₀ := Metric.ball_subset_ball hσ
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hgT] with x hx
    exact le_trans (hcoord (g x) k) hx
  have hmubnd : ∀ σ : ℝ, 0 < σ → σ ≤ R₀ → ∀ k : Fin n,
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ σ)), |g x k| ≤ mu σ := by
    intro σ hσ hσR k
    have hNB := hNBball σ hσ
    have hle : essSup (fun x => |g x k|)
        (volume.restrict (Metric.ball x₀ σ)) ≤ mu σ := by
      simp only [hmudef]
      exact Finset.le_sup'
        (fun j : Fin n => essSup (fun x => |g x j|)
          (volume.restrict (Metric.ball x₀ σ))) (Finset.mem_univ k)
    have hae : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ σ)),
        |g x k| ≤ essSup (fun y => |g y k|)
          (volume.restrict (Metric.ball x₀ σ)) := by
      refine ae_le_essSup ⟨T, ?_⟩
      rw [Filter.eventually_map]
      exact hgTk σ hσR k
    filter_upwards [hae] with x hx
    linarith
  have hmumin : ∀ σ : ℝ, 0 < σ → ∀ c : ℝ,
      (∀ k : Fin n, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ σ)), |g x k| ≤ c) →
      mu σ ≤ c := by
    intro σ hσ c hc
    have hNB := hNBball σ hσ
    simp only [hmudef]
    refine Finset.sup'_le hFne _ (fun k _ => ?_)
    exact essSup_le_of_ae_le c (hc k)
      (hcobdd hNB (Filter.Eventually.of_forall (fun x => abs_nonneg _)))
  have hmu0 : ∀ σ : ℝ, 0 < σ → σ ≤ R₀ → 0 ≤ mu σ := by
    intro σ hσ hσR
    have hNB := hNBball σ hσ
    obtain ⟨x, hx⟩ := (hmubnd σ hσ hσR ⟨0, hnpos⟩).exists
    exact le_trans (abs_nonneg _) hx
  have hmuT : ∀ σ : ℝ, 0 < σ → σ ≤ R₀ → mu σ ≤ T :=
    fun σ hσ hσR => hmumin σ hσ T (hgTk σ hσR)
  have hmumono : ∀ σ σ' : ℝ, 0 < σ → σ ≤ σ' → σ' ≤ R₀ → mu σ ≤ mu σ' := by
    intro σ σ' hσ hσσ' hσ'R
    have hsub : Metric.ball x₀ σ ⊆ Metric.ball x₀ σ' := Metric.ball_subset_ball hσσ'
    exact hmumin σ hσ (mu σ') (fun k =>
      ae_restrict_of_ae_restrict_of_subset hsub
        (hmubnd σ' (lt_of_lt_of_le hσ hσσ') hσ'R k))
  -- (B1) the dyadic scales and the alternative at each scale
  obtain ⟨Rm, hRmdef⟩ : ∃ s : ℕ → ℝ, s = fun m => R₀ / 2 ^ m := ⟨_, rfl⟩
  have hRm0 : ∀ m : ℕ, 0 < Rm m := by
    intro m
    simp only [hRmdef]
    positivity
  have hRmR : ∀ m : ℕ, Rm m ≤ R₀ := by
    intro m
    simp only [hRmdef]
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1:ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    nlinarith only [h1, hR₀]
  have hRmsucc : ∀ m : ℕ, Rm (m + 1) = Rm m / 2 := by
    intro m
    simp only [hRmdef, pow_succ]
    ring
  have hRmsub : ∀ m : ℕ, Metric.ball x₀ (Rm m) ⊆ Metric.ball x₀ R₀ :=
    fun m => Metric.ball_subset_ball (hRmR m)
  have hsolBm : ∀ m : ℕ, IsWeakSolutionOn n p (Metric.ball x₀ (Rm m))
      (fun _ _ h => A h) (fun _ _ _ => 0) u g := fun m =>
    IsWeakSolutionRestrict n p hn1 hp1 Ω₀ x₀ (Rm m) (fun _ _ h => A h)
      (fun _ _ _ => 0) u g hΩ₀ (hRm0 m) (subset_trans (hRmsub m) hballΩ) hsol
  have hDgm : ∀ (m : ℕ) (i : Fin n),
      MemW1pLocOn n 2 (Metric.ball x₀ (Rm m)) (fun x => g x i) (Dg i) := by
    intro m i
    exact (WeakGradientRestrict n 2 hn1 (by norm_num) (Metric.ball x₀ R₀)
      (Metric.ball x₀ (Rm m)) (fun x => g x i) (Dg i) Metric.isOpen_ball
      Metric.isOpen_ball (hRmsub m)).2.1 (hDg i)
  have hAltm := fun m : ℕ => hDA ε γ₀ γ₁ (mu (Rm m)) A u g Dg x₀ (Rm m)
    hε hγ₀ hγ₁ (hRm0 m)
    (hQrestrict Ω₀ (Metric.ball x₀ (Rm m)) (subset_trans (hRmsub m) hballΩ) hQ)
    (hC1 ε γ₀ γ₁ (Metric.ball x₀ (Rm m)) A hγ₀ hγ₁0 Metric.isOpen_ball)
    (hsolBm m) (hDgm m)
    (hmubnd (Rm m) (hRm0 m) (hRmR m)) (hmumin (Rm m) (hRm0 m))
  -- the alternative's hypothesis `H_m` at scale `m`
  obtain ⟨Hm, hHmdef⟩ : ∃ P : ℕ → Prop, P = fun m => ∃ k : Fin n,
      θ₂ * (volume (Metric.ball x₀ (Rm m))).toReal
          ≤ (volume (Metric.ball x₀ (Rm m) ∩
              {y | mu (Rm m) / 2 < g y k})).toReal ∨
        θ₂ * (volume (Metric.ball x₀ (Rm m))).toReal
          ≤ (volume (Metric.ball x₀ (Rm m) ∩
              {y | g y k < -(mu (Rm m) / 2)})).toReal := ⟨_, rfl⟩
  -- (3.25): when `H_m` fails, `μ` contracts by `ν`
  have hstep325 : ∀ m : ℕ, ¬ Hm m → mu (Rm (m + 1)) ≤ ν * mu (Rm m) := by
    intro m hfail
    rw [hHmdef] at hfail
    rw [hRmsucc m]
    exact hmumin (Rm m / 2) (by linarith [hRm0 m]) _ ((hAltm m).2 hfail)
  -- (3.26): when `H_m` holds with witness `k₀`, the gradient is bounded below
  have hstep326 : ∀ m : ℕ, Hm m → ∃ k₀ : Fin n,
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (Rm (m + 1)))),
        cp * mu (Rm m) ≤ |g x k₀| := by
    intro m hHm
    rw [hHmdef] at hHm
    obtain ⟨k₀, hk₀⟩ := hHm
    refine ⟨k₀, ?_⟩
    rw [hRmsucc m, hcpdef]
    exact (hAltm m).1 k₀ hk₀
  have hRm00 : Rm 0 = R₀ := by simp only [hRmdef]; norm_num
  -- the oscillation of a component is at most twice `μ`
  have hoscmu : ∀ σ : ℝ, 0 < σ → σ ≤ R₀ → ∀ k : Fin n,
      EssOscOn n (Metric.ball x₀ σ) (fun x => g x k) ≤ 2 * mu σ := by
    intro σ hσ hσR k
    have hNB := hNBball σ hσ
    have hb := hmubnd σ hσ hσR k
    have hhi : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ σ)), g x k ≤ mu σ := by
      filter_upwards [hb] with x hx
      exact le_trans (le_abs_self _) hx
    have hlo : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ σ)), -(mu σ) ≤ g x k := by
      filter_upwards [hb] with x hx
      have h1 := neg_abs_le (g x k)
      linarith
    have h1 : essSup (fun x => g x k) (volume.restrict (Metric.ball x₀ σ))
        ≤ mu σ := essSup_le_of_ae_le _ hhi (hcobdd hNB hlo)
    have h2 : -(mu σ)
        ≤ essInf (fun x => g x k) (volume.restrict (Metric.ball x₀ σ)) :=
      le_essInf_of_ae_le _ hlo (hcobddge hNB hhi)
    rw [EssOscOn]
    linarith
  -- the dyadic radius selection
  have hhalf : ∀ m : ℕ, Rm m = R₀ * ((1:ℝ) / 2) ^ m := by
    intro m
    simp only [hRmdef, div_pow, one_pow]
    ring
  have hradius : ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ R₀ →
      ∃ m : ℕ, Rm (m + 1) < ρ' ∧ ρ' ≤ Rm m := by
    intro ρ' hρ'0 hρ'R
    classical
    obtain ⟨m0, hm0⟩ :=
      exists_pow_lt_of_lt_one (div_pos hρ'0 hR₀) (by norm_num : (1:ℝ) / 2 < 1)
    have hex : ∃ m : ℕ, Rm (m + 1) < ρ' := by
      refine ⟨m0, ?_⟩
      rw [hhalf]
      have hpm : (0:ℝ) < ((1:ℝ) / 2) ^ (m0 + 1) := by positivity
      have h1 : ((1:ℝ) / 2) ^ (m0 + 1) ≤ ((1:ℝ) / 2) ^ m0 := by
        rw [pow_succ]
        have hpos : (0:ℝ) < ((1:ℝ) / 2) ^ m0 := by positivity
        nlinarith only [hpos]
      have h2 : R₀ * ((1:ℝ) / 2) ^ (m0 + 1) ≤ R₀ * ((1:ℝ) / 2) ^ m0 :=
        mul_le_mul_of_nonneg_left h1 hR₀.le
      have h3 : R₀ * ((1:ℝ) / 2) ^ m0 < R₀ * (ρ' / R₀) :=
        mul_lt_mul_of_pos_left hm0 hR₀
      have h4 : R₀ * (ρ' / R₀) = ρ' := by field_simp
      linarith
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, hRm00]; exact hρ'R
    · have hlt := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
      have heq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      rw [heq] at hlt
      exact not_lt.1 hlt
  -- the dyadic decay of `μ` in terms of `(ρ/R₀)^α`, which is (B.1)/(B.2)
  have hdecay : ∀ (m : ℕ) (ρ' : ℝ), 0 < ρ' → ρ' ≤ R₀ → Rm (m + 1) < ρ' → ρ' ≤ Rm m →
      mu (Rm m) ≤ ν ^ m * mu R₀ → mu ρ' ≤ 2 * (ρ' / R₀) ^ α * mu R₀ := by
    intro m ρ' hρ'0 hρ'R hlt hle hmum
    have hd0 : (0:ℝ) < ρ' / R₀ := div_pos hρ'0 hR₀
    have hd1 : ρ' / R₀ ≤ 1 := by rw [div_le_one hR₀]; exact hρ'R
    have hmuR0 : 0 ≤ mu R₀ := hmu0 R₀ hR₀ le_rfl
    -- `ν^m ≤ 2^{-(α₁ m)}`
    have hA : ν ^ m ≤ (2:ℝ) ^ (-(α₁ * m)) := by
      have h1 : ν ^ m ≤ ((2:ℝ) ^ (-α₁)) ^ m := pow_le_pow_left₀ hν.1.le hνα₁ m
      have h2 : ((2:ℝ) ^ (-α₁)) ^ m = (2:ℝ) ^ (-(α₁ * m)) := by
        rw [← Real.rpow_natCast ((2:ℝ) ^ (-α₁)) m, ← Real.rpow_mul (by norm_num)]
        congr 1
        ring
      linarith [h1, h2.le, h2.ge]
    -- `2^{-(α₁ m)} = (R_m/R₀)^{α₁}`
    have hratio : Rm m / R₀ = (2:ℝ) ^ (-(m:ℝ)) := by
      simp only [hRmdef]
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
      field_simp
    have hB : (2:ℝ) ^ (-(α₁ * m)) = (Rm m / R₀) ^ α₁ := by
      rw [hratio, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    -- `(R_m/R₀)^{α₁} ≤ 2 (ρ'/R₀)^α`
    have hrm0 : (0:ℝ) ≤ Rm m / R₀ := le_of_lt (div_pos (hRm0 m) hR₀)
    have hRm2 : Rm m / R₀ ≤ 2 * (ρ' / R₀) := by
      have hs : Rm m = 2 * Rm (m + 1) := by rw [hRmsucc m]; ring
      rw [hs, div_le_iff₀ hR₀]
      have : Rm (m + 1) < ρ' := hlt
      have h2 : 2 * (ρ' / R₀) * R₀ = 2 * ρ' := by field_simp
      rw [h2]
      linarith
    have hC : (Rm m / R₀) ^ α₁ ≤ (2 * (ρ' / R₀)) ^ α₁ :=
      Real.rpow_le_rpow hrm0 hRm2 hα₁0.le
    have hD : (2 * (ρ' / R₀)) ^ α₁ = (2:ℝ) ^ α₁ * (ρ' / R₀) ^ α₁ :=
      Real.mul_rpow (by norm_num) hd0.le
    have hE : (2:ℝ) ^ α₁ ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hα₁1
      rwa [Real.rpow_one] at h
    have hF : (ρ' / R₀) ^ α₁ ≤ (ρ' / R₀) ^ α :=
      Real.rpow_le_rpow_of_exponent_ge hd0 hd1 hαα₁
    have hα0' : (0:ℝ) ≤ (ρ' / R₀) ^ α := Real.rpow_nonneg hd0.le _
    have hα1' : (0:ℝ) ≤ (ρ' / R₀) ^ α₁ := Real.rpow_nonneg hd0.le _
    -- assemble
    have hchain : ν ^ m ≤ 2 * (ρ' / R₀) ^ α := by
      have h1 : (2:ℝ) ^ α₁ * (ρ' / R₀) ^ α₁ ≤ 2 * (ρ' / R₀) ^ α := by
        have ha : (2:ℝ) ^ α₁ * (ρ' / R₀) ^ α₁ ≤ 2 * (ρ' / R₀) ^ α₁ :=
          mul_le_mul_of_nonneg_right hE hα1'
        have hb : (2:ℝ) * (ρ' / R₀) ^ α₁ ≤ 2 * (ρ' / R₀) ^ α := by linarith
        linarith
      calc ν ^ m ≤ (2:ℝ) ^ (-(α₁ * m)) := hA
        _ = (Rm m / R₀) ^ α₁ := hB
        _ ≤ (2 * (ρ' / R₀)) ^ α₁ := hC
        _ = (2:ℝ) ^ α₁ * (ρ' / R₀) ^ α₁ := hD
        _ ≤ 2 * (ρ' / R₀) ^ α := h1
    have hmono := hmumono ρ' (Rm m) hρ'0 hle (hRmR m)
    nlinarith only [hmono, hmum, hchain, hmuR0]
  -- `μ` contracts geometrically as long as `H_j` fails below `m`
  have hchainmu : ∀ m : ℕ, (∀ j : ℕ, j < m → ¬ Hm j) →
      mu (Rm m) ≤ ν ^ m * mu R₀ := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [hRm00]
      simp
    | succ m ih =>
      intro h
      have h1 := hstep325 m (h m (Nat.lt_succ_self m))
      have h2 := ih (fun j hj => h j (lt_trans hj (Nat.lt_succ_self m)))
      have h3 : ν * mu (Rm m) ≤ ν * (ν ^ m * mu R₀) :=
        mul_le_mul_of_nonneg_left h2 hν.1.le
      calc mu (Rm (m + 1)) ≤ ν * mu (Rm m) := h1
        _ ≤ ν * (ν ^ m * mu R₀) := h3
        _ = ν ^ (m + 1) * mu R₀ := by ring
  -- the conversion from a bound on `μ(ρ)` to the asserted oscillation bound
  have hconclude : mu ρ ≤ 2 * (ρ / R₀) ^ α * mu R₀ →
      EssOscOn n (Metric.ball x₀ ρ) (fun x => g x k) ≤ 16 * T * (ρ / R₀) ^ α := by
    intro h
    have h1 := hoscmu ρ hρ hρR k
    have h2 : mu R₀ ≤ T := hmuT R₀ hR₀ le_rfl
    have h3 : (0:ℝ) ≤ (ρ / R₀) ^ α :=
      Real.rpow_nonneg (le_of_lt (div_pos hρ hR₀)) _
    have h4 : 0 ≤ mu R₀ := hmu0 R₀ hR₀ le_rfl
    have h5 : 0 ≤ (ρ / R₀) ^ α * (T - mu R₀) := mul_nonneg h3 (by linarith)
    have h6 : 0 ≤ (ρ / R₀) ^ α * T := mul_nonneg h3 hT0
    linarith only [h1, h, h5, h6]
  classical
  by_cases hCI : ∀ m : ℕ, ¬ Hm m
  · -- (B2) Case I: `H_m` fails at every scale
    obtain ⟨m, hm1, hm2⟩ := hradius ρ hρ hρR
    exact hconclude
      (hdecay m ρ hρ hρR hm1 hm2 (hchainmu m (fun j _ => hCI j)))
  · -- (B3)–(B7) Case II: the first scale at which `H_m` holds
    exact OscillationDecayFirstGoodScale n p r c₄ cp Kp γs δ ν α₂ α ε γ₀ γ₁ T hn
      hp hr hn1 hnR hc₄0 hcp0 hcp16 hKpdef hγs0 hδ hα₂0 hα₂1 hδα₂ hα0 hαα₂ hα1 Ω₀
      A u g g' Dg x₀ R₀ ρ k mu Rm Hm hε hγ₀ hγ₁ hT0 hR₀ hρ hρR hγ₁0 hQ hballΩ hC1
      hCLW hPCLB hODL hNBball hcobdd hcobddge hcoord hQrestrict hDg hgTk hmubnd hmu0
      hmuT hmumono hRm0 hRmR hRmsucc hRmsub hsolBm hDgm hstep326 hoscmu hradius
      hdecay hchainmu hconclude hg'cont hg'ae hRmdef hCI
