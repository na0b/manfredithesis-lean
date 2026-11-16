import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MemHolderOn
import ManfrediThesis.CitedDirichletHolder
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.BallComparisonPrinciple
import ManfrediThesis.WeakGradientLinear
import ManfrediThesis.WeakGradientRestrict
import ManfrediThesis.WeakGradientZeroExtend
import ManfrediThesis.WeakGradientOfC1
open MeasureTheory

/-- Lemma 3.1: existence, uniqueness and the oscillation bound for the
Dirichlet problem for (3.1) on a ball with Hölder boundary data. -/
theorem DirichletProblemRestricted :
    ∀ (n : ℕ) (p ε γ₀ γ₁ β : ℝ), 2 ≤ n → 1 < p → 0 ≤ ε → 0 < γ₀ → γ₀ ≤ γ₁ →
      0 ≤ β → β < 1 →
      CitedSobolevPoincareBall n →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
        (fb : EuclideanSpace ℝ (Fin n) → ℝ),
        IsOpen Ω → 0 < R → Metric.closedBall x₀ R ⊆ Ω →
        EllipticStructureQ12 n p ε γ₀ γ₁ Set.univ (fun _ _ h => A h) → A 0 = 0 →
        CitedDirichletHolder n p ε γ₀ γ₁ A →
        MemHolderOn n β (Metric.sphere x₀ R) fb →
        ∃ (u U : EuclideanSpace ℝ (Fin n) → ℝ)
          (gu : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h) (fun _ _ _ => 0) u gu ∧
            MemW1pLocOn n p (Metric.ball x₀ R) u gu ∧
            ContDiffOn ℝ 1 u (Metric.ball x₀ R) ∧
            MemHolderOn n β (Metric.closedBall x₀ R) U ∧
            (∀ x ∈ Metric.ball x₀ R, U x = u x) ∧
            (∀ x ∈ Metric.sphere x₀ R, U x = fb x) ∧
            (∀ x ∈ Metric.ball x₀ R, ∀ y ∈ Metric.ball x₀ R,
              U x - U y ≤ sSup (fb '' Metric.sphere x₀ R) - sInf (fb '' Metric.sphere x₀ R)) ∧
            (∀ (u' U' : EuclideanSpace ℝ (Fin n) → ℝ)
               (gu' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
              IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h)
                  (fun _ _ _ => 0) u' gu' →
              MemW1pLocOn n p (Metric.ball x₀ R) u' gu' →
              ContDiffOn ℝ 1 u' (Metric.ball x₀ R) →
              MemHolderOn n β (Metric.closedBall x₀ R) U' →
              (∀ x ∈ Metric.ball x₀ R, U' x = u' x) →
              (∀ x ∈ Metric.sphere x₀ R, U' x = fb x) →
              Set.EqOn u' u (Metric.ball x₀ R)) := by
  intro n p ε γ₀ γ₁ β hn hp hε hγ₀ hγ hβ0 hβ1 hSP Ω A x₀ R fb hΩ hR hsub hQ hA0 hC3 hfb
  -- Ambient facts.
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hp1 : (1:ℝ) ≤ p := hp.le
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hntriv : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, hnpos⟩ (1 : ℝ), ?_⟩⟩
    intro hcon
    have h := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w ⟨0, hnpos⟩) hcon
    simp at h
  have hballsub : ∀ r : ℝ, r ≤ R → Metric.ball x₀ r ⊆ Metric.ball x₀ R := fun r hr =>
    Metric.ball_subset_ball hr
  -- Step 1: existence and regularity, from the cited result (C3).
  obtain ⟨u, U, gu, hloc, hsol, hC1, hUH, hUu, hUfb, hzero⟩ :=
    hC3 hQ hε hA0 x₀ R β hR hβ0 hβ1 fb hfb
  -- (2a) restriction of the Sobolev memberships to an inner ball.
  have hclos : ∀ r : ℝ, 0 < r → r < R → closure (Metric.ball x₀ r) ⊆ Metric.ball x₀ R := by
    intro r hr hrR
    rw [closure_ball x₀ hr.ne']
    intro x hx
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) hrR)
  have hrestrict : ∀ (w : EuclideanSpace ℝ (Fin n) → ℝ)
      (gw : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → r < R →
      MemW1pLocOn n p (Metric.ball x₀ R) w gw → MemW1pOn n p (Metric.ball x₀ r) w gw := by
    intro w gw r hr hrR hwl
    refine (WeakGradientRestrict n p hn1 hp1 (Metric.ball x₀ R) (Metric.ball x₀ r) w gw
      Metric.isOpen_ball Metric.isOpen_ball (hballsub r hrR.le)).2.2.2 hwl ?_ (hclos r hr hrR)
    rw [closure_ball x₀ hr.ne']
    exact isCompact_closedBall x₀ r
  have hlocr : ∀ (w : EuclideanSpace ℝ (Fin n) → ℝ)
      (gw : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (r : ℝ), r ≤ R →
      MemW1pLocOn n p (Metric.ball x₀ R) w gw → MemW1pLocOn n p (Metric.ball x₀ r) w gw :=
    fun w gw r hrR =>
      (WeakGradientRestrict n p hn1 hp1 (Metric.ball x₀ R) (Metric.ball x₀ r) w gw
        Metric.isOpen_ball Metric.isOpen_ball (hballsub r hrR)).2.1
  -- (2b) the weak-solution property restricts to an inner ball.
  have hsolr : ∀ (w : EuclideanSpace ℝ (Fin n) → ℝ)
      (gw : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → r < R →
      MemW1pLocOn n p (Metric.ball x₀ R) w gw →
      IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h) (fun _ _ _ => 0) w gw →
      IsWeakSolutionOn n p (Metric.ball x₀ r) (fun _ _ h => A h) (fun _ _ _ => 0) w gw := by
    intro w gw r hr hrR hwl hws
    refine ⟨hlocr w gw r hrR.le hwl, ?_⟩
    intro φ gφ hφmem hφcs hφsup
    have hext := WeakGradientZeroExtend n p hn1 hp1 (Metric.ball x₀ R) x₀ r φ gφ
      Metric.isOpen_ball (hballsub r hrR.le) hφmem hφcs hφsup
    have hid := hws.2 φ ((Metric.ball x₀ r).indicator gφ) hext hφcs
      (hφsup.trans (hballsub r hrR.le))
    have hagree : ∀ x ∈ Metric.ball x₀ r,
        (∑ i, A (gw x) i * (Metric.ball x₀ r).indicator gφ x i) + 0 * φ x
          = (∑ i, A (gw x) i * gφ x i) + 0 * φ x := by
      intro x hx
      rw [Set.indicator_of_mem hx]
    have hvanish : ∀ x ∈ Metric.ball x₀ R \ Metric.ball x₀ r,
        (∑ i, A (gw x) i * (Metric.ball x₀ r).indicator gφ x i) + 0 * φ x = 0 := by
      intro x hx
      rw [Set.indicator_of_notMem hx.2]
      simp
    refine ⟨?_, ?_⟩
    · have h1 : IntegrableOn
          (fun x => (∑ i, A (gw x) i * (Metric.ball x₀ r).indicator gφ x i) + 0 * φ x)
          (Metric.ball x₀ r) volume := hid.1.mono_set (hballsub r hrR.le)
      exact h1.congr_fun hagree measurableSet_ball
    · have h2 := hid.2
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball
        (hballsub r hrR.le) hvanish] at h2
      rw [← setIntegral_congr_fun measurableSet_ball hagree]
      exact h2
  -- (2c) every constant is a weak solution, and this is where `A 0 = 0` is used.
  have hconstsol : ∀ (c : ℝ) (r : ℝ), 0 < r →
      MemW1pLocOn n p (Metric.ball x₀ r) (fun _ => c) (fun _ => 0) ∧
      IsWeakSolutionOn n p (Metric.ball x₀ r) (fun _ _ h => A h) (fun _ _ _ => 0)
        (fun _ => c) (fun _ => 0) := by
    intro c r hr
    have hWL := WeakGradientLinear n p hn1 hp1 (Metric.ball x₀ r) (fun _ => c) (fun _ => c)
      (fun _ => 0) (fun _ => 0) 1 1 c Metric.isOpen_ball
    refine ⟨hWL.2.2.1, hWL.2.2.1, ?_⟩
    intro φ gφ hφmem hφcs hφsup
    have hint0 : ∀ x : EuclideanSpace ℝ (Fin n),
        (0:ℝ) = (∑ i, A (0 : EuclideanSpace ℝ (Fin n)) i * gφ x i) + 0 * φ x := by
      intro x
      rw [hA0]
      simp
    refine ⟨?_, ?_⟩
    · exact integrableOn_zero.congr_fun (fun x _ => hint0 x) measurableSet_ball
    · rw [← setIntegral_congr_fun measurableSet_ball (fun x _ => hint0 x)]
      simp
  -- (2d) adding a constant to a solution gives a solution.
  have haddconst : ∀ (w : EuclideanSpace ℝ (Fin n) → ℝ)
      (gw : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (c : ℝ) (r : ℝ), 0 < r →
      MemW1pLocOn n p (Metric.ball x₀ r) w gw →
      IsWeakSolutionOn n p (Metric.ball x₀ r) (fun _ _ h => A h) (fun _ _ _ => 0) w gw →
      MemW1pLocOn n p (Metric.ball x₀ r) (fun x => w x + c) gw ∧
        IsWeakSolutionOn n p (Metric.ball x₀ r) (fun _ _ h => A h) (fun _ _ _ => 0)
          (fun x => w x + c) gw := by
    intro w gw c r hr hwl hws
    have hWL := WeakGradientLinear n p hn1 hp1 (Metric.ball x₀ r) w (fun _ => c) gw
      (fun _ => 0) 1 1 c Metric.isOpen_ball
    have hlc := hWL.1 hwl hWL.2.2.1
    have e1 : (fun x => (1:ℝ) * w x + (1:ℝ) * c) = fun x => w x + c := by
      funext x; ring
    have e2 : (fun x => (1:ℝ) • gw x + (1:ℝ) • (0 : EuclideanSpace ℝ (Fin n))) = gw := by
      funext x
      simp
    rw [e1, e2] at hlc
    exact ⟨hlc, hlc, fun φ gφ h1 h2 h3 => hws.2 φ gφ h1 h2 h3⟩
  -- The boundary device: a strict inequality on the sphere survives on all
  -- nearby inner spheres.
  have hbdry : ∀ (W : EuclideanSpace ℝ (Fin n) → ℝ) (t : ℝ),
      ContinuousOn W (Metric.closedBall x₀ R) →
      (∀ x ∈ Metric.sphere x₀ R, W x < t) →
      ∃ r₀ : ℝ, 0 ≤ r₀ ∧ r₀ < R ∧
        ∀ r : ℝ, r₀ < r → r < R → ∀ z ∈ Metric.sphere x₀ r, W z < t := by
    intro W t hWc hWs
    obtain ⟨K, hK⟩ : ∃ S, S = Metric.closedBall x₀ R ∩ W ⁻¹' Set.Ici t := ⟨_, rfl⟩
    have hKcl : IsClosed K := by
      rw [hK]
      exact hWc.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_Ici
    have hKc : IsCompact K :=
      (isCompact_closedBall x₀ R).of_isClosed_subset hKcl
        (by rw [hK]; exact Set.inter_subset_left)
    have hKball : ∀ z ∈ K, dist z x₀ < R := by
      intro z hz
      rw [hK] at hz
      have h1 : dist z x₀ ≤ R := Metric.mem_closedBall.mp hz.1
      have h2 : t ≤ W z := hz.2
      rcases lt_or_eq_of_le h1 with hlt | heq
      · exact hlt
      · exact absurd (hWs z (Metric.mem_sphere.mpr heq)) (by linarith)
    rcases Set.eq_empty_or_nonempty K with hKe | hKne
    · refine ⟨0, le_refl 0, hR, ?_⟩
      intro r hr1 hr2 z hz
      by_contra hcon
      rw [not_lt] at hcon
      have hzK : z ∈ K := by
        rw [hK]
        refine ⟨Metric.mem_closedBall.mpr ?_, hcon⟩
        rw [Metric.mem_sphere] at hz
        linarith
      rw [hKe] at hzK
      exact hzK
    · have hdc : ContinuousOn (fun x : EuclideanSpace ℝ (Fin n) => dist x x₀) K :=
        (Continuous.dist continuous_id continuous_const).continuousOn
      obtain ⟨z₁, hz₁K, hz₁max⟩ := hKc.exists_isMaxOn hKne hdc
      refine ⟨dist z₁ x₀, dist_nonneg, hKball z₁ hz₁K, ?_⟩
      intro r hr1 hr2 z hz
      by_contra hcon
      rw [not_lt] at hcon
      have hzsp : dist z x₀ = r := Metric.mem_sphere.mp hz
      have hzK : z ∈ K := by
        rw [hK]
        refine ⟨Metric.mem_closedBall.mpr (by linarith), hcon⟩
      have hmx := hz₁max hzK
      simp only [Set.mem_ofPred_eq] at hmx
      linarith
  -- The comparison engine: compare on every inner ball, then exhaust.
  have hengine : ∀ (w₁ : EuclideanSpace ℝ (Fin n) → ℝ)
      (gw₁ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (w₂ : EuclideanSpace ℝ (Fin n) → ℝ)
      (gw₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (W₁ W₂ : EuclideanSpace ℝ (Fin n) → ℝ) (r₀ : ℝ), 0 ≤ r₀ → r₀ < R →
      MemW1pLocOn n p (Metric.ball x₀ R) w₁ gw₁ →
      IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h) (fun _ _ _ => 0) w₁ gw₁ →
      MemW1pLocOn n p (Metric.ball x₀ R) w₂ gw₂ →
      IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h) (fun _ _ _ => 0) w₂ gw₂ →
      ContinuousOn W₁ (Metric.closedBall x₀ R) → (∀ x ∈ Metric.ball x₀ R, W₁ x = w₁ x) →
      ContinuousOn W₂ (Metric.closedBall x₀ R) → (∀ x ∈ Metric.ball x₀ R, W₂ x = w₂ x) →
      (∀ r : ℝ, r₀ < r → r < R → ∀ z ∈ Metric.sphere x₀ r, W₁ z ≤ W₂ z) →
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), w₁ x ≤ w₂ x := by
    intro w₁ gw₁ w₂ gw₂ W₁ W₂ r₀ hr₀ hr₀R hl1 hs1 hl2 hs2 hW1c hW1e hW2c hW2e hsph
    have hball : ∀ r : ℝ, r₀ < r → r < R →
        ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ r)), w₁ x ≤ w₂ x := by
      intro r hr1 hr2
      have hr : 0 < r := lt_of_le_of_lt hr₀ hr1
      exact BallComparisonPrinciple n p ε γ₀ γ₁ hn hp hε hγ₀ hγ hSP A x₀ r w₁ w₂ W₁ W₂ gw₁ gw₂
        hr hQ (hsolr w₁ gw₁ r hr hr2 hl1 hs1) (hsolr w₂ gw₂ r hr hr2 hl2 hs2)
        (hrestrict w₁ gw₁ r hr hr2 hl1) (hrestrict w₂ gw₂ r hr hr2 hl2)
        (hW1c.mono (Metric.closedBall_subset_closedBall hr2.le))
        (fun x hx => hW1e x (hballsub r hr2.le hx))
        (hW2c.mono (Metric.closedBall_subset_closedBall hr2.le))
        (fun x hx => hW2e x (hballsub r hr2.le hx))
        (hsph r hr1 hr2)
    have hnull : ∀ r : ℝ, r₀ < r → r < R →
        volume {x | x ∈ Metric.ball x₀ r ∧ ¬ (w₁ x ≤ w₂ x)} = 0 := by
      intro r hr1 hr2
      refine measure_mono_null ?_
        (ae_iff.mp ((ae_restrict_iff' measurableSet_ball).mp (hball r hr1 hr2)))
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      exact fun hc => hx.2 (hc hx.1)
    refine (ae_restrict_iff' measurableSet_ball).mpr (ae_iff.mpr ?_)
    have hcover : {x | ¬ (x ∈ Metric.ball x₀ R → w₁ x ≤ w₂ x)}
        ⊆ ⋃ j : ℕ, {x | x ∈ Metric.ball x₀ (R - (R - r₀) / ((j:ℝ) + 2)) ∧ ¬ (w₁ x ≤ w₂ x)} := by
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      have hxb : x ∈ Metric.ball x₀ R := by
        by_contra hb
        exact hx (fun h => absurd h hb)
      have hxn : ¬ (w₁ x ≤ w₂ x) := fun hc => hx (fun _ => hc)
      have hd : dist x x₀ < R := Metric.mem_ball.mp hxb
      have ht : 0 < R - dist x x₀ := by linarith
      obtain ⟨j, hj⟩ := exists_nat_gt ((R - r₀) / (R - dist x x₀))
      refine Set.mem_iUnion.mpr ⟨j, ?_, hxn⟩
      rw [Metric.mem_ball]
      have hj2 : R - r₀ < (j:ℝ) * (R - dist x x₀) := by
        rw [div_lt_iff₀ ht] at hj
        exact hj
      have hjn : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      have hlt : (R - r₀) / ((j:ℝ) + 2) < R - dist x x₀ := by
        rw [div_lt_iff₀ (by linarith)]
        nlinarith
      linarith
    refine measure_mono_null hcover ?_
    refine measure_iUnion_null (fun j => ?_)
    have hj0 : (0:ℝ) < (j:ℝ) + 2 := by positivity
    have hpos : 0 < (R - r₀) / ((j:ℝ) + 2) := div_pos (by linarith) hj0
    have hsmall : (R - r₀) / ((j:ℝ) + 2) ≤ (R - r₀) / 2 := by
      apply div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
    exact hnull _ (by linarith) (by linarith)
  -- Passing to the limit in a slack parameter.
  have hlim : ∀ (f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ η : ℝ, 0 < η → ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), f₁ x ≤ f₂ x + η) →
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), f₁ x ≤ f₂ x := by
    intro f₁ f₂ h
    have hall : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
        ∀ j : ℕ, f₁ x ≤ f₂ x + 1 / ((j:ℝ) + 1) := by
      rw [ae_all_iff]
      intro j
      exact h (1 / ((j:ℝ) + 1)) (by positivity)
    filter_upwards [hall] with x hx
    have h0 : f₁ x - f₂ x ≤ 0 :=
      ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat (fun j => by linarith [hx j])
    linarith
  -- An almost-everywhere bound on an open set, for a continuous function, is pointwise.
  have hpt : ∀ (W : EuclideanSpace ℝ (Fin n) → ℝ) (t : ℝ),
      ContinuousOn W (Metric.ball x₀ R) →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), W x ≤ t) →
      ∀ x ∈ Metric.ball x₀ R, W x ≤ t := by
    intro W t hWc hae y hy
    by_contra hcon
    rw [not_le] at hcon
    have hopen : IsOpen (Metric.ball x₀ R ∩ W ⁻¹' Set.Ioi t) :=
      hWc.isOpen_inter_preimage Metric.isOpen_ball isOpen_Ioi
    have hposm : 0 < volume (Metric.ball x₀ R ∩ W ⁻¹' Set.Ioi t) :=
      hopen.measure_pos volume ⟨y, hy, hcon⟩
    have hnull : volume (Metric.ball x₀ R ∩ W ⁻¹' Set.Ioi t) = 0 := by
      refine measure_mono_null ?_
        (ae_iff.mp ((ae_restrict_iff' measurableSet_ball).mp hae))
      intro x hx
      simp only [Set.mem_ofPred_eq]
      intro hc
      exact absurd (hc hx.1) (not_le.mpr hx.2)
    rw [hnull] at hposm
    exact absurd hposm (lt_irrefl 0)
  -- The boundary datum's supremum and infimum.
  have himgc : IsCompact (fb '' Metric.sphere x₀ R) :=
    (isCompact_sphere x₀ R).image_of_continuousOn hfb.1
  have hMle : ∀ x ∈ Metric.sphere x₀ R, fb x ≤ sSup (fb '' Metric.sphere x₀ R) :=
    fun x hx => le_csSup himgc.bddAbove ⟨x, hx, rfl⟩
  have hmle : ∀ x ∈ Metric.sphere x₀ R, sInf (fb '' Metric.sphere x₀ R) ≤ fb x :=
    fun x hx => csInf_le himgc.bddBelow ⟨x, hx, rfl⟩
  -- Step 3: the upper bound.
  have hupper : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      u x ≤ sSup (fb '' Metric.sphere x₀ R) := by
    refine hlim u (fun _ => sSup (fb '' Metric.sphere x₀ R)) ?_
    intro η hη
    obtain ⟨r₀, hr₀0, hr₀R, hr₀s⟩ := hbdry U (sSup (fb '' Metric.sphere x₀ R) + η) hUH.1
      (fun x hx => by rw [hUfb x hx]; linarith [hMle x hx])
    obtain ⟨hlc, hsc⟩ := hconstsol (sSup (fb '' Metric.sphere x₀ R) + η) R hR
    exact hengine u gu (fun _ => sSup (fb '' Metric.sphere x₀ R) + η) (fun _ => 0) U
      (fun _ => sSup (fb '' Metric.sphere x₀ R) + η) r₀ hr₀0 hr₀R hloc hsol hlc hsc
      hUH.1 hUu continuousOn_const (fun _ _ => rfl)
      (fun r h1 h2 z hz => (hr₀s r h1 h2 z hz).le)
  -- Step 4: the lower bound.
  have hlower : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      sInf (fb '' Metric.sphere x₀ R) ≤ u x := by
    refine hlim (fun _ => sInf (fb '' Metric.sphere x₀ R)) u ?_
    intro η hη
    obtain ⟨r₀, hr₀0, hr₀R, hr₀s⟩ := hbdry (fun x => sInf (fb '' Metric.sphere x₀ R) - U x) η
      (continuousOn_const.sub hUH.1)
      (fun x hx => by rw [hUfb x hx]; linarith [hmle x hx])
    obtain ⟨hlc, hsc⟩ := hconstsol (sInf (fb '' Metric.sphere x₀ R) - η) R hR
    have hcmp := hengine (fun _ => sInf (fb '' Metric.sphere x₀ R) - η) (fun _ => 0) u gu
      (fun _ => sInf (fb '' Metric.sphere x₀ R) - η) U r₀ hr₀0 hr₀R hlc hsc hloc hsol
      continuousOn_const (fun _ _ => rfl) hUH.1 hUu
      (fun r h1 h2 z hz => by linarith [hr₀s r h1 h2 z hz])
    filter_upwards [hcmp] with x hx
    linarith
  -- Step 5: the oscillation bound.
  have hUbd : ∀ x ∈ Metric.ball x₀ R, U x ≤ sSup (fb '' Metric.sphere x₀ R) := by
    refine hpt U _ (hUH.1.mono Metric.ball_subset_closedBall) ?_
    filter_upwards [hupper, ae_restrict_mem measurableSet_ball] with x h1 h2
    rw [hUu x h2]
    exact h1
  have hUbd' : ∀ x ∈ Metric.ball x₀ R, sInf (fb '' Metric.sphere x₀ R) ≤ U x := by
    have h := hpt (fun x => -U x) (-sInf (fb '' Metric.sphere x₀ R))
      ((hUH.1.mono Metric.ball_subset_closedBall).neg) ?_
    · intro x hx
      linarith [h x hx]
    · filter_upwards [hlower, ae_restrict_mem measurableSet_ball] with x h1 h2
      rw [hUu x h2]
      linarith
  refine ⟨u, U, gu, hsol, hloc, hC1, hUH, hUu, hUfb, ?_, ?_⟩
  · intro x hx y hy
    linarith [hUbd x hx, hUbd' y hy]
  -- Step 6: uniqueness.
  · intro u' U' gu' hsol' hloc' hC1' hUH' hUu' hUfb'
    have hhalf : ∀ (w₁ : EuclideanSpace ℝ (Fin n) → ℝ)
        (gw₁ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (w₂ : EuclideanSpace ℝ (Fin n) → ℝ)
        (gw₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (W₁ W₂ : EuclideanSpace ℝ (Fin n) → ℝ),
        MemW1pLocOn n p (Metric.ball x₀ R) w₁ gw₁ →
        IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h) (fun _ _ _ => 0) w₁ gw₁ →
        MemW1pLocOn n p (Metric.ball x₀ R) w₂ gw₂ →
        IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h) (fun _ _ _ => 0) w₂ gw₂ →
        ContinuousOn W₁ (Metric.closedBall x₀ R) → (∀ x ∈ Metric.ball x₀ R, W₁ x = w₁ x) →
        ContinuousOn W₂ (Metric.closedBall x₀ R) → (∀ x ∈ Metric.ball x₀ R, W₂ x = w₂ x) →
        (∀ x ∈ Metric.sphere x₀ R, W₁ x = W₂ x) →
        ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), w₁ x ≤ w₂ x := by
      intro w₁ gw₁ w₂ gw₂ W₁ W₂ hl1 hs1 hl2 hs2 hW1c hW1e hW2c hW2e hsphere
      refine hlim w₁ w₂ ?_
      intro η hη
      obtain ⟨r₀, hr₀0, hr₀R, hr₀s⟩ := hbdry (fun x => W₁ x - W₂ x) η (hW1c.sub hW2c)
        (fun x hx => by rw [hsphere x hx]; linarith)
      obtain ⟨hlc, hsc⟩ := haddconst w₂ gw₂ η R hR hl2 hs2
      exact hengine w₁ gw₁ (fun x => w₂ x + η) gw₂ W₁ (fun x => W₂ x + η) r₀ hr₀0 hr₀R
        hl1 hs1 hlc hsc hW1c hW1e (hW2c.add continuousOn_const)
        (fun x hx => by rw [hW2e x hx]) (fun r h1 h2 z hz => by linarith [hr₀s r h1 h2 z hz])
    have hsphUU : ∀ x ∈ Metric.sphere x₀ R, U x = U' x := by
      intro x hx
      rw [hUfb x hx, hUfb' x hx]
    have h1 := hhalf u gu u' gu' U U' hloc hsol hloc' hsol' hUH.1 hUu hUH'.1 hUu' hsphUU
    have h2 := hhalf u' gu' u gu U' U hloc' hsol' hloc hsol hUH'.1 hUu' hUH.1 hUu
      (fun x hx => (hsphUU x hx).symm)
    have hcu : ContinuousOn u (Metric.ball x₀ R) := hC1.continuousOn
    have hcu' : ContinuousOn u' (Metric.ball x₀ R) := hC1'.continuousOn
    have hd1 : ∀ x ∈ Metric.ball x₀ R, u x - u' x ≤ 0 := by
      refine hpt (fun x => u x - u' x) 0 (hcu.sub hcu') ?_
      filter_upwards [h1] with x hx
      linarith
    have hd2 : ∀ x ∈ Metric.ball x₀ R, u' x - u x ≤ 0 := by
      refine hpt (fun x => u' x - u x) 0 (hcu'.sub hcu) ?_
      filter_upwards [h2] with x hx
      linarith
    intro x hx
    linarith [hd1 x hx, hd2 x hx]
