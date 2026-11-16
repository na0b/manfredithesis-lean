import ManfrediThesis.Preamble
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.IsWeakSolutionRestrict
import ManfrediThesis.WeakGradientCompactSupportIntegral
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MemW1pZeroOn
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.WeakGradientRestrict
import ManfrediThesis.EssOscOn
import ManfrediThesis.CaccioppoliLevelWeight
import ManfrediThesis.DegenerateAlternative
import ManfrediThesis.OscillationDecayLemma
import ManfrediThesis.GradientOscillationEstimateEpsPos
import ManfrediThesis.DegenerateLimitTransfer
import ManfrediThesis.GradientSupEstimate
import ManfrediThesis.CitedDirichletW1p
import ManfrediThesis.CitedRegularityEpsPos
open MeasureTheory

/-- Theorem 2: the oscillation decay estimate for the gradient of a solution of
(3.1). -/
theorem GradientOscillationEstimate :
    ∀ (n : ℕ) (p r : ℝ), 2 ≤ n → 1 < p → 0 < r →
      CitedSobolevPoincareBall n →
      (∀ (ε' γ₀' γ₁' : ℝ)
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → CitedDirichletW1p n p ε' γ₀' γ₁' A') →
      (∀ (ε' γ₀' γ₁' : ℝ) (Ω' : Set (EuclideanSpace ℝ (Fin n)))
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → IsOpen Ω' → CitedRegularityEpsPos n p ε' γ₀' γ₁' Ω' A') →
      ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ α ≤ 1 ∧
        ∀ (ε γ₀ γ₁ S : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
          (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (x₀ : EuclideanSpace ℝ (Fin n)) (R ρ : ℝ),
          0 ≤ ε → 0 < γ₀ → γ₁ ≤ r * γ₀ → IsOpen Ω → 0 < ρ → ρ ≤ R →
          EllipticStructureQ12 n p ε γ₀ γ₁ Ω (fun _ _ h => A h) →
          IsWeakSolutionOn n p Ω (fun _ _ h => A h) (fun _ _ _ => 0) u g →
          Metric.closedBall x₀ R ⊆ Ω →
          (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), ‖g x‖ ≤ S) →
          ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ)),
            ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ ρ)),
              ‖g x - g y‖ ≤ C * S * (ρ / R) ^ α := by
  intro n p r hn hp hr hSP hC2 hC1
  have hn0 : (0:ℝ) < n := by
    have h2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  -- (A1): the ratio bound `rp = max r r'` that serves both the given problem
  -- and the approximating problems of Part B
  obtain ⟨r', hr'0, hDLT⟩ := DegenerateLimitTransfer n p r hn hp hr
  obtain ⟨rp, hrpdef⟩ : ∃ s : ℝ, s = max r r' := ⟨_, rfl⟩
  have hrr : r ≤ rp := by rw [hrpdef]; exact le_max_left _ _
  have hrr' : r' ≤ rp := by rw [hrpdef]; exact le_max_right _ _
  have hrp0 : 0 < rp := lt_of_lt_of_le hr hrr
  -- (A2): the nondegenerate oscillation estimate and its exponent `α`
  obtain ⟨α, hα0, hα1, hosc⟩ :=
    GradientOscillationEstimateEpsPos n p rp hn hp hrp0 hSP hC1
  -- (A3): the gradient sup bound and the constants `κ`, `C`
  obtain ⟨C₁, hC₁0, hsup⟩ := GradientSupEstimate n p rp hn hp hrp0 hSP hC2 hC1
  obtain ⟨ωn, hωn⟩ : ∃ s : ℝ,
      s = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ s : ℝ,
      s = (C₁ * 2 ^ (2 * p - 2) * ωn * 2 ^ (n:ℝ)) ^ (1 / p) := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ s : ℝ,
      s = max (max (64 * Real.sqrt n * κ) (16 * Real.sqrt n)) 8 := ⟨_, rfl⟩
  have hC0 : 0 < C := by
    rw [hCdef]; exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hC16 : 16 * Real.sqrt n ≤ C := by
    rw [hCdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hC8 : (8:ℝ) ≤ C := by rw [hCdef]; exact le_max_right _ _
  have hC64 : 64 * Real.sqrt n * κ ≤ C := by
    rw [hCdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  refine ⟨C, α, hC0, hα0, hα1, ?_⟩
  intro ε γ₀ γ₁ S Ω A u g x₀ R ρ hε hγ₀ hγ₁ hΩ hρ hρR hQ hsol hball hS
  have hR : 0 < R := lt_of_lt_of_le hρ hρR
  have hballΩ : Metric.ball x₀ R ⊆ Ω := Metric.ball_subset_closedBall.trans hball
  have hγ₁rp : γ₁ ≤ rp * γ₀ :=
    le_trans hγ₁ (mul_le_mul_of_nonneg_right hrr hγ₀.le)
  have hNB : ∀ {s : Set (EuclideanSpace ℝ (Fin n))}, volume s ≠ 0 →
      (ae (volume.restrict s)).NeBot := by
    intro s hs
    refine ⟨fun hb => ?_⟩
    rw [ae_eq_bot] at hb
    exact hs (by simpa using congrArg (fun m => m s) hb)
  have hNBR : (ae (volume.restrict (Metric.ball x₀ R))).NeBot :=
    hNB (Metric.measure_ball_pos volume x₀ hR).ne'
  -- (A0): `S ≥ 0`
  have hS0 : 0 ≤ S := by
    obtain ⟨x, hx⟩ := hS.exists
    exact le_trans (norm_nonneg _) hx
  have hpow : (0:ℝ) ≤ (ρ / R) ^ α := Real.rpow_nonneg (by positivity) _
  -- the coordinate bound `|v k| ≤ ‖v‖`
  have hcoord : ∀ (v : EuclideanSpace ℝ (Fin n)) (k : Fin n), |v k| ≤ ‖v‖ := by
    intro v k
    have h1 : (v k) ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (f := fun m => (v m) ^ 2)
        (fun m _ => sq_nonneg _) (Finset.mem_univ k)
    nlinarith [abs_nonneg (v k), norm_nonneg v, sq_abs (v k)]
  -- the volume of a ball, in the form both halves of the proof use
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hntriv : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, hnpos⟩ (1 : ℝ), ?_⟩⟩
    intro hc
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hnpos⟩) hc
    simp at h
  have hballvol : ∀ σ : ℝ, 0 ≤ σ →
      (volume (Metric.ball x₀ σ)).toReal = ωn * σ ^ n := by
    intro σ hσ
    rw [Measure.addHaar_ball volume x₀ hσ, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity),
      show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n by simp, hωn]
    ring
  -- the componentwise-to-vector conversion: an oscillation bound `D` on every
  -- component gives the two-point bound `√n · D` on the vector
  have hconv : ∀ (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (T D : ℝ), 0 ≤ D →
      (∀ᵐ z ∂(volume.restrict (Metric.ball x₀ ρ)), ‖f z‖ ≤ T) →
      (∀ k : Fin n, EssOscOn n (Metric.ball x₀ ρ) (fun z => f z k) ≤ D) →
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ)),
        ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ ρ)),
          ‖f x - f y‖ ≤ Real.sqrt n * D := by
    intro f T D hD0 hTb hoscf
    have hhi : ∀ k : Fin n, ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ ρ)),
        f z k ≤ essSup (fun w => f w k) (volume.restrict (Metric.ball x₀ ρ)) := by
      intro k
      refine ae_le_essSup ⟨T, ?_⟩
      rw [Filter.eventually_map]
      filter_upwards [hTb] with z hz
      exact le_trans (le_trans (le_abs_self _) (hcoord (f z) k)) hz
    have hlo : ∀ k : Fin n, ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ ρ)),
        essInf (fun w => f w k) (volume.restrict (Metric.ball x₀ ρ)) ≤ f z k := by
      intro k
      refine ae_essInf_le ⟨-T, ?_⟩
      rw [Filter.eventually_map]
      filter_upwards [hTb] with z hz
      have h1 := hcoord (f z) k
      have h2 := neg_abs_le (f z k)
      linarith
    have hall : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ ρ)), ∀ k : Fin n,
        essInf (fun w => f w k) (volume.restrict (Metric.ball x₀ ρ)) ≤ f z k ∧
          f z k ≤ essSup (fun w => f w k) (volume.restrict (Metric.ball x₀ ρ)) := by
      rw [ae_all_iff]
      exact fun k => (hlo k).and (hhi k)
    filter_upwards [hall] with x hx
    filter_upwards [hall] with y hy
    have hk : ∀ k : Fin n, (f x k - f y k) ^ 2 ≤ D ^ 2 := by
      intro k
      have h5 := hoscf k
      rw [EssOscOn] at h5
      have ha : f x k - f y k ≤ D := by
        have h1 := (hx k).2
        have h2 := (hy k).1
        linarith
      have hb : -D ≤ f x k - f y k := by
        have h1 := (hx k).1
        have h2 := (hy k).2
        linarith
      exact sq_le_sq' hb ha
    have hM0 : (0:ℝ) ≤ Real.sqrt n * D := mul_nonneg (Real.sqrt_nonneg _) hD0
    have hsum : ‖f x - f y‖ ^ 2 ≤ (Real.sqrt n * D) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, mul_pow, Real.sq_sqrt hn0.le]
      calc ∑ k : Fin n, ((f x - f y) k) ^ 2
          ≤ ∑ _k : Fin n, D ^ 2 := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            have hkk : (f x - f y) k = f x k - f y k := rfl
            rw [hkk]
            exact hk k
        _ = (n : ℝ) * D ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 : Real.sqrt (‖f x - f y‖ ^ 2) ≤ Real.sqrt ((Real.sqrt n * D) ^ 2) :=
      Real.sqrt_le_sqrt hsum
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hM0] at h1
  by_cases hεpos : 0 < ε
  · -- (B1′) the case `ε > 0`: apply (A2) and convert components to the vector
    have hoscρ : ∀ k : Fin n,
        EssOscOn n (Metric.ball x₀ ρ) (fun z => g z k) ≤ 16 * S * (ρ / R) ^ α :=
      fun k => hosc ε γ₀ γ₁ S Ω A u g x₀ R ρ k hεpos hγ₀ hγ₁rp hS0 hΩ hR hρ hρR
        hQ hsol hballΩ hS
    have hballρR : Metric.ball x₀ ρ ⊆ Metric.ball x₀ R := Metric.ball_subset_ball hρR
    have hSρ : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ ρ)), ‖g z‖ ≤ S :=
      ae_restrict_of_ae_restrict_of_subset hballρR hS
    have hD0 : (0:ℝ) ≤ 16 * S * (ρ / R) ^ α := by positivity
    filter_upwards [hconv g S (16 * S * (ρ / R) ^ α) hD0 hSρ hoscρ] with x hx
    filter_upwards [hx] with y hy
    calc ‖g x - g y‖ ≤ Real.sqrt n * (16 * S * (ρ / R) ^ α) := hy
      _ = (16 * Real.sqrt n) * S * (ρ / R) ^ α := by ring
      _ ≤ C * S * (ρ / R) ^ α :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC16 hS0) hpow
  · -- (B2′)–(B6′): the degenerate case `ε = 0`
    have hε0 : ε = 0 := le_antisymm (not_lt.1 hεpos) hε
    have hn1 : 1 ≤ n := le_trans (by norm_num) hn
    have hp1 : (1:ℝ) ≤ p := le_of_lt hp
    have hx₀Ω : x₀ ∈ Ω := hball (Metric.mem_closedBall_self hR.le)
    have hΩne : volume Ω ≠ 0 := fun hc =>
      (Metric.measure_ball_pos volume x₀ hR).ne' (measure_mono_null hballΩ hc)
    have hNBΩ : (ae (volume.restrict Ω)).NeBot := hNB hΩne
    -- a domain-free statement that holds a.e. on `Ω` holds outright
    have hextract : ∀ P : Prop,
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ∈ Ω → P) → P := by
      intro P hP
      have h1 : ∀ᵐ x ∂(volume.restrict Ω), x ∈ Ω → P := ae_restrict_of_ae hP
      have h2 : ∀ᵐ x ∂(volume.restrict Ω), x ∈ Ω := ae_restrict_mem hΩ.measurableSet
      obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
      exact hx1 hx2
    -- the structure conditions restrict to any subset
    have hQrestrict : ∀ (e c0 c1 : ℝ)
        (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (s t : Set (EuclideanSpace ℝ (Fin n))), t ⊆ s →
        EllipticStructureQ12 n p e c0 c1 s (fun _ _ h => F h) →
        EllipticStructureQ12 n p e c0 c1 t (fun _ _ h => F h) := by
      intro e c0 c1 F s t hst hQs
      refine ⟨hQs.meas_x, hQs.cont_zh, fun x hx z => hQs.hcont x (hst hx) z,
        fun x hx z => hQs.hdiff x (hst hx) z, ?_, ?_⟩
      · filter_upwards [hQs.Q1] with x hx hxt
        exact hx (hst hxt)
      · filter_upwards [hQs.Q2] with x hx hxt
        exact hx (hst hxt)
    -- (B2′): the normalisation `A(0) = 0`
    obtain ⟨At, hAtdef⟩ : ∃ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        F = fun h => A h - A 0 := ⟨_, rfl⟩
    have hAt0 : At 0 = 0 := by rw [hAtdef]; simp
    have hQt : EllipticStructureQ12 n p ε γ₀ γ₁ Ω (fun _ _ h => At h) := by
      refine ⟨fun z h => measurable_const, ?_, ?_, ?_, ?_, ?_⟩
      · intro x
        simp only [hAtdef]
        exact (hQ.cont_zh x).sub continuous_const
      · intro x hx z
        simp only [hAtdef]
        exact (hQ.hcont x hx z).sub continuous_const
      · intro x hx z
        simp only [hAtdef]
        exact (hQ.hdiff x hx z).sub contDiffOn_const
      · filter_upwards [hQ.Q1] with x hx hxΩ z h ξ hw
        simp only [hAtdef, fderiv_sub_const]
        exact hx hxΩ z h ξ hw
      · filter_upwards [hQ.Q2] with x hx hxΩ z h i j hw
        simp only [hAtdef, fderiv_sub_const]
        exact hx hxΩ z h i j hw
    -- the weak-solution property, restricted to `B_R` and transported to `At`
    have hsolB : IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h)
        (fun _ _ _ => 0) u g :=
      IsWeakSolutionRestrict n p hn1 hp1 Ω x₀ R (fun _ _ h => A h)
        (fun _ _ _ => 0) u g hΩ hR hballΩ hsol
    have hclcpt : IsCompact (closure (Metric.ball x₀ R)) :=
      IsCompact.of_isClosed_subset (isCompact_closedBall x₀ R) isClosed_closure
        Metric.closure_ball_subset_closedBall
    have hmemB : MemW1pOn n p (Metric.ball x₀ R) u g :=
      (WeakGradientRestrict n p hn1 hp1 Ω (Metric.ball x₀ R) u g hΩ
        Metric.isOpen_ball hballΩ).2.2.2 hsol.1 hclcpt
        (subset_trans Metric.closure_ball_subset_closedBall hball)
    have hsolBt : IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => At h)
        (fun _ _ _ => 0) u g := by
      refine ⟨hsolB.1, ?_⟩
      intro φ gφ hφ hcs hts
      obtain ⟨hIa, hZa⟩ := hsolB.2 φ gφ hφ hcs hts
      have hcomp : ∀ i : Fin n,
          IntegrableOn (fun x => gφ x i) (Metric.ball x₀ R) volume ∧
            (∫ x in Metric.ball x₀ R, gφ x i) = 0 := fun i =>
        WeakGradientCompactSupportIntegral n p hn1 hp1 x₀ R φ gφ hR hφ hcs hts i
      have hD : IntegrableOn (fun x => ∑ i, (A 0) i * gφ x i)
          (Metric.ball x₀ R) volume :=
        integrable_finsetSum _ (fun i _ => ((hcomp i).1).const_mul _)
      have hDz : (∫ x in Metric.ball x₀ R, ∑ i, (A 0) i * gφ x i) = 0 := by
        rw [integral_finsetSum _ (fun i _ => ((hcomp i).1).const_mul _)]
        refine Finset.sum_eq_zero (fun i _ => ?_)
        rw [integral_const_mul, (hcomp i).2, mul_zero]
      have heq : ∀ x : EuclideanSpace ℝ (Fin n),
          ((∑ i, (At (g x)) i * gφ x i) + (0:ℝ) * φ x)
            = (((∑ i, (A (g x)) i * gφ x i) + (0:ℝ) * φ x)
              - (∑ i, (A 0) i * gφ x i)) := by
        intro x
        have hterm : ∀ i : Fin n, (At (g x)) i * gφ x i
            = (A (g x)) i * gφ x i - (A 0) i * gφ x i := by
          intro i
          simp only [hAtdef]
          have hsub : ((A (g x) - A 0) : EuclideanSpace ℝ (Fin n)) i
              = (A (g x)) i - (A 0) i := rfl
          rw [hsub]
          ring
        rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib]
        ring
      refine ⟨?_, ?_⟩
      · refine IntegrableOn.congr_fun (hIa.sub hD) ?_ measurableSet_ball
        intro x _
        exact (heq x).symm
      · rw [setIntegral_congr_fun measurableSet_ball (fun x _ => heq x),
          integral_sub hIa hD, hZa, hDz, sub_zero]
    -- (B3′): the structure conditions hold on all of `ℝⁿ`
    have hQuniv : EllipticStructureQ12 n p 0 γ₀ γ₁ Set.univ (fun _ _ h => At h) := by
      rw [← hε0]
      refine ⟨hQt.meas_x, hQt.cont_zh, ?_, ?_, ?_, ?_⟩
      · exact fun x _ z => hQt.hcont x₀ hx₀Ω z
      · exact fun x _ z => hQt.hdiff x₀ hx₀Ω z
      · refine Filter.Eventually.of_forall (fun x _ => ?_)
        exact hextract _ hQt.Q1
      · refine Filter.Eventually.of_forall (fun x _ => ?_)
        exact hextract _ hQt.Q2
    -- (B4′): the approximating sequence
    obtain ⟨em, Ae, ue, ge, hem0, hemlim, hAestr, hAesol, hAezero, hAeconv, hgeae⟩ :=
      hDLT γ₀ γ₁ hγ₀ hγ₁ At hAt0 hQuniv hC2 x₀ R u g hR hmemB hsolBt
    rcases le_or_gt ρ (R / 4) with hρ4 | hρ4
    · -- (B5′)–(B6′): the inner range of radii
      -- the elementary convexity inequality `(a+b)^p ≤ 2^{p-1}(a^p+b^p)`
      have haddp : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
          (a + b) ^ p ≤ 2 ^ (p - 1) * (a ^ p + b ^ p) := by
        intro a b ha hb
        have h := NNReal.rpow_add_le_mul_rpow_add_rpow a.toNNReal b.toNNReal hp1
        have h2 := (NNReal.coe_le_coe).2 h
        push_cast [Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb] at h2
        exact h2
      have h2p0 : (0:ℝ) < 2 ^ (p - 1) := Real.rpow_pos_of_pos (by norm_num) _
      have h2pp : (2:ℝ) ^ (p - 1) * 2 ^ (p - 1) = 2 ^ (2 * p - 2) := by
        rw [← Real.rpow_add (by norm_num)]
        ring_nf
      -- the pointwise bound on the integrand of the sup estimate
      have hpt : ∀ e t a b : ℝ, 0 ≤ e → 0 ≤ t → 0 ≤ a → 0 ≤ b → t ≤ a + b →
          (e + t ^ 2) ^ (p / 2)
            ≤ 2 ^ (p - 1) * e ^ (p / 2) + 2 ^ (2 * p - 2) * (a ^ p + b ^ p) := by
        intro e t a b he ht ha hb htab
        have hs : (0:ℝ) ≤ Real.sqrt e := Real.sqrt_nonneg e
        have hse : Real.sqrt e ^ 2 = e := Real.sq_sqrt he
        have hX : (0:ℝ) ≤ Real.sqrt e + (a + b) := by linarith
        have h1 : e + t ^ 2 ≤ (Real.sqrt e + (a + b)) ^ 2 := by
          nlinarith [hs, ha, hb, ht, htab, hse]
        have h2 : (e + t ^ 2) ^ (p / 2)
            ≤ ((Real.sqrt e + (a + b)) ^ 2) ^ (p / 2) :=
          Real.rpow_le_rpow (by positivity) h1 (by linarith)
        have h3 : ((Real.sqrt e + (a + b)) ^ 2) ^ (p / 2)
            = (Real.sqrt e + (a + b)) ^ p := by
          rw [← Real.rpow_natCast (Real.sqrt e + (a + b)) 2, ← Real.rpow_mul hX]
          congr 1
          push_cast
          ring
        have h4 : (Real.sqrt e + (a + b)) ^ p
            ≤ 2 ^ (p - 1) * ((Real.sqrt e) ^ p + (a + b) ^ p) :=
          haddp _ _ hs (by linarith)
        have h5 : (Real.sqrt e) ^ p = e ^ (p / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul he]
          ring_nf
        have h6 : (a + b) ^ p ≤ 2 ^ (p - 1) * (a ^ p + b ^ p) := haddp a b ha hb
        have h7 : 2 ^ (p - 1) * ((Real.sqrt e) ^ p + (a + b) ^ p)
            ≤ 2 ^ (p - 1) * e ^ (p / 2) + 2 ^ (2 * p - 2) * (a ^ p + b ^ p) := by
          have hmul : 2 ^ (p - 1) * (a + b) ^ p
              ≤ 2 ^ (p - 1) * (2 ^ (p - 1) * (a ^ p + b ^ p)) :=
            mul_le_mul_of_nonneg_left h6 h2p0.le
          have hid : 2 ^ (p - 1) * (2 ^ (p - 1) * (a ^ p + b ^ p))
              = 2 ^ (2 * p - 2) * (a ^ p + b ^ p) := by
            rw [← mul_assoc, h2pp]
          rw [hid] at hmul
          rw [h5, mul_add]
          linarith
        rw [h3] at h2
        linarith
      -- the structure constants of the approximating problems
      have hAe0 : ∀ m : ℕ, Ae m 0 = 0 := fun m => (hAestr m).1
      choose c0 c1 hc0 hc1 hQe using fun m : ℕ => (hAestr m).2
      have hc1rp : ∀ m : ℕ, c1 m ≤ rp * c0 m := fun m =>
        le_trans (hc1 m) (mul_le_mul_of_nonneg_right hrr' (hc0 m).le)
      -- (B5′): the uniform gradient bound of `GradientSupEstimate` at each level
      have hsupm : ∀ m : ℕ, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2 / 2))),
          (em m + ‖ge m x‖ ^ 2) ^ (p / 2)
            ≤ C₁ / (R / 2) ^ (n : ℝ) *
                ∫ y in Metric.ball x₀ (R / 2), (em m + ‖ge m y‖ ^ 2) ^ (p / 2) := by
        intro m
        refine hsup (em m) (c0 m) (c1 m) (Metric.ball x₀ R) (Ae m) (ue m) (ge m)
          x₀ (R / 2) (hem0 m).le (hc0 m) (hc1rp m) Metric.isOpen_ball (by linarith)
          (hAe0 m) ?_ (hAesol m) (Metric.closedBall_subset_ball (by linarith))
        exact hQrestrict (em m) (c0 m) (c1 m) (Ae m) Set.univ (Metric.ball x₀ R)
          (Set.subset_univ _) (hQe m)
      -- the `L^p` data on `B_R` that bounds the right-hand side
      have hp0 : (0:ℝ) ≤ p := le_of_lt (lt_trans zero_lt_one hp)
      have hpne : ENNReal.ofReal p ≠ 0 := by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        linarith
      have hgp : IntegrableOn (fun x => ‖g x‖ ^ p) (Metric.ball x₀ R) volume := by
        have h := hmemB.2.2.integrable_norm_rpow hpne ENNReal.ofReal_ne_top
        rwa [ENNReal.toReal_ofReal hp0] at h
      have hdp : ∀ m : ℕ, IntegrableOn (fun x => ‖ge m x - g x‖ ^ p)
          (Metric.ball x₀ R) volume := by
        intro m
        have h := ((hAezero m).1.2.2).integrable_norm_rpow hpne ENNReal.ofReal_ne_top
        rwa [ENNReal.toReal_ofReal hp0] at h
      have hp0' : (0:ℝ) < p := lt_trans zero_lt_one hp
      have hωn0 : (0:ℝ) ≤ ωn := by rw [hωn]; exact ENNReal.toReal_nonneg
      have hR2 : (0:ℝ) < R / 2 := by linarith
      have hhalfsub : Metric.ball x₀ (R / 2) ⊆ Metric.ball x₀ R :=
        Metric.ball_subset_ball (by linarith)
      have hVhalf : (volume (Metric.ball x₀ (R / 2))).toReal = ωn * (R / 2) ^ n :=
        hballvol (R / 2) hR2.le
      have hfinhalf : IsFiniteMeasure (volume.restrict (Metric.ball x₀ (R / 2))) := by
        constructor
        rw [Measure.restrict_apply_univ]
        exact measure_ball_lt_top
      have hgphalf : IntegrableOn (fun x => ‖g x‖ ^ p) (Metric.ball x₀ (R / 2)) volume :=
        hgp.mono_set hhalfsub
      have hdphalf : ∀ m : ℕ, IntegrableOn (fun x => ‖ge m x - g x‖ ^ p)
          (Metric.ball x₀ (R / 2)) volume := fun m => (hdp m).mono_set hhalfsub
      -- the explicit bound on the mean of `(e_m + ‖g_m‖²)^{p/2}` over `B_{R/2}`
      obtain ⟨Em, hEmdef⟩ : ∃ s : ℕ → ℝ,
          s = fun m => ∫ x in Metric.ball x₀ R, ‖ge m x - g x‖ ^ p := ⟨_, rfl⟩
      have hEm0 : ∀ m : ℕ, 0 ≤ Em m := by
        intro m
        simp only [hEmdef]
        exact setIntegral_nonneg measurableSet_ball
          (fun y _ => Real.rpow_nonneg (norm_nonneg _) _)
      obtain ⟨Bm, hBmdef⟩ : ∃ s : ℕ → ℝ,
          s = fun m => 2 ^ (p - 1) * (em m) ^ (p / 2) * (ωn * (R / 2) ^ n)
            + 2 ^ (2 * p - 2) * ((ωn * (R / 2) ^ n) * S ^ p + Em m) := ⟨_, rfl⟩
      have hvol0 : (0:ℝ) ≤ ωn * (R / 2) ^ n := mul_nonneg hωn0 (by positivity)
      have hBm0 : ∀ m : ℕ, 0 ≤ Bm m := by
        intro m
        simp only [hBmdef]
        have t1 : (0:ℝ) ≤ 2 ^ (p - 1) * (em m) ^ (p / 2) * (ωn * (R / 2) ^ n) :=
          mul_nonneg (mul_nonneg h2p0.le (Real.rpow_nonneg (hem0 m).le _)) hvol0
        have t2 : (0:ℝ) ≤ 2 ^ (2 * p - 2) * ((ωn * (R / 2) ^ n) * S ^ p + Em m) := by
          refine mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le ?_
          have t3 : (0:ℝ) ≤ (ωn * (R / 2) ^ n) * S ^ p :=
            mul_nonneg hvol0 (Real.rpow_nonneg hS0 _)
          linarith [hEm0 m]
        linarith
      have hJB : ∀ m : ℕ,
          (∫ y in Metric.ball x₀ (R / 2), (em m + ‖ge m y‖ ^ 2) ^ (p / 2)) ≤ Bm m := by
        intro m
        have hAint : IntegrableOn (fun y : EuclideanSpace ℝ (Fin n) =>
            ‖g y‖ ^ p + ‖ge m y - g y‖ ^ p) (Metric.ball x₀ (R / 2)) volume :=
          hgphalf.add (hdphalf m)
        have hBint : IntegrableOn (fun y : EuclideanSpace ℝ (Fin n) =>
            2 ^ (2 * p - 2) * (‖g y‖ ^ p + ‖ge m y - g y‖ ^ p))
            (Metric.ball x₀ (R / 2)) volume := hAint.const_mul _
        have hCint : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) =>
            2 ^ (p - 1) * (em m) ^ (p / 2)) (Metric.ball x₀ (R / 2)) volume :=
          integrable_const _
        have hmaj : IntegrableOn
            (fun y => 2 ^ (p - 1) * (em m) ^ (p / 2)
              + 2 ^ (2 * p - 2) * (‖g y‖ ^ p + ‖ge m y - g y‖ ^ p))
            (Metric.ball x₀ (R / 2)) volume := hCint.add hBint
        have hptwise : ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ (R / 2))),
            (em m + ‖ge m y‖ ^ 2) ^ (p / 2)
              ≤ 2 ^ (p - 1) * (em m) ^ (p / 2)
                + 2 ^ (2 * p - 2) * (‖g y‖ ^ p + ‖ge m y - g y‖ ^ p) := by
          filter_upwards with y
          refine hpt (em m) ‖ge m y‖ ‖g y‖ ‖ge m y - g y‖ (hem0 m).le (norm_nonneg _)
            (norm_nonneg _) (norm_nonneg _) ?_
          have h := norm_add_le (g y) (ge m y - g y)
          simpa using h
        have hnn : (0 : EuclideanSpace ℝ (Fin n) → ℝ)
            ≤ᵐ[volume.restrict (Metric.ball x₀ (R / 2))]
            fun y => (em m + ‖ge m y‖ ^ 2) ^ (p / 2) := by
          filter_upwards with y
          exact Real.rpow_nonneg (add_nonneg (hem0 m).le (sq_nonneg _)) _
        have hmono := integral_mono_of_nonneg hnn hmaj hptwise
        have hcalc : (∫ y in Metric.ball x₀ (R / 2),
              (2 ^ (p - 1) * (em m) ^ (p / 2)
                + 2 ^ (2 * p - 2) * (‖g y‖ ^ p + ‖ge m y - g y‖ ^ p)))
            = 2 ^ (p - 1) * (em m) ^ (p / 2) * (ωn * (R / 2) ^ n)
              + 2 ^ (2 * p - 2) * ((∫ y in Metric.ball x₀ (R / 2), ‖g y‖ ^ p)
                + ∫ y in Metric.ball x₀ (R / 2), ‖ge m y - g y‖ ^ p) := by
          rw [integral_add hCint hBint, setIntegral_const, integral_const_mul,
            integral_add hgphalf (hdphalf m), measureReal_def, hVhalf, smul_eq_mul]
          ring
        have hgS : (∫ y in Metric.ball x₀ (R / 2), ‖g y‖ ^ p)
            ≤ (ωn * (R / 2) ^ n) * S ^ p := by
          have hb : ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ (R / 2))),
              ‖g y‖ ^ p ≤ S ^ p := by
            filter_upwards [ae_restrict_of_ae_restrict_of_subset hhalfsub hS] with y hy
            exact Real.rpow_le_rpow (norm_nonneg _) hy hp0
          have h := integral_mono_ae hgphalf (integrable_const (S ^ p)) hb
          rwa [setIntegral_const, measureReal_def, hVhalf, smul_eq_mul] at h
        have hdE : (∫ y in Metric.ball x₀ (R / 2), ‖ge m y - g y‖ ^ p) ≤ Em m := by
          simp only [hEmdef]
          refine setIntegral_mono_set (hdp m) ?_ ?_
          · filter_upwards with y
            exact Real.rpow_nonneg (norm_nonneg _) _
          · exact Filter.Eventually.of_forall (fun y hy => hhalfsub hy)
        simp only [hBmdef]
        rw [hcalc] at hmono
        have h2q : (0:ℝ) < 2 ^ (2 * p - 2) := Real.rpow_pos_of_pos (by norm_num) _
        have hb : (∫ y in Metric.ball x₀ (R / 2), ‖g y‖ ^ p)
            + (∫ y in Metric.ball x₀ (R / 2), ‖ge m y - g y‖ ^ p)
            ≤ (ωn * (R / 2) ^ n) * S ^ p + Em m := by linarith
        have hmul := mul_le_mul_of_nonneg_left hb h2q.le
        linarith
      -- `Um`: a uniform bound for `‖g_m‖` on `B_{R/4}`
      have hR2n : (0:ℝ) < (R / 2) ^ (n:ℝ) := Real.rpow_pos_of_pos hR2 _
      have hcoef0 : (0:ℝ) ≤ C₁ / (R / 2) ^ (n:ℝ) := div_nonneg hC₁0.le hR2n.le
      obtain ⟨Um, hUmdef⟩ : ∃ s : ℕ → ℝ,
          s = fun m => (C₁ / (R / 2) ^ (n:ℝ) * Bm m) ^ (1 / p) := ⟨_, rfl⟩
      have hUm0 : ∀ m : ℕ, 0 ≤ Um m := by
        intro m
        simp only [hUmdef]
        exact Real.rpow_nonneg (mul_nonneg hcoef0 (hBm0 m)) _
      have hgeUm : ∀ m : ℕ, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 4))),
          ‖ge m x‖ ≤ Um m := by
        intro m
        have hq : (R / 2 / 2 : ℝ) = R / 4 := by ring
        have h := hsupm m
        rw [hq] at h
        filter_upwards [h] with x hx
        have e1 : ‖ge m x‖ ^ p = (‖ge m x‖ ^ 2) ^ (p / 2) := by
          rw [← Real.rpow_natCast ‖ge m x‖ 2, ← Real.rpow_mul (norm_nonneg _)]
          congr 1
          push_cast
          ring
        have h1 : ‖ge m x‖ ^ p ≤ (em m + ‖ge m x‖ ^ 2) ^ (p / 2) := by
          rw [e1]
          exact Real.rpow_le_rpow (by positivity) (by linarith [(hem0 m).le])
            (by linarith)
        have h2 : (C₁ / (R / 2) ^ (n:ℝ)) * (∫ y in Metric.ball x₀ (R / 2),
            (em m + ‖ge m y‖ ^ 2) ^ (p / 2)) ≤ (C₁ / (R / 2) ^ (n:ℝ)) * Bm m :=
          mul_le_mul_of_nonneg_left (hJB m) hcoef0
        have h3 : ‖ge m x‖ ^ p ≤ C₁ / (R / 2) ^ (n:ℝ) * Bm m :=
          le_trans (le_trans h1 hx) h2
        simp only [hUmdef]
        have h4 : (‖ge m x‖ ^ p) ^ (1 / p)
            ≤ (C₁ / (R / 2) ^ (n:ℝ) * Bm m) ^ (1 / p) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) h3 (by positivity)
        rwa [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel (ne_of_gt hp0'),
          Real.rpow_one] at h4
      -- (B6′): apply (A2) at each level and pass to the limit
      have hρ4pos : (0:ℝ) < R / 4 := by linarith
      have hballρ4 : Metric.ball x₀ ρ ⊆ Metric.ball x₀ (R / 4) :=
        Metric.ball_subset_ball hρ4
      have hR4sub : Metric.ball x₀ (R / 4) ⊆ Metric.ball x₀ R :=
        Metric.ball_subset_ball (by linarith)
      obtain ⟨W, hWdef⟩ : ∃ s : ℕ → ℝ,
          s = fun m => Real.sqrt n * (16 * Um m * (ρ / (R / 4)) ^ α) := ⟨_, rfl⟩
      have hpair : ∀ m : ℕ, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ)),
          ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ ρ)),
            ‖ge m x - ge m y‖ ≤ W m := by
        intro m
        have hoscm : ∀ k : Fin n,
            EssOscOn n (Metric.ball x₀ ρ) (fun z => ge m z k)
              ≤ 16 * Um m * (ρ / (R / 4)) ^ α := by
          intro k
          refine hosc (em m) (c0 m) (c1 m) (Um m) (Metric.ball x₀ R) (Ae m) (ue m)
            (ge m) x₀ (R / 4) ρ k (hem0 m) (hc0 m) (hc1rp m) (hUm0 m)
            Metric.isOpen_ball hρ4pos hρ hρ4 ?_ (hAesol m) hR4sub (hgeUm m)
          exact hQrestrict (em m) (c0 m) (c1 m) (Ae m) Set.univ (Metric.ball x₀ R)
            (Set.subset_univ _) (hQe m)
        have hTb : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ ρ)), ‖ge m z‖ ≤ Um m :=
          ae_restrict_of_ae_restrict_of_subset hballρ4 (hgeUm m)
        have hD0 : (0:ℝ) ≤ 16 * Um m * (ρ / (R / 4)) ^ α := by
          have h := hUm0 m
          have h2 : (0:ℝ) ≤ (ρ / (R / 4)) ^ α :=
            Real.rpow_nonneg (by positivity) _
          have h3 : (0:ℝ) ≤ 16 * Um m := by linarith
          exact mul_nonneg h3 h2
        simp only [hWdef]
        exact hconv (ge m) (Um m) (16 * Um m * (ρ / (R / 4)) ^ α) hD0 hTb hoscm
      -- the limits
      have hemp : Filter.Tendsto (fun m => (em m) ^ (p / 2)) Filter.atTop (nhds 0) := by
        have h := hemlim.rpow_const (p := p / 2) (Or.inr (by positivity))
        rwa [Real.zero_rpow (by positivity)] at h
      have hElim : Filter.Tendsto Em Filter.atTop (nhds 0) := by
        simp only [hEmdef]; exact hAeconv
      have hBlim : Filter.Tendsto Bm Filter.atTop
          (nhds (2 ^ (2 * p - 2) * ((ωn * (R / 2) ^ n) * S ^ p))) := by
        simp only [hBmdef]
        have h1 : Filter.Tendsto
            (fun m => 2 ^ (p - 1) * (em m) ^ (p / 2) * (ωn * (R / 2) ^ n))
            Filter.atTop (nhds 0) := by
          have h := (hemp.const_mul (2 ^ (p - 1) : ℝ)).mul_const (ωn * (R / 2) ^ n)
          rw [mul_zero, zero_mul] at h
          exact h
        have h2 : Filter.Tendsto
            (fun m => 2 ^ (2 * p - 2) * ((ωn * (R / 2) ^ n) * S ^ p + Em m))
            Filter.atTop (nhds (2 ^ (2 * p - 2) * ((ωn * (R / 2) ^ n) * S ^ p))) := by
          have h := (Filter.Tendsto.const_add ((ωn * (R / 2) ^ n) * S ^ p)
            hElim).const_mul (2 ^ (2 * p - 2) : ℝ)
          rw [add_zero] at h
          exact h
        have h := h1.add h2
        rw [zero_add] at h
        exact h
      have hUlim : Filter.Tendsto Um Filter.atTop
          (nhds ((C₁ / (R / 2) ^ (n:ℝ) *
            (2 ^ (2 * p - 2) * ((ωn * (R / 2) ^ n) * S ^ p))) ^ (1 / p))) := by
        simp only [hUmdef]
        exact (hBlim.const_mul (C₁ / (R / 2) ^ (n:ℝ))).rpow_const
          (Or.inr (by positivity))
      have hWlim : Filter.Tendsto W Filter.atTop
          (nhds (Real.sqrt n * (16 * ((C₁ / (R / 2) ^ (n:ℝ) *
            (2 ^ (2 * p - 2) * ((ωn * (R / 2) ^ n) * S ^ p))) ^ (1 / p))
              * (ρ / (R / 4)) ^ α))) := by
        simp only [hWdef]
        exact ((hUlim.const_mul (16:ℝ)).mul_const _).const_mul (Real.sqrt n)
      -- the limiting bound is at most `C S (ρ/R)^α`
      have hκ0 : (0:ℝ) ≤ κ := by
        rw [hκ]
        refine Real.rpow_nonneg ?_ _
        exact mul_nonneg (mul_nonneg (mul_nonneg hC₁0.le
          (Real.rpow_pos_of_pos (by norm_num) _).le) hωn0)
          (Real.rpow_pos_of_pos (by norm_num) _).le
      have hκ' : (C₁ / (R / 2) ^ (n:ℝ) *
          (2 ^ (2 * p - 2) * ((ωn * (R / 2) ^ n) * S ^ p))) ^ (1 / p) ≤ κ * S := by
        have hbase : C₁ / (R / 2) ^ (n:ℝ)
              * (2 ^ (2 * p - 2) * ((ωn * (R / 2) ^ n) * S ^ p))
            = (C₁ * 2 ^ (2 * p - 2) * ωn) * S ^ p := by
          rw [Real.rpow_natCast (R / 2) n]
          have hne : ((R / 2) ^ n : ℝ) ≠ 0 := by positivity
          field_simp
        have hA0 : (0:ℝ) ≤ C₁ * 2 ^ (2 * p - 2) * ωn :=
          mul_nonneg (mul_nonneg hC₁0.le
            (Real.rpow_pos_of_pos (by norm_num) _).le) hωn0
        have hSp0 : (0:ℝ) ≤ S ^ p := Real.rpow_nonneg hS0 _
        have hsplit : ((C₁ * 2 ^ (2 * p - 2) * ωn) * S ^ p) ^ (1 / p)
            = (C₁ * 2 ^ (2 * p - 2) * ωn) ^ (1 / p) * S := by
          rw [Real.mul_rpow hA0 hSp0, ← Real.rpow_mul hS0,
            mul_one_div_cancel (ne_of_gt hp0'), Real.rpow_one]
        have h2n : (1:ℝ) ≤ 2 ^ (n:ℝ) := by
          have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
            (by positivity : (0:ℝ) ≤ (n:ℝ))
          rwa [Real.rpow_zero] at h
        have hmono2 : C₁ * 2 ^ (2 * p - 2) * ωn
            ≤ C₁ * 2 ^ (2 * p - 2) * ωn * 2 ^ (n:ℝ) := by
          nlinarith only [hA0, h2n]
        have hκle : (C₁ * 2 ^ (2 * p - 2) * ωn) ^ (1 / p) ≤ κ := by
          rw [hκ]
          exact Real.rpow_le_rpow hA0 hmono2 (by positivity)
        rw [hbase, hsplit]
        exact mul_le_mul_of_nonneg_right hκle hS0
      have hDle : (ρ / (R / 4)) ^ α ≤ 4 * (ρ / R) ^ α := by
        have hdpos : (0:ℝ) < ρ / R := div_pos hρ hR
        have he : ρ / (R / 4) = 4 * (ρ / R) := by
          field_simp
        rw [he, Real.mul_rpow (by norm_num) hdpos.le]
        have h4 : (4:ℝ) ^ α ≤ 4 := by
          have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) hα1
          rwa [Real.rpow_one] at h
        exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hdpos.le _)
      have hD40 : (0:ℝ) ≤ (ρ / (R / 4)) ^ α := Real.rpow_nonneg (by positivity) _
      have hfinal : Real.sqrt n * (16 * ((C₁ / (R / 2) ^ (n:ℝ) *
          (2 ^ (2 * p - 2) * ((ωn * (R / 2) ^ n) * S ^ p))) ^ (1 / p))
            * (ρ / (R / 4)) ^ α) ≤ C * S * (ρ / R) ^ α := by
        have hκS0 : (0:ℝ) ≤ κ * S := mul_nonneg hκ0 hS0
        have hstep : 16 * ((C₁ / (R / 2) ^ (n:ℝ) *
            (2 ^ (2 * p - 2) * ((ωn * (R / 2) ^ n) * S ^ p))) ^ (1 / p))
              * (ρ / (R / 4)) ^ α ≤ 16 * (κ * S) * (4 * (ρ / R) ^ α) := by
          refine mul_le_mul ?_ hDle hD40 (by linarith only [hκS0])
          linarith only [hκ']
        have h1 := mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg (n:ℝ))
        have h2 : Real.sqrt n * (16 * (κ * S) * (4 * (ρ / R) ^ α))
            = (64 * Real.sqrt n * κ) * S * (ρ / R) ^ α := by ring
        rw [h2] at h1
        have h3 : (64 * Real.sqrt n * κ) * S * (ρ / R) ^ α ≤ C * S * (ρ / R) ^ α :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC64 hS0) hpow
        linarith only [h1, h3]
      -- pass to the limit along the approximating sequence
      have hgeaeρ : ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ ρ)),
          Filter.Tendsto (fun m => ge m y) Filter.atTop (nhds (g y)) :=
        ae_restrict_of_ae_restrict_of_subset (hballρ4.trans hR4sub) hgeae
      have hcomb : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ)),
          (∀ m : ℕ, ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ ρ)),
              ‖ge m x - ge m y‖ ≤ W m)
            ∧ Filter.Tendsto (fun m => ge m x) Filter.atTop (nhds (g x)) := by
        refine Filter.Eventually.and ?_ hgeaeρ
        rw [ae_all_iff]
        exact hpair
      filter_upwards [hcomb] with x hx
      have hyall : ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ ρ)), ∀ m : ℕ,
          ‖ge m x - ge m y‖ ≤ W m := by
        rw [ae_all_iff]
        exact hx.1
      filter_upwards [hyall, hgeaeρ] with y hy1 hy2
      have hnormlim : Filter.Tendsto (fun m => ‖ge m x - ge m y‖) Filter.atTop
          (nhds ‖g x - g y‖) := (hx.2.sub hy2).norm
      have hle := le_of_tendsto_of_tendsto' hnormlim hWlim hy1
      linarith only [hle, hfinal]
    · -- the outer range `R/4 < ρ ≤ R`, where the trivial bound suffices
      have hballρR : Metric.ball x₀ ρ ⊆ Metric.ball x₀ R := Metric.ball_subset_ball hρR
      have hSρ : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ ρ)), ‖g z‖ ≤ S :=
        ae_restrict_of_ae_restrict_of_subset hballρR hS
      have hquart : (1:ℝ) / 4 < (ρ / R) ^ α := by
        have h1 : (0:ℝ) < ρ / R := div_pos hρ hR
        have h2 : ρ / R ≤ 1 := by
          rw [div_le_one hR]; exact hρR
        have h3 : (ρ / R) ^ (1:ℝ) ≤ (ρ / R) ^ α :=
          Real.rpow_le_rpow_of_exponent_ge h1 h2 hα1
        rw [Real.rpow_one] at h3
        have h4 : (1:ℝ) / 4 < ρ / R := by
          rw [lt_div_iff₀ hR]
          linarith only [hρ4]
        linarith only [h3, h4]
      filter_upwards [hSρ] with x hx
      filter_upwards [hSρ] with y hy
      have h5 : ‖g x - g y‖ ≤ 2 * S := by
        have h7 := norm_sub_le (g x) (g y)
        linarith only [h7, hx, hy]
      have ht0 : (0:ℝ) ≤ (ρ / R) ^ α := le_of_lt (lt_trans (by norm_num) hquart)
      have h6 : (0:ℝ) ≤ S * (4 * ((ρ / R) ^ α) - 1) :=
        mul_nonneg hS0 (by linarith only [hquart])
      have hstep1 : 2 * S ≤ 8 * S * ((ρ / R) ^ α) := by nlinarith only [h6]
      have hstep2 : 8 * S * ((ρ / R) ^ α) ≤ C * S * ((ρ / R) ^ α) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC8 hS0) ht0
      linarith only [h5, hstep1, hstep2]
