import ManfrediThesis.Preamble
import ManfrediThesis.SignedPowerRegularisedPair
import ManfrediThesis.SignedPowerLevelTransportCore
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.DifferentiatedEquationWeak
import ManfrediThesis.WeakGradientC1Comp
import ManfrediThesis.WeakGradientPositivePart
import ManfrediThesis.WeakGradientSmoothMul
import ManfrediThesis.WeakGradientLinear
import ManfrediThesis.WeakGradientRestrict
import ManfrediThesis.StandardRadialCutoff
import ManfrediThesis.RegularisedSignedPowerCaccioppoli
import ManfrediThesis.SignedPowerMemW12OnInnerBall
import ManfrediThesis.RegularisedCaccioppoliEtaLimit
set_option maxHeartbeats 800000
open MeasureTheory

/-- The subquadratic half of the signed-power estimate: for `1 < p < 2` the
function `v = |D_k u|^{p/2-1} D_k u` lies in `W^{1,2}` of every smaller ball
with the weak gradient `(p/2)|D_k u|^{p/2-1} D(D_k u)`, and it satisfies the
paper's inequality (3.12) on both sides.  The exponent restriction is not a
convenience: for `1 < p < 2` the map `s ↦ |s|^{p/2-1} s` is not `C¹` at `0`, so
the chain rule is unavailable and the thesis' `η`-regularisation is run instead,
through a different auxiliary function, a different source inequality and a
different producer node.  The `p ≥ 2` half is proved directly in
`SignedPowerGradientEstimate`, which is where the two halves are joined. -/
theorem SignedPowerGradientEstimateSubquadratic :
    ∀ (n : ℕ) (p r : ℝ), 2 ≤ n → 1 < p → p < 2 → 0 < r →
      ∃ C : ℝ, 0 < C ∧
        ∀ (ε γ₀ γ₁ μ : ℝ)
          (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ) (k : Fin n),
          0 < ε → 0 < γ₀ → γ₁ ≤ r * γ₀ → 0 < R → 0 < μ → ε < (μ / 2) ^ 2 →
          EllipticStructureQ12 n p ε γ₀ γ₁ (Metric.ball x₀ R) (fun _ _ h => A h) →
          CitedRegularityEpsPos n p ε γ₀ γ₁ (Metric.ball x₀ R) A →
          IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h)
            (fun _ _ _ => 0) u g →
          (∀ i : Fin n, MemW1pLocOn n 2 (Metric.ball x₀ R) (fun x => g x i) (Dg i)) →
          (∀ i : Fin n, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), |g x i| ≤ μ) →
          (∀ T : ℝ, 0 < T → T < R →
              MemW1pOn n 2 (Metric.ball x₀ T)
                (fun x => |g x k| ^ (p / 2 - 1) * g x k)
                (fun x => (p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x))
            ∧ (∀ ρ σ h : ℝ, 0 < ρ → ρ ≤ R → 0 < σ → σ < 1 →
              (-((μ / 2) ^ (p / 2)) ≤ h →
                  (∫ x in Metric.ball x₀ (ρ - σ * ρ)
                      ∩ {y | h < |g y k| ^ (p / 2 - 1) * g y k},
                      ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
                    ≤ C * ((μ / 2) ^ (p / 2)) ^ 2 / (σ * ρ) ^ 2
                      * (volume (Metric.ball x₀ ρ
                          ∩ {y | h < |g y k| ^ (p / 2 - 1) * g y k})).toReal)
                ∧ (h ≤ (μ / 2) ^ (p / 2) →
                  (∫ x in Metric.ball x₀ (ρ - σ * ρ)
                      ∩ {y | |g y k| ^ (p / 2 - 1) * g y k < h},
                      ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
                    ≤ C * ((μ / 2) ^ (p / 2)) ^ 2 / (σ * ρ) ^ 2
                      * (volume (Metric.ball x₀ ρ
                          ∩ {y | |g y k| ^ (p / 2 - 1) * g y k < h})).toReal)) := by
  intro n p r hn hp hp2 hr
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hp0 : (0:ℝ) < p := by linarith
  have hp10 : (0:ℝ) < p - 1 := by linarith
  -- the radial cut-off, with its absolute constant
  obtain ⟨Lc, hLc0, hcutN⟩ := StandardRadialCutoff n hn1
  -- negative exponents, this being the subquadratic regime
  have hexpn : p / 2 - 1 < 0 := by linarith
  have hp2n : p - 2 < 0 := by linarith
  -- the constant `C`
  obtain ⟨C₁, hC₁def⟩ : ∃ t : ℝ, t = 2 / p * (2:ℝ) ^ (1 - p / 2) := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂def⟩ : ∃ t : ℝ,
    t = (2 * (n:ℝ) * r * C₁ * p ^ 2 / (4 * (p - 1))) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Cb, hCbdef⟩ : ∃ t : ℝ,
    t = C₂ * (1 + (2:ℝ) ^ (p - 1)) ^ 2 * (1 + 4 * (n:ℝ)) ^ (1 - p / 2)
        * Lc := ⟨_, rfl⟩
  refine ⟨max 1 Cb, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro ε γ₀ γ₁ μ A u g Dg x₀ R k hε hγ₀ hγ₁ hR hμ hεμ hQ hC1 hsol hDg hbd
  obtain ⟨lam, hlamdef⟩ : ∃ t : ℝ, t = μ / 2 := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlamdef]; linarith
  have hεlam : ε < lam ^ 2 := by rw [hlamdef]; exact hεμ
  -- (A4) the radial cut-off at this centre
  have hcut : ∀ ρ₀ ρ₁ : ℝ, 0 < ρ₀ → ρ₀ < ρ₁ →
      ∃ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ (⊤:ℕ∞) ζ ∧ HasCompactSupport ζ ∧
        tsupport ζ ⊆ Metric.ball x₀ ρ₁ ∧
        (∀ x, 0 ≤ ζ x) ∧ (∀ x, ζ x ≤ 1) ∧
        (∀ x ∈ Metric.closedBall x₀ ρ₀, ζ x = 1) ∧
        (∀ x, ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2
            ≤ Lc / (ρ₁ - ρ₀) ^ 2) :=
    fun ρ₀ ρ₁ h1 h2 => hcutN x₀ ρ₀ ρ₁ h1 h2
  -- (A1) the two-sided bound on `w`
  have hbdall : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), ∀ i : Fin n, |g x i| ≤ μ :=
    ae_all_iff.2 hbd
  have hwup : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      ε + ‖g x‖ ^ 2 ≤ (1 + 4 * (n:ℝ)) * lam ^ 2 := by
    filter_upwards [hbdall] with x hx
    have hsq : ‖g x‖ ^ 2 ≤ 4 * (n:ℝ) * lam ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      have hterm : ∀ i : Fin n, (g x i) ^ 2 ≤ 4 * lam ^ 2 := by
        intro i
        have h1 := hx i
        rw [hlamdef]
        nlinarith [abs_nonneg (g x i), sq_abs (g x i)]
      calc ∑ i, (g x i) ^ 2 ≤ ∑ _i : Fin n, 4 * lam ^ 2 :=
            Finset.sum_le_sum fun i _ => hterm i
        _ = 4 * (n:ℝ) * lam ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            simp [nsmul_eq_mul]
            ring
    linarith
  have hwlow : ∀ x : EuclideanSpace ℝ (Fin n), ε ≤ ε + ‖g x‖ ^ 2 := by
    intro x
    have := sq_nonneg ‖g x‖
    linarith
  -- (A2) `γ₀ ≤ γ₁`
  have hNBR : Filter.NeBot (ae (volume.restrict (Metric.ball x₀ R))) := by
    rw [ae_neBot]
    intro hcc
    rw [← Measure.measure_univ_eq_zero, Measure.restrict_apply_univ] at hcc
    exact (Metric.measure_ball_pos volume x₀ hR).ne' hcc
  have hγ01 : γ₀ ≤ γ₁ := by
    have hmem : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
        x ∈ Metric.ball x₀ R := ae_restrict_mem Metric.isOpen_ball.measurableSet
    have hQ1 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), x ∈ Metric.ball x₀ R →
        ∀ (z : ℝ) (h ξ : EuclideanSpace ℝ (Fin n)), ε + ‖h‖ ^ 2 ≠ 0 →
          γ₀ * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖ξ‖ ^ 2
            ≤ ∑ i, (fderiv ℝ (fun h' => A h') h ξ) i * ξ i :=
      ae_restrict_of_ae hQ.Q1
    have hQ2 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), x ∈ Metric.ball x₀ R →
        ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)) (i j : Fin n), ε + ‖h‖ ^ 2 ≠ 0 →
          |(fderiv ℝ (fun h' => A h') h (EuclideanSpace.single j (1 : ℝ))) i|
            ≤ γ₁ * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) :=
      ae_restrict_of_ae hQ.Q2
    obtain ⟨x, hxx⟩ := ((hQ1.and hQ2).and hmem).exists
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hxx
    have hguard : ε + ‖(0 : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≠ 0 := by
      simp only [norm_zero]
      norm_num
      linarith
    obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, lt_of_lt_of_le (by norm_num) hn⟩⟩
    have he1 : ‖(EuclideanSpace.single i₀ (1:ℝ) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      simp
    have h1 := hx1 hx3 0 0 (EuclideanSpace.single i₀ (1:ℝ)) hguard
    have h2 := hx2 hx3 0 0 i₀ i₀ hguard
    rw [he1] at h1
    have hsum : ∑ i, (fderiv ℝ (fun h' => A h') 0
          (EuclideanSpace.single i₀ (1:ℝ))) i * (EuclideanSpace.single i₀ (1:ℝ) : EuclideanSpace ℝ (Fin n)) i
        = (fderiv ℝ (fun h' => A h') 0 (EuclideanSpace.single i₀ (1:ℝ))) i₀ := by
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hb
        exact absurd (Finset.mem_univ i₀) hb
    rw [hsum] at h1
    have hw0 : (0:ℝ) < (ε + ‖(0 : EuclideanSpace ℝ (Fin n))‖ ^ 2) ^ (p / 2 - 1) := by
      simp only [norm_zero]
      have : ε + (0:ℝ) ^ 2 = ε := by ring
      rw [this]
      exact Real.rpow_pos_of_pos hε _
    have habs := le_trans (le_abs_self _) h2
    simp only [norm_zero] at h1 habs hw0 ⊢
    nlinarith [h1, habs, hw0]
  -- (A3) localisation
  have hloc : ∀ T : ℝ, 0 < T → T < R →
      MemW1pOn n 2 (Metric.ball x₀ T) (fun x => g x k) (Dg k) := by
    intro T hT hTR
    have hcl : closure (Metric.ball x₀ T) ⊆ Metric.ball x₀ R := by
      refine subset_trans Metric.closure_ball_subset_closedBall ?_
      exact Metric.closedBall_subset_ball hTR
    have hcpt : IsCompact (closure (Metric.ball x₀ T)) := by
      refine IsCompact.of_isClosed_subset (isCompact_closedBall x₀ T) isClosed_closure ?_
      exact Metric.closure_ball_subset_closedBall
    exact (WeakGradientRestrict n 2 hn1 (by norm_num) (Metric.ball x₀ R)
      (Metric.ball x₀ T) (fun x => g x k) (Dg k) Metric.isOpen_ball
      Metric.isOpen_ball (Metric.ball_subset_ball hTR.le)).2.2.2 (hDg k) hcpt hcl
  -- Step B: the level correspondence, for the whole family `Φ_a(s) = |s|^{a-1} s`
  -- (`a = p/2` gives `v`, `a = p-1` gives `ψ`)
  obtain ⟨Phi, hPhidef⟩ : ∃ F : ℝ → ℝ → ℝ,
    F = fun a s => |s| ^ (a - 1) * s := ⟨_, rfl⟩
  have hPhi0 : ∀ a : ℝ, Phi a 0 = 0 := by
    intro a; rw [hPhidef]; simp
  have hPhineg : ∀ a s : ℝ, Phi a (-s) = -Phi a s := by
    intro a s; rw [hPhidef]; simp [abs_neg]
  have hPhipos : ∀ a s : ℝ, 0 < s → Phi a s = s ^ a := by
    intro a s hs
    rw [hPhidef]
    show |s| ^ (a - 1) * s = s ^ a
    simp only [abs_of_pos hs]
    calc s ^ (a - 1) * s = s ^ (a - 1) * s ^ (1:ℝ) := by rw [Real.rpow_one]
      _ = s ^ (a - 1 + 1) := (Real.rpow_add hs _ _).symm
      _ = s ^ a := by ring_nf
  have hPhimono : ∀ a : ℝ, 0 < a → StrictMono (Phi a) := by
    intro a ha
    have hposmono : ∀ b c : ℝ, 0 < b → b < c → Phi a b < Phi a c := by
      intro b c hb hbc
      rw [hPhipos a b hb, hPhipos a c (lt_trans hb hbc)]
      exact Real.rpow_lt_rpow hb.le hbc ha
    have hposval : ∀ b : ℝ, 0 < b → 0 < Phi a b := by
      intro b hb; rw [hPhipos a b hb]; exact Real.rpow_pos_of_pos hb _
    intro b c hbc
    rcases lt_trichotomy b 0 with hb | hb | hb
    · rcases lt_trichotomy c 0 with hc | hc | hc
      · have h1 : Phi a (-c) < Phi a (-b) :=
          hposmono (-c) (-b) (by linarith only [hc]) (by linarith only [hbc])
        rw [hPhineg, hPhineg] at h1
        linarith only [h1]
      · rw [hc, hPhi0]
        have h2 : 0 < Phi a (-b) := hposval (-b) (by linarith only [hb])
        rw [hPhineg] at h2
        linarith only [h2]
      · have h1 : 0 < Phi a (-b) := hposval (-b) (by linarith only [hb])
        have h2 : 0 < Phi a c := hposval c hc
        rw [hPhineg] at h1
        linarith only [h1, h2]
    · rw [hb, hPhi0]
      exact hposval c (by linarith only [hbc, hb])
    · exact hposmono b c hb hbc
  have hPhiinv : ∀ a : ℝ, 0 < a → ∀ t : ℝ, Phi a (Phi a⁻¹ t) = t := by
    intro a ha t
    rcases lt_trichotomy t 0 with ht | ht | ht
    · have hpp : (0:ℝ) < -t := by linarith only [ht]
      have h1 : Phi a (Phi a⁻¹ (-t)) = -t := by
        rw [hPhipos a⁻¹ (-t) hpp,
          hPhipos a _ (Real.rpow_pos_of_pos hpp _), ← Real.rpow_mul hpp.le,
          inv_mul_cancel₀ (ne_of_gt ha), Real.rpow_one]
      rw [hPhineg, hPhineg] at h1
      linarith only [h1]
    · rw [ht]
      simp [hPhi0]
    · rw [hPhipos a⁻¹ t ht, hPhipos a _ (Real.rpow_pos_of_pos ht _),
        ← Real.rpow_mul ht.le, inv_mul_cancel₀ (ne_of_gt ha), Real.rpow_one]
  -- the transport of `MemW1pOn` across an a.e. identity of pairs
  have htransport : ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
      (f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ)
      (G₁ G₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      MemW1pOn n 2 Ω f₁ G₁ →
      (∀ᵐ x ∂(volume.restrict Ω), f₁ x = f₂ x) →
      (∀ᵐ x ∂(volume.restrict Ω), G₁ x = G₂ x) →
      MemW1pOn n 2 Ω f₂ G₂ := by
    intro Ω f₁ f₂ G₁ G₂ hmem hf hG
    refine ⟨?_, hmem.2.1.ae_eq hf, hmem.2.2.ae_eq hG⟩
    intro ϕ hϕ1 hϕ2 hϕ3 i
    have e1 : (∫ x in Ω, f₂ x * fderiv ℝ ϕ x (EuclideanSpace.single i (1:ℝ)))
        = ∫ x in Ω, f₁ x * fderiv ℝ ϕ x (EuclideanSpace.single i (1:ℝ)) := by
      refine integral_congr_ae ?_
      filter_upwards [hf] with x hx
      rw [hx]
    have e2 : (∫ x in Ω, G₂ x i * ϕ x) = ∫ x in Ω, G₁ x i * ϕ x := by
      refine integral_congr_ae ?_
      filter_upwards [hG] with x hx
      rw [hx]
    rw [e1, e2]
    exact hmem.1 ϕ hϕ1 hϕ2 hϕ3 i
  -- Step D (D.1)-(D.2): the regularised pair `π_η`, `G_η`
  obtain ⟨Dpi, pie, Gee, DG, hpiedef, hGeedef, hDGdef, hbase, hDpilow, hDpibd,
    hDpicont, hpieC1, hpiederiv, hDGbd, hGeederiv, hGeeC1⟩ :=
    SignedPowerRegularisedPair p hp hexpn hp2n
  -- (D.2): the two memberships
  have hpsiW : ∀ (η : ℝ), 0 < η → ∀ T : ℝ, 0 < T → T < R →
      MemW1pOn n 2 (Metric.ball x₀ T) (fun x => pie η (g x k))
        (fun x => Dpi η (g x k) • Dg k x) := by
    intro η hη T hT hTR
    have hcomp := WeakGradientC1Comp n 2 (η ^ (p - 2)) hn1 (by norm_num)
      (Real.rpow_nonneg hη.le _) (Metric.ball x₀ T) (fun x => g x k) (Dg k)
      (pie η) Metric.isOpen_ball measure_ball_lt_top.ne (hloc T hT hTR)
      (hpieC1 η hη) (by rw [hpiederiv η hη]; exact hDpibd η hη)
    refine htransport _ _ _ _ _ hcomp (Filter.Eventually.of_forall fun x => rfl) ?_
    filter_upwards with x
    rw [hpiederiv η hη]
  have hveeW : ∀ (η : ℝ), 0 < η → ∀ T : ℝ, 0 < T → T < R →
      MemW1pOn n 2 (Metric.ball x₀ T) (fun x => Gee η (g x k))
        (fun x => (p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x) := by
    intro η hη T hT hTR
    have hcomp := WeakGradientC1Comp n 2 (p / 2 * η ^ (p / 2 - 1)) hn1 (by norm_num)
      (by positivity) (Metric.ball x₀ T) (fun x => g x k) (Dg k)
      (Gee η) Metric.isOpen_ball measure_ball_lt_top.ne (hloc T hT hTR)
      (hGeeC1 η hη) (by rw [hGeederiv η hη]; exact hDGbd η hη)
    refine htransport _ _ _ _ _ hcomp (Filter.Eventually.of_forall fun x => rfl) ?_
    filter_upwards with x
    rw [hGeederiv η hη, hDGdef]
  -- (D.0) The exhaustion of `B_R` by compact closed balls.  It carries the
  -- global measurability of `g^k` and of `Dg^k` on `B_R` -- `MemW1pLocOn` only
  -- offers them on compact subsets -- and it is the countable exhaustion that
  -- (D5) needs to pass `Dg^k = 0` a.e. on `{g^k = 0}` from each `B_T` to `B_R`.
  have hballU : Metric.ball x₀ R
      = ⋃ m : ℕ, Metric.closedBall x₀ (R - R / (m + 2)) := by
    ext z
    constructor
    · intro hz
      have hd : dist z x₀ < R := Metric.mem_ball.1 hz
      have h1 : (0:ℝ) < R - dist z x₀ := by linarith only [hd]
      obtain ⟨m, hm⟩ := exists_nat_gt (R / (R - dist z x₀))
      have h2 : (0:ℝ) < (m:ℝ) + 2 := by positivity
      have h3 : R / (R - dist z x₀) < (m:ℝ) + 2 := by linarith only [hm]
      rw [div_lt_iff₀ h1] at h3
      refine Set.mem_iUnion.2 ⟨m, Metric.mem_closedBall.2 ?_⟩
      have h4 : R / ((m:ℝ) + 2) ≤ R - dist z x₀ := by
        rw [div_le_iff₀ h2]
        nlinarith only [h3]
      linarith only [h4]
    · intro hz
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hz
      have h2 : (0:ℝ) < (m:ℝ) + 2 := by positivity
      have h5 : 0 < R / ((m:ℝ) + 2) := by positivity
      exact Metric.mem_ball.2
        (lt_of_le_of_lt (Metric.mem_closedBall.1 hm) (by linarith only [h5]))
  have hcbcpt : ∀ m : ℕ, IsCompact (Metric.closedBall x₀ (R - R / (m + 2))) :=
    fun m => isCompact_closedBall _ _
  have hcbsub : ∀ m : ℕ,
      Metric.closedBall x₀ (R - R / (m + 2)) ⊆ Metric.ball x₀ R := by
    intro m
    rw [hballU]
    exact Set.subset_iUnion
      (fun j : ℕ => Metric.closedBall x₀ (R - R / ((j:ℝ) + 2))) m
  have hgmRi : ∀ i : Fin n, AEStronglyMeasurable (fun x => g x i)
      (volume.restrict (Metric.ball x₀ R)) := by
    intro i
    rw [hballU]
    exact aestronglyMeasurable_iUnion_iff.2 fun m =>
      (((hDg i).2 _ (hcbcpt m) (hcbsub m)).1).1
  have hgmR : AEStronglyMeasurable (fun x => g x k)
      (volume.restrict (Metric.ball x₀ R)) := hgmRi k
  have hDgmR : AEStronglyMeasurable (Dg k)
      (volume.restrict (Metric.ball x₀ R)) := by
    rw [hballU]
    exact aestronglyMeasurable_iUnion_iff.2 fun m =>
      (((hDg k).2 _ (hcbcpt m) (hcbsub m)).2).1
  -- (D3)+(D4): inequality (D.5), the Caccioppoli estimate at the regularisation
  -- level `η`, for an ARBITRARY level `ℓ` and an ARBITRARY cut-off `ζ`.  BOTH
  -- conclusions are derived from it below -- (D5) for conclusion (1) and (D6)
  -- for inequality (3.17) -- so it is stated once, above both.  It is
  -- `RegularisedSignedPowerCaccioppoli`, whose docstring records the route (the
  -- `CaccioppoliLevelWeight` (3.4) skeleton with three named changes) and the
  -- discharges of REVIEWER ELISIONS (1)-(3).
  have hD5 := RegularisedSignedPowerCaccioppoli n p r hn hp hp2 hr C₁ C₂ hC₁def
    hC₂def Dpi pie hbase hDpilow hDpibd hDpicont hpieC1 ε γ₀ γ₁ A u g Dg x₀ R k
    hε hγ₀ hγ₁ hγ01 hR hQ hC1 hsol hDg htransport hpsiW
  -- (D.6a) The regularisation sequence `η_j ↓ 0` with `η_j² < ε`, the pointwise
  -- limit `ψ_{η_j} → ψ` it carries and the uniform bound on `ψ_η`.
  have hpieval : ∀ η s : ℝ, pie η s = (|s| + η) ^ (p - 2) * s := by
    intro η s; simp only [hpiedef]
  obtain ⟨e0, he0def⟩ : ∃ t : ℝ, t = min 1 (Real.sqrt ε / 2) := ⟨_, rfl⟩
  have he00 : 0 < e0 := by
    rw [he0def]; exact lt_min one_pos (half_pos (Real.sqrt_pos.2 hε))
  have he0ε : e0 ^ 2 < ε := by
    have h1 : e0 ≤ Real.sqrt ε / 2 := by rw [he0def]; exact min_le_right _ _
    have h2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
    nlinarith only [h1, he00, h2, hε]
  obtain ⟨ηs, hηsdef⟩ : ∃ f : ℕ → ℝ, f = fun j : ℕ => e0 / ((j:ℝ) + 1) := ⟨_, rfl⟩
  have hηsval : ∀ j : ℕ, ηs j = e0 / ((j:ℝ) + 1) := by
    intro j; simp only [hηsdef]
  have hηs0 : ∀ j : ℕ, 0 < ηs j := by
    intro j
    rw [hηsval j]
    have h1 : (0:ℝ) < (j:ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) j; linarith only [this]
    exact div_pos he00 h1
  have hηsε : ∀ j : ℕ, (ηs j) ^ 2 < ε := by
    intro j
    have h1 : (1:ℝ) ≤ (j:ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) j; linarith only [this]
    have h2 : ηs j ≤ e0 := by rw [hηsval j]; exact div_le_self he00.le h1
    have h3 := hηs0 j
    nlinarith only [h2, h3, he0ε, he00]
  have hηt : Filter.Tendsto ηs Filter.atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul e0
    rw [mul_zero] at h
    refine Filter.Tendsto.congr (fun j => ?_) h
    rw [hηsval j, mul_one_div]
  have hpielim : ∀ t : ℝ, Filter.Tendsto (fun j : ℕ => pie (ηs j) t) Filter.atTop
      (nhds (|t| ^ (p - 2) * t)) := by
    intro t
    rcases eq_or_ne t 0 with h0 | h0
    · subst h0
      refine Filter.Tendsto.congr (fun j => ?_) (tendsto_const_nhds
        (x := |(0:ℝ)| ^ (p - 2) * 0) (f := (Filter.atTop : Filter ℕ)))
      rw [hpieval (ηs j) 0]; ring
    · have hta : |t| ≠ 0 := abs_ne_zero.2 h0
      have hc : ContinuousAt (fun s : ℝ => s ^ (p - 2)) |t| :=
        Real.continuousAt_rpow_const _ _ (Or.inl hta)
      have h1 : Filter.Tendsto (fun j : ℕ => |t| + ηs j) Filter.atTop (nhds |t|) := by
        have h2 := (tendsto_const_nhds (x := |t|)
          (f := (Filter.atTop : Filter ℕ))).add hηt
        simpa using h2
      refine Filter.Tendsto.congr (fun j => ?_) ((hc.tendsto.comp h1).mul_const t)
      simp only [Function.comp_apply, hpieval]
  have hpieabs : ∀ (η : ℝ), 0 < η → ∀ t : ℝ, |pie η t| ≤ |t| ^ (p - 1) := by
    intro η hη t
    rcases eq_or_ne t 0 with h0 | h0
    · subst h0
      have hz : pie η (0:ℝ) = 0 := by rw [hpieval η 0]; ring
      rw [hz, abs_zero]
      exact Real.rpow_nonneg le_rfl _
    · have hta : 0 < |t| := abs_pos.2 h0
      have h1 : |pie η t| = (|t| + η) ^ (p - 2) * |t| := by
        rw [hpieval η t, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (hbase η hη t).le _)]
      have h2 : (|t| + η) ^ (p - 2) ≤ |t| ^ (p - 2) :=
        Real.rpow_le_rpow_of_nonpos hta (by linarith only [hη]) hp2n.le
      have h3 : |t| ^ (p - 2) * |t| = |t| ^ (p - 1) := by
        rw [show (p:ℝ) - 1 = (p - 2) + 1 by ring,
          Real.rpow_add_one (ne_of_gt hta)]
      calc |pie η t| = (|t| + η) ^ (p - 2) * |t| := h1
        _ ≤ |t| ^ (p - 2) * |t| := mul_le_mul_of_nonneg_right h2 hta.le
        _ = |t| ^ (p - 1) := h3
  have hpiebd : ∀ (η : ℝ), 0 < η →
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), |pie η (g x k)| ≤ μ ^ (p - 1) := by
    intro η hη
    filter_upwards [hbdall] with x hx
    exact le_trans (hpieabs η hη (g x k))
      (Real.rpow_le_rpow (abs_nonneg _) (hx k) (by linarith only [hp10]))
  -- (D.6b) Measurability on all of `B_R`, from the exhaustion (D.0).
  have hwmR : AEStronglyMeasurable (fun x => ‖g x‖ ^ 2)
      (volume.restrict (Metric.ball x₀ R)) := by
    have he : (fun x : EuclideanSpace ℝ (Fin n) => ‖g x‖ ^ 2)
        = fun x => ∑ i, (g x i) ^ 2 := by
      funext x; exact EuclideanSpace.real_norm_sq_eq (g x)
    rw [he]
    have hsum := Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin n))
      (fun i _ => ((hgmRi i).pow 2))
    exact hsum.congr (Filter.Eventually.of_forall fun x => by simp [Finset.sum_apply])
  have habsR : AEStronglyMeasurable (fun x => |g x k|)
      (volume.restrict (Metric.ball x₀ R)) :=
    continuous_abs.comp_aestronglyMeasurable hgmR
  have hwrpowR : AEStronglyMeasurable (fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1))
      (volume.restrict (Metric.ball x₀ R)) :=
    ((hwmR.aemeasurable.const_add ε).pow_const _).aestronglyMeasurable
  have hFmeasη : ∀ (η : ℝ) (ζ : EuclideanSpace ℝ (Fin n) → ℝ), Continuous ζ →
      AEStronglyMeasurable (fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
          * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
        (volume.restrict (Metric.ball x₀ R)) := by
    intro η ζ hζc
    have h1 : AEStronglyMeasurable
        (fun x => (p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x)
        (volume.restrict (Metric.ball x₀ R)) :=
      ((((habsR.aemeasurable.add_const η).pow_const
        (p / 2 - 1)).const_mul (p / 2)).aestronglyMeasurable).smul hDgmR
    exact (hwrpowR.mul (h1.norm.pow 2)).mul ((hζc.aestronglyMeasurable).pow 2)
  have hFmeas0 : ∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous ζ →
      AEStronglyMeasurable (fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
          * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
        (volume.restrict (Metric.ball x₀ R)) := by
    intro ζ hζc
    have h1 : AEStronglyMeasurable
        (fun x => (p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x)
        (volume.restrict (Metric.ball x₀ R)) :=
      (((habsR.aemeasurable.pow_const
        (p / 2 - 1)).const_mul (p / 2)).aestronglyMeasurable).smul hDgmR
    exact (hwrpowR.mul (h1.norm.pow 2)).mul ((hζc.aestronglyMeasurable).pow 2)
  -- (D6) The limit `η_j ↓ 0` in (D.5), stated once for both signs.  This is
  -- `RegularisedCaccioppoliEtaLimit`, whose docstring records the route: Fatou
  -- on the left, which consumes only the POINTWISE statement (D.6) and NOT any
  -- monotonicity of the sets `A^±_ℓ(η)` -- false, and the one thing a reader
  -- will ask about -- and dominated convergence on the right.
  have hD6 := RegularisedCaccioppoliEtaLimit n p hp hp2 C₂ ε μ g Dg x₀ R k
    (by rw [hC₂def]; positivity) hε hgmR habsR pie hpieC1 ηs hηs0 hηt hpielim
    hpiebd hFmeasη hFmeas0
  -- (D5): conclusion (1).  This is `SignedPowerMemW12OnInnerBall`, whose
  -- docstring records the route (`MemLp v 2` free from `|v| = |g^k|^{p/2} ≤ μ^{p/2}`;
  -- `MemLp V 2` from (3.17±) at `ℓ = 0` with `ζ = ζ_{T,T'}` and the lower bound
  -- `w^{p/2-1} ≥ ((1+4n)lam²)^{p/2-1}`; then the weak-gradient identity by
  -- dominated convergence in `hveeW` as `η = ηs j ↓ 0`, via the closed form of
  -- `Gee` and the domination `‖V_η‖ ≤ ‖V‖`, REVIEWER ELISION (4) being the
  -- `{g^k = 0}` case).
  have hconc1 := SignedPowerMemW12OnInnerBall n p hp hp2 Lc C₂ ε μ lam g Dg x₀ R k
    hε hμ hlamdef hlam0 (by rw [hC₂def]; positivity) hbd hcut hwup hwlow hgmRi
    hDgmR pie Gee hGeedef hbase hGeeC1 hpiebd hveeW e0 ηs he00
    (by rw [he0def]; exact min_le_left _ _) hηsval hηs0 hηsε hηt hD5
  -- (D3)+(D4)+(D6): inequality (3.17±), for EVERY real level `ℓ`.
  -- THIS IS THE ONLY THING STEP E STILL NEEDS: (E3) and (E4) below are proved
  -- and consume exactly this, at the level `ℓ = Φ_{p-1}(Φ_{2/p}(h))`.
  -- ROUTE: `θ⁺_η = (ψ_η - ℓ)⁺` by `WeakGradientPositivePart` on `B_T`, lifted to
  -- `W^{1,2}_loc(B_R)` by (A.2'), multiplied by `ζ²` by clause (2) of
  -- `WeakGradientSmoothMul`, and fed to `DifferentiatedEquationWeak` (whose
  -- `γ₀ ≤ γ₁` is `hγ01`); then `Q1`/`Q2` of `EllipticStructureQ12` and the
  -- lower half of (D.1) give (3.13), Cauchy-Schwarz gives (3.16±), and Fatou
  -- plus dominated convergence along `η_j ↓ 0` give (3.17±).
  -- REVIEWER ELISION (2): the split of `DifferentiatedEquationWeak`'s single
  -- vanishing integral into two summands needs `integral_add`, and both are
  -- integrable by the bounds (D4) already carries --
  -- `w^{p/2-1} ≤ ε^{p/2-1}`, `Dpi η ≤ η^{p-2}` (`hDpibd`), `‖Dg^k‖² ∈ L¹` of
  -- the compact `tsupport ζ` by `hDg`, and `L² ⊆ L¹` there.
  -- REVIEWER ELISION (1): the division by the left Cauchy-Schwarz factor needs
  -- its `X = 0` branch, where the inequality is trivial because the right side
  -- is nonnegative; `CaccioppoliLevelWeight` states that dichotomy at its
  -- Step 8.  The same effect is available one level earlier through the
  -- `by_cases` on integrability recorded in handoff section 21.3.
  have hD17 : ∀ (ℓ : ℝ) (ζ : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball x₀ R →
      ((∫ x in Metric.ball x₀ R ∩ {y | ℓ < |g y k| ^ (p - 2) * g y k},
            (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
              * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
          ≤ C₂ * (∫ x in Metric.ball x₀ R,
              max (|g x k| ^ (p - 2) * g x k - ℓ) 0 ^ 2
                * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)))
        ∧ ((∫ x in Metric.ball x₀ R ∩ {y | |g y k| ^ (p - 2) * g y k < ℓ},
            (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
              * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
          ≤ C₂ * (∫ x in Metric.ball x₀ R,
              max (ℓ - |g x k| ^ (p - 2) * g x k) 0 ^ 2
                * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2))) := by
    intro ℓ ζ hζsmA hζcsA hζtsA
    have habsle : ∀ a c : ℝ, |a - c| ≤ |a| + |c| := by
      intro a c
      rw [sub_eq_add_neg]
      exact (abs_add_le a (-c)).trans (le_of_eq (by rw [abs_neg]))
    have hbMp : ∀ s : ℝ, |s| ≤ μ ^ (p - 1) →
        max (s - ℓ) 0 ≤ μ ^ (p - 1) + |ℓ| := by
      intro s hs
      have h1 : max (s - ℓ) 0 ≤ |s - ℓ| := max_le (le_abs_self _) (abs_nonneg _)
      linarith only [h1, habsle s ℓ, hs]
    have hbMm : ∀ s : ℝ, |s| ≤ μ ^ (p - 1) →
        max (ℓ - s) 0 ≤ μ ^ (p - 1) + |ℓ| := by
      intro s hs
      have h1 : max (ℓ - s) 0 ≤ |ℓ - s| := max_le (le_abs_self _) (abs_nonneg _)
      linarith only [h1, habsle ℓ s, hs]
    refine ⟨?_, ?_⟩
    · exact hD6 (Set.Ioi ℓ) isOpen_Ioi (fun s => max (s - ℓ) 0)
        ((continuous_id.sub continuous_const).max continuous_const)
        (fun s => le_max_right _ _) (μ ^ (p - 1) + |ℓ|) hbMp ζ hζsmA
        (fun j => (hD5 (ηs j) (hηs0 j) (hηsε j) ℓ ζ hζsmA hζcsA hζtsA).2.1)
        (fun j => (hD5 (ηs j) (hηs0 j) (hηsε j) ℓ ζ hζsmA hζcsA hζtsA).1)
    · exact hD6 (Set.Iio ℓ) isOpen_Iio (fun s => max (ℓ - s) 0)
        ((continuous_const.sub continuous_id).max continuous_const)
        (fun s => le_max_right _ _) (μ ^ (p - 1) + |ℓ|) hbMm ζ hζsmA
        (fun j => (hD5 (ηs j) (hηs0 j) (hηsε j) ℓ ζ hζsmA hζcsA hζtsA).2.2)
        (fun j => (hD5 (ηs j) (hηs0 j) (hηsε j) ℓ ζ hζsmA hζcsA hζtsA).1)
  refine ⟨hconc1, ?_⟩
  -- Step E, cases (E3) and (E4).  ROUTE: with `ℓ = |h|^{2(p-1)/p - 1} h` the
  -- level transports exactly -- `{ψ < ℓ} = {v < h}` and `h ≤ h₀ ↔ ℓ ≤ lam^{p-1}`
  -- -- and (3.17∓) at that `ℓ` gives the two halves of conclusion (2) after
  -- dividing by `(1+4n)^{p/2-1} lam^{p-2} > 0`, using `w^{p/2-1} ≥
  -- ((1+4n)lam²)^{p/2-1}` (the LOWER bound here, since `p/2-1 < 0`) and
  -- `0 < ℓ - ψ ≤ (1+2^{p-1})lam^{p-1}`.  In scope: `hD17`, `hcut`, `hwup`,
  -- `hφ*` (the level transport of Step B is the same shape one exponent along),
  -- and `hCbdef`, the constant this branch has to meet.
  -- Step E, cases (E3) and (E4)
  intro ρ σ h hρ hρR hσ hσ1
  obtain ⟨ρ₀, hρ₀def⟩ : ∃ t : ℝ, t = ρ - σ * ρ := ⟨_, rfl⟩
  have hρ₀0 : 0 < ρ₀ := by rw [hρ₀def]; nlinarith only [hρ, hσ, hσ1]
  have hρ₀ρ : ρ₀ < ρ := by rw [hρ₀def]; nlinarith only [hρ, hσ]
  have hdρ : ρ - ρ₀ = σ * ρ := by rw [hρ₀def]; ring
  obtain ⟨ζ, hζsm, hζcs, hζts, hζnn, hζle1, hζone, hζgrad⟩ := hcut ρ₀ ρ hρ₀0 hρ₀ρ
  have hζtsR : tsupport ζ ⊆ Metric.ball x₀ R :=
    hζts.trans (Metric.ball_subset_ball hρR)
  have hKcpt : IsCompact (tsupport ζ) := hζcs
  have hKmeas : MeasurableSet (tsupport ζ) := (isClosed_tsupport ζ).measurableSet
  have hζ0out : ∀ x, x ∉ tsupport ζ → ζ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport hx
  have hDz0 : ∀ x, x ∉ tsupport ζ →
      ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 = 0 := by
    intro x hx
    have hopen : IsOpen (tsupport ζ)ᶜ := (isClosed_tsupport ζ).isOpen_compl
    have hev : ζ =ᶠ[nhds x] fun _ => (0:ℝ) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have h0 : fderiv ℝ ζ x = 0 := by rw [hev.fderiv_eq]; simp
    simp [h0]
  -- a radius `T < R` with `tsupport ζ ⊆ B_T`
  obtain ⟨T, hT0, hTR, hTsub⟩ : ∃ T : ℝ, 0 < T ∧ T < R ∧
      tsupport ζ ⊆ Metric.ball x₀ T := by
    rcases Set.eq_empty_or_nonempty (tsupport ζ) with he | hne
    · exact ⟨R / 2, by linarith only [hR], by linarith only [hR],
        by rw [he]; exact Set.empty_subset _⟩
    · obtain ⟨y, hy, hmax⟩ := hKcpt.exists_isMaxOn
        (f := fun z : EuclideanSpace ℝ (Fin n) => dist z x₀) hne
        (Continuous.continuousOn (continuous_id.dist continuous_const))
      have hyR : dist y x₀ < R := Metric.mem_ball.1 (hζtsR hy)
      have hy0 : (0:ℝ) ≤ dist y x₀ := dist_nonneg
      refine ⟨(dist y x₀ + R) / 2, by linarith only [hy0, hR],
        by linarith only [hyR], fun z hz => ?_⟩
      have hzy : dist z x₀ ≤ dist y x₀ := hmax hz
      exact Metric.mem_ball.2 (by linarith only [hzy, hyR])
  -- `‖V‖²` is integrable on `B_T`, by conclusion (1)
  have hVsq : IntegrableOn
      (fun x => ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
      (Metric.ball x₀ T) volume := by
    have hmem := (hconc1 T hT0 hTR).2.2
    have h1 : Integrable (fun x =>
        ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ (ENNReal.ofReal 2).toReal)
        (volume.restrict (Metric.ball x₀ T)) :=
      hmem.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp] at h1
    refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
    show ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ (2:ℝ)
        = ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2
    rw [← Real.rpow_natCast ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ 2]
    norm_num
  have hVsqK : IntegrableOn
      (fun x => ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
      (tsupport ζ) volume := hVsq.mono_set hTsub
  have hVms : AEStronglyMeasurable
      (fun x => ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
      (volume.restrict (tsupport ζ)) := hVsqK.1
  have hgm : ∀ i : Fin n, AEStronglyMeasurable (fun x => g x i)
      (volume.restrict (tsupport ζ)) := fun i =>
    (((hDg i).2 (tsupport ζ) hKcpt hζtsR).1).1
  have hwm : AEStronglyMeasurable (fun x => ‖g x‖ ^ 2)
      (volume.restrict (tsupport ζ)) := by
    have he : (fun x : EuclideanSpace ℝ (Fin n) => ‖g x‖ ^ 2)
        = fun x => ∑ i, (g x i) ^ 2 := by
      funext x; exact EuclideanSpace.real_norm_sq_eq (g x)
    rw [he]
    have hsum := Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin n))
      (fun i _ => ((hgm i).pow 2))
    refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Finset.sum_apply]
  -- the globalisation helper
  have hglob : ∀ u gg : EuclideanSpace ℝ (Fin n) → ℝ,
      Integrable gg volume →
      AEStronglyMeasurable u (volume.restrict (tsupport ζ)) →
      (∀ x, x ∉ tsupport ζ → u x = 0) →
      (∀ x, x ∉ tsupport ζ → 0 ≤ gg x) →
      (∀ᵐ x ∂(volume.restrict (tsupport ζ)), ‖u x‖ ≤ gg x) →
      Integrable u volume := by
    intro u gg hg hum hu0 hg0 hub
    have hueq : u = (tsupport ζ).indicator u := by
      funext x
      by_cases hb : x ∈ tsupport ζ
      · rw [Set.indicator_of_mem hb]
      · rw [Set.indicator_of_notMem hb, hu0 x hb]
    have humg : AEStronglyMeasurable u volume := by
      rw [hueq]
      exact (aestronglyMeasurable_indicator_iff hKmeas).2 hum
    refine Integrable.mono' hg humg ?_
    have h1 : ∀ᵐ x ∂volume, x ∈ tsupport ζ → ‖u x‖ ≤ gg x :=
      (ae_restrict_iff' hKmeas).1 hub
    filter_upwards [h1] with x hx
    by_cases hb : x ∈ tsupport ζ
    · exact hx hb
    · rw [hu0 x hb, norm_zero]
      exact hg0 x hb
  -- the weighted integrand is integrable
  obtain ⟨Mw, hMwdef⟩ : ∃ t : ℝ, t = ε ^ (p / 2 - 1) := ⟨_, rfl⟩
  have hMw0 : 0 < Mw := by rw [hMwdef]; exact Real.rpow_pos_of_pos hε _
  have hwupε : ∀ x : EuclideanSpace ℝ (Fin n),
      (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) ≤ Mw := by
    intro x
    rw [hMwdef]
    exact Real.rpow_le_rpow_of_nonpos hε (hwlow x) hexpn.le
  have hintW : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      IntegrableOn (fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
        * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2) S volume := by
    intro S
    refine Integrable.mono_measure ?_ Measure.restrict_le_self
    refine hglob _ ((tsupport ζ).indicator (fun x => Mw *
      ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2))
      ((integrable_indicator_iff hKmeas).2 (hVsqK.const_mul Mw)) ?_ ?_ ?_ ?_
    · have hwrpow : AEStronglyMeasurable
          (fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1))
          (volume.restrict (tsupport ζ)) :=
        ((hwm.aemeasurable.const_add ε).pow_const _).aestronglyMeasurable
      exact (hwrpow.mul hVms).mul ((hζsm.continuous.aestronglyMeasurable).pow 2)
    · intro x hx; rw [hζ0out x hx]; ring
    · intro x hx; rw [Set.indicator_of_notMem hx]
    · filter_upwards [ae_restrict_mem hKmeas] with x hx
      rw [Set.indicator_of_mem hx]
      have h1 : (0:ℝ) ≤ (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) :=
        Real.rpow_nonneg (le_trans hε.le (hwlow x)) _
      have h2 : ζ x ^ 2 ≤ 1 := pow_le_one₀ (hζnn x) (hζle1 x)
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg h1 (sq_nonneg _)) (sq_nonneg _))]
      calc (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2
          ≤ Mw * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hwupε x) (sq_nonneg _)) (sq_nonneg _)
        _ ≤ Mw * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hMw0.le (sq_nonneg _))
        _ = Mw * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 := mul_one _
  -- the lower bound on the weight, and the rpow bookkeeping
  obtain ⟨W2L, hW2Ldef⟩ : ∃ t : ℝ, t = ((1 + 4 * (n:ℝ)) * lam ^ 2) ^ (p / 2 - 1) :=
    ⟨_, rfl⟩
  have hW2L0 : 0 < W2L := by
    rw [hW2Ldef]; exact Real.rpow_pos_of_pos (by positivity) _
  have hwlowK : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      W2L ≤ (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) := by
    filter_upwards [hwup] with x hx
    rw [hW2Ldef]
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hε (hwlow x)) hx hexpn.le
  have hsq0 : (0:ℝ) < (σ * ρ) ^ 2 := by positivity
  have hCmax : (0:ℝ) < max 1 Cb := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hCble : Cb ≤ max 1 Cb := le_max_right _ _
  have hlamp : (lam ^ (p / 2)) ^ 2 = lam ^ p := by
    rw [← Real.rpow_natCast (lam ^ (p / 2)) 2, ← Real.rpow_mul hlam0.le]
    congr 1; push_cast; ring
  have hlam2 : (lam ^ (p - 1)) ^ 2 = lam ^ (2 * p - 2) := by
    rw [← Real.rpow_natCast (lam ^ (p - 1)) 2, ← Real.rpow_mul hlam0.le]
    congr 1; push_cast; ring
  have hW2Linv : W2L⁻¹ = (1 + 4 * (n:ℝ)) ^ (1 - p / 2) * lam ^ (2 - p) := by
    rw [hW2Ldef, ← Real.rpow_neg (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    · congr 1; ring
    · rw [← Real.rpow_natCast lam 2, ← Real.rpow_mul hlam0.le]
      congr 1; push_cast; ring
  have hlamsum : lam ^ (2 - p) * lam ^ (2 * p - 2) = lam ^ p := by
    rw [← Real.rpow_add hlam0]; congr 1; ring
  have h2lam : ((2:ℝ) * lam) ^ (p - 1) = (2:ℝ) ^ (p - 1) * lam ^ (p - 1) :=
    Real.mul_rpow (by norm_num) hlam0.le
  have hcommon : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      (0:ℝ) ≤ max 1 Cb * (lam ^ (p / 2)) ^ 2 / (σ * ρ) ^ 2
        * (volume (Metric.ball x₀ ρ ∩ S)).toReal := fun S =>
    mul_nonneg (div_nonneg (mul_nonneg hCmax.le (sq_nonneg _)) hsq0.le)
      ENNReal.toReal_nonneg
  -- the common core of the two sides
  have core : ∀ (S : Set (EuclideanSpace ℝ (Fin n)))
      (d : EuclideanSpace ℝ (Fin n) → ℝ),
      (∫ x in Metric.ball x₀ R ∩ S, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
          * ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
        ≤ C₂ * (∫ x in Metric.ball x₀ R, d x ^ 2
            * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)) →
      (∀ x, 0 ≤ d x) →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
          d x ≤ (1 + (2:ℝ) ^ (p - 1)) * lam ^ (p - 1)) →
      (∀ x, x ∉ S → d x = 0) →
      (∫ x in Metric.ball x₀ ρ₀ ∩ S,
          ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
        ≤ max 1 Cb * (lam ^ (p / 2)) ^ 2 / (σ * ρ) ^ 2
          * (volume (Metric.ball x₀ ρ ∩ S)).toReal :=
    SignedPowerLevelTransportCore n p r C₁ Lc C₂ Cb ε lam ρ σ ρ₀ W2L R g Dg k ζ
      x₀ hC₂def hCbdef hε hlam0 hρ hσ hLc0 hwlow hρR hρ₀ρ hdρ hζts hζone hζgrad
      hDz0 hintW hW2L0 hwlowK hsq0 hCble hlamp hlam2 hW2Linv hlamsum hcommon
  -- the two level transports
  have hp2pos : (0:ℝ) < p / 2 := by linarith only [hp0]
  have hPhip2 : ∀ s : ℝ, Phi (p / 2) s = |s| ^ (p / 2 - 1) * s := by
    intro s; rw [hPhidef]
  have hPhipm : ∀ s : ℝ, Phi (p - 1) s = |s| ^ (p - 2) * s := by
    intro s
    rw [hPhidef]
    show |s| ^ (p - 1 - 1) * s = |s| ^ (p - 2) * s
    congr 2
    ring
  have hPhiabs : ∀ s : ℝ, |Phi (p - 1) s| = |s| ^ (p - 1) := by
    intro s
    rcases lt_trichotomy s 0 with hs | hs | hs
    · have hpp : (0:ℝ) < -s := by linarith only [hs]
      have hneg' : Phi (p - 1) s = -Phi (p - 1) (-s) := by
        have hh := hPhineg (p - 1) (-s)
        rwa [neg_neg] at hh
      rw [hneg', abs_neg, hPhipos (p - 1) (-s) hpp,
        abs_of_pos (Real.rpow_pos_of_pos hpp _), abs_of_neg hs]
    · rw [hs, hPhi0]
      simp [Real.zero_rpow (ne_of_gt hp10)]
    · rw [hPhipos (p - 1) s hs, abs_of_pos (Real.rpow_pos_of_pos hs _), abs_of_pos hs]
  have hpsibd : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      |Phi (p - 1) (g x k)| ≤ (2:ℝ) ^ (p - 1) * lam ^ (p - 1) := by
    filter_upwards [hbd k] with x hx
    rw [hPhiabs, ← h2lam]
    refine Real.rpow_le_rpow (abs_nonneg _) ?_ hp10.le
    rw [hlamdef]
    linarith only [hx]
  have hlamp1 : lam ^ (p - 1) = Phi (p - 1) lam := (hPhipos (p - 1) lam hlam0).symm
  constructor
  · -- (E4) the `+` side
    intro hh
    have hh' : -(lam ^ (p / 2)) ≤ h := by rw [hlamdef]; exact hh
    obtain ⟨s₀, hs₀def⟩ : ∃ t : ℝ, t = Phi ((p / 2)⁻¹) h := ⟨_, rfl⟩
    have hs₀ : Phi (p / 2) s₀ = h := by rw [hs₀def]; exact hPhiinv (p / 2) hp2pos h
    have hs₀ge : -lam ≤ s₀ := by
      refine ((hPhimono (p / 2) hp2pos).le_iff_le).1 ?_
      rw [hPhineg, hPhipos (p / 2) lam hlam0, hs₀]
      exact hh'
    obtain ⟨l, hldef⟩ : ∃ t : ℝ, t = Phi (p - 1) s₀ := ⟨_, rfl⟩
    have hlge : -(lam ^ (p - 1)) ≤ l := by
      rw [hldef, hlamp1, ← hPhineg]
      exact ((hPhimono (p - 1) hp10).le_iff_le).2 hs₀ge
    have hset : {y : EuclideanSpace ℝ (Fin n) | h < |g y k| ^ (p / 2 - 1) * g y k}
        = {y | l < |g y k| ^ (p - 2) * g y k} := by
      ext y
      simp only [Set.mem_ofPred_eq, ← hPhip2, ← hPhipm, ← hs₀, hldef]
      exact ⟨fun hy => (hPhimono (p - 1) hp10) ((hPhimono (p / 2) hp2pos).lt_iff_lt.1 hy),
        fun hy => (hPhimono (p / 2) hp2pos) ((hPhimono (p - 1) hp10).lt_iff_lt.1 hy)⟩
    have hcacc := (hD17 l ζ hζsm hζcs hζtsR).1
    rw [← hset] at hcacc
    have hres := core {y | h < |g y k| ^ (p / 2 - 1) * g y k}
      (fun x => max (|g x k| ^ (p - 2) * g x k - l) 0) hcacc
      (fun x => le_max_right _ _) ?_ ?_
    · rw [hρ₀def] at hres
      rw [← hlamdef]
      exact hres
    · filter_upwards [hpsibd] with x hx
      rw [← hPhipm]
      refine max_le ?_ (by positivity)
      have h1 : Phi (p - 1) (g x k) ≤ (2:ℝ) ^ (p - 1) * lam ^ (p - 1) :=
        le_trans (le_abs_self _) hx
      linarith only [h1, hlge]
    · intro x hx
      show max (|g x k| ^ (p - 2) * g x k - l) 0 = 0
      have h2 : ¬ (l < |g x k| ^ (p - 2) * g x k) := by
        intro hc
        exact hx (by rw [hset]; exact hc)
      exact max_eq_right (by linarith only [not_lt.1 h2])
  · -- (E3) the `-` side
    intro hh
    have hh' : h ≤ lam ^ (p / 2) := by rw [hlamdef]; exact hh
    obtain ⟨s₀, hs₀def⟩ : ∃ t : ℝ, t = Phi ((p / 2)⁻¹) h := ⟨_, rfl⟩
    have hs₀ : Phi (p / 2) s₀ = h := by rw [hs₀def]; exact hPhiinv (p / 2) hp2pos h
    have hs₀le : s₀ ≤ lam := by
      refine ((hPhimono (p / 2) hp2pos).le_iff_le).1 ?_
      rw [hPhipos (p / 2) lam hlam0, hs₀]
      exact hh'
    obtain ⟨l, hldef⟩ : ∃ t : ℝ, t = Phi (p - 1) s₀ := ⟨_, rfl⟩
    have hlle : l ≤ lam ^ (p - 1) := by
      rw [hldef, hlamp1]
      exact ((hPhimono (p - 1) hp10).le_iff_le).2 hs₀le
    have hset : {y : EuclideanSpace ℝ (Fin n) | |g y k| ^ (p / 2 - 1) * g y k < h}
        = {y | |g y k| ^ (p - 2) * g y k < l} := by
      ext y
      simp only [Set.mem_ofPred_eq, ← hPhip2, ← hPhipm, ← hs₀, hldef]
      exact ⟨fun hy => (hPhimono (p - 1) hp10) ((hPhimono (p / 2) hp2pos).lt_iff_lt.1 hy),
        fun hy => (hPhimono (p / 2) hp2pos) ((hPhimono (p - 1) hp10).lt_iff_lt.1 hy)⟩
    have hcacc := (hD17 l ζ hζsm hζcs hζtsR).2
    rw [← hset] at hcacc
    have hres := core {y | |g y k| ^ (p / 2 - 1) * g y k < h}
      (fun x => max (l - |g x k| ^ (p - 2) * g x k) 0) hcacc
      (fun x => le_max_right _ _) ?_ ?_
    · rw [hρ₀def] at hres
      rw [← hlamdef]
      exact hres
    · filter_upwards [hpsibd] with x hx
      rw [← hPhipm]
      refine max_le ?_ (by positivity)
      have h1 : -((2:ℝ) ^ (p - 1) * lam ^ (p - 1)) ≤ Phi (p - 1) (g x k) :=
        neg_le_of_abs_le hx
      linarith only [h1, hlle]
    · intro x hx
      show max (l - |g x k| ^ (p - 2) * g x k) 0 = 0
      have h2 : ¬ (|g x k| ^ (p - 2) * g x k < l) := by
        intro hc
        exact hx (by rw [hset]; exact hc)
      exact max_eq_right (by linarith only [not_lt.1 h2])
