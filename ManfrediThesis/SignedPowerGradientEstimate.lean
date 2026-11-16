import ManfrediThesis.Preamble
import ManfrediThesis.SignedPowerLevelTransportSuperquadratic
import ManfrediThesis.TruncatedSignedPowerPrimitive
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.CaccioppoliLevelWeight
import ManfrediThesis.DifferentiatedEquationWeak
import ManfrediThesis.WeakGradientC1Comp
import ManfrediThesis.WeakGradientPositivePart
import ManfrediThesis.WeakGradientSmoothMul
import ManfrediThesis.WeakGradientLinear
import ManfrediThesis.WeakGradientRestrict
import ManfrediThesis.StandardRadialCutoff
import ManfrediThesis.SignedPowerGradientEstimateSubquadratic
open MeasureTheory
set_option maxHeartbeats 600000

/-- The signed power `v = |D_k u|^{p/2-1} D_k u` of a partial derivative of a
solution of (3.1) in the degenerate regime `ε < (μ/2)²`: it lies in `W^{1,2}` of
every smaller ball with the weak gradient `(p/2)|D_k u|^{p/2-1} D(D_k u)`, and it
satisfies the paper's inequality (3.12) on both sides, with a constant depending
only on `n`, `p` and `r`.  The product form `|s|^{p/2-1} s` is the thesis'
`|s|^{p/2} sgn s` written without a sign function: the two agree at every real
`s`, the factor `s` killing the value of `|0|^{p/2-1}` at `s = 0`.  The two
exponent regimes `p ≥ 2` and `1 < p < 2` are proved by different routes but
deliver the same two conclusions, which is why they are packaged as one
statement. -/
theorem SignedPowerGradientEstimate :
    ∀ (n : ℕ) (p r : ℝ), 2 ≤ n → 1 < p → 0 < r →
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
  intro n p r hn hp hr
  rcases le_or_gt 2 p with hp2 | hp2
  · -- THE REGIME `p ≥ 2`: Steps A, B, C and E1/E2
    have hn1 : 1 ≤ n := le_trans (by norm_num) hn
    have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    -- the cut-off from `StandardRadialCutoff`
    obtain ⟨L, hL0, hSRC⟩ := StandardRadialCutoff n hn1
    -- Step A5's constant
    obtain ⟨c₄, hc₄0, hCacc⟩ := CaccioppoliLevelWeight n p r hn hp hr
    -- the constant `C`
    obtain ⟨Ca, hCadef⟩ : ∃ t : ℝ,
      t = 9 * p ^ 2 / 4 * c₄ * (1 + 4 * (n:ℝ)) ^ (p / 2 - 1) * L := ⟨_, rfl⟩
    refine ⟨max 1 Ca, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
    intro ε γ₀ γ₁ μ A u g Dg x₀ R k hε hγ₀ hγ₁ hR hμ hεμ hQ hC1 hsol hDg hbd
    obtain ⟨lam, hlamdef⟩ : ∃ t : ℝ, t = μ / 2 := ⟨_, rfl⟩
    have hlam0 : 0 < lam := by rw [hlamdef]; linarith
    have hεlam : ε < lam ^ 2 := by rw [hlamdef]; exact hεμ
    -- (A4) the radial cut-off
    have hcut := hSRC x₀
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
    -- Step B: the level correspondence
    obtain ⟨φ, hφdef⟩ : ∃ f : ℝ → ℝ, f = fun s => |s| ^ (p / 2 - 1) * s := ⟨_, rfl⟩
    have hφ0 : φ 0 = 0 := by rw [hφdef]; simp
    have hφneg : ∀ s : ℝ, φ (-s) = -φ s := by
      intro s; rw [hφdef]; simp [abs_neg]
    have hφpos : ∀ s : ℝ, 0 < s → φ s = s ^ (p / 2) := by
      intro s hs
      rw [hφdef]
      simp only [abs_of_pos hs]
      calc s ^ (p / 2 - 1) * s = s ^ (p / 2 - 1) * s ^ (1:ℝ) := by
            rw [Real.rpow_one]
        _ = s ^ (p / 2 - 1 + 1) := (Real.rpow_add hs _ _).symm
        _ = s ^ (p / 2) := by ring_nf
    have hφmono : StrictMono φ := by
      have hposmono : ∀ a b : ℝ, 0 < a → a < b → φ a < φ b := by
        intro a b ha hab
        rw [hφpos a ha, hφpos b (lt_trans ha hab)]
        exact Real.rpow_lt_rpow ha.le hab (by linarith)
      have hposval : ∀ a : ℝ, 0 < a → 0 < φ a := by
        intro a ha; rw [hφpos a ha]; exact Real.rpow_pos_of_pos ha _
      intro a b hab
      rcases lt_trichotomy a 0 with ha | ha | ha
      · rcases lt_trichotomy b 0 with hb | hb | hb
        · have h1 : φ (-b) < φ (-a) := hposmono (-b) (-a) (by linarith) (by linarith)
          rw [hφneg, hφneg] at h1
          linarith
        · rw [hb, hφ0]
          have : 0 < φ (-a) := hposval (-a) (by linarith)
          rw [hφneg] at this
          linarith
        · have h1 : 0 < φ (-a) := hposval (-a) (by linarith)
          have h2 : 0 < φ b := hposval b hb
          rw [hφneg] at h1
          linarith
      · rw [ha, hφ0]
        exact hposval b (by linarith)
      · exact hposmono a b ha hab
    have hφsurj : ∀ h : ℝ, φ (|h| ^ (2 / p - 1) * h) = h := by
      intro h
      rcases lt_trichotomy h 0 with hh | hh | hh
      · have hpos : φ (|(-h)| ^ (2 / p - 1) * (-h)) = -h := by
          have hpp : (0:ℝ) < -h := by linarith
          have : |(-h)| ^ (2 / p - 1) * (-h) = (-h) ^ (2 / p) := by
            simp only [abs_of_pos hpp]
            calc (-h) ^ (2 / p - 1) * (-h) = (-h) ^ (2 / p - 1) * (-h) ^ (1:ℝ) := by
                  rw [Real.rpow_one]
              _ = (-h) ^ (2 / p - 1 + 1) := (Real.rpow_add hpp _ _).symm
              _ = (-h) ^ (2 / p) := by ring_nf
          rw [this, hφpos _ (Real.rpow_pos_of_pos hpp _), ← Real.rpow_mul hpp.le]
          rw [show 2 / p * (p / 2) = 1 by field_simp]
          exact Real.rpow_one _
        have e1 : |(-h)| ^ (2 / p - 1) * (-h) = -(|h| ^ (2 / p - 1) * h) := by
          rw [abs_neg]; ring
        rw [e1, hφneg] at hpos
        linarith
      · rw [hh]; simp [hφ0]
      · have : |h| ^ (2 / p - 1) * h = h ^ (2 / p) := by
          simp only [abs_of_pos hh]
          calc h ^ (2 / p - 1) * h = h ^ (2 / p - 1) * h ^ (1:ℝ) := by rw [Real.rpow_one]
            _ = h ^ (2 / p - 1 + 1) := (Real.rpow_add hh _ _).symm
            _ = h ^ (2 / p) := by ring_nf
        rw [this, hφpos _ (Real.rpow_pos_of_pos hh _), ← Real.rpow_mul hh.le]
        rw [show 2 / p * (p / 2) = 1 by field_simp]
        exact Real.rpow_one _
    have hφlam : φ lam = lam ^ (p / 2) := hφpos lam hlam0
    -- the pointwise identity (C.2)
    have hVnorm : ∀ x : EuclideanSpace ℝ (Fin n),
        ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2
          = p ^ 2 / 4 * |g x k| ^ (p - 2) * ‖Dg k x‖ ^ 2 := by
      intro x
      rw [norm_smul, Real.norm_eq_abs, mul_pow,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ p / 2 * |g x k| ^ (p / 2 - 1))]
      have e : (|g x k| ^ (p / 2 - 1)) ^ 2 = |g x k| ^ (p - 2) := by
        rw [← Real.rpow_natCast (|g x k| ^ (p / 2 - 1)) 2,
          ← Real.rpow_mul (abs_nonneg _)]
        norm_num
        ring_nf
      calc (p / 2 * |g x k| ^ (p / 2 - 1)) ^ 2 * ‖Dg k x‖ ^ 2
          = (p / 2) ^ 2 * (|g x k| ^ (p / 2 - 1)) ^ 2 * ‖Dg k x‖ ^ 2 := by ring
        _ = p ^ 2 / 4 * |g x k| ^ (p - 2) * ‖Dg k x‖ ^ 2 := by rw [e]; ring
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
    have hexp0 : (0:ℝ) ≤ p / 2 - 1 := by linarith
    obtain ⟨F, hFC1, hFbd, hFeq, hderivFeq⟩ :=
      TruncatedSignedPowerPrimitive p μ φ hp hμ hexp0 hφ0 hφneg hφpos
    -- Step C: conclusion (1)
    have stepC : ∀ T : ℝ, 0 < T → T < R →
        MemW1pOn n 2 (Metric.ball x₀ T)
          (fun x => |g x k| ^ (p / 2 - 1) * g x k)
          (fun x => (p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x) := by
      intro T hT hTR
      have hsubT : Metric.ball x₀ T ⊆ Metric.ball x₀ R := Metric.ball_subset_ball hTR.le
      have hbdT : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ T)), |g x k| ≤ μ :=
        ae_restrict_of_ae_restrict_of_subset hsubT (hbd k)
      have hcomp := WeakGradientC1Comp n 2 (p / 2 * μ ^ (p / 2 - 1)) hn1 (by norm_num)
        (by positivity) (Metric.ball x₀ T) (fun x => g x k) (Dg k) F
        Metric.isOpen_ball measure_ball_lt_top.ne (hloc T hT hTR) hFC1 hFbd
      refine htransport _ _ _ _ _ hcomp ?_ ?_
      · filter_upwards [hbdT] with x hx
        have := hFeq (g x k) hx
        rw [this, hφdef]
      · filter_upwards [hbdT] with x hx
        rw [hderivFeq (g x k) hx]
    refine ⟨stepC, ?_⟩
    -- Step E: conclusion (2) in the regime `p ≥ 2`
    intro ρ σ h hρ hρR hσ hσ1
    obtain ⟨ρ₀, hρ₀def⟩ : ∃ t : ℝ, t = ρ - σ * ρ := ⟨_, rfl⟩
    have hρ₀0 : 0 < ρ₀ := by rw [hρ₀def]; nlinarith
    have hρ₀ρ : ρ₀ < ρ := by rw [hρ₀def]; nlinarith
    have hdρ : ρ - ρ₀ = σ * ρ := by rw [hρ₀def]; ring
    obtain ⟨ζ, hζsm, hζcs, hζts, hζnn, hζle1, hζone, hζgrad⟩ := hcut ρ₀ ρ hρ₀0 hρ₀ρ
    have hζtsR : tsupport ζ ⊆ Metric.ball x₀ R :=
      hζts.trans (Metric.ball_subset_ball hρR)
    have hKcpt : IsCompact (tsupport ζ) := hζcs
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
    -- measurability and integrability on the support
    have hgm : ∀ i : Fin n, AEStronglyMeasurable (fun x => g x i)
        (volume.restrict (tsupport ζ)) := fun i =>
      (((hDg i).2 (tsupport ζ) hKcpt hζtsR).1).1
    have hDgm : AEStronglyMeasurable (Dg k) (volume.restrict (tsupport ζ)) :=
      (((hDg k).2 (tsupport ζ) hKcpt hζtsR).2).1
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
    have hDgsq : IntegrableOn (fun x => ‖Dg k x‖ ^ 2) (tsupport ζ) volume := by
      have hmem := ((hDg k).2 (tsupport ζ) hKcpt hζtsR).2
      have h1 : Integrable (fun x => ‖Dg k x‖ ^ (ENNReal.ofReal 2).toReal)
          (volume.restrict (tsupport ζ)) :=
        hmem.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
      rw [show (ENNReal.ofReal 2).toReal = 2 from by simp] at h1
      refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
      show ‖Dg k x‖ ^ (2:ℝ) = ‖Dg k x‖ ^ 2
      rw [← Real.rpow_natCast ‖Dg k x‖ 2]
      norm_num
    have hKmeas : MeasurableSet (tsupport ζ) := (isClosed_tsupport ζ).measurableSet
    -- globalisation: an integrand vanishing off `tsupport ζ` and dominated there
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
    obtain ⟨W2, hW2def⟩ : ∃ t : ℝ, t = ((1 + 4 * (n:ℝ)) * lam ^ 2) ^ (p / 2 - 1) :=
      ⟨_, rfl⟩
    have hW20 : 0 < W2 := by
      rw [hW2def]; exact Real.rpow_pos_of_pos (by positivity) _
    have hwpow : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
        (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) ≤ W2 := by
      filter_upwards [hwup] with x hx
      rw [hW2def]
      exact Real.rpow_le_rpow (by positivity) hx hexp0
    have hwpowK : ∀ᵐ x ∂(volume.restrict (tsupport ζ)),
        (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) ≤ W2 :=
      ae_restrict_of_ae_restrict_of_subset hζtsR hwpow
    -- the two integrands that need integrability
    have hintB : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
        IntegrableOn (fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
          S volume := by
      intro S
      refine Integrable.mono_measure ?_ Measure.restrict_le_self
      refine hglob _ ((tsupport ζ).indicator (fun x => W2 * ‖Dg k x‖ ^ 2))
        ((integrable_indicator_iff hKmeas).2 (hDgsq.const_mul W2)) ?_ ?_ ?_ ?_
      · have hwrpow : AEStronglyMeasurable
            (fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1))
            (volume.restrict (tsupport ζ)) :=
          ((hwm.aemeasurable.const_add ε).pow_const _).aestronglyMeasurable
        exact (hwrpow.mul (hDgm.norm.pow 2)).mul
          ((hζsm.continuous.aestronglyMeasurable).pow 2)
      · intro x hx; rw [hζ0out x hx]; ring
      · intro x hx; rw [Set.indicator_of_notMem hx]
      · filter_upwards [ae_restrict_mem hKmeas, hwpowK] with x hx hw
        rw [Set.indicator_of_mem hx]
        have h1 : (0:ℝ) ≤ (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) :=
          Real.rpow_nonneg (le_trans hε.le (hwlow x)) _
        have h2 : ζ x ^ 2 ≤ 1 := pow_le_one₀ (hζnn x) (hζle1 x)
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (mul_nonneg h1 (sq_nonneg _)) (sq_nonneg _))]
        calc (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2
            ≤ W2 * ‖Dg k x‖ ^ 2 * ζ x ^ 2 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hw (sq_nonneg _)) (sq_nonneg _)
          _ ≤ W2 * ‖Dg k x‖ ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left h2 (mul_nonneg hW20.le (sq_nonneg _))
          _ = W2 * ‖Dg k x‖ ^ 2 := mul_one _
    -- the rpow bookkeeping of the constant
    have hW2val : W2 = (1 + 4 * (n:ℝ)) ^ (p / 2 - 1) * lam ^ (p - 2) := by
      rw [hW2def, Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      rw [← Real.rpow_natCast lam 2, ← Real.rpow_mul hlam0.le]
      congr 1
      push_cast
      ring
    have hlampow : (lam ^ (p / 2)) ^ 2 = lam ^ p := by
      rw [← Real.rpow_natCast (lam ^ (p / 2)) 2, ← Real.rpow_mul hlam0.le]
      congr 1
      push_cast
      ring
    have hlamsplit : lam ^ (p - 2) * lam ^ 2 = lam ^ p := by
      rw [← Real.rpow_natCast lam 2, ← Real.rpow_add hlam0]
      congr 1
      push_cast
      ring
    have hσρ : (0:ℝ) < σ * ρ := by positivity
    have hsq0 : (0:ℝ) < (σ * ρ) ^ 2 := by positivity
    have hCmax : (0:ℝ) < max 1 Ca := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hCale : Ca ≤ max 1 Ca := le_max_right _ _
    have hcommon : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
        (0:ℝ) ≤ max 1 Ca * (lam ^ (p / 2)) ^ 2 / (σ * ρ) ^ 2
          * (volume (Metric.ball x₀ ρ ∩ S)).toReal := fun S =>
      mul_nonneg (div_nonneg (mul_nonneg hCmax.le (sq_nonneg _)) hsq0.le)
        ENNReal.toReal_nonneg
    -- the coordinate bound and `|g^k|^{p-2} ≤ w^{p/2-1}`
    have hcoordle : ∀ (y : EuclideanSpace ℝ (Fin n)) (i : Fin n), (y i) ^ 2 ≤ ‖y‖ ^ 2 := by
      intro y i
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (f := fun j => (y j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hwge : ∀ x : EuclideanSpace ℝ (Fin n),
        |g x k| ^ (p - 2) ≤ (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) := by
      intro x
      have h1 : |g x k| ^ 2 ≤ ε + ‖g x‖ ^ 2 :=
        calc |g x k| ^ 2 = (g x k) ^ 2 := sq_abs _
          _ ≤ ‖g x‖ ^ 2 := hcoordle (g x) k
          _ ≤ ε + ‖g x‖ ^ 2 := le_add_of_nonneg_left hε.le
      have h2 : (|g x k| ^ 2 : ℝ) ^ (p / 2 - 1) = |g x k| ^ (p - 2) := by
        rw [← Real.rpow_natCast |g x k| 2, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        push_cast
        ring
      rw [← h2]
      exact Real.rpow_le_rpow (sq_nonneg _) h1 hexp0
    -- the common core of the two sides
    have core : ∀ (S : Set (EuclideanSpace ℝ (Fin n)))
        (d : EuclideanSpace ℝ (Fin n) → ℝ),
        (∫ x in Metric.ball x₀ R ∩ S,
            (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
          ≤ c₄ * ∫ x in Metric.ball x₀ R, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * d x ^ 2
              * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 →
        (∀ x, 0 ≤ d x) →
        (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), d x ≤ 3 * lam) →
        (∀ x, x ∉ S → d x = 0) →
        (∫ x in Metric.ball x₀ ρ₀ ∩ S,
            ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2)
          ≤ max 1 Ca * (lam ^ (p / 2)) ^ 2 / (σ * ρ) ^ 2
            * (volume (Metric.ball x₀ ρ ∩ S)).toReal :=
      SignedPowerLevelTransportSuperquadratic n p L c₄ Ca ε lam ρ σ ρ₀ W2 R g Dg k
        ζ x₀ hc₄0 hε hlam0 hL0 hρ hσ hCadef hwlow hVnorm hwge hρR hρ₀ρ hdρ hζts
        hζone hζgrad hDz0 hW20 hwpow hintB hW2val hlampow hlamsplit hsq0 hCale
        hcommon
    have hμlam : μ = 2 * lam := by rw [hlamdef]; ring
    constructor
    · -- the `+` side
      intro hh
      obtain ⟨l, hldef⟩ : ∃ t : ℝ, t = |h| ^ (2 / p - 1) * h := ⟨_, rfl⟩
      have hφl : φ l = h := by rw [hldef]; exact hφsurj h
      have hlge : -lam ≤ l := by
        have h1 : φ (-lam) ≤ φ l := by
          rw [hφneg, hφlam, hφl]
          have hh' : -(lam ^ (p / 2)) ≤ h := by rw [hlamdef]; exact hh
          exact hh'
        exact (hφmono.le_iff_le).1 h1
      have hset : {y : EuclideanSpace ℝ (Fin n) | l < g y k}
          = {y | h < |g y k| ^ (p / 2 - 1) * g y k} := by
        ext y
        constructor
        · intro hy
          show h < |g y k| ^ (p / 2 - 1) * g y k
          have := hφmono hy
          rw [hφl, hφdef] at this
          exact this
        · intro hy
          show l < g y k
          have hy' : φ l < φ (g y k) := by
            rw [hφl, hφdef]
            exact hy
          exact hφmono.lt_iff_lt.1 hy'
      have hcacc := (hCacc ε γ₀ γ₁ (Metric.ball x₀ R) A u g Dg ζ k l hε hγ₀ hγ₁
        Metric.isOpen_ball hQ hC1 hsol hDg hζsm hζcs hζtsR).1
      rw [hset] at hcacc
      have hres := core {y | h < |g y k| ^ (p / 2 - 1) * g y k}
        (fun x => max (g x k - l) 0) hcacc (fun x => le_max_right _ _) ?_ ?_
      · rw [hρ₀def] at hres
        rw [← hlamdef]
        exact hres
      · filter_upwards [hbd k] with x hx
        have h1 : g x k ≤ μ := le_trans (le_abs_self _) hx
        rw [hμlam] at h1
        refine max_le ?_ (mul_nonneg (by norm_num) hlam0.le)
        linarith only [h1, hlge]
      · intro x hx
        have h2 : ¬ (l < g x k) := by
          intro hc
          exact hx (by rw [← hset]; exact hc)
        exact max_eq_right (by linarith only [not_lt.1 h2])
    · -- the `-` side
      intro hh
      obtain ⟨l, hldef⟩ : ∃ t : ℝ, t = |h| ^ (2 / p - 1) * h := ⟨_, rfl⟩
      have hφl : φ l = h := by rw [hldef]; exact hφsurj h
      have hlle : l ≤ lam := by
        have h1 : φ l ≤ φ lam := by
          rw [hφlam, hφl]
          have hh' : h ≤ lam ^ (p / 2) := by rw [hlamdef]; exact hh
          exact hh'
        exact (hφmono.le_iff_le).1 h1
      have hset : {y : EuclideanSpace ℝ (Fin n) | g y k < l}
          = {y | |g y k| ^ (p / 2 - 1) * g y k < h} := by
        ext y
        constructor
        · intro hy
          show |g y k| ^ (p / 2 - 1) * g y k < h
          have := hφmono hy
          rw [hφl, hφdef] at this
          exact this
        · intro hy
          show g y k < l
          have hy' : φ (g y k) < φ l := by
            rw [hφl, hφdef]
            exact hy
          exact hφmono.lt_iff_lt.1 hy'
      have hcacc := (hCacc ε γ₀ γ₁ (Metric.ball x₀ R) A u g Dg ζ k l hε hγ₀ hγ₁
        Metric.isOpen_ball hQ hC1 hsol hDg hζsm hζcs hζtsR).2
      rw [hset] at hcacc
      have hres := core {y | |g y k| ^ (p / 2 - 1) * g y k < h}
        (fun x => max (l - g x k) 0) hcacc (fun x => le_max_right _ _) ?_ ?_
      · rw [hρ₀def] at hres
        rw [← hlamdef]
        exact hres
      · filter_upwards [hbd k] with x hx
        have h1 : -μ ≤ g x k := neg_le_of_abs_le hx
        rw [hμlam] at h1
        refine max_le ?_ (mul_nonneg (by norm_num) hlam0.le)
        linarith only [h1, hlle]
      · intro x hx
        have h2 : ¬ (g x k < l) := by
          intro hc
          exact hx (by rw [← hset]; exact hc)
        show max (l - g x k) 0 = 0
        exact max_eq_right (by linarith only [not_lt.1 h2])
  · -- THE REGIME `1 < p < 2`: the subquadratic node, whose statement is
    -- this one with `p < 2` added.
    exact SignedPowerGradientEstimateSubquadratic n p r hn hp hp2 hr
