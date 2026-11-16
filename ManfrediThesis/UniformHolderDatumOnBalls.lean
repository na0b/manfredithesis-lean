import ManfrediThesis.Preamble
import ManfrediThesis.IsBoundedLipschitzDomain
import ManfrediThesis.BallIsLipschitzDomain
import ManfrediThesis.CampanatoBoundOn
import ManfrediThesis.MorreyBoundOn
import ManfrediThesis.MemHolderOn
import ManfrediThesis.CitedCampanatoEmbedding
open MeasureTheory

/-- The Hölder datum of §4 and §5 at the *fixed* exponent `1/2`, with a constant
uniform in the centre.  From a Campanato bound at the exponent `n/(n-1)` on each
ball `B_{d/4}(y₀)`, `y₀ ∈ Ω'`, with one constant `N₂`, the cited Campanato
embedding (C5) -- applied once, at the ball of the *origin*, so that the
constant it returns is bound before the data -- gives a single `C₁` such that the
continuous representative `U` obeys `|U x - U y| ≤ C₁ dist(x,y)^{1/2}` on every
closed ball of radius at most `d/16` centred in `Ω'`.  This is the datum both
`ComparisonSchemeCampanatoCore` and the Lemma 4.1 / 5.1 rate clauses ask for,
and the fixed exponent is what keeps the exponents of Theorems 4 and 6 free of
`‖u‖_{L^∞}`. -/
theorem UniformHolderDatumOnBalls :
    ∀ (n : ℕ) (p τ d M N₂ : ℝ),
      2 ≤ n → 1 < p → 0 < τ → τ ≤ p / 2 → 0 < d → 0 ≤ M → 0 ≤ N₂ →
      CitedCampanatoEmbedding n ((n : ℝ) / ((n : ℝ) - 1))
        (Metric.ball 0 (d / 4)) →
      ∃ C₁ : ℝ, 0 ≤ C₁ ∧
        ∀ (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
          (u U : EuclideanSpace ℝ (Fin n) → ℝ),
          IsOpen Ω →
          (∀ x ∈ Ω', ∀ y, y ∉ Ω → d ≤ dist x y) →
          (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
          (∀ᵐ x ∂(volume.restrict Ω), U x = u x) →
          (∀ y₀ ∈ Ω', ContinuousOn U (Metric.ball y₀ (d / 4))) →
          (∀ y₀ ∈ Ω', CampanatoBoundOn n ((n : ℝ) / ((n : ℝ) - 1))
            ((n : ℝ) + (1 - τ / p) * ((n : ℝ) / ((n : ℝ) - 1)))
            (Metric.ball y₀ (d / 4)) u N₂) →
          ∀ x₀ ∈ Ω', ∀ R : ℝ, 0 < R → R ≤ d / 16 →
            MemHolderOn n (1 / 2) (Metric.closedBall x₀ R) U ∧
              ∀ x ∈ Metric.closedBall x₀ R, ∀ y ∈ Metric.closedBall x₀ R,
                |U x - U y| ≤ C₁ * dist x y ^ ((1 : ℝ) / 2) := by
  intro n p τ d M N₂ hn hp hτ0 hτp hd hM hN₂ hC5
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnm1 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  set q : ℝ := (n:ℝ)/((n:ℝ)-1) with hqdef
  have hq0 : 0 < q := div_pos (by linarith) hnm1
  set s : ℝ := 1 - τ/p with hsdef
  have hτpos : 0 < τ/p := div_pos hτ0 hp0
  have hτhalf : τ/p ≤ 1/2 := by rw [div_le_iff₀ hp0]; linarith
  have hs2 : (1:ℝ)/2 ≤ s := by rw [hsdef]; linarith
  have hs1 : s < 1 := by rw [hsdef]; linarith
  have hs0 : 0 < s := by linarith
  have hlam1 : (n:ℝ) < (n:ℝ) + s * q := by nlinarith
  have hlam2 : (n:ℝ) + s * q < (n:ℝ) + q := by nlinarith
  have hdq : (0:ℝ) < d/4 := by linarith
  have hlip : IsBoundedLipschitzDomain n
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4)) :=
    BallIsLipschitzDomain n hn1 0 (d/4) hdq
  set V : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4))).toReal with hVdef
  have hV0 : (0:ℝ) ≤ V := ENNReal.toReal_nonneg
  set Nnat : ℝ := max N₂ (M * V ^ (1/q)) with hNnatdef
  have hNnat0 : (0:ℝ) ≤ Nnat := le_trans hN₂ (le_max_left _ _)
  obtain ⟨Nh, hNh0, hNh⟩ := hC5 hlip ((n:ℝ) + s * q) hlam1 hlam2 Nnat hNnat0
  have hmax1 : (1:ℝ) ≤ max 1 d := le_max_left _ _
  have hpow0 : (0:ℝ) < (max 1 d) ^ (s - 1/2) :=
    Real.rpow_pos_of_pos (by linarith) _
  refine ⟨Nh * (max 1 d) ^ (s - 1/2), mul_nonneg hNh0 hpow0.le, ?_⟩
  intro Ω Ω' u U hΩ hsep hubd hUeq hUcont hcamp x₀ hx₀ R hR0 hRd
  -- the ball at the centre lies in Ω
  have hBcl : Metric.closedBall x₀ (d/4) ⊆ Ω := by
    intro z hz
    by_contra hzn
    have h1 := hsep x₀ hx₀ z hzn
    rw [Metric.mem_closedBall, dist_comm] at hz
    linarith
  have hBsub : Metric.ball x₀ (d/4) ⊆ Ω :=
    Metric.ball_subset_closedBall.trans hBcl
  have hRsub : Metric.closedBall x₀ R ⊆ Metric.ball x₀ (d/4) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    linarith
  -- translation machinery
  set T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun z => z + x₀ with hT
  have hmp : MeasurePreserving T volume volume := measurePreserving_add_right volume x₀
  have hme : MeasurableEmbedding T := (MeasurableEquiv.addRight x₀).measurableEmbedding
  have hpre : ∀ (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ),
      T ⁻¹' Metric.ball (c + x₀) ρ = Metric.ball c ρ := by
    intro c ρ; ext z; simp [hT, Metric.mem_ball, dist_eq_norm]
  have hpre0 : T ⁻¹' Metric.ball x₀ (d/4) = Metric.ball 0 (d/4) := by
    have := hpre 0 (d/4); simpa using this
  have hvol : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      volume (T ⁻¹' A) = volume A := fun A hA => hmp.measure_preimage hA.nullMeasurableSet
  have hsi : ∀ (A : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ),
      ∫ z in T ⁻¹' A, f (T z) = ∫ y in A, f y := fun A f =>
    hmp.setIntegral_preimage_emb hme f A
  have hmpr : MeasurePreserving T (volume.restrict (Metric.ball 0 (d/4)))
      (volume.restrict (Metric.ball x₀ (d/4))) := by
    have hh := hmp.restrict_preimage (measurableSet_ball :
      MeasurableSet (Metric.ball x₀ (d/4)))
    rwa [hpre0] at hh
  have hdiameq : Metric.diam (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4))
      = Metric.diam (Metric.ball x₀ (d/4)) := by
    have himg : (IsometryEquiv.addRight x₀) ''
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4) = Metric.ball x₀ (d/4) := by
      rw [IsometryEquiv.image_ball]; simp
    rw [← himg, (IsometryEquiv.addRight x₀).isometry.diam_image]
  -- (T1) the Campanato datum, widened to Nnat and transported to the origin's ball
  have hT1 : CampanatoBoundOn n q ((n:ℝ) + s * q)
      (Metric.ball 0 (d/4)) (fun z => u (z + x₀)) Nnat := by
    obtain ⟨h1, h2⟩ := hcamp x₀ hx₀
    refine ⟨?_, ?_⟩
    · simpa [hT, Function.comp_def] using h1.comp_measurePreserving hmpr
    · intro x hx ρ hρ hdm
      have hdm' : ρ < Metric.diam (Metric.ball x₀ (d/4)) := by rwa [← hdiameq]
      have hxmem : x + x₀ ∈ Metric.ball x₀ (d/4) := by
        simpa [Metric.mem_ball, dist_eq_norm] using hx
      have key := h2 (x + x₀) hxmem ρ hρ hdm'
      have hset : T ⁻¹' (Metric.ball x₀ (d/4) ∩ Metric.ball (x + x₀) ρ)
          = Metric.ball 0 (d/4) ∩ Metric.ball x ρ := by
        rw [Set.preimage_inter, hpre0, hpre x ρ]
      have hv : volume (Metric.ball 0 (d/4) ∩ Metric.ball x ρ)
          = volume (Metric.ball x₀ (d/4) ∩ Metric.ball (x + x₀) ρ) := by
        rw [← hset, hvol _ (measurableSet_ball.inter measurableSet_ball)]
      have hmean : (∫ w in Metric.ball 0 (d/4) ∩ Metric.ball x ρ, u (w + x₀))
          = ∫ w in Metric.ball x₀ (d/4) ∩ Metric.ball (x + x₀) ρ, u w := by
        rw [← hset]; exact hsi _ u
      have hmain : (∫ y in Metric.ball 0 (d/4) ∩ Metric.ball x ρ,
          |u (y + x₀) - (volume (Metric.ball 0 (d/4) ∩ Metric.ball x ρ)).toReal⁻¹
            * ∫ w in Metric.ball 0 (d/4) ∩ Metric.ball x ρ, u (w + x₀)| ^ q)
          = ∫ y in Metric.ball x₀ (d/4) ∩ Metric.ball (x + x₀) ρ,
              |u y - (volume (Metric.ball x₀ (d/4) ∩ Metric.ball (x + x₀) ρ)).toReal⁻¹
                * ∫ w in Metric.ball x₀ (d/4) ∩ Metric.ball (x + x₀) ρ, u w| ^ q := by
        rw [hv, hmean, ← hset]
        exact hsi _ (fun y => |u y
          - (volume (Metric.ball x₀ (d/4) ∩ Metric.ball (x + x₀) ρ)).toReal⁻¹
            * ∫ w in Metric.ball x₀ (d/4) ∩ Metric.ball (x + x₀) ρ, u w| ^ q)
      rw [hmain]
      refine le_trans key ?_
      have hmono : N₂ ^ q ≤ Nnat ^ q := Real.rpow_le_rpow hN₂ (le_max_left _ _) hq0.le
      exact mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hρ.le _)
  -- (T2) the Morrey datum at exponent 0, from |u| ≤ M
  have hballfin : IsFiniteMeasure
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hVtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4)) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hubdB : ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4))),
      |u (z + x₀)| ≤ M := by
    have h1 : ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ (d/4))), |u y| ≤ M :=
      ae_restrict_of_ae_restrict_of_subset hBsub hubd
    exact hmpr.quasiMeasurePreserving.ae h1
  have hintball : Integrable (fun z => |u (z + x₀)| ^ q)
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4))) := by
    have h := hT1.1.integrable_norm_rpow'
    rw [ENNReal.toReal_ofReal hq0.le] at h
    simpa [Real.norm_eq_abs] using h
  have hT2 : MorreyBoundOn n q 0 (Metric.ball 0 (d/4)) (fun z => u (z + x₀)) Nnat := by
    refine ⟨hT1.1, ?_⟩
    intro x hx ρ hρ hdm
    rw [Real.rpow_zero, mul_one]
    have hSsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4) ∩ Metric.ball x ρ
        ⊆ Metric.ball 0 (d/4) := Set.inter_subset_left
    have hSfin : IsFiniteMeasure (volume.restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4) ∩ Metric.ball x ρ)) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_lt (measure_mono hSsub) measure_ball_lt_top⟩
    have hbd : ∀ᵐ z ∂(volume.restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4) ∩ Metric.ball x ρ)),
        |u (z + x₀)| ^ q ≤ M ^ q := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hSsub hubdB] with z hz
      exact Real.rpow_le_rpow (abs_nonneg _) hz hq0.le
    have hintS : Integrable (fun z => |u (z + x₀)| ^ q) (volume.restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4) ∩ Metric.ball x ρ)) :=
      hintball.mono_measure (Measure.restrict_mono hSsub le_rfl)
    have hstep1 : (∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4) ∩ Metric.ball x ρ,
        |u (y + x₀)| ^ q)
        ≤ ∫ _y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4) ∩ Metric.ball x ρ, M ^ q :=
      integral_mono_ae hintS (integrable_const _) hbd
    have hMq0 : (0:ℝ) ≤ M ^ q := Real.rpow_nonneg hM _
    have hstep2 : (∫ _y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4) ∩ Metric.ball x ρ,
        M ^ q) ≤ M ^ q * V := by
      rw [setIntegral_const, smul_eq_mul]
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ hMq0
      rw [hVdef]
      exact ENNReal.toReal_mono hVtop (measure_mono hSsub)
    have hstep3 : M ^ q * V ≤ Nnat ^ q := by
      have hval : (M * V ^ (1/q)) ^ q = M ^ q * V := by
        rw [Real.mul_rpow hM (Real.rpow_nonneg hV0 _), ← Real.rpow_mul hV0,
          one_div_mul_cancel hq0.ne', Real.rpow_one]
      rw [← hval]
      exact Real.rpow_le_rpow (mul_nonneg hM (Real.rpow_nonneg hV0 _))
        (le_max_right _ _) hq0.le
    linarith [hstep1, hstep2, hstep3]
  -- the (C5) conclusion at the origin's ball
  have hexp : ((n:ℝ) + s * q - (n:ℝ))/q = s := by field_simp; ring
  obtain ⟨w0, hw0eq, hw0hol, hw0bd⟩ := hNh (fun z => u (z + x₀)) hT1 hT2
  rw [hexp] at hw0hol hw0bd
  -- translate back
  have hmp2 : MeasurePreserving (fun y : EuclideanSpace ℝ (Fin n) => y - x₀) volume volume := by
    simpa [sub_eq_add_neg] using measurePreserving_add_right volume (-x₀)
  have hpre2 : (fun y : EuclideanSpace ℝ (Fin n) => y - x₀) ⁻¹'
      Metric.ball 0 (d/4) = Metric.ball x₀ (d/4) := by
    ext z; simp [Metric.mem_ball, dist_eq_norm]
  have hmpr' : MeasurePreserving (fun y : EuclideanSpace ℝ (Fin n) => y - x₀)
      (volume.restrict (Metric.ball x₀ (d/4)))
      (volume.restrict (Metric.ball 0 (d/4))) := by
    have hh := hmp2.restrict_preimage (measurableSet_ball :
      MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4)))
    rwa [hpre2] at hh
  have hueqw : ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ (d/4))), u y = w0 (y - x₀) := by
    have hh := hmpr'.quasiMeasurePreserving.ae hw0eq
    filter_upwards [hh] with y hy
    simpa using hy
  have hmaps : ∀ y ∈ Metric.ball x₀ (d/4),
      (y - x₀) ∈ closure (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (d/4)) := by
    intro y hy
    refine subset_closure ?_
    rw [Metric.mem_ball] at hy ⊢
    simpa [dist_eq_norm] using hy
  have hwcont : ContinuousOn (fun z => w0 (z - x₀)) (Metric.ball x₀ (d/4)) := by
    have hc : ContinuousOn (fun y : EuclideanSpace ℝ (Fin n) => y - x₀)
        (Metric.ball x₀ (d/4)) := (continuous_id.sub continuous_const).continuousOn
    exact hw0hol.1.comp hc hmaps
  have hUeqB : ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ (d/4))), U y = w0 (y - x₀) := by
    have h1 : ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ (d/4))), U y = u y :=
      ae_restrict_of_ae_restrict_of_subset hBsub hUeq
    filter_upwards [h1, hueqw] with y h2 h3
    rw [h2, h3]
  have hUw : Set.EqOn U (fun z => w0 (z - x₀)) (Metric.ball x₀ (d/4)) :=
    Measure.eqOn_open_of_ae_eq hUeqB Metric.isOpen_ball (hUcont x₀ hx₀) hwcont
  -- the two-point bound at the fixed exponent 1/2
  have hkey : ∀ x ∈ Metric.closedBall x₀ R, ∀ y ∈ Metric.closedBall x₀ R,
      |U x - U y| ≤ Nh * (max 1 d) ^ (s - 1/2) * dist x y ^ ((1:ℝ)/2) := by
    intro x hx y hy
    rcases eq_or_ne x y with rfl | hne
    · simp [Real.zero_rpow]
    have hxB := hRsub hx
    have hyB := hRsub hy
    rw [hUw hxB, hUw hyB]
    have hb := hw0bd (x - x₀) (hmaps x hxB) (y - x₀) (hmaps y hyB)
    have hdd : dist (x - x₀) (y - x₀) = dist x y := by
      simp [dist_eq_norm, sub_sub_sub_cancel_right]
    rw [hdd] at hb
    have ht : (0:ℝ) < dist x y := dist_pos.2 hne
    have htle : dist x y ≤ max 1 d := by
      rw [Metric.mem_closedBall] at hx hy
      have h1 : dist x y ≤ R + R := by
        calc dist x y ≤ dist x x₀ + dist x₀ y := dist_triangle _ _ _
          _ ≤ R + R := by rw [dist_comm x₀ y]; linarith
      have h2 : R + R ≤ d := by linarith
      calc dist x y ≤ R + R := h1
        _ ≤ d := h2
        _ ≤ max 1 d := le_max_right _ _
    have hsplit : dist x y ^ s = dist x y ^ ((1:ℝ)/2) * dist x y ^ (s - 1/2) := by
      rw [← Real.rpow_add ht]; ring_nf
    have hmono : dist x y ^ (s - 1/2) ≤ (max 1 d) ^ (s - 1/2) :=
      Real.rpow_le_rpow ht.le htle (by linarith)
    calc |w0 (x - x₀) - w0 (y - x₀)| ≤ Nh * dist x y ^ s := hb
      _ = Nh * (dist x y ^ ((1:ℝ)/2) * dist x y ^ (s - 1/2)) := by rw [hsplit]
      _ ≤ Nh * (dist x y ^ ((1:ℝ)/2) * (max 1 d) ^ (s - 1/2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hNh0
          exact mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg dist_nonneg _)
      _ = Nh * (max 1 d) ^ (s - 1/2) * dist x y ^ ((1:ℝ)/2) := by ring
  exact ⟨⟨(hUcont x₀ hx₀).mono hRsub, Nh * (max 1 d) ^ (s - 1/2),
    mul_nonneg hNh0 hpow0.le, hkey⟩, hkey⟩
