import ManfrediThesis.Preamble
import ManfrediThesis.DeGiorgiLevelBound
import ManfrediThesis.MemW1pLocOn
set_option maxHeartbeats 1600000
open MeasureTheory

/-- A weighted Caccioppoli inequality above a level yields the De Giorgi level
bound: if `(F, Γ)` is a `W^{1,2}_loc` pair on `B_R(x₀)` with `|F| ≤ Θ`, if the
weight `w` is pinched between `κ₁` and `κ₂` on the super-level set
`B_R(x₀) ∩ {ℓ < F}`, and if the weighted Caccioppoli inequality
\[
∫_{B_R∩\{ℓ<F\}}w^s\|Γ\|^2ζ'^2
  \ \le\ c∫_{B_R}w^s\bigl((F-ℓ)^+\bigr)^2|∇ζ'|^2
\]
holds for every smooth compactly supported cut-off `ζ'` on `B_R(x₀)`, then
`DeGiorgiLevelBound n γ F Γ x₀ ℓ ρ₀ ρ₁` holds with
`γ = cK^{2|s|}(1 + L)`.

Conventions, restated here because a helper inherits none of its parent's.
`supp ζ` means `tsupport ζ`, the CLOSED support, and `|∇ζ|²` abbreviates
`∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i 1))²`; `(F-ℓ)^+` is
`max (F x - ℓ) 0`; `w^s` is the real power of the positive weight, with `s` an
arbitrary real, so the pinch hypothesis is what controls it in both directions
and no sign hypothesis on `s` is needed.  The cut-off `ζ` is supplied as data
together with its seven clauses, exactly in the form
\noderef{StandardRadialCutoff} returns them, with the gradient bound
`|∇ζ|² ≤ L/(ρ₁ - ρ₀)²`; `L` is that node's absolute constant and enters `γ`
through the defining equation.  `K` is the pinch ratio and `hratio` the
one-dimensional comparison `a^s ≤ K^{|s|}b^s` it yields.

The route.  Insert the fixed cut-off `ζ` into the Caccioppoli hypothesis.  On
the super-level set the weight is pinched, so `w^s` may be replaced by the
constant `κ₁^s` up to the factor `K^{|s|}` on the left and by the same constant
up to `K^{|s|}` on the right, which is exactly what `hratio` provides; the two
replacements are what make the resulting inequality weight-free and are the
reason the constant carries `K^{2|s|}` rather than `K^{|s|}`.  Since `ζ = 1` on
the closed ball of radius `ρ₀` and `supp ζ ⊆ B_{ρ₁}(x₀)`, the left-hand side
dominates the integral of `\|Γ\|^2` over `B_{ρ₀}∩\{ℓ<F\}` and the right-hand
side is dominated by
`cL(ρ₁-ρ₀)^{-2}∫_{B_{ρ₁}}\bigl((F-ℓ)^+\bigr)^2`, using the gradient bound and
the containment of supports.  Finally `(F-ℓ)^+ ≤ Θ + |ℓ|` almost everywhere by
the bound on `|F|`, and the two pieces assemble into the inequality
`DeGiorgiLevelBound` asserts, with the constant `γ = cK^{2|s|}(1+L)`: the `1`
absorbs the term coming from the region where the cut-off is already `1` and
the `L` the term coming from its gradient. -/
theorem WeightedCaccioppoliToDeGiorgiLevelBound :
    ∀ (n : ℕ) (s K c L γ R Θ κ₁ κ₂ ρ₀ ρ₁ : ℝ)
      (x₀ : EuclideanSpace ℝ (Fin n))
      (w ζ : EuclideanSpace ℝ (Fin n) → ℝ),
      0 < c → 0 < K → 0 < L → 0 < R → 0 < κ₁ → κ₂ ≤ K * κ₁ → Measurable w →
      γ = c * K ^ (2 * |s|) * (1 + L) →
      (0:ℝ) < K ^ (2 * |s|) →
      ρ₀ < ρ₁ → ρ₁ < R → (0:ℝ) < ρ₁ → (0:ℝ) < ρ₁ - ρ₀ →
      (∀ a b : ℝ, 0 < a → 0 < b → a ≤ K * b → b ≤ K * a →
        a ^ s ≤ K ^ |s| * b ^ s) →
      ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball x₀ ρ₁ →
      (∀ x, 0 ≤ ζ x) → (∀ x, ζ x ≤ 1) →
      (∀ x ∈ Metric.closedBall x₀ ρ₀, ζ x = 1) →
      (∀ x, ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2
        ≤ L / (ρ₁ - ρ₀) ^ 2) →
      ∀ (F : EuclideanSpace ℝ (Fin n) → ℝ)
      (Γ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (ℓ : ℝ),
      MemW1pLocOn n 2 (Metric.ball x₀ R) F Γ →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), |F x| ≤ Θ) →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R ∩ {y | ℓ < F y})),
      κ₁ ≤ w x ∧ w x ≤ κ₂) →
      (∀ ζ' : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ζ' → HasCompactSupport ζ' →
      tsupport ζ' ⊆ Metric.ball x₀ R →
      (∫ x in Metric.ball x₀ R ∩ {y | ℓ < F y},
      w x ^ s * ‖Γ x‖ ^ 2 * ζ' x ^ 2)
      ≤ c * ∫ x in Metric.ball x₀ R, w x ^ s * max (F x - ℓ) 0 ^ 2
      * ∑ i, (fderiv ℝ ζ' x (EuclideanSpace.single i (1 : ℝ))) ^ 2) →
      DeGiorgiLevelBound n γ F Γ x₀ ℓ ρ₀ ρ₁ := by
  intro n s K c L γ R Θ κ₁ κ₂ ρ₀ ρ₁ x₀ w ζ hc hK0 hL0 hR hκ₁ hκ₂ hwm hγdef hKabs
    hρ01 hρ1R hρ₁ hdpos hratio hζsm hζcs hζts hζnn hζle1 hζone hζgrad
  intro F Γ ℓ hFW hFΘ hp hcac
  -- (4a): `Θ ≥ 0` and the pointwise bound on `(F-ℓ)^+`
  have hNBR : (ae (volume.restrict (Metric.ball x₀ R))).NeBot := by
    rw [ae_neBot]
    intro hcc
    rw [← Measure.measure_univ_eq_zero, Measure.restrict_apply_univ] at hcc
    exact (Metric.measure_ball_pos volume x₀ hR).ne' hcc
  have hΘ0 : (0:ℝ) ≤ Θ := by
    obtain ⟨x, hx⟩ := hFΘ.exists
    exact le_trans (abs_nonneg _) hx
  obtain ⟨Θℓ, hΘℓdef⟩ : ∃ t : ℝ, t = Θ + |ℓ| := ⟨_, rfl⟩
  have hΘℓ0 : (0:ℝ) ≤ Θℓ := by rw [hΘℓdef]; positivity
  have hsub1 : Metric.ball x₀ ρ₁ ⊆ Metric.ball x₀ R := Metric.ball_subset_ball hρ1R.le
  have hbdR : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), max (F x - ℓ) 0 ≤ Θℓ := by
    filter_upwards [hFΘ] with x hx
    refine max_le ?_ hΘℓ0
    rw [hΘℓdef]
    have h1 := abs_le.1 hx
    have h2 := neg_abs_le ℓ
    linarith [h1.2]
  have hbd1 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ₁)), max (F x - ℓ) 0 ≤ Θℓ :=
    ae_restrict_of_ae_restrict_of_subset hsub1 hbdR
  refine ⟨⟨Θℓ, hbd1⟩, ?_⟩
  -- the essential supremum `S`
  obtain ⟨S, hSdef⟩ : ∃ t : ℝ, t = essSup (fun x => max (F x - ℓ) 0 ^ 2)
      (volume.restrict (Metric.ball x₀ ρ₁)) := ⟨_, rfl⟩
  have hbd1sq : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ₁)),
      max (F x - ℓ) 0 ^ 2 ≤ Θℓ ^ 2 := by
    filter_upwards [hbd1] with x hx
    exact pow_le_pow_left₀ (le_max_right _ _) hx 2
  have hSbd : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ₁)),
      max (F x - ℓ) 0 ^ 2 ≤ S := by
    rw [hSdef]
    exact ae_le_essSup ⟨Θℓ ^ 2, hbd1sq⟩
  have hNB1 : (ae (volume.restrict (Metric.ball x₀ ρ₁))).NeBot := by
    rw [ae_neBot]
    intro hcc
    rw [← Measure.measure_univ_eq_zero, Measure.restrict_apply_univ] at hcc
    exact (Metric.measure_ball_pos volume x₀ hρ₁).ne' hcc
  have hS0 : (0:ℝ) ≤ S := by
    obtain ⟨x, hx⟩ := hSbd.exists
    exact le_trans (sq_nonneg _) hx
  rw [← hSdef]
  obtain ⟨V, hVdef⟩ : ∃ t : ℝ,
    t = (volume (Metric.ball x₀ ρ₁ ∩ {y | ℓ < F y})).toReal := ⟨_, rfl⟩
  rw [← hVdef]
  -- the cut-off, specialised
  have hζtsR : tsupport ζ ⊆ Metric.ball x₀ R := hζts.trans hsub1
  have hcacζ := hcac ζ hζsm hζcs hζtsR
  have hζ0out : ∀ x, x ∉ Metric.ball x₀ ρ₁ → ζ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hζts h))
  have hDz0 : ∀ x, x ∉ Metric.ball x₀ ρ₁ →
      ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 = 0 := by
    intro x hx
    have hxt : x ∉ tsupport ζ := fun h => hx (hζts h)
    have hopen : IsOpen (tsupport ζ)ᶜ := (isClosed_tsupport ζ).isOpen_compl
    have hev : ζ =ᶠ[nhds x] fun _ => (0:ℝ) := by
      filter_upwards [hopen.mem_nhds hxt] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have h0 : fderiv ℝ ζ x = 0 := by rw [hev.fderiv_eq]; simp
    simp [h0]
  -- `F` and `Γ` on the inner ball
  have hcsub : Metric.closedBall x₀ ρ₁ ⊆ Metric.ball x₀ R :=
    Metric.closedBall_subset_ball hρ1R
  obtain ⟨hFmem, hΓmem⟩ := hFW.2 (Metric.closedBall x₀ ρ₁) (isCompact_closedBall x₀ ρ₁) hcsub
  have hΓsqC : IntegrableOn (fun x => ‖Γ x‖ ^ 2) (Metric.closedBall x₀ ρ₁) volume := by
    have h1 : Integrable (fun x => ‖Γ x‖ ^ (ENNReal.ofReal 2).toReal)
        (volume.restrict (Metric.closedBall x₀ ρ₁)) :=
      hΓmem.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp] at h1
    refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
    show ‖Γ x‖ ^ (2:ℝ) = ‖Γ x‖ ^ 2
    rw [← Real.rpow_natCast ‖Γ x‖ 2]
    norm_num
  have hΓsq : IntegrableOn (fun x => ‖Γ x‖ ^ 2) (Metric.ball x₀ ρ₁) volume :=
    hΓsqC.mono_set Metric.ball_subset_closedBall
  have hFms : AEStronglyMeasurable F (volume.restrict (Metric.ball x₀ ρ₁)) :=
    hFmem.1.mono_measure (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  have hΓms : AEStronglyMeasurable Γ (volume.restrict (Metric.ball x₀ ρ₁)) :=
    hΓmem.1.mono_measure (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  have hζms : ∀ μ : Measure (EuclideanSpace ℝ (Fin n)),
      AEStronglyMeasurable (fun x => ζ x ^ 2) μ := fun μ =>
    ((hζsm.continuous.aestronglyMeasurable).pow 2)
  have hDzms : ∀ μ : Measure (EuclideanSpace ℝ (Fin n)),
      AEStronglyMeasurable
        (fun x => ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2) μ := by
    intro μ
    have hcont : Continuous fun x : EuclideanSpace ℝ (Fin n) =>
        ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 := by
      refine continuous_finsetSum _ fun i _ => ?_
      exact ((hζsm.continuous_fderiv (by simp)).clm_apply
        continuous_const).pow 2
    exact hcont.aestronglyMeasurable
  -- globalisation of measurability for functions vanishing off `B_{ρ₁}`
  have hmsglob : ∀ u : EuclideanSpace ℝ (Fin n) → ℝ,
      AEStronglyMeasurable u (volume.restrict (Metric.ball x₀ ρ₁)) →
      (∀ x, x ∉ Metric.ball x₀ ρ₁ → u x = 0) →
      AEStronglyMeasurable u volume := by
    intro u hum hu0
    have hueq : u = (Metric.ball x₀ ρ₁).indicator u := by
      funext x
      by_cases hb : x ∈ Metric.ball x₀ ρ₁
      · rw [Set.indicator_of_mem hb]
      · rw [Set.indicator_of_notMem hb, hu0 x hb]
    rw [hueq]
    exact (aestronglyMeasurable_indicator_iff Metric.isOpen_ball.measurableSet).2 hum
  have hglob : ∀ u g : EuclideanSpace ℝ (Fin n) → ℝ,
      Integrable g volume →
      AEStronglyMeasurable u (volume.restrict (Metric.ball x₀ ρ₁)) →
      (∀ x, x ∉ Metric.ball x₀ ρ₁ → u x = 0) →
      (∀ x, x ∉ Metric.ball x₀ ρ₁ → 0 ≤ g x) →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ₁)), ‖u x‖ ≤ g x) →
      Integrable u volume := by
    intro u g hg hum hu0 hg0 hub
    refine Integrable.mono' hg (hmsglob u hum hu0) ?_
    have h1 : ∀ᵐ x ∂volume, x ∈ Metric.ball x₀ ρ₁ → ‖u x‖ ≤ g x :=
      (ae_restrict_iff' Metric.isOpen_ball.measurableSet).1 hub
    filter_upwards [h1] with x hx
    by_cases hb : x ∈ Metric.ball x₀ ρ₁
    · exact hx hb
    · rw [hu0 x hb, norm_zero]
      exact hg0 x hb
  -- Step 2 consequences, as bounds on `w ^ s`
  obtain ⟨Kc, hKcdef⟩ : ∃ t : ℝ, t = K ^ |s| * κ₁ ^ s := ⟨_, rfl⟩
  obtain ⟨Kinv, hKinvdef⟩ : ∃ t : ℝ, t = K ^ |s| * κ₁ ^ (-s) := ⟨_, rfl⟩
  obtain ⟨Gb, hGbdef⟩ : ∃ t : ℝ, t = L / (ρ₁ - ρ₀) ^ 2 := ⟨_, rfl⟩
  have hKs0 : (0:ℝ) < K ^ |s| := Real.rpow_pos_of_pos hK0 _
  have hKc0 : (0:ℝ) < Kc := by
    rw [hKcdef]; exact mul_pos hKs0 (Real.rpow_pos_of_pos hκ₁ _)
  have hKinv0 : (0:ℝ) < Kinv := by
    rw [hKinvdef]; exact mul_pos hKs0 (Real.rpow_pos_of_pos hκ₁ _)
  have hGb0 : (0:ℝ) ≤ Gb := by rw [hGbdef]; positivity
  have hKK : Kinv * Kc = K ^ (2 * |s|) := by
    rw [hKinvdef, hKcdef]
    have e1 : κ₁ ^ (-s) * κ₁ ^ s = 1 := by
      rw [← Real.rpow_add hκ₁]
      simp
    calc K ^ |s| * κ₁ ^ (-s) * (K ^ |s| * κ₁ ^ s)
        = (K ^ |s| * K ^ |s|) * (κ₁ ^ (-s) * κ₁ ^ s) := by ring
      _ = K ^ |s| * K ^ |s| := by rw [e1, mul_one]
      _ = K ^ (|s| + |s|) := (Real.rpow_add hK0 _ _).symm
      _ = K ^ (2 * |s|) := by rw [show |s| + |s| = 2 * |s| by ring]
  have hwU : ∀ v : ℝ, κ₁ ≤ v → v ≤ κ₂ → v ^ s ≤ Kc := by
    intro v h1 h2
    have hv0 : (0:ℝ) < v := lt_of_lt_of_le hκ₁ h1
    rw [hKcdef]
    refine hratio v κ₁ hv0 hκ₁ (by linarith) ?_
    nlinarith
  have hwL : ∀ v : ℝ, κ₁ ≤ v → v ≤ κ₂ → 1 ≤ Kinv * v ^ s := by
    intro v h1 h2
    have hv0 : (0:ℝ) < v := lt_of_lt_of_le hκ₁ h1
    have h3 : κ₁ ^ s ≤ K ^ |s| * v ^ s :=
      hratio κ₁ v hκ₁ hv0 (by nlinarith) (by linarith)
    have h4 : (0:ℝ) < κ₁ ^ (-s) := Real.rpow_pos_of_pos hκ₁ _
    have h5 := mul_le_mul_of_nonneg_left h3 h4.le
    rw [hKinvdef]
    calc (1:ℝ) = κ₁ ^ (-s) * κ₁ ^ s := by rw [← Real.rpow_add hκ₁]; simp
      _ ≤ κ₁ ^ (-s) * (K ^ |s| * v ^ s) := h5
      _ = K ^ |s| * κ₁ ^ (-s) * v ^ s := by ring
  have hwpos : ∀ v : ℝ, κ₁ ≤ v → (0:ℝ) ≤ v ^ s := fun v h1 =>
    (Real.rpow_pos_of_pos (lt_of_lt_of_le hκ₁ h1) s).le
  -- the pinch, transferred to `B_R` under the guard `ℓ < F`
  have hptrans : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      ℓ < F x → (κ₁ ≤ w x ∧ w x ≤ κ₂) := by
    have hbadm : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | ¬(κ₁ ≤ w x ∧ w x ≤ κ₂)} :=
      ((measurableSet_le measurable_const hwm).inter
        (measurableSet_le hwm measurable_const)).compl
    have hE0 := hp
    rw [ae_iff, Measure.restrict_apply hbadm] at hE0
    rw [ae_iff, Measure.restrict_apply' Metric.isOpen_ball.measurableSet]
    refine measure_mono_null ?_ hE0
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hA, hB⟩ := Classical.not_imp.1 hx1
    exact ⟨hB, ⟨hx2, hA⟩⟩
  -- (4b): the four integrands are integrable where they are integrated
  have hfinball : IsFiniteMeasure (volume.restrict (Metric.ball x₀ ρ₁)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hindΓ : Integrable ((Metric.ball x₀ ρ₁).indicator (fun x => ‖Γ x‖ ^ 2)) volume :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).2 hΓsq
  have hindΓK : Integrable
      ((Metric.ball x₀ ρ₁).indicator (fun x => Kc * ‖Γ x‖ ^ 2)) volume :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).2 (hΓsq.const_mul Kc)
  have hindC : ∀ M : ℝ,
      Integrable ((Metric.ball x₀ ρ₁).indicator (fun _ => M)) volume := fun M =>
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).2 (integrable_const M)
  have hwms : AEMeasurable (fun x => w x ^ s) volume := (hwm.pow_const s).aemeasurable
  have hPms : AEStronglyMeasurable (fun x => max (F x - ℓ) 0 ^ 2)
      (volume.restrict (Metric.ball x₀ ρ₁)) :=
    ((((hFms.aemeasurable.sub_const ℓ).max aemeasurable_const).pow_const
      2).aestronglyMeasurable)
  have hU1 : Integrable (fun x => ‖Γ x‖ ^ 2 * ζ x ^ 2) volume := by
    refine hglob _ _ hindΓ ((hΓms.norm.pow 2).mul (hζms _)) ?_ ?_ ?_
    · intro x hx; rw [hζ0out x hx]; ring
    · intro x hx; rw [Set.indicator_of_notMem hx]
    · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      rw [Set.indicator_of_mem hx, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      have hz2 : ζ x ^ 2 ≤ 1 := by nlinarith [hζnn x, hζle1 x]
      calc ‖Γ x‖ ^ 2 * ζ x ^ 2 ≤ ‖Γ x‖ ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hz2 (sq_nonneg _)
        _ = ‖Γ x‖ ^ 2 := mul_one _
  have hU2ms : AEStronglyMeasurable (fun x => w x ^ s * ‖Γ x‖ ^ 2 * ζ x ^ 2) volume := by
    refine hmsglob _ ?_ ?_
    · exact ((hwms.aestronglyMeasurable.mono_measure Measure.restrict_le_self).mul
        (hΓms.norm.pow 2)).mul (hζms _)
    · intro x hx; rw [hζ0out x hx]; ring
  have hU2 : IntegrableOn (fun x => w x ^ s * ‖Γ x‖ ^ 2 * ζ x ^ 2)
      (Metric.ball x₀ R ∩ {y | ℓ < F y}) volume := by
    refine Integrable.mono' (g := (Metric.ball x₀ ρ₁).indicator (fun x => Kc * ‖Γ x‖ ^ 2))
      (hindΓK.mono_measure Measure.restrict_le_self)
      (hU2ms.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [hp] with x hx
    by_cases hb : x ∈ Metric.ball x₀ ρ₁
    · have hws0 : (0:ℝ) ≤ w x ^ s := hwpos _ hx.1
      have hwsU : w x ^ s ≤ Kc := hwU _ hx.1 hx.2
      rw [Set.indicator_of_mem hb, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg hws0 (sq_nonneg _)) (sq_nonneg _))]
      calc w x ^ s * ‖Γ x‖ ^ 2 * ζ x ^ 2 ≤ Kc * ‖Γ x‖ ^ 2 * ζ x ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hwsU (sq_nonneg _)) (sq_nonneg _)
        _ ≤ Kc * ‖Γ x‖ ^ 2 * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hKc0.le (sq_nonneg _))
            nlinarith [hζnn x, hζle1 x]
        _ = Kc * ‖Γ x‖ ^ 2 := mul_one _
    · rw [hζ0out x hb, Set.indicator_of_notMem hb]
      simp
  have hU3 : Integrable (fun x => w x ^ s * max (F x - ℓ) 0 ^ 2
      * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2) volume := by
    refine hglob _ _ (hindC (Kc * Θℓ ^ 2 * Gb))
      (((hwms.aestronglyMeasurable.mono_measure Measure.restrict_le_self).mul hPms).mul
        (hDzms _)) ?_ ?_ ?_
    · intro x hx; rw [hDz0 x hx]; ring
    · intro x hx; rw [Set.indicator_of_notMem hx]
    · have hg1 := ae_restrict_of_ae_restrict_of_subset hsub1 hptrans
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet, hg1, hbd1sq]
        with x hx hgd hsq
      rw [Set.indicator_of_mem hx]
      rcases le_or_gt (F x) ℓ with hfl | hfl
      · have h0 : max (F x - ℓ) 0 = 0 := max_eq_right (by linarith)
        rw [h0]
        simp
        positivity
      · obtain ⟨h1, h2⟩ := hgd hfl
        have hws0 : (0:ℝ) ≤ w x ^ s := hwpos _ h1
        have hwsU : w x ^ s ≤ Kc := hwU _ h1 h2
        have hDzb := hζgrad x
        rw [← hGbdef] at hDzb
        have hDz0' : (0:ℝ) ≤ ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 :=
          Finset.sum_nonneg fun i _ => sq_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (mul_nonneg hws0 (sq_nonneg _)) hDz0')]
        exact mul_le_mul (mul_le_mul hwsU hsq (sq_nonneg _) hKc0.le) hDzb hDz0'
          (mul_nonneg hKc0.le (sq_nonneg _))
  have hU4 : Integrable (fun x => max (F x - ℓ) 0 ^ 2
      * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2) volume := by
    refine hglob _ _ (hindC (Θℓ ^ 2 * Gb)) (hPms.mul (hDzms _)) ?_ ?_ ?_
    · intro x hx; rw [hDz0 x hx]; ring
    · intro x hx; rw [Set.indicator_of_notMem hx]
    · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet, hbd1sq]
        with x hx hsq
      have hDzb := hζgrad x
      rw [← hGbdef] at hDzb
      have hDz0' : (0:ℝ) ≤ ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      rw [Set.indicator_of_mem hx, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) hDz0')]
      exact mul_le_mul hsq hDzb hDz0' (sq_nonneg _)
  have hP1 : IntegrableOn (fun x => max (F x - ℓ) 0 ^ 2) (Metric.ball x₀ ρ₁) volume := by
    refine Integrable.mono' (g := fun _ => Θℓ ^ 2) (integrable_const _) hPms ?_
    filter_upwards [hbd1sq] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx
  -- (4f): the left-hand side of the conclusion
  have hA : (∫ x in Metric.ball x₀ ρ₀ ∩ {y | ℓ < F y}, ‖Γ x‖ ^ 2)
      ≤ ∫ x in Metric.ball x₀ R ∩ {y | ℓ < F y}, ‖Γ x‖ ^ 2 * ζ x ^ 2 := by
    have heqball : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ₀)),
        ‖Γ x‖ ^ 2 = ‖Γ x‖ ^ 2 * ζ x ^ 2 := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      rw [hζone x (Metric.ball_subset_closedBall hx)]
      ring
    have heq : (fun x => ‖Γ x‖ ^ 2)
        =ᵐ[volume.restrict (Metric.ball x₀ ρ₀ ∩ {y | ℓ < F y})]
          fun x => ‖Γ x‖ ^ 2 * ζ x ^ 2 :=
      heqball.filter_mono
        (ae_mono (Measure.restrict_mono Set.inter_subset_left le_rfl))
    rw [integral_congr_ae heq]
    refine setIntegral_mono_set (hU1.mono_measure Measure.restrict_le_self)
      (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Filter.Eventually.of_forall fun x hx =>
        ⟨Metric.ball_subset_ball (le_of_lt (lt_trans hρ01 hρ1R)) hx.1, hx.2⟩)
  -- (4c): removing the weight on the left
  have hB : (∫ x in Metric.ball x₀ R ∩ {y | ℓ < F y}, ‖Γ x‖ ^ 2 * ζ x ^ 2)
      ≤ Kinv * ∫ x in Metric.ball x₀ R ∩ {y | ℓ < F y},
          w x ^ s * ‖Γ x‖ ^ 2 * ζ x ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono_ae (hU1.mono_measure Measure.restrict_le_self)
      (hU2.const_mul Kinv) ?_
    filter_upwards [hp] with x hx
    have h1 : 1 ≤ Kinv * w x ^ s := hwL _ hx.1 hx.2
    have h2 : (0:ℝ) ≤ ‖Γ x‖ ^ 2 * ζ x ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    calc ‖Γ x‖ ^ 2 * ζ x ^ 2 = 1 * (‖Γ x‖ ^ 2 * ζ x ^ 2) := by ring
      _ ≤ Kinv * w x ^ s * (‖Γ x‖ ^ 2 * ζ x ^ 2) := h3
      _ = Kinv * (w x ^ s * ‖Γ x‖ ^ 2 * ζ x ^ 2) := by ring
  -- (4d): removing the weight on the right
  have hD : (∫ x in Metric.ball x₀ R, w x ^ s * max (F x - ℓ) 0 ^ 2
        * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
      ≤ Kc * ∫ x in Metric.ball x₀ R, max (F x - ℓ) 0 ^ 2
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono_ae (hU3.mono_measure Measure.restrict_le_self)
      ((hU4.mono_measure Measure.restrict_le_self).const_mul Kc) ?_
    filter_upwards [hptrans] with x hgd
    rcases le_or_gt (F x) ℓ with hfl | hfl
    · rw [max_eq_right (by linarith : F x - ℓ ≤ 0)]
      simp
    · obtain ⟨h1, h2⟩ := hgd hfl
      have hwsU : w x ^ s ≤ Kc := hwU _ h1 h2
      have hDz0' : (0:ℝ) ≤ ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      have e : Kc * (max (F x - ℓ) 0 ^ 2
            * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
          = Kc * max (F x - ℓ) 0 ^ 2
            * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hwsU (sq_nonneg _)) hDz0'
  -- (4g): the right-hand side is the one the conclusion names
  have hE : (∫ x in Metric.ball x₀ R, max (F x - ℓ) 0 ^ 2
        * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
      ≤ Gb * (S * V) := by
    have hindP : Integrable
        ((Metric.ball x₀ ρ₁).indicator (fun y => max (F y - ℓ) 0 ^ 2)) volume :=
      (integrable_indicator_iff Metric.isOpen_ball.measurableSet).2 hP1
    have e1 : (∫ x in Metric.ball x₀ R, Gb *
          (Metric.ball x₀ ρ₁).indicator (fun y => max (F y - ℓ) 0 ^ 2) x)
        = Gb * ∫ x in Metric.ball x₀ ρ₁, max (F x - ℓ) 0 ^ 2 := by
      rw [integral_const_mul, setIntegral_indicator Metric.isOpen_ball.measurableSet,
        Set.inter_eq_self_of_subset_right hsub1]
    have hstep1 : (∫ x in Metric.ball x₀ R, max (F x - ℓ) 0 ^ 2
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
        ≤ Gb * ∫ x in Metric.ball x₀ ρ₁, max (F x - ℓ) 0 ^ 2 := by
      rw [← e1]
      refine integral_mono_ae (hU4.mono_measure Measure.restrict_le_self)
        ((hindP.const_mul Gb).mono_measure Measure.restrict_le_self)
        (Filter.Eventually.of_forall fun x => ?_)
      show max (F x - ℓ) 0 ^ 2
            * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
          ≤ Gb * (Metric.ball x₀ ρ₁).indicator (fun y => max (F y - ℓ) 0 ^ 2) x
      by_cases hb : x ∈ Metric.ball x₀ ρ₁
      · rw [Set.indicator_of_mem hb]
        have hDzb := hζgrad x
        rw [← hGbdef] at hDzb
        have e : Gb * max (F x - ℓ) 0 ^ 2 = max (F x - ℓ) 0 ^ 2 * Gb := by ring
        rw [e]
        exact mul_le_mul_of_nonneg_left hDzb (sq_nonneg _)
      · rw [hDz0 x hb, Set.indicator_of_notMem hb]
        simp
    -- the essential supremum and the measure of the level set
    obtain ⟨T, hTm, hTsub, hTvol⟩ : ∃ T : Set (EuclideanSpace ℝ (Fin n)),
        MeasurableSet T ∧ Metric.ball x₀ ρ₁ ∩ {y | ℓ < F y} ⊆ T ∧
        volume T = volume (Metric.ball x₀ ρ₁ ∩ {y | ℓ < F y}) :=
      ⟨toMeasurable volume _, measurableSet_toMeasurable _ _,
        subset_toMeasurable _ _, measure_toMeasurable _⟩
    have hTfin : volume T ≠ ⊤ := by
      rw [hTvol]
      exact (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
        measure_ball_lt_top).ne
    have hindT : IntegrableOn (fun x => S * T.indicator (fun _ => (1:ℝ)) x)
        (Metric.ball x₀ ρ₁) volume := by
      refine Integrable.const_mul ?_ S
      refine Integrable.mono' (g := fun _ => (1:ℝ)) (integrable_const _)
        ((measurable_const.indicator hTm).aestronglyMeasurable) ?_
      refine Filter.Eventually.of_forall fun x => ?_
      by_cases hb : x ∈ T
      · rw [Set.indicator_of_mem hb]; simp
      · rw [Set.indicator_of_notMem hb]; simp
    have hbound : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ₁)),
        max (F x - ℓ) 0 ^ 2 ≤ S * T.indicator (fun _ => (1:ℝ)) x := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet, hSbd]
        with x hx hS
      rcases le_or_gt (F x) ℓ with hfl | hfl
      · rw [max_eq_right (by linarith : F x - ℓ ≤ 0)]
        have h0 : (0:ℝ) ≤ T.indicator (fun _ => (1:ℝ)) x :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) x
        have : (0:ℝ) ^ 2 = 0 := by ring
        rw [this]
        exact mul_nonneg hS0 h0
      · rw [Set.indicator_of_mem (hTsub ⟨hx, hfl⟩), mul_one]
        exact hS
    have hstep2 : (∫ x in Metric.ball x₀ ρ₁, max (F x - ℓ) 0 ^ 2) ≤ S * V := by
      refine le_trans (integral_mono_ae hP1 hindT hbound) ?_
      rw [integral_const_mul, setIntegral_indicator hTm, setIntegral_const,
        MeasureTheory.measureReal_def, smul_eq_mul, mul_one]
      refine mul_le_mul_of_nonneg_left ?_ hS0
      rw [hVdef]
      refine ENNReal.toReal_mono ?_ ?_
      · exact (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
          measure_ball_lt_top).ne
      · rw [← hTvol]
        exact le_trans (measure_mono Set.inter_subset_right) le_rfl
    exact le_trans hstep1 (mul_le_mul_of_nonneg_left hstep2 hGb0)
  -- the chain
  have hSV : (0:ℝ) ≤ S * V := mul_nonneg hS0 (by rw [hVdef]; exact ENNReal.toReal_nonneg)
  have hfinal : Kinv * (c * (Kc * (Gb * (S * V)))) ≤ γ / (ρ₁ - ρ₀) ^ 2 * S * V := by
    have hne : (ρ₁ - ρ₀) ≠ 0 := ne_of_gt hdpos
    have hd2 : (0:ℝ) < (ρ₁ - ρ₀) ^ 2 := by positivity
    have e1 : Kinv * (c * (Kc * (Gb * (S * V))))
        = (Kinv * Kc) * (c * Gb) * (S * V) := by ring
    rw [e1, hKK, hGbdef, hγdef]
    have h2 : K ^ (2 * |s|) * (c * (L))
        ≤ c * K ^ (2 * |s|) * (1 + L) := by
      nlinarith [hKabs, hc, hL0.le]
    have e2 : K ^ (2 * |s|) * (c * (L / (ρ₁ - ρ₀) ^ 2)) * (S * V)
        = (K ^ (2 * |s|) * (c * (L))) * (S * V) / (ρ₁ - ρ₀) ^ 2 := by
      field_simp
    have e3 : c * K ^ (2 * |s|) * (1 + L) / (ρ₁ - ρ₀) ^ 2 * S * V
        = (c * K ^ (2 * |s|) * (1 + L)) * (S * V) / (ρ₁ - ρ₀) ^ 2 := by
      field_simp
    rw [e2, e3, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hSV)
      (le_of_lt (inv_pos.2 hd2))
  refine le_trans hA (le_trans hB ?_)
  refine le_trans (mul_le_mul_of_nonneg_left hcacζ hKinv0.le) ?_
  refine le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hD hc.le) hKinv0.le) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hE hKc0.le) hc.le) hKinv0.le) ?_
  exact hfinal
