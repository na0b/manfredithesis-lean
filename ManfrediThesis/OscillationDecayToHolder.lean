import ManfrediThesis.Preamble
import ManfrediThesis.EssOscOn
import ManfrediThesis.MemHolderOn
open MeasureTheory

/-- From oscillation decay to a Hölder continuous representative: an
essentially bounded function whose essential oscillation over every ball whose
closure lies in `Ω` decays like `(ρ/R)^α` agrees almost everywhere on `Ω` with a
function that is continuous on `Ω` and Hölder continuous of exponent `α` on
`closedBall x₀ (R/2)`, with a Hölder seminorm bounded there by `C * K / R^α`. -/
theorem OscillationDecayToHolder :
    ∀ (n : ℕ) (α K M : ℝ), 1 ≤ n → 0 < α → α ≤ 1 → 0 ≤ K → 0 ≤ M →
      ∃ C : ℝ, 0 < C ∧
        ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ),
          IsOpen Ω → 0 < R → Metric.closedBall x₀ R ⊆ Ω →
          (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
          (∀ (y : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
            Metric.closedBall y ρ ⊆ Ω →
            EssOscOn n (Metric.ball y ρ) u ≤ K * (ρ / R) ^ α) →
          ∃ U : EuclideanSpace ℝ (Fin n) → ℝ,
            (∀ᵐ x ∂(volume.restrict Ω), U x = u x) ∧
              ContinuousOn U Ω ∧
              MemHolderOn n α (Metric.closedBall x₀ (R / 2)) U ∧
              (∀ x ∈ Metric.closedBall x₀ (R / 2),
                ∀ y ∈ Metric.closedBall x₀ (R / 2),
                  |U x - U y| ≤ C * K * (dist x y / R) ^ α) := by
  intro n α K M hn hα hα1 hK hM
  -- ===================== Step 0 =====================
  have hNeBot : ∀ {s : Set (EuclideanSpace ℝ (Fin n))}, volume s ≠ 0 →
      (ae (volume.restrict s)).NeBot := by
    intro s hs
    refine ⟨fun hb => ?_⟩
    rw [ae_eq_bot] at hb
    exact hs (by simpa using congrArg (fun m => m s) hb)
  have hcobdd_le : ∀ {μ : Measure (EuclideanSpace ℝ (Fin n))}
      {v : EuclideanSpace ℝ (Fin n) → ℝ} {m : ℝ}, (ae μ).NeBot →
      (∀ᵐ x ∂μ, m ≤ v x) → Filter.IsCoboundedUnder (· ≤ ·) (ae μ) v := by
    intro μ v m hb hlo
    have := hb
    refine ⟨m, fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨x, hax, hxm⟩ := (ha.and hlo).exists
    linarith
  have hcobdd_ge : ∀ {μ : Measure (EuclideanSpace ℝ (Fin n))}
      {v : EuclideanSpace ℝ (Fin n) → ℝ} {Mb : ℝ}, (ae μ).NeBot →
      (∀ᵐ x ∂μ, v x ≤ Mb) → Filter.IsCoboundedUnder (· ≥ ·) (ae μ) v := by
    intro μ v Mb hb hhi
    have := hb
    refine ⟨Mb, fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨x, hax, hxM⟩ := (ha.and hhi).exists
    linarith
  have E1 : ∀ {μ : Measure (EuclideanSpace ℝ (Fin n))}
      {v : EuclideanSpace ℝ (Fin n) → ℝ} {m t : ℝ}, (ae μ).NeBot →
      (∀ᵐ x ∂μ, m ≤ v x) → (∀ᵐ x ∂μ, v x ≤ t) → essSup v μ ≤ t := by
    intro μ v m t hb hlo h
    exact essSup_le_of_ae_le t h (hcobdd_le hb hlo)
  have E2 : ∀ {μ : Measure (EuclideanSpace ℝ (Fin n))}
      {v : EuclideanSpace ℝ (Fin n) → ℝ} {t : ℝ},
      (∀ᵐ x ∂μ, v x ≤ t) → ∀ᵐ x ∂μ, v x ≤ essSup v μ := by
    intro μ v t h
    exact ae_le_essSup ⟨t, h⟩
  have E3 : ∀ {μ : Measure (EuclideanSpace ℝ (Fin n))}
      {v : EuclideanSpace ℝ (Fin n) → ℝ} {Mb t : ℝ}, (ae μ).NeBot →
      (∀ᵐ x ∂μ, v x ≤ Mb) → (∀ᵐ x ∂μ, t ≤ v x) → t ≤ essInf v μ := by
    intro μ v Mb t hb hhi h
    exact le_essInf_of_ae_le t h (hcobdd_ge hb hhi)
  have E4 : ∀ {μ : Measure (EuclideanSpace ℝ (Fin n))}
      {v : EuclideanSpace ℝ (Fin n) → ℝ} {t : ℝ},
      (∀ᵐ x ∂μ, t ≤ v x) → ∀ᵐ x ∂μ, essInf v μ ≤ v x := by
    intro μ v t h
    exact ae_essInf_le ⟨t, h⟩
  -- ===================== Step 1 =====================
  refine ⟨8, by norm_num, ?_⟩
  intro Ω u x₀ R hΩ hR hball hMu hosc
  have hballpos : ∀ (y : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
      volume (Metric.ball y ρ) ≠ 0 := fun y ρ hρ => (Metric.measure_ball_pos volume y hρ).ne'
  have hsub : ∀ (s : Set (EuclideanSpace ℝ (Fin n))), s ⊆ Ω →
      ∀ᵐ y ∂(volume.restrict s), |u y| ≤ M :=
    fun s hs => ae_restrict_of_ae_restrict_of_subset hs hMu
  have hsubhi : ∀ (s : Set (EuclideanSpace ℝ (Fin n))), s ⊆ Ω →
      ∀ᵐ y ∂(volume.restrict s), u y ≤ M := by
    intro s hs
    filter_upwards [hsub s hs] with y hy using (abs_le.1 hy).2
  have hsublo : ∀ (s : Set (EuclideanSpace ℝ (Fin n))), s ⊆ Ω →
      ∀ᵐ y ∂(volume.restrict s), -M ≤ u y := by
    intro s hs
    filter_upwards [hsub s hs] with y hy using (abs_le.1 hy).1
  -- monotonicity in the set, which is (3)
  have hmonoS : ∀ (E' E : Set (EuclideanSpace ℝ (Fin n))), E' ⊆ E → E ⊆ Ω →
      volume E' ≠ 0 →
      essSup u (volume.restrict E') ≤ essSup u (volume.restrict E) := by
    intro E' E hss hEΩ hE'
    have h1 : ∀ᵐ y ∂(volume.restrict E), u y ≤ essSup u (volume.restrict E) :=
      E2 (hsubhi E hEΩ)
    exact E1 (hNeBot hE') (hsublo E' (hss.trans hEΩ))
      (ae_restrict_of_ae_restrict_of_subset hss h1)
  have hmonoI : ∀ (E' E : Set (EuclideanSpace ℝ (Fin n))), E' ⊆ E → E ⊆ Ω →
      volume E' ≠ 0 →
      essInf u (volume.restrict E) ≤ essInf u (volume.restrict E') := by
    intro E' E hss hEΩ hE'
    have h1 : ∀ᵐ y ∂(volume.restrict E), essInf u (volume.restrict E) ≤ u y :=
      E4 (hsublo E hEΩ)
    exact E3 (hNeBot hE') (hsubhi E' (hss.trans hEΩ))
      (ae_restrict_of_ae_restrict_of_subset hss h1)
  set S : EuclideanSpace ℝ (Fin n) → ℝ → ℝ :=
    fun x ρ => essSup u (volume.restrict (Metric.ball x ρ)) with hS
  set I : EuclideanSpace ℝ (Fin n) → ℝ → ℝ :=
    fun x ρ => essInf u (volume.restrict (Metric.ball x ρ)) with hI
  -- (2) and the two a.e. inequalities
  have hcore : ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
      Metric.closedBall x ρ ⊆ Ω →
      (-M ≤ I x ρ ∧ I x ρ ≤ S x ρ ∧ S x ρ ≤ M) ∧
        (∀ᵐ y ∂(volume.restrict (Metric.ball x ρ)), I x ρ ≤ u y ∧ u y ≤ S x ρ) := by
    intro x ρ hρ h
    have hbΩ : Metric.ball x ρ ⊆ Ω := Metric.ball_subset_closedBall.trans h
    have hne := hNeBot (hballpos x ρ hρ)
    have := hne
    have hhi := hsubhi _ hbΩ
    have hlo := hsublo _ hbΩ
    have hSM : S x ρ ≤ M := E1 hne hlo hhi
    have hIM : -M ≤ I x ρ := E3 hne hhi hlo
    have ha1 : ∀ᵐ y ∂(volume.restrict (Metric.ball x ρ)), I x ρ ≤ u y := E4 hlo
    have ha2 : ∀ᵐ y ∂(volume.restrict (Metric.ball x ρ)), u y ≤ S x ρ := E2 hhi
    obtain ⟨y, hy1, hy2⟩ := (ha1.and ha2).exists
    exact ⟨⟨hIM, le_trans hy1 hy2, hSM⟩, ha1.and ha2⟩
  -- (5)
  have hosc' : ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
      Metric.closedBall x ρ ⊆ Ω → S x ρ - I x ρ ≤ K * (ρ / R) ^ α := by
    intro x ρ hρ h
    have h0 := hosc x ρ hρ h
    rw [EssOscOn] at h0
    exact h0
  -- (4)
  have hmono4 : ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ ρ' : ℝ), 0 < ρ → ρ ≤ ρ' →
      Metric.closedBall x ρ' ⊆ Ω → S x ρ ≤ S x ρ' ∧ I x ρ' ≤ I x ρ := by
    intro x ρ ρ' hρ hle h'
    have hss : Metric.ball x ρ ⊆ Metric.ball x ρ' := Metric.ball_subset_ball hle
    have hbΩ : Metric.ball x ρ' ⊆ Ω := Metric.ball_subset_closedBall.trans h'
    exact ⟨hmonoS _ _ hss hbΩ (hballpos x ρ hρ),
      hmonoI _ _ hss hbΩ (hballpos x ρ hρ)⟩
  -- the admissible radii are nonempty at every point of Ω
  have hAne : ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall x ρ ⊆ Ω := by
    intro x hx
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hΩ x hx
    exact ⟨ε/2, by linarith, (Metric.closedBall_subset_ball (by linarith)).trans hεsub⟩
  -- ===================== Step 2 =====================
  set T : EuclideanSpace ℝ (Fin n) → Set ℝ :=
    fun x => S x '' {ρ : ℝ | 0 < ρ ∧ Metric.closedBall x ρ ⊆ Ω} with hT
  have hTbdd : ∀ x : EuclideanSpace ℝ (Fin n), BddBelow (T x) := by
    intro x
    refine ⟨-M, ?_⟩
    rintro b ⟨ρ, ⟨hρ, h⟩, rfl⟩
    obtain ⟨⟨h1, h2, h3⟩, -⟩ := hcore x ρ hρ h
    linarith
  have hTne : ∀ x ∈ Ω, (T x).Nonempty := by
    intro x hx
    obtain ⟨ρ, hρ, h⟩ := hAne x hx
    exact ⟨S x ρ, ρ, ⟨hρ, h⟩, rfl⟩
  set U : EuclideanSpace ℝ (Fin n) → ℝ := fun x => sInf (T x) with hU
  have hU6 : ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
      Metric.closedBall x ρ ⊆ Ω → I x ρ ≤ U x ∧ U x ≤ S x ρ := by
    intro x ρ hρ h
    have hxΩ : x ∈ Ω := h (Metric.mem_closedBall_self hρ.le)
    refine ⟨le_csInf (hTne x hxΩ) ?_, csInf_le (hTbdd x) ⟨ρ, ⟨hρ, h⟩, rfl⟩⟩
    rintro b ⟨ρ', ⟨hρ', h'⟩, rfl⟩
    rcases le_total ρ' ρ with hc | hc
    · obtain ⟨⟨-, h2, -⟩, -⟩ := hcore x ρ' hρ' h'
      have h5 := (hmono4 x ρ' ρ hρ' hc h).2
      linarith
    · obtain ⟨⟨-, h2, -⟩, -⟩ := hcore x ρ hρ h
      have h5 := (hmono4 x ρ ρ' hρ hc h').1
      linarith
  -- ===================== Step 4 =====================
  have hstep4 : ∀ (x y : EuclideanSpace ℝ (Fin n)),
      0 < dist x y → Metric.closedBall x (2 * dist x y) ⊆ Ω →
      |U x - U y| ≤ 2 * K * (dist x y / R) ^ α := by
    intro x y hr h2r
    set r := dist x y with hrdef
    have hadm : (0:ℝ) < 2 * r := by linarith
    have hyadm : Metric.closedBall y (r/2) ⊆ Metric.closedBall x (2*r) := by
      intro z hz
      simp only [Metric.mem_closedBall] at hz ⊢
      have ht : dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      rw [dist_comm y x, ← hrdef] at ht
      linarith
    have hyadm' : Metric.closedBall y (r/2) ⊆ Ω := hyadm.trans h2r
    have hssball : Metric.ball y (r/2) ⊆ Metric.ball x (2*r) := by
      intro z hz
      simp only [Metric.mem_ball] at hz ⊢
      have ht : dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      rw [dist_comm y x, ← hrdef] at ht
      linarith
    have hbΩ : Metric.ball x (2*r) ⊆ Ω := Metric.ball_subset_closedBall.trans h2r
    have hIy : I x (2*r) ≤ I y (r/2) :=
      hmonoI _ _ hssball hbΩ (hballpos y (r/2) (by linarith))
    have hSy : S y (r/2) ≤ S x (2*r) :=
      hmonoS _ _ hssball hbΩ (hballpos y (r/2) (by linarith))
    obtain ⟨hIUy, hUSy⟩ := hU6 y (r/2) (by linarith) hyadm'
    obtain ⟨hIUx, hUSx⟩ := hU6 x (2*r) hadm h2r
    have hlen := hosc' x (2*r) hadm h2r
    have h1 : |U x - U y| ≤ S x (2*r) - I x (2*r) := by
      rw [abs_le]; constructor <;> linarith
    have h2 : (2*r/R) ^ α = 2 ^ α * (r/R) ^ α := by
      rw [show 2*r/R = 2 * (r/R) by ring,
        Real.mul_rpow (by norm_num) (by positivity)]
    have h3 : (2:ℝ) ^ α ≤ 2 := by
      calc (2:ℝ) ^ α ≤ (2:ℝ) ^ (1:ℝ) :=
            (Real.rpow_le_rpow_left_iff (by norm_num)).2 hα1
        _ = 2 := Real.rpow_one 2
    have h4 : (0:ℝ) ≤ (r/R) ^ α := Real.rpow_nonneg (by positivity) α
    calc |U x - U y| ≤ S x (2*r) - I x (2*r) := h1
      _ ≤ K * (2*r/R) ^ α := hlen
      _ = K * (2 ^ α * (r/R) ^ α) := by rw [h2]
      _ ≤ K * (2 * (r/R) ^ α) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 h4) hK
      _ = 2 * K * (r/R) ^ α := by ring
  -- ===================== Step 5 =====================
  have hcont : ContinuousOn U Ω := by
    rw [Metric.continuousOn_iff]
    intro x hx ε hε
    obtain ⟨ρx, hρx, hρxsub⟩ := hAne x hx
    refine ⟨min (ρx/4) ((ε * R ^ α / (2*K+1)) ^ (1/α)), ?_, ?_⟩
    · refine lt_min (by linarith) (Real.rpow_pos_of_pos ?_ _)
      have : (0:ℝ) < R ^ α := Real.rpow_pos_of_pos hR α
      positivity
    · intro y hy hd
      rcases eq_or_ne y x with rfl | hyx
      · simpa using hε
      have hr : 0 < dist y x := dist_pos.2 hyx
      have hd1 : dist y x < ρx/4 := lt_of_lt_of_le hd (min_le_left _ _)
      have hd2 : dist y x < (ε * R ^ α / (2*K+1)) ^ (1/α) :=
        lt_of_lt_of_le hd (min_le_right _ _)
      have h2r : Metric.closedBall y (2 * dist y x) ⊆ Ω := by
        refine subset_trans ?_ hρxsub
        intro z hz
        simp only [Metric.mem_closedBall] at hz ⊢
        have ht := dist_triangle z y x
        linarith
      have hb := hstep4 y x hr h2r
      have hRa : (0:ℝ) < R ^ α := Real.rpow_pos_of_pos hR α
      have hκ : (0:ℝ) < ε * R ^ α / (2*K+1) := by positivity
      have hinv : ((ε * R ^ α / (2*K+1)) ^ (1/α)) ^ α = ε * R ^ α / (2*K+1) := by
        rw [← Real.rpow_mul hκ.le, one_div, inv_mul_cancel₀ (ne_of_gt hα), Real.rpow_one]
      have hdiv : dist y x / R < (ε * R ^ α / (2*K+1)) ^ (1/α) / R := by
        gcongr
      have hpow : (dist y x / R) ^ α < ε / (2*K+1) := by
        have h5 : (dist y x / R) ^ α
            < ((ε * R ^ α / (2*K+1)) ^ (1/α) / R) ^ α :=
          Real.rpow_lt_rpow (by positivity) hdiv hα
        rw [Real.div_rpow (Real.rpow_nonneg hκ.le _) hR.le, hinv] at h5
        calc (dist y x / R) ^ α < ε * R ^ α / (2*K+1) / R ^ α := h5
          _ = ε / (2*K+1) := by field_simp
      have hnn : (0:ℝ) ≤ (dist y x / R) ^ α := Real.rpow_nonneg (by positivity) α
      rw [Real.dist_eq]
      have hfin : (2*K+1) * ((dist y x / R) ^ α) < (2*K+1) * (ε / (2*K+1)) :=
        mul_lt_mul_of_pos_left hpow (by linarith)
      have hfin2 : (2*K+1) * (ε / (2*K+1)) = ε := by field_simp
      nlinarith [hb, hnn, hK]
  -- ===================== Step 6 =====================
  set D : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall x₀ (R/2) with hD
  have hDΩ : D ⊆ Ω :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hball
  have hadm1 : ∀ x ∈ D, ∀ ρ : ℝ, 0 < ρ → ρ ≤ R/2 → Metric.closedBall x ρ ⊆ Ω := by
    intro x hx ρ hρ hle
    refine subset_trans ?_ hball
    intro z hz
    rw [hD, Metric.mem_closedBall] at hx
    simp only [Metric.mem_closedBall] at hz ⊢
    have ht := dist_triangle z x x₀
    linarith
  have hnear : ∀ x ∈ D, ∀ y ∈ D, 0 < dist x y → dist x y ≤ R/4 →
      |U x - U y| ≤ 2 * K * (dist x y / R) ^ α := fun x hx y _ hr hle =>
    hstep4 x y hr (hadm1 x hx (2 * dist x y) (by linarith) (by linarith))
  have hstep6 : ∀ x ∈ D, ∀ y ∈ D, |U x - U y| ≤ 8 * K * (dist x y / R) ^ α := by
    intro x hx y hy
    rcases eq_or_lt_of_le (dist_nonneg (x := x) (y := y)) with hr0 | hr0
    · have hxy : x = y := dist_le_zero.1 hr0.ge
      subst hxy
      simp [Real.zero_rpow (ne_of_gt hα)]
    set r := dist x y with hrdef
    have hrR : r ≤ R := by
      have h1 : r ≤ dist x x₀ + dist x₀ y := dist_triangle x x₀ y
      rw [hD, Metric.mem_closedBall] at hx hy
      rw [dist_comm x₀ y] at h1
      linarith
    have hnn : (0:ℝ) ≤ (r/R) ^ α := Real.rpow_nonneg (by positivity) α
    rcases le_or_gt r (R/4) with hc | hc
    · have := hnear x hx y hy hr0 hc
      nlinarith [hK, hnn]
    -- the far case: a chain of four steps of length r/4
    have hP : ∀ s s' : ℝ, dist ((1-s) • x + s • y) ((1-s') • x + s' • y)
        = |s - s'| * r := by
      intro s s'
      rw [dist_eq_norm, hrdef, dist_eq_norm,
        show (1-s) • x + s • y - ((1-s') • x + s' • y) = (s - s') • (y - x) by module,
        norm_smul, Real.norm_eq_abs, norm_sub_rev]
    have hm : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1-t) • x + t • y ∈ D := by
      intro t h0 h1
      exact (convex_closedBall x₀ (R/2)) hx hy (by linarith) h0 (by ring)
    have key : ∀ s s' : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ s' → s' ≤ 1 → |s - s'| = 1/4 →
        |U ((1-s) • x + s • y) - U ((1-s') • x + s' • y)| ≤ 2 * K * (r/4/R) ^ α := by
      intro s s' hs0 hs1 hs'0 hs'1 hdd
      have hdist : dist ((1-s) • x + s • y) ((1-s') • x + s' • y) = r/4 := by
        rw [hP, hdd]; ring
      rw [show r/4/R = dist ((1-s) • x + s • y) ((1-s') • x + s' • y) / R by rw [hdist]]
      exact hnear _ (hm s hs0 hs1) _ (hm s' hs'0 hs'1)
        (by rw [hdist]; linarith) (by rw [hdist]; linarith)
    have hx0 : (1-(0:ℝ)) • x + (0:ℝ) • y = x := by module
    have hy1 : (1-(1:ℝ)) • x + (1:ℝ) • y = y := by module
    have b1 := key 0 (1/4) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have b2 := key (1/4) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [abs_of_nonpos])
    have b3 := key (1/2) (3/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [abs_of_nonpos])
    have b4 := key (3/4) 1 (by norm_num) (by norm_num) (by norm_num) le_rfl
      (by norm_num [abs_of_nonpos])
    rw [hx0] at b1
    rw [hy1] at b4
    have hq : (r/4/R) ^ α ≤ (r/R) ^ α := by
      rw [show r/4/R = (1/4) * (r/R) by ring,
        Real.mul_rpow (by norm_num) (by positivity)]
      have h1 : ((1:ℝ)/4) ^ α ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) hα.le
      nlinarith [hnn]
    have hbb : 2 * K * (r/4/R) ^ α ≤ 2 * K * (r/R) ^ α := by nlinarith [hK, hq]
    have c1 := abs_sub_le (U x) (U ((1-(1/4:ℝ)) • x + (1/4:ℝ) • y)) (U y)
    have c2 := abs_sub_le (U ((1-(1/4:ℝ)) • x + (1/4:ℝ) • y))
      (U ((1-(1/2:ℝ)) • x + (1/2:ℝ) • y)) (U y)
    have c3 := abs_sub_le (U ((1-(1/2:ℝ)) • x + (1/2:ℝ) • y))
      (U ((1-(3/4:ℝ)) • x + (3/4:ℝ) • y)) (U y)
    linarith [b1, b2, b3, b4, c1, c2, c3, hbb]
  -- ===================== Step 7 and the assembly =====================
  have hRa : (0:ℝ) < R ^ α := Real.rpow_pos_of_pos hR α
  refine ⟨U, ?_, hcont, ⟨hcont.mono hDΩ, 8*K/R ^ α, by positivity, ?_⟩, hstep6⟩
  · -- ===================== Step 3 =====================
    obtain ⟨Dq, hDqc, hDqd⟩ := TopologicalSpace.exists_countable_dense (EuclideanSpace ℝ (Fin n))
    set 𝒬 : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
      {p | p.1 ∈ Dq ∧ (∃ q : ℚ, (q : ℝ) = p.2) ∧ 0 < p.2 ∧
        Metric.closedBall p.1 p.2 ⊆ Ω} with hQ
    have hQc : 𝒬.Countable := by
      refine Set.Countable.mono ?_ (hDqc.prod (Set.countable_range ((↑) : ℚ → ℝ)))
      rintro p ⟨h1, ⟨q, hq⟩, -, -⟩
      exact ⟨h1, q, hq⟩
    set Zf : EuclideanSpace ℝ (Fin n) × ℝ → Set (EuclideanSpace ℝ (Fin n)) :=
      fun p => {y | y ∈ Metric.ball p.1 p.2 ∧ ¬(I p.1 p.2 ≤ u y ∧ u y ≤ S p.1 p.2)}
      with hZf
    have hZ : ∀ p ∈ 𝒬, volume (Zf p) = 0 := by
      rintro p ⟨-, -, hp2, hp3⟩
      have hae := (hcore p.1 p.2 hp2 hp3).2
      rw [ae_restrict_iff' measurableSet_ball, ae_iff] at hae
      refine measure_mono_null ?_ hae
      intro y hy
      exact fun hcon => hy.2 (hcon hy.1)
    have hZnull : volume (⋃ p ∈ 𝒬, Zf p) = 0 := (measure_biUnion_null_iff hQc).2 hZ
    -- the pointwise identity off the null set
    have hpt : ∀ x ∈ Ω, x ∉ (⋃ p ∈ 𝒬, Zf p) → U x = u x := by
      intro x hxΩ hxZ
      obtain ⟨ρx, hρx, hρxsub⟩ := hAne x hxΩ
      have key : ∀ ε : ℝ, 0 < ε → |u x - U x| < ε := by
        intro ε hε
        have hth : (0:ℝ) < R/2 * (ε/(K+1)) ^ (1/α) := by
          have : (0:ℝ) < (ε/(K+1)) ^ (1/α) := Real.rpow_pos_of_pos (by positivity) _
          positivity
        obtain ⟨t, ht0, htlt⟩ :=
          exists_rat_btwn (show (0:ℝ) < min (ρx/2) (R/2 * (ε/(K+1)) ^ (1/α)) from
            lt_min (by linarith) hth)
        have ht0' : (0:ℝ) < (t : ℝ) := ht0
        have ht1 : (t : ℝ) < ρx/2 := lt_of_lt_of_le htlt (min_le_left _ _)
        have ht2 : (t : ℝ) < R/2 * (ε/(K+1)) ^ (1/α) :=
          lt_of_lt_of_le htlt (min_le_right _ _)
        -- (x, 2t) is admissible
        have hadm2 : Metric.closedBall x (2 * (t:ℝ)) ⊆ Ω := by
          refine subset_trans ?_ hρxsub
          exact Metric.closedBall_subset_closedBall (by linarith)
        have h2t : (0:ℝ) < 2 * (t:ℝ) := by linarith
        -- a point of the countable dense set close to x
        obtain ⟨q, hqD, hqd⟩ := Metric.dense_iff.1 hDqd x (t:ℝ) ht0'
        have hqd' : dist q x < (t:ℝ) := Metric.mem_ball.1 hqD
        have hqmem : q ∈ Dq := hqd
        have hballsub : Metric.ball q (t:ℝ) ⊆ Metric.ball x (2 * (t:ℝ)) := by
          intro z hz
          simp only [Metric.mem_ball] at hz ⊢
          have := dist_triangle z q x
          linarith
        have hcballsub : Metric.closedBall q (t:ℝ) ⊆ Ω := by
          refine subset_trans ?_ hadm2
          intro z hz
          simp only [Metric.mem_closedBall] at hz ⊢
          have := dist_triangle z q x
          linarith
        have hqQ : ((q, (t:ℝ)) : EuclideanSpace ℝ (Fin n) × ℝ) ∈ 𝒬 :=
          ⟨hqmem, ⟨t, rfl⟩, ht0', hcballsub⟩
        -- x is not in the exceptional set of this pair
        have hxq : x ∈ Metric.ball q (t:ℝ) := by
          simp only [Metric.mem_ball]
          rw [dist_comm]; exact hqd'
        have hgood : I q (t:ℝ) ≤ u x ∧ u x ≤ S q (t:ℝ) := by
          by_contra hcon
          exact hxZ (Set.mem_biUnion hqQ ⟨hxq, hcon⟩)
        -- transport to the bigger ball
        have hSq : S q (t:ℝ) ≤ S x (2 * (t:ℝ)) :=
          hmonoS _ _ hballsub (Metric.ball_subset_closedBall.trans hadm2)
            (hballpos q (t:ℝ) ht0')
        have hIq : I x (2 * (t:ℝ)) ≤ I q (t:ℝ) :=
          hmonoI _ _ hballsub (Metric.ball_subset_closedBall.trans hadm2)
            (hballpos q (t:ℝ) ht0')
        obtain ⟨hIU, hUS⟩ := hU6 x (2 * (t:ℝ)) h2t hadm2
        have hlen := hosc' x (2 * (t:ℝ)) h2t hadm2
        have habs : |u x - U x| ≤ S x (2*(t:ℝ)) - I x (2*(t:ℝ)) := by
          rw [abs_le]; constructor <;> linarith [hgood.1, hgood.2]
        -- the quantitative smallness
        have hq1 : 2 * (t:ℝ) / R < (ε/(K+1)) ^ (1/α) := by
          rw [div_lt_iff₀ hR]
          nlinarith [ht2, hR]
        have hq2 : (2 * (t:ℝ) / R) ^ α < ε/(K+1) := by
          have h5 := Real.rpow_lt_rpow (by positivity) hq1 hα
          rwa [← Real.rpow_mul (by positivity : (0:ℝ) ≤ ε/(K+1)), one_div,
            inv_mul_cancel₀ (ne_of_gt hα), Real.rpow_one] at h5
        have hnn : (0:ℝ) ≤ (2 * (t:ℝ) / R) ^ α := Real.rpow_nonneg (by positivity) α
        have hfin : (K+1) * (2 * (t:ℝ) / R) ^ α < (K+1) * (ε/(K+1)) :=
          mul_lt_mul_of_pos_left hq2 (by linarith)
        have hfin2 : (K+1) * (ε/(K+1)) = ε := by field_simp
        nlinarith [habs, hlen, hnn, hK]
      have hzero : |u x - U x| = 0 := by
        by_contra hne
        exact absurd (key _ (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne))) (lt_irrefl _)
      have := abs_eq_zero.1 hzero
      linarith
    rw [ae_restrict_iff' hΩ.measurableSet, ae_iff]
    refine measure_mono_null ?_ hZnull
    intro x hx
    by_contra hxZ
    exact hx (fun hxΩ => hpt x hxΩ hxZ)
  · intro x hx y hy
    have h1 := hstep6 x hx y hy
    rw [Real.div_rpow dist_nonneg hR.le] at h1
    calc |U x - U y| ≤ 8 * K * (dist x y ^ α / R ^ α) := h1
      _ = 8*K/R ^ α * dist x y ^ α := by field_simp
