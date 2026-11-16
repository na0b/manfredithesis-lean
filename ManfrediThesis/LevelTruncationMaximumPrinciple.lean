import ManfrediThesis.Preamble
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.DeGiorgiLevelBound
import ManfrediThesis.MemW1pOn
import ManfrediThesis.DeGiorgiSequenceLemma
import ManfrediThesis.DeGiorgiLevelSetMeasure
import ManfrediThesis.WeakGradientRestrict
open MeasureTheory
set_option maxHeartbeats 600000

/-- Lemma 2.3: a maximum principle for functions satisfying (2.1) on a range of
levels and radii. -/
theorem LevelTruncationMaximumPrinciple :
    ∀ (n : ℕ) (γ lam₀ lam₁ : ℝ), 2 ≤ n → 0 < γ →
      lam₀ ∈ Set.Ioo (0 : ℝ) 1 → lam₁ ∈ Set.Ioo (0 : ℝ) 1 →
      CitedSobolevPoincareBall n →
      ∃ θ₀ : ℝ, 0 < θ₀ ∧
        ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R k M : ℝ)
          (f : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 < R → MemW1pOn n 2 (Metric.ball x₀ R) f g →
          (∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), f x ≤ C) →
          M = essSup f (volume.restrict (Metric.ball x₀ R)) → k < M →
          (∀ l ρ₀ ρ₁ : ℝ, l ∈ Set.Icc k (lam₀ * k + (1 - lam₀) * M) →
            ρ₀ ∈ Set.Icc (lam₁ * R) R → ρ₁ ∈ Set.Icc (lam₁ * R) R → ρ₀ < ρ₁ →
            DeGiorgiLevelBound n γ f g x₀ l ρ₀ ρ₁) →
          (volume (Metric.ball x₀ R ∩ {y | k < f y})).toReal
            ≤ θ₀ * (volume (Metric.ball x₀ R)).toReal →
          ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (lam₁ * R))),
            f x ≤ lam₀ * k + (1 - lam₀) * M := by
  intro n γ lam₀ lam₁ hn hγ hlam₀ hlam₁ hSP
  obtain ⟨hlam₀0, hlam₀1⟩ := hlam₀
  obtain ⟨hlam₁0, hlam₁1⟩ := hlam₁
  have hnR : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hntriv : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, hnpos⟩ (1 : ℝ), ?_⟩⟩
    intro hc
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hnpos⟩) hc
    simp at h
  have hn1 : (0:ℝ) < (n : ℝ) - 1 := by linarith
  obtain ⟨β, hβ0, hDG2⟩ := DeGiorgiLevelSetMeasure n hn hSP
  -- `ω_n`
  have hωn : (0:ℝ) < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
    refine ENNReal.toReal_pos ?_ measure_ball_lt_top.ne
    exact (Metric.isOpen_ball.measure_pos volume
      ⟨0, Metric.mem_ball_self one_pos⟩).ne'
  -- Step 0: the constants, all of them functions of `n, γ, lam₀, lam₁` alone
  obtain ⟨ωn, hωndef⟩ : ∃ w : ℝ,
    w = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := ⟨_, rfl⟩
  rw [← hωndef] at hωn
  obtain ⟨ε, hεdef⟩ : ∃ e : ℝ, e = 1 / ((n : ℝ) - 1) := ⟨_, rfl⟩
  have hε0 : (0:ℝ) < ε := by rw [hεdef]; positivity
  obtain ⟨q, hqdef⟩ : ∃ s : ℝ, s = (n : ℝ) / ((n : ℝ) - 1) := ⟨_, rfl⟩
  have hq1 : q = 1 + ε := by
    rw [hqdef, hεdef]
    field_simp
    ring
  have hq0 : (0:ℝ) < q := by rw [hq1]; linarith
  obtain ⟨b, hbdef⟩ : ∃ s : ℝ,
    s = ((1 - lam₀) * (1 - lam₁)) ^ ((n : ℝ) / (1 - (n : ℝ))) := ⟨_, rfl⟩
  have hbase0 : (0:ℝ) < (1 - lam₀) * (1 - lam₁) := by nlinarith
  have hbase1 : (1 - lam₀) * (1 - lam₁) < 1 := by nlinarith
  have hb1 : 1 < b := by
    rw [hbdef]
    refine (Real.one_lt_rpow_iff_of_pos hbase0).2 (Or.inr ⟨hbase1, ?_⟩)
    refine div_neg_of_pos_of_neg (by linarith) (by linarith)
  have hb0 : (0:ℝ) < b := lt_trans one_pos hb1
  obtain ⟨C₁, hC₁def⟩ : ∃ s : ℝ,
    s = 2 * β * Real.sqrt γ / (ωn * lam₁ ^ (n + 1)) := ⟨_, rfl⟩
  have hsqγ : (0:ℝ) < Real.sqrt γ := Real.sqrt_pos.2 hγ
  have hC₁0 : (0:ℝ) < C₁ := by
    rw [hC₁def]
    have h1 : (0:ℝ) < lam₁ ^ (n + 1) := by positivity
    exact div_pos (mul_pos (mul_pos two_pos hβ0) hsqγ) (mul_pos hωn h1)
  obtain ⟨C₂, hC₂def⟩ : ∃ s : ℝ,
    s = C₁ / (lam₀ * (1 - lam₀) * (1 - lam₁)) := ⟨_, rfl⟩
  have hC₂0 : (0:ℝ) < C₂ := by
    rw [hC₂def]
    have h1 : (0:ℝ) < lam₀ * (1 - lam₀) * (1 - lam₁) := by nlinarith
    exact div_pos hC₁0 h1
  obtain ⟨c, hcdef⟩ : ∃ s : ℝ, s = C₂ ^ q := ⟨_, rfl⟩
  have hc0 : (0:ℝ) < c := by rw [hcdef]; exact Real.rpow_pos_of_pos hC₂0 _
  obtain ⟨θ₁, hθ₁def⟩ : ∃ s : ℝ, s = lam₁ ^ n / 2 := ⟨_, rfl⟩
  have hθ₁0 : (0:ℝ) < θ₁ := by rw [hθ₁def]; positivity
  obtain ⟨θ₂, hθ₂def⟩ : ∃ s : ℝ,
    s = (c ^ (-(1:ℝ) / ε) * b ^ (-(1:ℝ) / ε ^ 2)) / ωn := ⟨_, rfl⟩
  have hθ₂0 : (0:ℝ) < θ₂ := by
    rw [hθ₂def]
    have h1 : (0:ℝ) < c ^ (-(1:ℝ) / ε) := Real.rpow_pos_of_pos hc0 _
    have h2 : (0:ℝ) < b ^ (-(1:ℝ) / ε ^ 2) := Real.rpow_pos_of_pos hb0 _
    exact div_pos (mul_pos h1 h2) hωn
  refine ⟨min θ₁ θ₂, lt_min hθ₁0 hθ₂0, ?_⟩
  intro x₀ R k M f g hR hW hbdd hM hkM hDGB hsmall
  have hRn : (0:ℝ) < R ^ n := by positivity
  -- the volume of a ball, in the form used throughout
  have hballvol : ∀ σ : ℝ, 0 ≤ σ →
      (volume (Metric.ball x₀ σ)).toReal = ωn * σ ^ n := by
    intro σ hσ
    rw [Measure.addHaar_ball volume x₀ hσ, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity),
      show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n by simp, hωndef]
    ring
  -- Step 1: the two sequences
  obtain ⟨rr, hrrdef⟩ : ∃ s : ℕ → ℝ,
    s = fun h => lam₁ * R + (1 - lam₁) ^ (h + 1) * R := ⟨_, rfl⟩
  obtain ⟨kk, hkkdef⟩ : ∃ s : ℕ → ℝ,
    s = fun h => k + (1 - lam₀) * (M - k) - (1 - lam₀) ^ (h + 1) * (M - k) := ⟨_, rfl⟩
  have hMk : (0:ℝ) < M - k := by linarith
  have hrr0 : rr 0 = R := by rw [hrrdef]; ring
  have hrrgt : ∀ h : ℕ, lam₁ * R < rr h := by
    intro h
    rw [hrrdef]
    have h1 : (0:ℝ) < (1 - lam₁) ^ (h + 1) := by positivity
    nlinarith
  have hrrle : ∀ h : ℕ, rr h ≤ R := by
    intro h
    rw [hrrdef]
    have h1 : (1 - lam₁) ^ (h + 1) ≤ 1 - lam₁ := by
      calc (1 - lam₁) ^ (h + 1) ≤ (1 - lam₁) ^ 1 :=
            pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
        _ = 1 - lam₁ := pow_one _
    nlinarith
  have hrrpos : ∀ h : ℕ, (0:ℝ) < rr h := fun h =>
    lt_trans (by positivity) (hrrgt h)
  have hrrdiff : ∀ h : ℕ, rr h - rr (h + 1) = lam₁ * (1 - lam₁) ^ (h + 1) * R := by
    intro h
    rw [hrrdef]
    ring
  have hrrdec : ∀ h : ℕ, rr (h + 1) < rr h := by
    intro h
    have h1 := hrrdiff h
    have h2 : (0:ℝ) < lam₁ * (1 - lam₁) ^ (h + 1) * R := by positivity
    linarith
  have hkk0 : kk 0 = k := by rw [hkkdef]; ring
  have hkkge : ∀ h : ℕ, k ≤ kk h := by
    intro h
    rw [hkkdef]
    have h1 : (1 - lam₀) ^ (h + 1) ≤ 1 - lam₀ := by
      calc (1 - lam₀) ^ (h + 1) ≤ (1 - lam₀) ^ 1 :=
            pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
        _ = 1 - lam₀ := pow_one _
    nlinarith
  have hkklt : ∀ h : ℕ, kk h < lam₀ * k + (1 - lam₀) * M := by
    intro h
    rw [hkkdef]
    have h1 : (0:ℝ) < (1 - lam₀) ^ (h + 1) := by positivity
    nlinarith
  have hkkdiff : ∀ h : ℕ, kk (h + 1) - kk h
      = lam₀ * (1 - lam₀) ^ (h + 1) * (M - k) := by
    intro h
    rw [hkkdef]
    ring
  have hkkmono : ∀ h : ℕ, kk h ≤ kk (h + 1) := by
    intro h
    have h1 := hkkdiff h
    have h2 : (0:ℝ) ≤ lam₀ * (1 - lam₀) ^ (h + 1) * (M - k) := by positivity
    linarith
  -- the normalized level-set measures
  obtain ⟨ν, hνdef⟩ : ∃ s : ℕ → ℝ, s = fun h =>
    (volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal / R ^ n := ⟨_, rfl⟩
  have hν0 : ∀ h : ℕ, 0 ≤ ν h := by
    intro h
    rw [hνdef]
    positivity
  -- `f ≤ M` almost everywhere: this is where the essential-boundedness
  -- hypothesis is consumed, through `ae_le_essSup`
  have hbddU : Filter.IsBoundedUnder (· ≤ ·)
      (ae (volume.restrict (Metric.ball x₀ R))) f := by
    obtain ⟨C, hC⟩ := hbdd
    exact ⟨C, hC⟩
  have hfM : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), f x ≤ M := by
    rw [hM]
    exact ae_le_essSup hbddU
  have hn1' : 1 ≤ n := le_trans (by norm_num) hn
  have hfin : ∀ σ : ℝ, IsFiniteMeasure (volume.restrict (Metric.ball x₀ σ)) := by
    intro σ
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  -- `f ∈ W^{1,1}` on every smaller ball
  have hW1 : ∀ σ : ℝ, 0 < σ → σ ≤ R → MemW1pOn n 1 (Metric.ball x₀ σ) f g := by
    intro σ hσ hσR
    have hsub : Metric.ball x₀ σ ⊆ Metric.ball x₀ R := Metric.ball_subset_ball hσR
    have hW2 : MemW1pOn n 2 (Metric.ball x₀ σ) f g :=
      (WeakGradientRestrict n 2 hn1' (by norm_num) (Metric.ball x₀ R)
        (Metric.ball x₀ σ) f g Metric.isOpen_ball Metric.isOpen_ball hsub).1 hW
    have hfm := hfin σ
    have hle : (ENNReal.ofReal (1:ℝ)) ≤ ENNReal.ofReal (2:ℝ) :=
      ENNReal.ofReal_le_ofReal (by norm_num)
    exact ⟨hW2.1, hW2.2.1.mono_exponent hle, hW2.2.2.mono_exponent hle⟩
  -- the finiteness facts used throughout
  have hmonofin : ∀ (σ : ℝ) (S : Set (EuclideanSpace ℝ (Fin n))),
      S ⊆ Metric.ball x₀ σ → volume S ≠ ⊤ := fun σ S hS =>
    (lt_of_le_of_lt (measure_mono hS) measure_ball_lt_top).ne
  have hsubR : ∀ h : ℕ, Metric.ball x₀ (rr h) ⊆ Metric.ball x₀ R := fun h =>
    Metric.ball_subset_ball (hrrle h)
  -- `|g| ∈ L¹` and `|g| ∈ L²` on the big ball
  have hgL2 : MemLp g (ENNReal.ofReal 2) (volume.restrict (Metric.ball x₀ R)) := hW.2.2
  have hgL1 : IntegrableOn (fun x => ‖g x‖) (Metric.ball x₀ R) volume := by
    have h1 : MemLp g (ENNReal.ofReal 1) (volume.restrict (Metric.ball x₀ R)) :=
      (hW1 R hR le_rfl).2.2
    have h2 : Integrable g (volume.restrict (Metric.ball x₀ R)) := by
      rw [← memLp_one_iff_integrable]
      simpa using h1
    exact h2.norm
  -- Step 2: the nondegeneracy `(2.2a)`
  have hVpos : (0:ℝ) < (volume (Metric.ball x₀ (lam₁ * R))).toReal := by
    rw [hballvol (lam₁ * R) (by positivity)]
    positivity
  have hAmR : ∀ h : ℕ, Metric.ball x₀ (rr (h + 1)) ∩ {y | kk h < f y}
      ⊆ Metric.ball x₀ R ∩ {y | k < f y} := by
    intro h z hz
    exact ⟨hsubR (h + 1) hz.1, lt_of_le_of_lt (hkkge h) hz.2⟩
  have hWhalf : ∀ h : ℕ,
      (volume (Metric.ball x₀ (rr (h + 1)) ∩ {y | kk h < f y})).toReal
        ≤ (volume (Metric.ball x₀ (lam₁ * R))).toReal / 2 := by
    intro h
    have h1 : (volume (Metric.ball x₀ (rr (h + 1)) ∩ {y | kk h < f y})).toReal
        ≤ (volume (Metric.ball x₀ R ∩ {y | k < f y})).toReal :=
      ENNReal.toReal_mono (hmonofin R _ Set.inter_subset_left)
        (measure_mono (hAmR h))
    refine le_trans h1 (le_trans hsmall ?_)
    rw [hballvol R hR.le, hballvol (lam₁ * R) (by positivity)]
    have h2 : min θ₁ θ₂ ≤ θ₁ := min_le_left _ _
    have h3 : (0:ℝ) ≤ ωn * R ^ n := by positivity
    have h4 : θ₁ * (ωn * R ^ n) = ωn * (lam₁ * R) ^ n / 2 := by
      rw [hθ₁def, mul_pow]
      ring
    calc min θ₁ θ₂ * (ωn * R ^ n) ≤ θ₁ * (ωn * R ^ n) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ = ωn * (lam₁ * R) ^ n / 2 := h4
  have hZlb : ∀ h : ℕ,
      (volume (Metric.ball x₀ (lam₁ * R))).toReal / 2
        ≤ (volume (Metric.ball x₀ (rr (h + 1)) \ {y | kk h < f y})).toReal := by
    intro h
    have hcover : Metric.ball x₀ (lam₁ * R)
        ⊆ (Metric.ball x₀ (rr (h + 1)) \ {y | kk h < f y})
          ∪ (Metric.ball x₀ (rr (h + 1)) ∩ {y | kk h < f y}) := by
      intro z hz
      have hzb : z ∈ Metric.ball x₀ (rr (h + 1)) :=
        Metric.ball_subset_ball (le_of_lt (hrrgt (h + 1))) hz
      by_cases hc : kk h < f z
      · exact Or.inr ⟨hzb, hc⟩
      · exact Or.inl ⟨hzb, hc⟩
    have hf1 : volume (Metric.ball x₀ (rr (h + 1)) \ {y | kk h < f y}) ≠ ⊤ :=
      hmonofin (rr (h + 1)) _ Set.sdiff_subset
    have hf2 : volume (Metric.ball x₀ (rr (h + 1)) ∩ {y | kk h < f y}) ≠ ⊤ :=
      hmonofin (rr (h + 1)) _ Set.inter_subset_left
    have hsub1 : volume (Metric.ball x₀ (lam₁ * R))
        ≤ volume (Metric.ball x₀ (rr (h + 1)) \ {y | kk h < f y})
          + volume (Metric.ball x₀ (rr (h + 1)) ∩ {y | kk h < f y}) :=
      le_trans (measure_mono hcover) (measure_union_le _ _)
    have hVle : (volume (Metric.ball x₀ (lam₁ * R))).toReal
        ≤ (volume (Metric.ball x₀ (rr (h + 1)) \ {y | kk h < f y})).toReal
          + (volume (Metric.ball x₀ (rr (h + 1)) ∩ {y | kk h < f y})).toReal := by
      rw [← ENNReal.toReal_add hf1 hf2]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf1, hf2⟩) hsub1
    linarith [hWhalf h, hVle]
  have hZpos : ∀ h : ℕ,
      0 < (volume (Metric.ball x₀ (rr (h + 1)) \ {y | kk h < f y})).toReal := by
    intro h
    have := hZlb h
    linarith [hVpos]
  -- Step 3: the gradient integral, estimated by `DeGiorgiLevelBound`
  have hMkk : ∀ h : ℕ, kk h < M := by
    intro h
    have h1 := hkklt h
    nlinarith
  have hgrad2 : ∀ h : ℕ,
      (∫ x in Metric.ball x₀ (rr (h + 1)) ∩ {y | kk h < f y}, ‖g x‖ ^ 2)
        ≤ γ / (rr h - rr (h + 1)) ^ 2 * (M - k) ^ 2
          * (volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal := by
    intro h
    have hb2 := (hDGB (kk h) (rr (h + 1)) (rr h) ⟨hkkge h, (hkklt h).le⟩
      ⟨(hrrgt (h + 1)).le, hrrle (h + 1)⟩ ⟨(hrrgt h).le, hrrle h⟩ (hrrdec h)).2
    refine le_trans hb2 ?_
    have hEle : essSup (fun x => max (f x - kk h) 0 ^ 2)
        (volume.restrict (Metric.ball x₀ (rr h))) ≤ (M - k) ^ 2 := by
      have hneb : (ae (volume.restrict (Metric.ball x₀ (rr h)))).NeBot := by
        refine ae_neBot.2 ?_
        simp only [ne_eq, Measure.restrict_eq_zero]
        exact (Metric.isOpen_ball.measure_pos volume
          ⟨x₀, Metric.mem_ball_self (hrrpos h)⟩).ne'
      have hcob : Filter.IsCoboundedUnder (· ≤ ·)
          (ae (volume.restrict (Metric.ball x₀ (rr h))))
          (fun x => max (f x - kk h) 0 ^ 2) :=
        Filter.isCoboundedUnder_le_of_le _ (fun x => by positivity)
      refine essSup_le_of_ae_le _ ?_ hcob
      have hsub : Metric.ball x₀ (rr h) ⊆ Metric.ball x₀ R := hsubR h
      have hfM' : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (rr h))), f x ≤ M :=
        ae_restrict_of_ae_restrict_of_subset hsub hfM
      filter_upwards [hfM'] with x hx
      show max (f x - kk h) 0 ^ 2 ≤ (M - k) ^ 2
      have h1 : max (f x - kk h) 0 ≤ M - k := by
        refine max_le ?_ (by linarith)
        have := hkkge h
        linarith
      have h2 : (0:ℝ) ≤ max (f x - kk h) 0 := le_max_right _ _
      nlinarith
    have hc0' : (0:ℝ) ≤ γ / (rr h - rr (h + 1)) ^ 2 := by positivity
    have hv0 : (0:ℝ) ≤ (volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal :=
      ENNReal.toReal_nonneg
    have hstep := mul_le_mul_of_nonneg_left hEle hc0'
    exact mul_le_mul_of_nonneg_right hstep hv0
  -- Cauchy-Schwarz on a subset of the big ball
  have hcs : ∀ S : Set (EuclideanSpace ℝ (Fin n)), S ⊆ Metric.ball x₀ R →
      (∫ x in S, ‖g x‖)
        ≤ Real.sqrt ((volume S).toReal) * Real.sqrt (∫ x in S, ‖g x‖ ^ 2) := by
    intro S hS
    have hfinS : IsFiniteMeasure (volume.restrict S) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_lt (measure_mono hS) measure_ball_lt_top
    have hgS : MemLp g (ENNReal.ofReal 2) (volume.restrict S) :=
      hgL2.mono_measure (Measure.restrict_mono hS le_rfl)
    have hconj : Real.HolderConjugate 2 2 := by
      rw [Real.holderConjugate_iff]
      norm_num
    have hone : MemLp (fun _ : EuclideanSpace ℝ (Fin n) => (1:ℝ))
        (ENNReal.ofReal 2) (volume.restrict S) := memLp_const 1
    have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict S) hconj
      (Filter.Eventually.of_forall fun _ => (zero_le_one : (0:ℝ) ≤ 1))
      (Filter.Eventually.of_forall fun x => norm_nonneg (g x)) hone hgS.norm
    have e1 : (∫ x in S, (1:ℝ) * ‖g x‖) = ∫ x in S, ‖g x‖ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (1:ℝ) * ‖g x‖ = ‖g x‖
      ring
    have e2 : (∫ _x in S, (1:ℝ) ^ (2:ℝ)) = (volume S).toReal := by
      have h1 : ∀ _x : EuclideanSpace ℝ (Fin n), (1:ℝ) ^ (2:ℝ) = (1:ℝ) := fun _ =>
        Real.one_rpow 2
      rw [integral_congr_ae (Filter.Eventually.of_forall h1), setIntegral_const,
        MeasureTheory.measureReal_def, smul_eq_mul, mul_one]
    have e3 : (∫ x in S, ‖g x‖ ^ (2:ℝ)) = ∫ x in S, ‖g x‖ ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show ‖g x‖ ^ (2:ℝ) = ‖g x‖ ^ 2
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [e1, e2, e3] at hH
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact hH
  -- the `L¹` bound on the gradient over the intermediate set
  have hgradL1 : ∀ h : ℕ,
      (∫ x in Metric.ball x₀ (rr (h + 1)) ∩ {y | kk h < f y}, ‖g x‖)
        ≤ Real.sqrt γ * (M - k) / (rr h - rr (h + 1))
          * (volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal := by
    intro h
    have hd : (0:ℝ) < rr h - rr (h + 1) := by
      have := hrrdec h
      linarith
    have hAmsub : Metric.ball x₀ (rr (h + 1)) ∩ {y | kk h < f y}
        ⊆ Metric.ball x₀ (rr h) ∩ {y | kk h < f y} := by
      intro z hz
      exact ⟨Metric.ball_subset_ball (le_of_lt (hrrdec h)) hz.1, hz.2⟩
    have ham : (volume (Metric.ball x₀ (rr (h + 1)) ∩ {y | kk h < f y})).toReal
        ≤ (volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal :=
      ENNReal.toReal_mono (hmonofin (rr h) _ Set.inter_subset_left)
        (measure_mono hAmsub)
    have ha0 : (0:ℝ) ≤ (volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal :=
      ENNReal.toReal_nonneg
    have h1 := hcs (Metric.ball x₀ (rr (h + 1)) ∩ {y | kk h < f y})
      (Set.inter_subset_left.trans (hsubR (h + 1)))
    have h2 := hgrad2 h
    have h3 : Real.sqrt (∫ x in Metric.ball x₀ (rr (h + 1)) ∩ {y | kk h < f y},
          ‖g x‖ ^ 2)
        ≤ Real.sqrt (γ / (rr h - rr (h + 1)) ^ 2 * (M - k) ^ 2
          * (volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal) :=
      Real.sqrt_le_sqrt h2
    have hMk : (0:ℝ) ≤ M - k := by linarith
    have hcoef : (0:ℝ) ≤ Real.sqrt γ * (M - k) / (rr h - rr (h + 1)) := by
      have := Real.sqrt_nonneg γ
      positivity
    have h4 : Real.sqrt (γ / (rr h - rr (h + 1)) ^ 2 * (M - k) ^ 2
          * (volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal)
        = Real.sqrt γ * (M - k) / (rr h - rr (h + 1))
          * Real.sqrt ((volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal) := by
      have hrw : γ / (rr h - rr (h + 1)) ^ 2 * (M - k) ^ 2
          = (Real.sqrt γ * (M - k) / (rr h - rr (h + 1))) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hγ.le]
        ring
      rw [hrw, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hcoef]
    have h5 : Real.sqrt ((volume (Metric.ball x₀ (rr (h + 1))
          ∩ {y | kk h < f y})).toReal)
        ≤ Real.sqrt ((volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal) :=
      Real.sqrt_le_sqrt ham
    have hsq : Real.sqrt ((volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal)
        * Real.sqrt ((volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal)
        = (volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal :=
      Real.mul_self_sqrt ha0
    calc (∫ x in Metric.ball x₀ (rr (h + 1)) ∩ {y | kk h < f y}, ‖g x‖)
        ≤ Real.sqrt ((volume (Metric.ball x₀ (rr (h + 1))
              ∩ {y | kk h < f y})).toReal)
          * Real.sqrt (∫ x in Metric.ball x₀ (rr (h + 1)) ∩ {y | kk h < f y},
              ‖g x‖ ^ 2) := h1
      _ ≤ Real.sqrt ((volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal)
          * (Real.sqrt γ * (M - k) / (rr h - rr (h + 1))
            * Real.sqrt ((volume (Metric.ball x₀ (rr h)
              ∩ {y | kk h < f y})).toReal)) := by
          rw [← h4]
          exact mul_le_mul h5 h3 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt γ * (M - k) / (rr h - rr (h + 1))
          * (volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal := by
          rw [show Real.sqrt ((volume (Metric.ball x₀ (rr h)
                  ∩ {y | kk h < f y})).toReal)
                * (Real.sqrt γ * (M - k) / (rr h - rr (h + 1))
                  * Real.sqrt ((volume (Metric.ball x₀ (rr h)
                    ∩ {y | kk h < f y})).toReal))
              = Real.sqrt γ * (M - k) / (rr h - rr (h + 1))
                * (Real.sqrt ((volume (Metric.ball x₀ (rr h)
                    ∩ {y | kk h < f y})).toReal)
                  * Real.sqrt ((volume (Metric.ball x₀ (rr h)
                    ∩ {y | kk h < f y})).toReal)) by ring, hsq]
  -- the arithmetic core of Step 4: divide `(2.3)` by `lam₀ (1-lam₀)^{h+1} (M-k)`
  have harith : ∀ (h : ℕ) (a1 a0 Z : ℝ), 0 ≤ a0 → 0 < Z →
      (volume (Metric.ball x₀ (lam₁ * R))).toReal / 2 ≤ Z →
      (kk (h + 1) - kk h) * a1 ^ (1 - 1 / (n : ℝ))
        ≤ β * rr (h + 1) ^ (n : ℝ) / Z
          * (Real.sqrt γ * (M - k) / (rr h - rr (h + 1)) * a0) →
      a1 ^ (1 - 1 / (n : ℝ))
        ≤ C₂ / ((1 - lam₀) * (1 - lam₁)) ^ h * (a0 / R) := by
    intro h a1 a0 Z ha0 hZ0 hZge hmain
    have hLpos : (0:ℝ) < kk (h + 1) - kk h := by
      rw [hkkdiff h]
      have : (0:ℝ) < (1 - lam₀) ^ (h + 1) := by positivity
      positivity
    refine le_of_mul_le_mul_left (le_trans hmain ?_) hLpos
    have hZge' : ωn * lam₁ ^ n * R ^ n / 2 ≤ Z := by
      have := hZge
      rw [hballvol (lam₁ * R) (by positivity), mul_pow] at this
      linarith [this]
    have hrrn : rr (h + 1) ^ (n : ℝ) ≤ R ^ n := by
      rw [Real.rpow_natCast]
      exact pow_le_pow_left₀ (hrrpos (h + 1)).le (hrrle (h + 1)) n
    have hstep1 : β * rr (h + 1) ^ (n : ℝ) / Z ≤ 2 * β / (ωn * lam₁ ^ n) := by
      rw [div_le_div_iff₀ hZ0 (by positivity)]
      have e1 : β * rr (h + 1) ^ (n : ℝ) * (ωn * lam₁ ^ n)
          ≤ β * R ^ n * (ωn * lam₁ ^ n) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrrn hβ0.le) (by positivity)
      have e2 := mul_le_mul_of_nonneg_left hZge' (by positivity : (0:ℝ) ≤ 2 * β)
      linarith
    have hnn : (0:ℝ) ≤ Real.sqrt γ * (M - k) / (rr h - rr (h + 1)) * a0 := by
      have h1 : (0:ℝ) < rr h - rr (h + 1) := by linarith [hrrdec h]
      have h2 : (0:ℝ) ≤ Real.sqrt γ := Real.sqrt_nonneg γ
      have h3 : (0:ℝ) ≤ Real.sqrt γ * (M - k) / (rr h - rr (h + 1)) := by positivity
      exact mul_nonneg h3 ha0
    refine le_trans (mul_le_mul_of_nonneg_right hstep1 hnn) (le_of_eq ?_)
    rw [hkkdiff h, hrrdiff h, hC₂def, hC₁def, mul_pow]
    have hne1 : ((1:ℝ) - lam₀) ^ h ≠ 0 := by positivity
    have hne2 : ((1:ℝ) - lam₁) ^ h ≠ 0 := by positivity
    have hne3 : (ωn : ℝ) ≠ 0 := ne_of_gt hωn
    have hne4 : (lam₁ : ℝ) ^ n ≠ 0 := by positivity
    have hne5 : (R : ℝ) ≠ 0 := ne_of_gt hR
    have hne6 : (lam₀ : ℝ) ≠ 0 := ne_of_gt hlam₀0
    have hne7 : ((1:ℝ) - lam₀) ≠ 0 := by positivity
    have hne8 : ((1:ℝ) - lam₁) ≠ 0 := by positivity
    have hne9 : (lam₁ : ℝ) ≠ 0 := ne_of_gt hlam₁0
    rw [pow_succ, pow_succ, pow_succ]
    field_simp
  -- `(2.3)`-`(2.4)`: the De Giorgi isoperimetric inequality on `B_{r_{h+1}}`,
  -- fed by the gradient bound and Cauchy-Schwarz
  have hA : ∀ h : ℕ,
      (volume (Metric.ball x₀ (rr (h + 1)) ∩ {y | kk (h + 1) < f y})).toReal
          ^ (1 - 1 / (n : ℝ))
        ≤ C₂ / ((1 - lam₀) * (1 - lam₁)) ^ h
          * ((volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal / R) := by
    intro h
    refine harith h _ _ _ ENNReal.toReal_nonneg (hZpos h) (hZlb h) ?_
    refine le_trans (hDG2 x₀ (rr (h + 1)) f g (kk h) (kk (h + 1)) (hrrpos (h + 1))
      (hW1 (rr (h + 1)) (hrrpos (h + 1)) (hrrle (h + 1))) (hkkmono h) (hZpos h)) ?_
    refine mul_le_mul_of_nonneg_left ?_
      (div_nonneg (mul_nonneg hβ0.le (Real.rpow_nonneg (hrrpos (h + 1)).le _))
        ENNReal.toReal_nonneg)
    refine le_trans ?_ (hgradL1 h)
    refine setIntegral_mono_set
      (hgL1.mono_set (Set.inter_subset_left.trans (hsubR (h + 1))))
      (Filter.Eventually.of_forall fun x => norm_nonneg (g x))
      (Filter.Eventually.of_forall fun x hx => hx.1)
  -- Step 4: raise `(2.4)` to the power `q` and normalize
  have hrec : ∀ h : ℕ, ν (h + 1) ≤ c * b ^ (h : ℝ) * ν h ^ (1 + ε) := by
    intro h
    obtain ⟨a1, ha1def⟩ : ∃ s : ℝ,
      s = (volume (Metric.ball x₀ (rr (h + 1)) ∩ {y | kk (h + 1) < f y})).toReal :=
      ⟨_, rfl⟩
    obtain ⟨a0, ha0def⟩ : ∃ s : ℝ,
      s = (volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal := ⟨_, rfl⟩
    have ha1 : (0:ℝ) ≤ a1 := by rw [ha1def]; exact ENNReal.toReal_nonneg
    have ha0 : (0:ℝ) ≤ a0 := by rw [ha0def]; exact ENNReal.toReal_nonneg
    have hA' : a1 ^ (1 - 1 / (n : ℝ))
        ≤ C₂ / ((1 - lam₀) * (1 - lam₁)) ^ h * (a0 / R) := by
      rw [ha1def, ha0def]; exact hA h
    have hDh : (0:ℝ) < ((1 - lam₀) * (1 - lam₁)) ^ h := by positivity
    have hRn0 : (0:ℝ) < R ^ n := hRn
    have hexp : (1 - 1 / (n : ℝ)) * q = 1 := by
      rw [hqdef]
      field_simp
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg ha1 _) hA' hq0.le
    rw [← Real.rpow_mul ha1, hexp, Real.rpow_one] at hpow
    -- the `q`-th power of the right-hand side
    have hY0 : (0:ℝ) < (((1 - lam₀) * (1 - lam₁)) ^ h) ^ q :=
      Real.rpow_pos_of_pos hDh _
    have hbh : (((1 - lam₀) * (1 - lam₁)) ^ h) ^ q * b ^ (h : ℝ) = 1 := by
      rw [← Real.rpow_natCast ((1 - lam₀) * (1 - lam₁)) h,
        ← Real.rpow_mul hbase0.le, hbdef, ← Real.rpow_mul hbase0.le,
        ← Real.rpow_add hbase0]
      rw [show (h : ℝ) * q + (n : ℝ) / (1 - (n : ℝ)) * (h : ℝ) = 0 by
        have e1 : (1:ℝ) - (n : ℝ) ≠ 0 := by linarith
        have e2 : (n : ℝ) - 1 ≠ 0 := by linarith
        rw [hqdef]
        field_simp
        ring]
      exact Real.rpow_zero _
    have hbh' : b ^ (h : ℝ) = 1 / (((1 - lam₀) * (1 - lam₁)) ^ h) ^ q := by
      field_simp
      linarith [hbh]
    have hkey : (C₂ / ((1 - lam₀) * (1 - lam₁)) ^ h * (a0 / R)) ^ q
        = c * b ^ (h : ℝ) * (a0 ^ q / R ^ q) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.div_rpow hC₂0.le hDh.le, Real.div_rpow ha0 hR.le, ← hcdef, hbh']
      ring
    rw [hkey] at hpow
    -- divide by `R ^ n`
    have hRident : (a0 / R ^ n) ^ q = a0 ^ q / R ^ q / R ^ n := by
      rw [Real.div_rpow ha0 (by positivity), div_div]
      congr 1
      rw [← Real.rpow_natCast R n, ← Real.rpow_mul hR.le, ← Real.rpow_add hR]
      congr 1
      rw [hqdef]
      field_simp
      ring
    have hstep := mul_le_mul_of_nonneg_right hpow (le_of_lt (inv_pos.2 hRn0))
    simp only [hνdef]
    rw [← ha1def, ← ha0def, ← hq1, hRident]
    calc a1 / R ^ n = a1 * (R ^ n)⁻¹ := by ring
      _ ≤ c * b ^ (h : ℝ) * (a0 ^ q / R ^ q) * (R ^ n)⁻¹ := hstep
      _ = c * b ^ (h : ℝ) * (a0 ^ q / R ^ q / R ^ n) := by ring
  -- Step 5: the De Giorgi iteration
  have hthr : ν 0 ≤ c ^ (-(1:ℝ) / ε) * b ^ (-(1:ℝ) / ε ^ 2) := by
    have h1 : (volume (Metric.ball x₀ (rr 0) ∩ {y | kk 0 < f y})).toReal
        ≤ min θ₁ θ₂ * (volume (Metric.ball x₀ R)).toReal := by
      rw [hrr0, hkk0]
      exact hsmall
    rw [hνdef]
    show (volume (Metric.ball x₀ (rr 0) ∩ {y | kk 0 < f y})).toReal / R ^ n ≤ _
    rw [div_le_iff₀ hRn]
    refine le_trans h1 ?_
    rw [hballvol R hR.le]
    have h2 : min θ₁ θ₂ ≤ θ₂ := min_le_right _ _
    have h3 : (0:ℝ) ≤ ωn * R ^ n := by positivity
    calc min θ₁ θ₂ * (ωn * R ^ n) ≤ θ₂ * (ωn * R ^ n) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ = (θ₂ * ωn) * R ^ n := by ring
      _ = c ^ (-(1:ℝ) / ε) * b ^ (-(1:ℝ) / ε ^ 2) * R ^ n := by
          rw [hθ₂def]
          field_simp
  have hlim : Filter.Tendsto ν Filter.atTop (nhds (0:ℝ)) :=
    DeGiorgiSequenceLemma c ε b ν hc0 hε0 hb1 hν0 hrec hthr
  -- Step 6: the conclusion
  have hsubh : ∀ h : ℕ,
      Metric.ball x₀ (lam₁ * R) ∩ {y | lam₀ * k + (1 - lam₀) * M < f y}
        ⊆ Metric.ball x₀ (rr h) ∩ {y | kk h < f y} := by
    intro h z hz
    refine ⟨Metric.ball_subset_ball (le_of_lt (hrrgt h)) hz.1, ?_⟩
    exact lt_trans (hkklt h) hz.2
  have hStop : volume (Metric.ball x₀ (lam₁ * R)
      ∩ {y | lam₀ * k + (1 - lam₀) * M < f y}) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_ball_lt_top).ne
  have hSle : ∀ h : ℕ, (volume (Metric.ball x₀ (lam₁ * R)
      ∩ {y | lam₀ * k + (1 - lam₀) * M < f y})).toReal ≤ R ^ n * ν h := by
    intro h
    rw [hνdef]
    show _ ≤ R ^ n * ((volume (Metric.ball x₀ (rr h) ∩ {y | kk h < f y})).toReal / R ^ n)
    rw [mul_div_cancel₀ _ (ne_of_gt hRn)]
    refine ENNReal.toReal_mono ?_ (measure_mono (hsubh h))
    exact (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_ball_lt_top).ne
  have hzero : volume (Metric.ball x₀ (lam₁ * R)
      ∩ {y | lam₀ * k + (1 - lam₀) * M < f y}) = 0 := by
    have hle0 : (volume (Metric.ball x₀ (lam₁ * R)
        ∩ {y | lam₀ * k + (1 - lam₀) * M < f y})).toReal ≤ 0 := by
      have hto : Filter.Tendsto (fun h : ℕ => R ^ n * ν h) Filter.atTop (nhds 0) := by
        have h := hlim.const_mul (R ^ n)
        rw [mul_zero] at h
        exact h
      exact ge_of_tendsto hto (Filter.Eventually.of_forall hSle)
    have hnn : (0:ℝ) ≤ (volume (Metric.ball x₀ (lam₁ * R)
        ∩ {y | lam₀ * k + (1 - lam₀) * M < f y})).toReal := ENNReal.toReal_nonneg
    have : (volume (Metric.ball x₀ (lam₁ * R)
        ∩ {y | lam₀ * k + (1 - lam₀) * M < f y})).toReal = 0 := le_antisymm hle0 hnn
    exact (ENNReal.toReal_eq_zero_iff _).1 this |>.resolve_right hStop
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hzero] with x hx hxb
  by_contra hcon
  exact hx ⟨hxb, not_le.1 hcon⟩
