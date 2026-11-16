import ManfrediThesis.Preamble
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.DeGiorgiLevelBound
import ManfrediThesis.MemW1pOn
import ManfrediThesis.EssOscOn
import ManfrediThesis.LevelTruncationMaximumPrinciple
import ManfrediThesis.LevelSetMeasureImprovement
import ManfrediThesis.WeakGradientLinear
import ManfrediThesis.WeakGradientRestrict
open MeasureTheory

/-- Lemma 2.5: the oscillation decay estimate for functions such that both `f`
and `-f` satisfy conditions of the form (2.1). -/
theorem OscillationDecayLemma :
    ∀ (n : ℕ) (γ lam₁ : ℝ), 2 ≤ n → 0 < γ → lam₁ ∈ Set.Ioo (0 : ℝ) 1 →
      CitedSobolevPoincareBall n →
      ∃ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R m M : ℝ)
          (f : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 < R → MemW1pOn n 2 (Metric.ball x₀ R) f g →
          (∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), |f x| ≤ C) →
          M = essSup f (volume.restrict (Metric.ball x₀ R)) →
          m = essInf f (volume.restrict (Metric.ball x₀ R)) →
          (∀ l ρ₀ ρ₁ : ℝ, l ∈ Set.Icc ((m + M) / 2) M →
            ρ₀ ∈ Set.Icc (lam₁ * R) R → ρ₁ ∈ Set.Icc (lam₁ * R) R → ρ₀ < ρ₁ →
            DeGiorgiLevelBound n γ f g x₀ l ρ₀ ρ₁) →
          (∀ l ρ₀ ρ₁ : ℝ, l ∈ Set.Icc m ((m + M) / 2) →
            ρ₀ ∈ Set.Icc (lam₁ * R) R → ρ₁ ∈ Set.Icc (lam₁ * R) R → ρ₀ < ρ₁ →
            DeGiorgiLevelBound n γ (fun x => -f x) (fun x => -g x) x₀ (-l) ρ₀ ρ₁) →
          EssOscOn n (Metric.ball x₀ (lam₁ * R)) f
            ≤ δ * EssOscOn n (Metric.ball x₀ R) f := by
  intro n γ lam₁ hn hγ hlam₁ hSP
  obtain ⟨hl10, hl11⟩ := hlam₁
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  -- Step 0: the constants
  obtain ⟨sq, hsqdef⟩ : ∃ t : ℝ, t = Real.sqrt lam₁ := ⟨_, rfl⟩
  have hsq0 : 0 < sq := by rw [hsqdef]; exact Real.sqrt_pos.2 hl10
  have hsqsq : sq * sq = lam₁ := by rw [hsqdef]; exact Real.mul_self_sqrt hl10.le
  have hsq1 : sq < 1 := by nlinarith
  have hlamsq : lam₁ ≤ sq := by nlinarith
  obtain ⟨θ₀, hθ₀0, hLTMP⟩ := LevelTruncationMaximumPrinciple n γ (1/2) sq hn hγ
    ⟨by norm_num, by norm_num⟩ ⟨hsq0, hsq1⟩ hSP
  obtain ⟨θ₁, hθ₁def⟩ : ∃ t : ℝ, t = min θ₀ (1/2) := ⟨_, rfl⟩
  have hθ₁0 : 0 < θ₁ := by rw [hθ₁def]; exact lt_min hθ₀0 (by norm_num)
  have hθ₁1 : θ₁ < 1 := by
    rw [hθ₁def]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hθ₁θ₀ : θ₁ ≤ θ₀ := by rw [hθ₁def]; exact min_le_left _ _
  obtain ⟨lam₂, hlam₂, hLSMI⟩ := LevelSetMeasureImprovement n γ sq (1/2) θ₁ hn hγ
    ⟨hsq0, hsq1⟩ (by norm_num) (by norm_num) ⟨hθ₁0, hθ₁1⟩ hSP
  obtain ⟨hl20, hl21⟩ := hlam₂
  refine ⟨1 - lam₂ / 4, ⟨by linarith, by linarith⟩, ?_⟩
  intro x₀ R m M f g hR hW hbdd hM hm hH1 hH2
  have hlamR : 0 < lam₁ * R := by positivity
  have hsqR : 0 < sq * R := by positivity
  have hsqRle : sq * R ≤ R := by nlinarith
  have hsqRlt : sq * R < R := by nlinarith
  have hlamRle : lam₁ * R ≤ sq * R := by nlinarith
  have hsubsq : Metric.ball x₀ (sq * R) ⊆ Metric.ball x₀ R :=
    Metric.ball_subset_ball hsqRle
  have hsublam : Metric.ball x₀ (lam₁ * R) ⊆ Metric.ball x₀ (sq * R) :=
    Metric.ball_subset_ball hlamRle
  have hsublamR : Metric.ball x₀ (lam₁ * R) ⊆ Metric.ball x₀ R :=
    hsublam.trans hsubsq
  -- the `ae` filters are nontrivial on every ball of positive radius
  have hNBof : ∀ σ : ℝ, 0 < σ →
      Filter.NeBot (ae (volume.restrict (Metric.ball x₀ σ))) := by
    intro σ hσ
    rw [ae_neBot]
    intro hcc
    rw [← Measure.measure_univ_eq_zero, Measure.restrict_apply_univ] at hcc
    exact (Metric.measure_ball_pos volume x₀ hσ).ne' hcc
  -- Step 4-5, for an arbitrary admissible pair `(F, Γ)`
  have core : ∀ (F : EuclideanSpace ℝ (Fin n) → ℝ)
      (Γ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (mF MF : ℝ),
      MemW1pOn n 2 (Metric.ball x₀ R) F Γ →
      (∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), |F x| ≤ C) →
      MF = essSup F (volume.restrict (Metric.ball x₀ R)) →
      mF = essInf F (volume.restrict (Metric.ball x₀ R)) →
      (∀ l ρ₀ ρ₁ : ℝ, l ∈ Set.Icc ((mF + MF) / 2) MF →
        ρ₀ ∈ Set.Icc (lam₁ * R) R → ρ₁ ∈ Set.Icc (lam₁ * R) R → ρ₀ < ρ₁ →
        DeGiorgiLevelBound n γ F Γ x₀ l ρ₀ ρ₁) →
      (volume (Metric.ball x₀ (sq * R) ∩ {y | (mF + MF) / 2 < F y})).toReal
        ≤ (1 / 2) * (volume (Metric.ball x₀ (sq * R))).toReal →
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (lam₁ * R))),
        F x ≤ (mF + MF) / 2 + (1 - lam₂ / 2) * ((MF - mF) / 2) := by
    intro F Γ mF MF hFW hFb hFM hFm hFlev hFmeas
    have hNBR := hNBof R hR
    obtain ⟨C, hC⟩ := hFb
    have hbU : Filter.IsBoundedUnder (· ≤ ·) (ae (volume.restrict (Metric.ball x₀ R))) F := by
      refine ⟨C, ?_⟩
      rw [Filter.eventually_map]
      filter_upwards [hC] with x hx
      exact (abs_le.1 hx).2
    have hbL : Filter.IsBoundedUnder (· ≥ ·) (ae (volume.restrict (Metric.ball x₀ R))) F := by
      refine ⟨-C, ?_⟩
      rw [Filter.eventually_map]
      filter_upwards [hC] with x hx
      exact (abs_le.1 hx).1
    have hFle : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), F x ≤ MF := by
      rw [hFM]; exact ae_le_essSup hbU
    have hFge : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), mF ≤ F x := by
      rw [hFm]; exact ae_essInf_le hbL
    have hmM : mF ≤ MF := by
      obtain ⟨x, hx1, hx2⟩ := (hFle.and hFge).exists
      linarith
    have hFb1 : ∃ C' : ℝ, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), F x ≤ C' :=
      ⟨MF, hFle⟩
    rcases eq_or_lt_of_le hmM with heq | hlt
    · -- degenerate: `mF = MF`
      have hR0 : (mF + MF) / 2 + (1 - lam₂ / 2) * ((MF - mF) / 2) = MF := by
        rw [← heq]; ring
      rw [hR0]
      exact ae_restrict_of_ae_restrict_of_subset hsublamR hFle
    · -- the main case
      have hmid : (mF + MF) / 2 < MF := by linarith
      -- Step 4: Lemma 2.4
      have hlevLS : ∀ l : ℝ, l ∈ Set.Icc ((mF + MF) / 2) MF →
          DeGiorgiLevelBound n γ F Γ x₀ l (sq * R) R := by
        intro l hl
        exact hFlev l (sq * R) R hl ⟨hlamRle, hsqRle⟩ ⟨by nlinarith, le_rfl⟩ hsqRlt
      have hA := hLSMI x₀ R ((mF + MF) / 2) MF F Γ hR hFW hFb1 hFM hmid hlevLS hFmeas
      obtain ⟨k, hkdef⟩ : ∃ t : ℝ, t = lam₂ * ((mF + MF) / 2) + (1 - lam₂) * MF :=
        ⟨_, rfl⟩
      rw [← hkdef] at hA
      have hkge : (mF + MF) / 2 ≤ k := by rw [hkdef]; nlinarith
      have hkle : k ≤ MF := by rw [hkdef]; nlinarith
      -- Step 5: the two cases against `M'`
      obtain ⟨M', hM'def⟩ : ∃ t : ℝ,
        t = essSup F (volume.restrict (Metric.ball x₀ (sq * R))) := ⟨_, rfl⟩
      have hNBs := hNBof (sq * R) hsqR
      have hbUs : Filter.IsBoundedUnder (· ≤ ·)
          (ae (volume.restrict (Metric.ball x₀ (sq * R)))) F := by
        refine ⟨MF, ?_⟩
        rw [Filter.eventually_map]
        exact ae_restrict_of_ae_restrict_of_subset hsubsq hFle
      have hFles : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (sq * R))), F x ≤ M' := by
        rw [hM'def]; exact ae_le_essSup hbUs
      have hbLs : Filter.IsBoundedUnder (· ≥ ·)
          (ae (volume.restrict (Metric.ball x₀ (sq * R)))) F := by
        refine ⟨mF, ?_⟩
        rw [Filter.eventually_map]
        exact ae_restrict_of_ae_restrict_of_subset hsubsq hFge
      have hM'le : M' ≤ MF := by
        rw [hM'def]
        exact essSup_le_of_ae_le MF
          (ae_restrict_of_ae_restrict_of_subset hsubsq hFle) hbLs.isCobounded_flip
      have hFWs : MemW1pOn n 2 (Metric.ball x₀ (sq * R)) F Γ :=
        (WeakGradientRestrict n 2 hn1 (by norm_num) (Metric.ball x₀ R)
          (Metric.ball x₀ (sq * R)) F Γ Metric.isOpen_ball Metric.isOpen_ball
          hsubsq).1 hFW
      have hFb1s : ∃ C' : ℝ,
          ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (sq * R))), F x ≤ C' := ⟨M', hFles⟩
      rcases lt_or_ge k M' with hcase | hcase
      · -- Case 1: apply Lemma 2.3 on `B_{sq R}` at the level `k`
        have hlevLT : ∀ l ρ₀ ρ₁ : ℝ,
            l ∈ Set.Icc k ((1/2) * k + (1 - 1/2) * M') →
            ρ₀ ∈ Set.Icc (sq * (sq * R)) (sq * R) →
            ρ₁ ∈ Set.Icc (sq * (sq * R)) (sq * R) → ρ₀ < ρ₁ →
            DeGiorgiLevelBound n γ F Γ x₀ l ρ₀ ρ₁ := by
          intro l ρ₀ ρ₁ hl hr0 hr1 hlt'
          have hsqsqR : sq * (sq * R) = lam₁ * R := by rw [← mul_assoc, hsqsq]
          rw [hsqsqR] at hr0 hr1
          refine hFlev l ρ₀ ρ₁ ⟨?_, ?_⟩ ⟨hr0.1, le_trans hr0.2 hsqRle⟩
            ⟨hr1.1, le_trans hr1.2 hsqRle⟩ hlt'
          · linarith [hl.1]
          · have := hl.2
            linarith
        have hmeasLT : (volume (Metric.ball x₀ (sq * R) ∩ {y | k < F y})).toReal
            ≤ θ₀ * (volume (Metric.ball x₀ (sq * R))).toReal := by
          refine le_trans hA ?_
          exact mul_le_mul_of_nonneg_right hθ₁θ₀ ENNReal.toReal_nonneg
        have hB := hLTMP x₀ (sq * R) k M' F Γ hsqR hFWs hFb1s hM'def hcase
          hlevLT hmeasLT
        have hsqsqR : sq * (sq * R) = lam₁ * R := by rw [← mul_assoc, hsqsq]
        rw [hsqsqR] at hB
        filter_upwards [hB] with x hx
        have : (1/2 : ℝ) * k + (1 - 1/2) * M'
            ≤ (mF + MF) / 2 + (1 - lam₂ / 2) * ((MF - mF) / 2) := by
          rw [hkdef]; nlinarith
        linarith
      · -- Case 2: `M' ≤ k`
        have hle : M' ≤ (mF + MF) / 2 + (1 - lam₂ / 2) * ((MF - mF) / 2) := by
          have : k ≤ (mF + MF) / 2 + (1 - lam₂ / 2) * ((MF - mF) / 2) := by
            rw [hkdef]; nlinarith
          linarith
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hsublam hFles] with x hx
        linarith
  -- Step 1: the two symmetries, and the boundedness facts for `f`
  have hNBR := hNBof R hR
  have hNBlam := hNBof (lam₁ * R) hlamR
  obtain ⟨C, hC⟩ := hbdd
  have hbU : Filter.IsBoundedUnder (· ≤ ·)
      (ae (volume.restrict (Metric.ball x₀ R))) f := by
    refine ⟨C, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hC] with x hx
    exact (abs_le.1 hx).2
  have hbL : Filter.IsBoundedUnder (· ≥ ·)
      (ae (volume.restrict (Metric.ball x₀ R))) f := by
    refine ⟨-C, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hC] with x hx
    exact (abs_le.1 hx).1
  have hfle : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), f x ≤ M := by
    rw [hM]; exact ae_le_essSup hbU
  have hfge : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), m ≤ f x := by
    rw [hm]; exact ae_essInf_le hbL
  have hmM : m ≤ M := by
    obtain ⟨x, hx1, hx2⟩ := (hfle.and hfge).exists
    linarith
  -- the reflected pair `(-f, -g)`
  have hWneg : MemW1pOn n 2 (Metric.ball x₀ R) (fun x => -f x) (fun x => -g x) := by
    have hlin := (WeakGradientLinear n 2 hn1 (by norm_num) (Metric.ball x₀ R)
      f f g g (-1) 0 0 Metric.isOpen_ball).2.1 hW hW
    have e1 : (fun x => (-1:ℝ) * f x + (0:ℝ) * f x) = fun x => -f x := by
      funext x; ring
    have e2 : (fun x => (-1:ℝ) • g x + (0:ℝ) • g x) = fun x => -g x := by
      funext x; simp
    rw [e1, e2] at hlin
    exact hlin
  have hbddneg : ∃ C' : ℝ,
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), |(-f x)| ≤ C' := by
    refine ⟨C, ?_⟩
    filter_upwards [hC] with x hx
    rwa [abs_neg]
  have hbUneg : Filter.IsBoundedUnder (· ≤ ·)
      (ae (volume.restrict (Metric.ball x₀ R))) (fun x => -f x) := by
    refine ⟨-m, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hfge] with x hx
    linarith
  have hbLneg : Filter.IsBoundedUnder (· ≥ ·)
      (ae (volume.restrict (Metric.ball x₀ R))) (fun x => -f x) := by
    refine ⟨-M, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hfle] with x hx
    show -M ≤ -f x
    linarith
  have hnegM : essSup (fun x => -f x) (volume.restrict (Metric.ball x₀ R)) = -m := by
    refine le_antisymm ?_ ?_
    · refine essSup_le_of_ae_le (-m) ?_ hbLneg.isCobounded_flip
      filter_upwards [hfge] with x hx
      show -f x ≤ -m
      linarith
    · have h1 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
          -essSup (fun x => -f x) (volume.restrict (Metric.ball x₀ R)) ≤ f x := by
        filter_upwards [ae_le_essSup hbUneg] with x hx
        show -essSup (fun x => -f x) (volume.restrict (Metric.ball x₀ R)) ≤ f x
        have : -f x ≤ essSup (fun x => -f x) (volume.restrict (Metric.ball x₀ R)) := hx
        linarith
      have h2 := le_essInf_of_ae_le
        (-essSup (fun x => -f x) (volume.restrict (Metric.ball x₀ R))) h1
        hbU.isCobounded_flip
      rw [← hm] at h2
      linarith
  have hnegm : essInf (fun x => -f x) (volume.restrict (Metric.ball x₀ R)) = -M := by
    refine le_antisymm ?_ ?_
    · have h1 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
          f x ≤ -essInf (fun x => -f x) (volume.restrict (Metric.ball x₀ R)) := by
        filter_upwards [ae_essInf_le hbLneg] with x hx
        have : essInf (fun x => -f x) (volume.restrict (Metric.ball x₀ R)) ≤ -f x := hx
        linarith
      have h2 := essSup_le_of_ae_le
        (-essInf (fun x => -f x) (volume.restrict (Metric.ball x₀ R))) h1
        hbL.isCobounded_flip
      rw [← hM] at h2
      linarith
    · refine le_essInf_of_ae_le (-M) ?_ hbUneg.isCobounded_flip
      filter_upwards [hfle] with x hx
      show -M ≤ -f x
      linarith
  have hH2' : ∀ l ρ₀ ρ₁ : ℝ, l ∈ Set.Icc ((-M + -m) / 2) (-m) →
      ρ₀ ∈ Set.Icc (lam₁ * R) R → ρ₁ ∈ Set.Icc (lam₁ * R) R → ρ₀ < ρ₁ →
      DeGiorgiLevelBound n γ (fun x => -f x) (fun x => -g x) x₀ l ρ₀ ρ₁ := by
    intro l ρ₀ ρ₁ hl hr0 hr1 hlt'
    have h := hH2 (-l) ρ₀ ρ₁ ⟨by linarith [hl.2], by linarith [hl.1]⟩ hr0 hr1 hlt'
    rwa [neg_neg] at h
  -- Step 3: the dichotomy on the measure of the upper level set
  have hfam : AEMeasurable f (volume.restrict (Metric.ball x₀ R)) :=
    hW.2.1.1.aemeasurable
  obtain ⟨f', hf'meas, hf'ae⟩ : ∃ f' : EuclideanSpace ℝ (Fin n) → ℝ,
      Measurable f' ∧ f =ᵐ[volume.restrict (Metric.ball x₀ R)] f' :=
    ⟨_, hfam.measurable_mk, hfam.ae_eq_mk⟩
  have haeR : ∀ᵐ x ∂volume, x ∈ Metric.ball x₀ R → f x = f' x := by
    rw [← ae_restrict_iff' Metric.isOpen_ball.measurableSet]
    exact hf'ae
  have hSpnm : NullMeasurableSet
      (Metric.ball x₀ R ∩ {y | (m + M) / 2 < f y}) volume := by
    have hmeas : MeasurableSet (Metric.ball x₀ R ∩ {y | (m + M) / 2 < f' y}) :=
      Metric.isOpen_ball.measurableSet.inter
        (measurableSet_lt measurable_const hf'meas)
    refine (hmeas.nullMeasurableSet).congr ?_
    rw [Filter.eventuallyEq_set]
    filter_upwards [haeR] with x hx
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      show (m + M) / 2 < f x
      rw [hx h1]
      exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      show (m + M) / 2 < f' x
      rw [← hx h1]
      exact h2
  have hsplit := measure_inter_add_sdiff₀ (Metric.ball x₀ (sq * R)) hSpnm
  have hfinv : volume (Metric.ball x₀ (sq * R)) ≠ ⊤ := measure_ball_lt_top.ne
  have hfin1 : volume (Metric.ball x₀ (sq * R) ∩
      (Metric.ball x₀ R ∩ {y | (m + M) / 2 < f y})) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_ball_lt_top).ne
  have hfin2 : volume (Metric.ball x₀ (sq * R) \
      (Metric.ball x₀ R ∩ {y | (m + M) / 2 < f y})) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.sdiff_subset) measure_ball_lt_top).ne
  have hsplitR : (volume (Metric.ball x₀ (sq * R) ∩
        (Metric.ball x₀ R ∩ {y | (m + M) / 2 < f y}))).toReal
      + (volume (Metric.ball x₀ (sq * R) \
        (Metric.ball x₀ R ∩ {y | (m + M) / 2 < f y}))).toReal
      = (volume (Metric.ball x₀ (sq * R))).toReal := by
    rw [← ENNReal.toReal_add hfin1 hfin2, hsplit]
  have hinterEq : Metric.ball x₀ (sq * R) ∩
      (Metric.ball x₀ R ∩ {y | (m + M) / 2 < f y})
      = Metric.ball x₀ (sq * R) ∩ {y | (m + M) / 2 < f y} := by
    rw [← Set.inter_assoc, Set.inter_eq_self_of_subset_left hsubsq]
  -- the bounds for `f` on the inner ball
  have hbUlam : Filter.IsBoundedUnder (· ≤ ·)
      (ae (volume.restrict (Metric.ball x₀ (lam₁ * R)))) f := by
    refine ⟨M, ?_⟩
    rw [Filter.eventually_map]
    exact ae_restrict_of_ae_restrict_of_subset hsublamR hfle
  have hbLlam : Filter.IsBoundedUnder (· ≥ ·)
      (ae (volume.restrict (Metric.ball x₀ (lam₁ * R)))) f := by
    refine ⟨m, ?_⟩
    rw [Filter.eventually_map]
    exact ae_restrict_of_ae_restrict_of_subset hsublamR hfge
  rcases le_or_gt ((volume (Metric.ball x₀ (sq * R) ∩
      {y | (m + M) / 2 < f y})).toReal)
      ((1 / 2) * (volume (Metric.ball x₀ (sq * R))).toReal) with hcase | hcase
  · -- the upper level set is small: work with `f`
    have hres := core f g m M hW ⟨C, hC⟩ hM hm hH1 hcase
    have hup : essSup f (volume.restrict (Metric.ball x₀ (lam₁ * R)))
        ≤ (m + M) / 2 + (1 - lam₂ / 2) * ((M - m) / 2) :=
      essSup_le_of_ae_le _ hres hbLlam.isCobounded_flip
    have hlo : m ≤ essInf f (volume.restrict (Metric.ball x₀ (lam₁ * R))) :=
      le_essInf_of_ae_le m
        (ae_restrict_of_ae_restrict_of_subset hsublamR hfge) hbUlam.isCobounded_flip
    simp only [EssOscOn]
    rw [← hM, ← hm]
    linarith
  · -- the lower level set is small: work with `-f`
    have hBsmall : (volume (Metric.ball x₀ (sq * R) \
        (Metric.ball x₀ R ∩ {y | (m + M) / 2 < f y}))).toReal
        ≤ (1 / 2) * (volume (Metric.ball x₀ (sq * R))).toReal := by
      rw [hinterEq] at hsplitR
      linarith
    have hsubneg : Metric.ball x₀ (sq * R) ∩ {y | (-M + -m) / 2 < -f y}
        ⊆ Metric.ball x₀ (sq * R) \
          (Metric.ball x₀ R ∩ {y | (m + M) / 2 < f y}) := by
      rintro x ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rintro ⟨-, h3⟩
      have h2' : (-M + -m) / 2 < -f x := h2
      have h3' : (m + M) / 2 < f x := h3
      linarith
    have hcaseB : (volume (Metric.ball x₀ (sq * R) ∩
        {y | (-M + -m) / 2 < -f y})).toReal
        ≤ (1 / 2) * (volume (Metric.ball x₀ (sq * R))).toReal := by
      refine le_trans (ENNReal.toReal_mono hfin2 (measure_mono hsubneg)) hBsmall
    have hres := core (fun x => -f x) (fun x => -g x) (-M) (-m) hWneg hbddneg
      hnegM.symm hnegm.symm hH2' hcaseB
    have hlo : (m + M) / 2 - (1 - lam₂ / 2) * ((M - m) / 2)
        ≤ essInf f (volume.restrict (Metric.ball x₀ (lam₁ * R))) := by
      refine le_essInf_of_ae_le _ ?_ hbUlam.isCobounded_flip
      filter_upwards [hres] with x hx
      have hx' : -f x ≤ (-M + -m) / 2 + (1 - lam₂ / 2) * ((-m - -M) / 2) := hx
      show (m + M) / 2 - (1 - lam₂ / 2) * ((M - m) / 2) ≤ f x
      linarith
    have hup : essSup f (volume.restrict (Metric.ball x₀ (lam₁ * R))) ≤ M :=
      essSup_le_of_ae_le M
        (ae_restrict_of_ae_restrict_of_subset hsublamR hfle) hbLlam.isCobounded_flip
    simp only [EssOscOn]
    rw [← hM, ← hm]
    linarith
