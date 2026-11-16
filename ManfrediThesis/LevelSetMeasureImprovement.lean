import ManfrediThesis.Preamble
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.DeGiorgiLevelBound
import ManfrediThesis.MemW1pOn
import ManfrediThesis.DeGiorgiLevelSetMeasure
open MeasureTheory

/-- Lemma 2.4: a one-sided improvement of the measure of a level set. -/
theorem LevelSetMeasureImprovement :
    ∀ (n : ℕ) (γ lam₁ c₀ θ₁ : ℝ), 2 ≤ n → 0 < γ →
      lam₁ ∈ Set.Ioo (0 : ℝ) 1 → 0 ≤ c₀ → c₀ < 1 → θ₁ ∈ Set.Ioo (0 : ℝ) 1 →
      CitedSobolevPoincareBall n →
      ∃ lam₂ : ℝ, lam₂ ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R k M : ℝ)
          (f : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 < R → MemW1pOn n 2 (Metric.ball x₀ R) f g →
          (∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), f x ≤ C) →
          M = essSup f (volume.restrict (Metric.ball x₀ R)) → k < M →
          (∀ l : ℝ, l ∈ Set.Icc k M →
            DeGiorgiLevelBound n γ f g x₀ l (lam₁ * R) R) →
          (volume (Metric.ball x₀ (lam₁ * R) ∩ {y | k < f y})).toReal
            ≤ c₀ * (volume (Metric.ball x₀ (lam₁ * R))).toReal →
          (volume (Metric.ball x₀ (lam₁ * R) ∩
              {y | lam₂ * k + (1 - lam₂) * M < f y})).toReal
            ≤ θ₁ * (volume (Metric.ball x₀ (lam₁ * R))).toReal := by
  intro n γ lam₁ c₀ θ₁ hn hγ hlam₁ hc₀ hc₀1 hθ₁ hSPB
  -- dimension facts
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn22 : (0 : ℝ) < 2 * (n : ℝ) - 2 := by linarith
  have hntriv : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, hnpos⟩ (1 : ℝ), ?_⟩⟩
    intro hc
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hnpos⟩) hc
    simp at h
  -- the volume of the unit ball
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℝ,
      ω = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := ⟨_, rfl⟩
  have hω : 0 < ω := by
    rw [hωdef]
    refine ENNReal.toReal_pos ?_ measure_ball_lt_top.ne
    exact (Metric.isOpen_ball.measure_pos volume
      ⟨0, Metric.mem_ball_self one_pos⟩).ne'
  -- the constant of the De Giorgi level-set measure estimate
  obtain ⟨β, hβ0, hDG⟩ := DeGiorgiLevelSetMeasure n hn hSPB
  -- the two exponents
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = 1 - 1 / (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = (n : ℝ) / (2 * (n : ℝ) - 2) := ⟨_, rfl⟩
  have hp0 : 0 < p := by
    rw [hpdef]
    have : 1 / (n : ℝ) < 1 := by
      rw [div_lt_one hnR0]; linarith
    linarith
  have he0 : 0 < e := by rw [hedef]; exact div_pos hnR0 hn22
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR0
  have h22 : 2 * (n : ℝ) - 2 ≠ 0 := ne_of_gt hn22
  have hnm1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hnm1' : (-1 : ℝ) + (n : ℝ) ≠ 0 := by intro h; apply hnm1; linarith
  have hpe : 2 * p * e = 1 := by
    rw [hpdef, hedef]
    field_simp
  have h2pe : (2 * (n : ℝ) - 2) * e = (n : ℝ) := by
    rw [hedef]
    field_simp
  -- the constants `C₃`, `C₄`, `C₅` of the .tex, built from `n γ lam₁ c₀ θ₁` alone
  obtain ⟨C₃, hC₃def⟩ : ∃ C : ℝ, C = β / ((1 - c₀) * ω) := ⟨_, rfl⟩
  have h1c₀ : (0 : ℝ) < 1 - c₀ := by linarith
  have h1lam : (0 : ℝ) < 1 - lam₁ := by linarith [hlam₁.2]
  have hC₃0 : 0 < C₃ := by rw [hC₃def]; exact div_pos hβ0 (mul_pos h1c₀ hω)
  obtain ⟨C₄, hC₄def⟩ : ∃ C : ℝ,
      C = 2 * C₃ * Real.sqrt γ * Real.sqrt ω / (1 - lam₁) := ⟨_, rfl⟩
  have hC₄0 : 0 < C₄ := by
    rw [hC₄def]
    exact div_pos (mul_pos (mul_pos (by linarith) (Real.sqrt_pos.2 hγ))
      (Real.sqrt_pos.2 hω)) h1lam
  obtain ⟨C₅, hC₅def⟩ : ∃ C : ℝ, C = (C₄ ^ 2 * ω) ^ e / (ω * lam₁ ^ n) := ⟨_, rfl⟩
  have hC₅0 : 0 < C₅ := by
    rw [hC₅def]
    exact div_pos (Real.rpow_pos_of_pos (mul_pos (pow_pos hC₄0 2) hω) _)
      (mul_pos hω (pow_pos hlam₁.1 n))
  -- (2.10a): the choice of the integer `s`
  obtain ⟨s, hs2, hs⟩ : ∃ s : ℕ, 2 ≤ s ∧ C₅ / (((s : ℝ) - 1) ^ e) ≤ θ₁ := by
    have hx0 : 0 < (C₅ / θ₁) ^ e⁻¹ := Real.rpow_pos_of_pos (div_pos hC₅0 hθ₁.1) _
    obtain ⟨m, hm⟩ := exists_nat_ge (1 + (C₅ / θ₁) ^ e⁻¹)
    refine ⟨max m 2, le_max_right _ _, ?_⟩
    have hs1 : 1 + (C₅ / θ₁) ^ e⁻¹ ≤ ((max m 2 : ℕ) : ℝ) :=
      hm.trans (Nat.cast_le.2 (le_max_left _ _))
    have hb : (C₅ / θ₁) ^ e⁻¹ ≤ ((max m 2 : ℕ) : ℝ) - 1 := by linarith
    have hD : C₅ / θ₁ ≤ (((max m 2 : ℕ) : ℝ) - 1) ^ e := by
      have h1 := Real.rpow_le_rpow hx0.le hb he0.le
      rwa [Real.rpow_inv_rpow (div_pos hC₅0 hθ₁.1).le he0.ne'] at h1
    have hDpos : (0 : ℝ) < (((max m 2 : ℕ) : ℝ) - 1) ^ e :=
      lt_of_lt_of_le (div_pos hC₅0 hθ₁.1) hD
    rw [div_le_iff₀ hDpos]
    rw [div_le_iff₀ hθ₁.1] at hD
    linarith
  have hs1R : (1 : ℝ) ≤ (s : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs2
    linarith
  refine ⟨1 / 2 ^ s, ⟨by positivity, ?_⟩, ?_⟩
  · rw [div_lt_one (by positivity)]
    calc (1 : ℝ) < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ s := by
          refine pow_le_pow_right₀ (by norm_num) ?_
          omega
  intro x₀ R k M f g hR hW hbdd hM hkM hDGL hc₀bound
  -- radii
  have hlamR : 0 < lam₁ * R := mul_pos hlam₁.1 hR
  have hlamRR : lam₁ * R ≤ R := by nlinarith [hlam₁.2]
  have hlamRlt : lam₁ * R < R := by nlinarith [hlam₁.2]
  -- ball volumes
  have hballvol : ∀ r : ℝ, 0 ≤ r →
      (volume (Metric.ball x₀ r)).toReal = ω * r ^ n := by
    intro r hr
    rw [Measure.addHaar_ball volume x₀ hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity),
      show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n by simp, ← hωdef]
    ring
  have hmB : (volume (Metric.ball x₀ (lam₁ * R))).toReal = ω * (lam₁ * R) ^ n :=
    hballvol _ hlamR.le
  have hmBpos : 0 < (volume (Metric.ball x₀ (lam₁ * R))).toReal := by
    rw [hmB]; exact mul_pos hω (pow_pos hlamR n)
  have hBtop : volume (Metric.ball x₀ (lam₁ * R)) ≠ ⊤ := measure_ball_lt_top.ne
  -- the levels `k_t`
  obtain ⟨kk, hkkdef⟩ : ∃ kk : ℕ → ℝ,
      kk = fun t => (1 / 2 ^ t) * k + (1 - 1 / 2 ^ t) * M := ⟨_, rfl⟩
  have hMk : 0 < M - k := by linarith
  have hkkM : ∀ t : ℕ, M - kk t = (M - k) / (2 : ℝ) ^ t := by
    intro t
    simp only [hkkdef]
    field_simp
    ring
  have hkkge : ∀ t : ℕ, k ≤ kk t := by
    intro t
    have h2 : (1 : ℝ) / 2 ^ t ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
    have h3 : (0 : ℝ) ≤ (1 - 1 / (2 : ℝ) ^ t) * (M - k) :=
      mul_nonneg (by linarith) hMk.le
    simp only [hkkdef]
    linarith
  have hkklt : ∀ t : ℕ, kk t < M := by
    intro t
    have h1 : (0 : ℝ) < 1 / (2 : ℝ) ^ t := by positivity
    have h3 : (0 : ℝ) < 1 / (2 : ℝ) ^ t * (M - k) := mul_pos h1 hMk
    simp only [hkkdef]
    linarith
  have hkkmono : ∀ t u : ℕ, t ≤ u → kk t ≤ kk u := by
    intro t u htu
    have h1 : (1 : ℝ) / 2 ^ u ≤ 1 / 2 ^ t :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) htu)
    have h3 : (0 : ℝ) ≤ (1 / (2 : ℝ) ^ t - 1 / (2 : ℝ) ^ u) * (M - k) :=
      mul_nonneg (by linarith) hMk.le
    simp only [hkkdef]
    linarith
  have hkkIcc : ∀ t : ℕ, kk t ∈ Set.Icc k M := fun t => ⟨hkkge t, (hkklt t).le⟩
  -- the level sets and the slabs
  obtain ⟨AA, hAAdef⟩ : ∃ AA : ℕ → Set (EuclideanSpace ℝ (Fin n)),
      AA = fun t => Metric.ball x₀ (lam₁ * R) ∩ {y | kk t < f y} := ⟨_, rfl⟩
  obtain ⟨DD, hDDdef⟩ : ∃ DD : ℕ → Set (EuclideanSpace ℝ (Fin n)),
      DD = fun t => AA t \ {y | kk (t + 1) < f y} := ⟨_, rfl⟩
  have hAAsub : ∀ t : ℕ, AA t ⊆ Metric.ball x₀ (lam₁ * R) := by
    intro t; rw [hAAdef]; exact Set.inter_subset_left
  have hDDsub : ∀ t : ℕ, DD t ⊆ AA t := by
    intro t; rw [hDDdef]; exact Set.sdiff_subset
  have hAAmono : ∀ t u : ℕ, t ≤ u → AA u ⊆ AA t := by
    intro t u htu y hy
    simp only [hAAdef, Set.mem_inter_iff, Set.mem_ofPred_eq] at hy ⊢
    exact ⟨hy.1, lt_of_le_of_lt (hkkmono t u htu) hy.2⟩
  have hAAtop : ∀ t : ℕ, volume (AA t) ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top hBtop (measure_mono (hAAsub t))
  -- `W^{1,2}(B_R)` restricts to `W^{1,1}(B_{lam₁ R})`
  have hW1 : MemW1pOn n 1 (Metric.ball x₀ (lam₁ * R)) f g := by
    obtain ⟨hwg, hf2, hg2⟩ := hW
    have hres : HasWeakGradientOn n (Metric.ball x₀ (lam₁ * R)) f g := by
      intro φ hφ hcs hts i
      have hsub : Metric.ball x₀ (lam₁ * R) ⊆ Metric.ball x₀ R :=
        Metric.ball_subset_ball hlamRR
      have h1 : ∫ x in Metric.ball x₀ (lam₁ * R),
          f x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))
          = ∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
        intro x hx
        rw [fderiv_of_notMem_tsupport ℝ (fun hc => hx (hts hc))]
        simp
      have h2 : ∫ x in Metric.ball x₀ R,
          f x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))
          = ∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
        intro x hx
        rw [fderiv_of_notMem_tsupport ℝ (fun hc => hx (hsub (hts hc)))]
        simp
      have h3 : ∫ x in Metric.ball x₀ (lam₁ * R), g x i * φ x = ∫ x, g x i * φ x := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun hc => hx (hts hc))]
        simp
      have h4 : ∫ x in Metric.ball x₀ R, g x i * φ x = ∫ x, g x i * φ x := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun hc => hx (hsub (hts hc)))]
        simp
      have h5 := hwg φ hφ hcs (hts.trans hsub) i
      rw [h1, h3]
      rw [h2, h4] at h5
      exact h5
    have hle : volume.restrict (Metric.ball x₀ (lam₁ * R))
        ≤ volume.restrict (Metric.ball x₀ R) :=
      Measure.restrict_mono (Metric.ball_subset_ball hlamRR) le_rfl
    have hfin : IsFiniteMeasure (volume.restrict (Metric.ball x₀ (lam₁ * R))) := by
      constructor
      rw [Measure.restrict_apply_univ]
      exact measure_ball_lt_top
    have h12 : (ENNReal.ofReal 1 : ENNReal) ≤ ENNReal.ofReal 2 :=
      ENNReal.ofReal_le_ofReal (by norm_num)
    exact ⟨hres, (hf2.mono_measure hle).mono_exponent h12,
      (hg2.mono_measure hle).mono_exponent h12⟩
  -- pm-0006: the essential-boundedness hypothesis makes `M` an a.e. bound for `f`
  have hfM : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), f x ≤ M := by
    obtain ⟨C, hC⟩ := hbdd
    rw [hM]
    exact ae_le_essSup ⟨C, hC⟩
  -- a measurable representative of `f` on `B_R`, and the null-measurability bridge
  obtain ⟨f', hf'meas, hf'ae⟩ : ∃ f' : EuclideanSpace ℝ (Fin n) → ℝ, Measurable f' ∧
      f =ᵐ[volume.restrict (Metric.ball x₀ R)] f' :=
    ⟨hW.2.1.1.mk f, hW.2.1.1.stronglyMeasurable_mk.measurable, hW.2.1.1.ae_eq_mk⟩
  have hnull : volume ({x | f x = f' x}ᶜ ∩ Metric.ball x₀ R) = 0 := by
    have h := hf'ae
    rw [Filter.EventuallyEq, Filter.eventually_iff, mem_ae_iff,
      Measure.restrict_apply' measurableSet_ball] at h
    simpa using h
  have hkey : ∀ T U : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      (∀ y, ¬ (y ∈ T ↔ y ∈ U) → y ∈ {x | f x = f' x}ᶜ ∩ Metric.ball x₀ R) →
      NullMeasurableSet U volume := by
    intro T U hT hsub
    refine (hT.nullMeasurableSet).congr ?_
    rw [Filter.eventuallyEq_set]
    exact (MeasureTheory.ae_iff).2 (measure_mono_null hsub hnull)
  have hnmDD : ∀ t : ℕ, NullMeasurableSet (DD t) volume := by
    intro t
    have hrw : DD t = (Metric.ball x₀ (lam₁ * R) ∩ {y | kk t < f y})
        \ {y | kk (t + 1) < f y} := by simp only [hDDdef, hAAdef]
    rw [hrw]
    refine hkey ((Metric.ball x₀ (lam₁ * R) ∩ {y | kk t < f' y})
        \ {y | kk (t + 1) < f' y}) _
      ((measurableSet_ball.inter (measurableSet_lt measurable_const hf'meas)).diff
        (measurableSet_lt measurable_const hf'meas)) ?_
    intro y hy
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_compl_iff] at hy ⊢
    refine ⟨?_, ?_⟩
    · intro hfe
      rw [hfe] at hy
      tauto
    · by_contra hyB
      have hyB' : y ∉ Metric.ball x₀ (lam₁ * R) := fun hc =>
        hyB (Metric.ball_subset_ball hlamRR hc)
      refine hy ?_
      constructor
      · intro hT; exact absurd hT.1.1 hyB'
      · intro hD; exact absurd hD.1.1 hyB'
  -- the slabs are pairwise disjoint
  have hdisj : ∀ t u : ℕ, t < u → Disjoint (DD t) (DD u) := by
    intro t u htu
    rw [Set.disjoint_left]
    intro y hyt hyu
    simp only [hDDdef, hAAdef, Set.mem_sdiff, Set.mem_inter_iff,
      Set.mem_ofPred_eq, not_lt] at hyt hyu
    have h3 : kk (t + 1) ≤ kk u := hkkmono _ _ htu
    linarith [hyt.2, hyu.1.2]
  -- Cauchy-Schwarz for the real `rpow` form of the `L^2` norms
  have hCSgen : ∀ (S : Set (EuclideanSpace ℝ (Fin n)))
      (F G : EuclideanSpace ℝ (Fin n) → ℝ),
      MemLp F (ENNReal.ofReal 2) (volume.restrict S) →
      MemLp G (ENNReal.ofReal 2) (volume.restrict S) →
      (∫ y in S, |F y * G y|)
        ≤ Real.sqrt (∫ y in S, |F y| ^ (2:ℝ))
          * Real.sqrt (∫ y in S, |G y| ^ (2:ℝ)) := by
    intro S F G hF hG
    have hcq : Continuous (fun t : ℝ => |t| ^ (2:ℝ)) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (Real.continuousAt_rpow_const _ _
        (Or.inr (by norm_num : (0:ℝ) ≤ 2))).comp continuous_abs.continuousAt
    have h2z : (ENNReal.ofReal 2) ≠ 0 := by simp
    have h2t : (ENNReal.ofReal 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h2r : (ENNReal.ofReal 2).toReal = 2 := by simp
    -- the dictionary between the real `rpow` integral and the `lintegral`
    have hdict : ∀ u : EuclideanSpace ℝ (Fin n) → ℝ,
        AEStronglyMeasurable u (volume.restrict S) →
        (∫ y in S, |u y| ^ (2:ℝ))
          = (∫⁻ y in S, ‖u y‖ₑ ^ (2:ℝ)).toReal := by
      intro u hu
      rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (abs_nonneg _) _)
        (hcq.comp_aestronglyMeasurable hu)]
      refine congrArg ENNReal.toReal (lintegral_congr fun y => ?_)
      rw [← ofReal_norm, Real.norm_eq_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    -- finiteness of the two `lintegral`s
    have hfin : ∀ u : EuclideanSpace ℝ (Fin n) → ℝ,
        MemLp u (ENNReal.ofReal 2) (volume.restrict S) →
        (∫⁻ y in S, ‖u y‖ₑ ^ (2:ℝ)) ≠ ⊤ := by
      intro u hu
      have h1 := hu.eLpNorm_lt_top
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2z h2t, h2r] at h1
      intro hc
      rw [hc, ENNReal.top_rpow_of_pos (by norm_num)] at h1
      exact absurd h1 (by simp)
    have hFfin := hfin F hF
    have hGfin := hfin G hG
    have hconj : (2:ℝ).HolderConjugate (2:ℝ) :=
      Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
    have hHold := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict S) hconj
      (hF.1.enorm : AEMeasurable _ _) (hG.1.enorm : AEMeasurable _ _)
    simp only [Pi.mul_apply] at hHold
    have hprodtop : ((∫⁻ y in S, ‖F y‖ₑ ^ (2:ℝ)) ^ (1/(2:ℝ))
        * (∫⁻ y in S, ‖G y‖ₑ ^ (2:ℝ)) ^ (1/(2:ℝ))) ≠ ⊤ := by
      refine ENNReal.mul_ne_top ?_ ?_
      · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hFfin
      · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hGfin
    calc (∫ y in S, |F y * G y|)
        = (∫⁻ y in S, ‖F y‖ₑ * ‖G y‖ₑ).toReal := by
          have hm : AEStronglyMeasurable (fun y => F y * G y) (volume.restrict S) :=
            hF.1.mul hG.1
          have h1 : (∫ y in S, ‖F y * G y‖)
              = (∫⁻ y in S, ‖F y * G y‖ₑ).toReal :=
            integral_norm_eq_lintegral_enorm hm
          simp only [Real.norm_eq_abs] at h1
          rw [h1]
          refine congrArg ENNReal.toReal (lintegral_congr fun y => ?_)
          rw [enorm_mul]
      _ ≤ ((∫⁻ y in S, ‖F y‖ₑ ^ (2:ℝ)) ^ (1/(2:ℝ))
            * (∫⁻ y in S, ‖G y‖ₑ ^ (2:ℝ)) ^ (1/(2:ℝ))).toReal :=
          ENNReal.toReal_mono hprodtop hHold
      _ = Real.sqrt (∫ y in S, |F y| ^ (2:ℝ))
            * Real.sqrt (∫ y in S, |G y| ^ (2:ℝ)) := by
          rw [ENNReal.toReal_mul, hdict F hF.1, hdict G hG.1,
            ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
            Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hAAnn : ∀ t : ℕ, (0 : ℝ) ≤ (volume (AA t)).toReal := fun t => ENNReal.toReal_nonneg
  have hRne : R ≠ 0 := ne_of_gt hR
  have h1lamne : (1 : ℝ) - lam₁ ≠ 0 := ne_of_gt h1lam
  have hC₄sq : C₄ ^ 2 = 4 * C₃ ^ 2 * γ * ω / (1 - lam₁) ^ 2 := by
    rw [hC₄def, div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hγ.le,
      Real.sq_sqrt hω.le]
    ring
  have hRn : (R ^ ((n : ℝ) / 2 - 1)) ^ 2 * R ^ 2 = R ^ n := by
    rw [← Real.rpow_natCast (R ^ ((n : ℝ) / 2 - 1)) 2, ← Real.rpow_mul hR.le,
      ← Real.rpow_natCast R 2, ← Real.rpow_add hR, ← Real.rpow_natCast R n]
    congr 1
    push_cast
    ring
  -- (2.9), in squared form
  have h29 : ∀ t : ℕ, 1 ≤ t →
      ((volume (AA (t + 1))).toReal ^ p) ^ 2
        ≤ C₄ ^ 2 * (R ^ ((n : ℝ) / 2 - 1)) ^ 2 * (volume (DD t)).toReal := by
    intro t ht
    -- (2.7a): this is where `c₀ < 1` is consumed
    have hBcap : volume (Metric.ball x₀ (lam₁ * R))
        ≤ volume (Metric.ball x₀ (lam₁ * R) ∩ {y | kk t < f y})
          + volume (Metric.ball x₀ (lam₁ * R) \ {y | kk t < f y}) := by
      calc volume (Metric.ball x₀ (lam₁ * R))
          = volume ((Metric.ball x₀ (lam₁ * R) ∩ {y | kk t < f y})
              ∪ (Metric.ball x₀ (lam₁ * R) \ {y | kk t < f y})) := by
            rw [Set.inter_union_sdiff]
        _ ≤ _ := measure_union_le _ _
    have hcapt : volume (Metric.ball x₀ (lam₁ * R) ∩ {y | kk t < f y}) ≠ ⊤ :=
      ne_top_of_le_ne_top hBtop (measure_mono Set.inter_subset_left)
    have hdift : volume (Metric.ball x₀ (lam₁ * R) \ {y | kk t < f y}) ≠ ⊤ :=
      ne_top_of_le_ne_top hBtop (measure_mono Set.sdiff_subset)
    have hBt : (volume (Metric.ball x₀ (lam₁ * R))).toReal
        ≤ (volume (Metric.ball x₀ (lam₁ * R) ∩ {y | kk t < f y})).toReal
          + (volume (Metric.ball x₀ (lam₁ * R) \ {y | kk t < f y})).toReal := by
      rw [← ENNReal.toReal_add hcapt hdift]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hcapt, hdift⟩) hBcap
    have hc₀t : (volume (Metric.ball x₀ (lam₁ * R) ∩ {y | kk t < f y})).toReal
        ≤ c₀ * (volume (Metric.ball x₀ (lam₁ * R))).toReal := by
      refine le_trans (ENNReal.toReal_mono ?_ (measure_mono ?_)) hc₀bound
      · exact ne_top_of_le_ne_top hBtop (measure_mono Set.inter_subset_left)
      · intro y hy
        exact ⟨hy.1, lt_of_le_of_lt (hkkge t) hy.2⟩
    have hZpos : (1 - c₀) * (volume (Metric.ball x₀ (lam₁ * R))).toReal
        ≤ (volume (Metric.ball x₀ (lam₁ * R) \ {y | kk t < f y})).toReal := by
      linarith
    have hZ0 : 0 < (volume (Metric.ball x₀ (lam₁ * R) \ {y | kk t < f y})).toReal := by
      linarith [mul_pos h1c₀ hmBpos]
    -- Step 2: one application of `DeGiorgiLevelSetMeasure` on `B_{lam₁ R}`
    have hstep2 := hDG x₀ (lam₁ * R) f g (kk t) (kk (t + 1)) hlamR hW1
      (hkkmono t (t + 1) (Nat.le_succ t)) hZ0
    rw [Real.rpow_natCast (lam₁ * R) n,
      show Metric.ball x₀ (lam₁ * R) ∩ {y | kk (t + 1) < f y} = AA (t + 1) from by
        simp only [hAAdef],
      show (Metric.ball x₀ (lam₁ * R) ∩ {y | kk t < f y}) \ {y | kk (t + 1) < f y}
          = DD t from by simp only [hDDdef, hAAdef],
      ← hpdef] at hstep2
    -- the De Giorgi constant absorbs the level-set measure lower bound
    have hconst : β * (lam₁ * R) ^ n
        / (volume (Metric.ball x₀ (lam₁ * R) \ {y | kk t < f y})).toReal ≤ C₃ := by
      rw [div_le_iff₀ hZ0]
      have h1 : C₃ * ((1 - c₀) * (volume (Metric.ball x₀ (lam₁ * R))).toReal)
          = β * (lam₁ * R) ^ n := by
        rw [hC₃def, hmB]
        field_simp
      have h2 : C₃ * ((1 - c₀) * (volume (Metric.ball x₀ (lam₁ * R))).toReal)
          ≤ C₃ * (volume (Metric.ball x₀ (lam₁ * R) \ {y | kk t < f y})).toReal :=
        mul_le_mul_of_nonneg_left hZpos hC₃0.le
      linarith
    have hI0 : 0 ≤ ∫ x in DD t, ‖g x‖ :=
      integral_nonneg (fun x => norm_nonneg (g x))
    have hJ0 : 0 ≤ ∫ x in DD t, ‖g x‖ ^ 2 :=
      integral_nonneg (fun x => sq_nonneg ‖g x‖)
    -- Cauchy-Schwarz on the slab
    have hCS : (∫ x in DD t, ‖g x‖)
        ≤ Real.sqrt (volume (DD t)).toReal
          * Real.sqrt (∫ x in DD t, ‖g x‖ ^ 2) := by
      have hDsub : DD t ⊆ Metric.ball x₀ R :=
        ((hDDsub t).trans (hAAsub t)).trans (Metric.ball_subset_ball hlamRR)
      have hfinD : IsFiniteMeasure (volume.restrict (DD t)) := by
        constructor
        rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_lt (measure_mono hDsub) measure_ball_lt_top
      have hF : MemLp (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))
          (ENNReal.ofReal 2) (volume.restrict (DD t)) := memLp_const 1
      have hG : MemLp (fun x => ‖g x‖) (ENNReal.ofReal 2) (volume.restrict (DD t)) :=
        (hW.2.2.mono_measure (Measure.restrict_mono hDsub le_rfl)).norm
      have h0 := hCSgen (DD t) (fun _ => 1) (fun x => ‖g x‖) hF hG
      have e1 : (∫ y in DD t, |(1 : ℝ) * ‖g y‖|) = ∫ y in DD t, ‖g y‖ := by
        simp only [one_mul, abs_norm]
      have e2 : (∫ _y in DD t, |(1 : ℝ)| ^ (2 : ℝ)) = (volume (DD t)).toReal := by
        simp only [abs_one, Real.one_rpow, setIntegral_const]
        simp [MeasureTheory.measureReal_def]
      have e3 : (∫ y in DD t, |‖g y‖| ^ (2 : ℝ)) = ∫ y in DD t, ‖g y‖ ^ 2 := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show |‖g y‖| ^ (2 : ℝ) = ‖g y‖ ^ 2
        rw [abs_norm, ← Real.rpow_natCast ‖g y‖ 2]
        norm_num
      rw [e1, e2, e3] at h0
      exact h0
    -- Step 3: the gradient integral, via the `DeGiorgiLevelBound` hypothesis at `k_t`
    have hstep3 : (∫ x in DD t, ‖g x‖ ^ 2)
        ≤ γ / ((1 - lam₁) * R) ^ 2 * ((M - k) / 2 ^ t) ^ 2 * (ω * R ^ n) := by
      obtain ⟨-, hb⟩ := hDGL (kk t) (hkkIcc t)
      have hintR' : Integrable (fun x => ‖g x‖ ^ (ENNReal.ofReal 2).toReal)
          (volume.restrict (Metric.ball x₀ R)) :=
        hW.2.2.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
      have hintR : IntegrableOn (fun x => ‖g x‖ ^ 2) (Metric.ball x₀ R) volume := by
        rw [show (ENNReal.ofReal 2).toReal = 2 from by simp] at hintR'
        refine hintR'.congr (Filter.Eventually.of_forall fun x => ?_)
        show ‖g x‖ ^ (2 : ℝ) = ‖g x‖ ^ 2
        rw [← Real.rpow_natCast ‖g x‖ 2]
        norm_num
      have hint : IntegrableOn (fun x => ‖g x‖ ^ 2)
          (Metric.ball x₀ (lam₁ * R) ∩ {y | kk t < f y}) volume :=
        hintR.mono_set (Set.inter_subset_left.trans (Metric.ball_subset_ball hlamRR))
      have hmset : (∫ x in DD t, ‖g x‖ ^ 2)
          ≤ ∫ x in Metric.ball x₀ (lam₁ * R) ∩ {y | kk t < f y}, ‖g x‖ ^ 2 := by
        refine setIntegral_mono_set hint
          (Filter.Eventually.of_forall fun x => sq_nonneg ‖g x‖) ?_
        refine LE.le.eventuallyLE ?_
        intro y hy
        simpa only [hAAdef] using hDDsub t hy
      refine hmset.trans (hb.trans ?_)
      have hes : essSup (fun x => max (f x - kk t) 0 ^ 2)
          (volume.restrict (Metric.ball x₀ R)) ≤ ((M - k) / 2 ^ t) ^ 2 := by
        have hvolR : volume (Metric.ball x₀ R) ≠ 0 :=
          (Metric.isOpen_ball.measure_pos volume ⟨x₀, Metric.mem_ball_self hR⟩).ne'
        have hneb : Filter.NeBot (ae (volume.restrict (Metric.ball x₀ R))) := by
          refine ae_neBot.2 ?_
          simp only [ne_eq, Measure.restrict_eq_zero]
          exact hvolR
        have hcob : Filter.IsCoboundedUnder (· ≤ ·)
            (ae (volume.restrict (Metric.ball x₀ R)))
            (fun x => max (f x - kk t) 0 ^ 2) := by
          refine ⟨0, fun a ha => ?_⟩
          obtain ⟨x, hx⟩ := (Filter.eventually_map.1 ha).exists
          exact le_trans (by positivity) hx
        refine essSup_le_of_ae_le _ ?_ hcob
        filter_upwards [hfM] with x hx
        have h1 : max (f x - kk t) 0 ≤ (M - k) / 2 ^ t := by
          rcases le_or_gt (f x - kk t) 0 with h | h
          · rw [max_eq_right h]
            exact div_nonneg hMk.le (by positivity)
          · rw [max_eq_left h.le]
            have h2 := hkkM t
            linarith
        exact pow_le_pow_left₀ (le_max_right _ _) h1 2
      have hvol : (volume (Metric.ball x₀ R ∩ {y | kk t < f y})).toReal ≤ ω * R ^ n := by
        rw [← hballvol R hR.le]
        exact ENNReal.toReal_mono measure_ball_lt_top.ne
          (measure_mono Set.inter_subset_left)
      have hA0 : (0 : ℝ) ≤ γ / ((1 - lam₁) * R) ^ 2 :=
        div_nonneg hγ.le (sq_nonneg _)
      rw [show γ / (R - lam₁ * R) ^ 2 = γ / ((1 - lam₁) * R) ^ 2 from by
        congr 2; ring]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hes hA0) hvol
        ENNReal.toReal_nonneg (mul_nonneg hA0 (sq_nonneg _))
    -- combine, squared
    have hL0 : 0 ≤ (kk (t + 1) - kk t) * (volume (AA (t + 1))).toReal ^ p := by
      refine mul_nonneg ?_ (Real.rpow_nonneg (hAAnn _) _)
      linarith [hkkmono t (t + 1) (Nat.le_succ t)]
    have hU : (kk (t + 1) - kk t) * (volume (AA (t + 1))).toReal ^ p
        ≤ C₃ * (Real.sqrt (volume (DD t)).toReal
          * Real.sqrt (∫ x in DD t, ‖g x‖ ^ 2)) := by
      refine hstep2.trans ?_
      exact (mul_le_mul_of_nonneg_right hconst hI0).trans
        (mul_le_mul_of_nonneg_left hCS hC₃0.le)
    have hsqd := pow_le_pow_left₀ hL0 hU 2
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg,
      Real.sq_sqrt hJ0] at hsqd
    have hchain : (kk (t + 1) - kk t) ^ 2 * ((volume (AA (t + 1))).toReal ^ p) ^ 2
        ≤ C₃ ^ 2 * ((volume (DD t)).toReal
          * (γ / ((1 - lam₁) * R) ^ 2 * ((M - k) / 2 ^ t) ^ 2 * (ω * R ^ n))) := by
      refine hsqd.trans ?_
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hstep3 ENNReal.toReal_nonneg) (sq_nonneg C₃)
    have hcc : kk (t + 1) - kk t = (M - k) / 2 ^ (t + 1) := by
      simp only [hkkdef]
      rw [pow_succ]
      field_simp
      ring
    have hident : C₃ ^ 2 * ((volume (DD t)).toReal
          * (γ / ((1 - lam₁) * R) ^ 2 * ((M - k) / 2 ^ t) ^ 2 * (ω * R ^ n)))
        = ((M - k) / 2 ^ (t + 1)) ^ 2
          * (C₄ ^ 2 * (R ^ ((n : ℝ) / 2 - 1)) ^ 2 * (volume (DD t)).toReal) := by
      rw [hC₄sq, ← hRn, pow_succ]
      field_simp
      ring
    rw [hcc, hident] at hchain
    refine le_of_mul_le_mul_left hchain ?_
    positivity
  -- (2.6b): the slabs are disjoint and sit inside the ball
  have h26b : ∑ t ∈ Finset.Ico 1 s, (volume (DD t)).toReal ≤ ω * R ^ n := by
    have hstep : ∑ t ∈ Finset.Ico 1 s, (volume (DD t)).toReal
        ≤ (volume (Metric.ball x₀ (lam₁ * R))).toReal := by
      have hsum : ∑ t ∈ Finset.Ico 1 s, volume (DD t)
          = volume (⋃ t ∈ Finset.Ico 1 s, DD t) := by
        refine (measure_biUnion_finset₀ ?_ (fun t _ => hnmDD t)).symm
        intro t _ u _ htu
        rcases lt_or_gt_of_ne htu with h | h
        · exact (hdisj t u h).aedisjoint
        · exact AEDisjoint.symm (hdisj u t h).aedisjoint
      have hle : volume (⋃ t ∈ Finset.Ico 1 s, DD t)
          ≤ volume (Metric.ball x₀ (lam₁ * R)) :=
        measure_mono (Set.iUnion₂_subset fun t _ => (hDDsub t).trans (hAAsub t))
      have hfin : ∀ t ∈ Finset.Ico 1 s, volume (DD t) ≠ ⊤ := fun t _ =>
        ne_top_of_le_ne_top hBtop (measure_mono ((hDDsub t).trans (hAAsub t)))
      rw [← ENNReal.toReal_sum hfin]
      exact ENNReal.toReal_mono hBtop (hsum.trans_le hle)
    refine hstep.trans ?_
    rw [hmB]
    refine mul_le_mul_of_nonneg_left ?_ hω.le
    rw [mul_pow]
    have h1 : lam₁ ^ n ≤ 1 := pow_le_one₀ hlam₁.1.le hlam₁.2.le
    calc lam₁ ^ n * R ^ n ≤ 1 * R ^ n :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg hR.le n)
      _ = R ^ n := one_mul _
  -- Step 4: the telescoping sum
  have hmono : ∀ t : ℕ, t + 1 ≤ s →
      (volume (AA s)).toReal ^ p ≤ (volume (AA (t + 1))).toReal ^ p := by
    intro t ht
    refine Real.rpow_le_rpow ENNReal.toReal_nonneg ?_ hp0.le
    exact ENNReal.toReal_mono (hAAtop (t + 1)) (measure_mono (hAAmono (t + 1) s ht))
  have hsq : ∀ t ∈ Finset.Ico 1 s,
      ((volume (AA s)).toReal ^ p) ^ 2
        ≤ C₄ ^ 2 * (R ^ ((n : ℝ) / 2 - 1)) ^ 2 * (volume (DD t)).toReal := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Ico.1 ht).1
    have ht2 : t + 1 ≤ s := (Finset.mem_Ico.1 ht).2
    refine le_trans ?_ (h29 t ht1)
    exact pow_le_pow_left₀ (Real.rpow_nonneg (hAAnn s) _) (hmono t ht2) 2
  have hexp : (R ^ ((n : ℝ) / 2 - 1)) ^ 2 * R ^ (n : ℝ) = R ^ (2 * (n : ℝ) - 2) := by
    rw [← Real.rpow_natCast (R ^ ((n : ℝ) / 2 - 1)) 2, ← Real.rpow_mul hR.le,
      ← Real.rpow_add hR]
    congr 1
    push_cast
    ring
  have hsum : ((s : ℝ) - 1) * ((volume (AA s)).toReal ^ p) ^ 2
      ≤ C₄ ^ 2 * ω * R ^ (2 * (n : ℝ) - 2) := by
    have hcard : (Finset.Ico 1 s).card = s - 1 := by simp
    have h1 := Finset.sum_le_sum hsq
    rw [Finset.sum_const, hcard, ← Finset.mul_sum] at h1
    have h2 : C₄ ^ 2 * (R ^ ((n : ℝ) / 2 - 1)) ^ 2
        * ∑ t ∈ Finset.Ico 1 s, (volume (DD t)).toReal
        ≤ C₄ ^ 2 * (R ^ ((n : ℝ) / 2 - 1)) ^ 2 * (ω * R ^ n) :=
      mul_le_mul_of_nonneg_left h26b (by positivity)
    have h3 : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
      have h4 : (1 : ℕ) ≤ s := by omega
      rw [Nat.cast_sub h4, Nat.cast_one]
    rw [nsmul_eq_mul, h3] at h1
    refine (h1.trans h2).trans_eq ?_
    rw [← Real.rpow_natCast R n,
      show C₄ ^ 2 * (R ^ ((n : ℝ) / 2 - 1)) ^ 2 * (ω * R ^ (n : ℝ))
          = C₄ ^ 2 * ω * ((R ^ ((n : ℝ) / 2 - 1)) ^ 2 * R ^ (n : ℝ)) from by ring,
      hexp]
  -- (2.10)
  have h210 : (volume (AA s)).toReal
      ≤ C₅ / (((s : ℝ) - 1) ^ e) * (volume (Metric.ball x₀ (lam₁ * R))).toReal := by
    have hY0 : (0 : ℝ) ≤ C₄ ^ 2 * ω * R ^ (2 * (n : ℝ) - 2) := by
      have := hC₄0; have := hω
      positivity
    have hX2 : ((volume (AA s)).toReal ^ p) ^ 2
        ≤ C₄ ^ 2 * ω * R ^ (2 * (n : ℝ) - 2) / ((s : ℝ) - 1) := by
      rw [le_div_iff₀ (by linarith)]
      linarith [hsum]
    have hXa : ((volume (AA s)).toReal ^ p) ^ 2 = (volume (AA s)).toReal ^ (2 * p) := by
      rw [← Real.rpow_natCast ((volume (AA s)).toReal ^ p) 2,
        ← Real.rpow_mul (hAAnn s)]
      push_cast
      ring_nf
    have hXb : ((volume (AA s)).toReal ^ (2 * p)) ^ e = (volume (AA s)).toReal := by
      rw [← Real.rpow_mul (hAAnn s), hpe, Real.rpow_one]
    have hstep : (volume (AA s)).toReal
        ≤ (C₄ ^ 2 * ω * R ^ (2 * (n : ℝ) - 2) / ((s : ℝ) - 1)) ^ e := by
      rw [← hXb, ← hXa]
      exact Real.rpow_le_rpow (by positivity) hX2 he0.le
    refine hstep.trans_eq ?_
    rw [Real.div_rpow hY0 (by linarith),
      Real.mul_rpow (by positivity) (Real.rpow_nonneg hR.le _),
      ← Real.rpow_mul hR.le, h2pe, hC₅def, hmB]
    rw [mul_pow, ← Real.rpow_natCast R n]
    have hωne : ω ≠ 0 := ne_of_gt hω
    have hlne : lam₁ ^ n ≠ 0 := ne_of_gt (pow_pos hlam₁.1 n)
    have hsne : ((s : ℝ) - 1) ^ e ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)
    field_simp
  -- Step 5: `k_s = lam₂ * k + (1 - lam₂) * M`
  rw [show Metric.ball x₀ (lam₁ * R) ∩ {y | 1 / 2 ^ s * k + (1 - 1 / 2 ^ s) * M < f y}
      = AA s from by rw [hAAdef, hkkdef]]
  exact h210.trans (mul_le_mul_of_nonneg_right hs ENNReal.toReal_nonneg)
