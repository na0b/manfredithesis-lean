import ManfrediThesis.Preamble
import ManfrediThesis.WeakGradientRestrict
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MorreyBoundOn
import ManfrediThesis.CampanatoBoundOn
import ManfrediThesis.CitedSobolevPoincareBall
open MeasureTheory

/-- Lemma 4.2: a Morrey bound for the gradient on `Ω'` yields a Campanato bound
for the function on an inner subdomain `Ω''`. -/
theorem MorreyGradientToCampanato :
    ∀ (n : ℕ) (p τ N d : ℝ), 2 ≤ n → 1 < p → 0 < τ → τ ≤ (n : ℝ) → 0 ≤ N → 0 < d →
      CitedSobolevPoincareBall n →
      ∃ N' : ℝ, 0 ≤ N' ∧
        ∀ (Ω Ω' Ω'' : Set (EuclideanSpace ℝ (Fin n)))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          IsOpen Ω → IsOpen Ω' → IsOpen Ω'' →
          Bornology.IsBounded Ω' → closure Ω' ⊆ Ω → closure Ω'' ⊆ Ω' →
          (∀ x ∈ Ω'', ∀ y, y ∉ Ω' → d ≤ dist x y) →
          MemW1pLocOn n p Ω u g →
          MorreyBoundOn n p ((n : ℝ) - τ) Ω' (fun x => ‖g x‖) N →
          MorreyBoundOn n ((n : ℝ) / ((n : ℝ) - 1)) 0 Ω' u N →
          CampanatoBoundOn n ((n : ℝ) / ((n : ℝ) - 1))
            ((n : ℝ) + ((n : ℝ) / ((n : ℝ) - 1)) * (1 - τ / p)) Ω'' u N' := by
  intro n p τ N d hn hp hτ hτn hN hd hSP
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hp1 : (1:ℝ) ≤ p := hp.le
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp
  have hnR : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnm1 : (0:ℝ) < (n : ℝ) - 1 := by linarith
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  -- `q` and `λ`, with the two elementary facts (0a) and (0b).
  obtain ⟨q, hq⟩ : ∃ t : ℝ, t = (n : ℝ) / ((n : ℝ) - 1) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; exact div_pos (by linarith) hnm1
  have hq1 : 1 < q := by
    rw [hq, lt_div_iff₀ hnm1]
    linarith
  obtain ⟨lam, hlam⟩ : ∃ t : ℝ, t = (n : ℝ) + q * (1 - τ / p) := ⟨_, rfl⟩
  have hqn : q * ((n : ℝ) - 1) = (n : ℝ) := by
    rw [hq]
    field_simp
  have hlam_eq : lam = q * ((n : ℝ) - τ / p) := by
    rw [hlam]
    have h1 : q * ((n : ℝ) - τ / p) = q * ((n : ℝ) - 1) + q * (1 - τ / p) := by ring
    rw [h1, hqn]
  have hτp : τ / p < τ := by
    rw [div_lt_iff₀ hp0]
    nlinarith
  have hlam0 : 0 < lam := by
    rw [hlam_eq]
    have h2 : (0:ℝ) < (n : ℝ) - τ / p := by linarith
    positivity
  -- the Sobolev-Poincaré constant, the unit-ball volume, and `N'`
  obtain ⟨C, hC0, hC6⟩ := hSP
  obtain ⟨ω, hω⟩ : ∃ t : ℝ,
      t = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := ⟨_, rfl⟩
  have hω0 : 0 < ω := by
    rw [hω]
    refine ENNReal.toReal_pos ?_ measure_ball_lt_top.ne
    exact (Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self one_pos⟩).ne'
  have hntriv : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, hnpos⟩ (1 : ℝ), ?_⟩⟩
    intro hcon
    have h := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w ⟨0, hnpos⟩) hcon
    simp at h
  have hballvol : ∀ (y : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 ≤ t →
      (volume (Metric.ball y t)).toReal = ω * t ^ n := by
    intro y t ht
    rw [Measure.addHaar_ball volume y ht, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity),
      show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n by simp, hω]
    ring
  obtain ⟨K, hK⟩ : ∃ t : ℝ, t = C * ω ^ (1 - 1 / p) := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨M, hM⟩ : ∃ t : ℝ, t = max K (d ^ (-(lam / q))) := ⟨_, rfl⟩
  have hKM : K ≤ M := by rw [hM]; exact le_max_left _ _
  have hdM : d ^ (-(lam / q)) ≤ M := by rw [hM]; exact le_max_right _ _
  have hM0 : 0 < M := lt_of_lt_of_le hK0 hKM
  -- `(s + t)^q ≤ 2^q (s^q + t^q)`
  have hsum_rpow : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → (s + t) ^ q ≤ 2 ^ q * (s ^ q + t ^ q) := by
    intro s t hs ht
    have h2q : (0:ℝ) ≤ 2 ^ q := Real.rpow_nonneg (by norm_num) q
    have hsq : (0:ℝ) ≤ s ^ q := Real.rpow_nonneg hs q
    have htq : (0:ℝ) ≤ t ^ q := Real.rpow_nonneg ht q
    rcases le_total s t with h | h
    · have hb : (s + t) ^ q ≤ (2 * t) ^ q :=
        Real.rpow_le_rpow (by linarith) (by linarith) hq0.le
      rw [Real.mul_rpow (by norm_num) ht] at hb
      exact le_trans hb (mul_le_mul_of_nonneg_left (by linarith) h2q)
    · have hb : (s + t) ^ q ≤ (2 * s) ^ q :=
        Real.rpow_le_rpow (by linarith) (by linarith) hq0.le
      rw [Real.mul_rpow (by norm_num) hs] at hb
      exact le_trans hb (mul_le_mul_of_nonneg_left (by linarith) h2q)
  -- Hölder's inequality on a set of finite measure
  have hholder : ∀ (s : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (t : ℝ), 1 < t → volume s ≠ ⊤ → (∀ y, 0 ≤ f y) →
      MemLp f (ENNReal.ofReal t) (volume.restrict s) →
      (∫ y in s, f y)
        ≤ (∫ y in s, f y ^ t) ^ (1 / t) * (volume s).toReal ^ (1 - 1 / t) := by
    intro s f t ht hsfin hf0 hfLp
    have hfin : IsFiniteMeasure (volume.restrict s) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hsfin⟩
    have hconj : Real.HolderConjugate t (t / (t - 1)) :=
      (Real.holderConjugate_iff_eq_conjExponent ht).mpr rfl
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict s) hconj
      (Filter.Eventually.of_forall hf0)
      (Filter.Eventually.of_forall (fun _ => zero_le_one) :
        (0 : EuclideanSpace ℝ (Fin n) → ℝ) ≤ᵐ[volume.restrict s] fun _ => (1:ℝ))
      hfLp (memLp_const (1:ℝ))
    simp only [mul_one, Real.one_rpow, integral_const, smul_eq_mul, mul_one] at h
    have he : 1 / (t / (t - 1)) = 1 - 1 / t := by
      rw [one_div_div]
      field_simp
    rw [he, Measure.real_def, Measure.restrict_apply_univ] at h
    exact h
  refine ⟨2 ^ ((q + 1) / q) * N * M, by positivity, ?_⟩
  intro Ω Ω' Ω'' u g hΩ hΩ' hΩ'' hbdd hcl1 hcl2 hsep hloc hMg hMu
  rw [← hq] at hMu
  rw [← hq, ← hlam]
  -- geometry of the three domains
  have hsub2 : Ω'' ⊆ Ω' := subset_trans subset_closure hcl2
  have hsub1 : Ω' ⊆ Ω := subset_trans subset_closure hcl1
  have hdiam : Metric.diam Ω'' ≤ Metric.diam Ω' := Metric.diam_mono hsub2 hbdd
  have hΩ'fin : volume Ω' ≠ ⊤ := by
    obtain ⟨y, t, hball⟩ := hbdd.subset_ball_lt 0 0
    exact (lt_of_le_of_lt (measure_mono hball) measure_ball_lt_top).ne
  have huLq : MemLp u (ENNReal.ofReal q) (volume.restrict Ω') := hMu.1
  have hmemsub : ∀ (s : Set (EuclideanSpace ℝ (Fin n))) (c : ℝ), s ⊆ Ω' →
      MemLp (fun y => u y - c) (ENNReal.ofReal q) (volume.restrict s) := by
    intro s c hs
    have hfin : IsFiniteMeasure (volume.restrict s) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_lt (measure_mono hs) (lt_of_le_of_ne le_top hΩ'fin)⟩
    exact (huLq.mono_measure (Measure.restrict_mono hs le_rfl)).sub (memLp_const c)
  have hintpow : ∀ (s : Set (EuclideanSpace ℝ (Fin n))) (c : ℝ), s ⊆ Ω' →
      IntegrableOn (fun y => |u y - c| ^ q) s volume := by
    intro s c hs
    have h3 := (hmemsub s c hs).integrable_norm_rpow
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hq0) (by simp)
    rw [ENNReal.toReal_ofReal hq0.le] at h3
    have h4 : Integrable (fun y => |u y - c| ^ q) (volume.restrict s) := by
      simpa only [Real.norm_eq_abs] using h3
    exact h4
  -- Step 1: the oscillation lemma, used in both regimes.
  have hosc : ∀ (A B : Set (EuclideanSpace ℝ (Fin n))) (c : ℝ),
      MeasurableSet A → A ⊆ B → 0 < volume A → volume B ≠ ⊤ → B ⊆ Ω' →
      (∫ y in A, |u y - (volume A).toReal⁻¹ * ∫ z in A, u z| ^ q)
        ≤ 2 ^ (q + 1) * ∫ y in B, |u y - c| ^ q := by
    intro A B c hAm hAB hApos hBfin hBΩ'
    have hAΩ' : A ⊆ Ω' := hAB.trans hBΩ'
    have hAfin : volume A ≠ ⊤ := (lt_of_le_of_lt (measure_mono hAB)
      (lt_of_le_of_ne le_top hBfin)).ne
    have hAtr : 0 < (volume A).toReal := ENNReal.toReal_pos hApos.ne' hAfin
    have hfinA : IsFiniteMeasure (volume.restrict A) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hAfin⟩
    have hwA : MemLp (fun y => u y - c) (ENNReal.ofReal q) (volume.restrict A) :=
      hmemsub A c hAΩ'
    have hwabsA : MemLp (fun y => |u y - c|) (ENNReal.ofReal q) (volume.restrict A) := by
      simpa only [Real.norm_eq_abs] using hwA.norm
    have huq : MemLp u (ENNReal.ofReal q) (volume.restrict A) :=
      huLq.mono_measure (Measure.restrict_mono hAΩ' le_rfl)
    have hwL1 : IntegrableOn u A volume := by
      have h2 : MemLp u 1 (volume.restrict A) := by
        refine huq.mono_exponent ?_
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hq1.le
      have h3 : Integrable u (volume.restrict A) := (memLp_one_iff_integrable).mp h2
      exact h3
    have hwcL1 : IntegrableOn (fun y => |u y - c|) A volume := by
      have h1 : MemLp (fun y => |u y - c|) 1 (volume.restrict A) := by
        refine hwabsA.mono_exponent ?_
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hq1.le
      have h2 : Integrable (fun y => |u y - c|) (volume.restrict A) :=
        (memLp_one_iff_integrable).mp h1
      exact h2
    have hpowA : IntegrableOn (fun y => |u y - c| ^ q) A volume := hintpow A c hAΩ'
    have hpowB : IntegrableOn (fun y => |u y - c| ^ q) B volume := hintpow B c hBΩ'
    obtain ⟨mA, hmA⟩ : ∃ t : ℝ, t = (volume A).toReal⁻¹ * ∫ z in A, u z := ⟨_, rfl⟩
    obtain ⟨m, hm⟩ : ∃ t : ℝ, t = (volume A).toReal⁻¹ * ∫ y in A, |u y - c| := ⟨_, rfl⟩
    have hIabs : (0:ℝ) ≤ ∫ y in A, |u y - c| :=
      setIntegral_nonneg hAm (fun y _ => abs_nonneg _)
    have hXnn : (0:ℝ) ≤ ∫ y in A, |u y - c| ^ q :=
      setIntegral_nonneg hAm (fun y _ => Real.rpow_nonneg (abs_nonneg _) _)
    have hm0 : 0 ≤ m := by
      rw [hm]
      exact mul_nonneg (by positivity) hIabs
    -- `|c - mA| ≤ m`
    have hconstint : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => c) A volume :=
      integrableOn_const hAfin (by simp)
    have hcmA : |c - mA| ≤ m := by
      have hconst : (∫ _y in A, c) = (volume A).toReal * c := by
        rw [setIntegral_const, Measure.real_def, smul_eq_mul]
      have h1 : (∫ y in A, (c - u y)) = (volume A).toReal * c - ∫ y in A, u y := by
        rw [integral_sub hconstint hwL1, hconst]
      have h2 : c - mA = (volume A).toReal⁻¹ * ∫ y in A, (c - u y) := by
        rw [h1, hmA]
        field_simp
      have h3 : |∫ y in A, (c - u y)| ≤ ∫ y in A, |u y - c| := by
        refine le_trans abs_integral_le_integral_abs ?_
        refine setIntegral_mono_on ?_ hwcL1 hAm (fun y _ => ?_)
        · exact (hwcL1.congr_fun (fun y _ => abs_sub_comm (u y) c) hAm)
        · rw [abs_sub_comm]
      rw [h2, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (volume A).toReal⁻¹), hm]
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    -- the pointwise bound
    have hptw : ∀ y ∈ A, |u y - mA| ^ q ≤ 2 ^ q * (|u y - c| ^ q + m ^ q) := by
      intro y _
      have h2 : |u y - mA| ≤ |u y - c| + |c - mA| := by
        have h3 : u y - mA = (u y - c) + (c - mA) := by ring
        rw [h3]
        exact abs_add_le _ _
      have h1 : |u y - mA| ≤ |u y - c| + m := le_trans h2 (by linarith)
      exact le_trans (Real.rpow_le_rpow (abs_nonneg _) h1 hq0.le)
        (hsum_rpow _ _ (abs_nonneg _) hm0)
    have hdomint : IntegrableOn (fun y => 2 ^ q * (|u y - c| ^ q + m ^ q)) A volume :=
      ((hpowA.add (integrableOn_const (C := m ^ q) hAfin (by simp))).const_mul _)
    have hmeasosc : AEStronglyMeasurable (fun y => |u y - mA| ^ q) (volume.restrict A) := by
      have hc : Continuous fun s : ℝ => |s - mA| ^ q := by
        have h1 : Continuous fun s : ℝ => s ^ q :=
          continuous_iff_continuousAt.mpr fun s =>
            Real.continuousAt_rpow_const s q (Or.inr hq0.le)
        exact h1.comp (continuous_abs.comp (continuous_id.sub continuous_const))
      exact hc.comp_aestronglyMeasurable hwL1.aestronglyMeasurable
    have hoscint : IntegrableOn (fun y => |u y - mA| ^ q) A volume := by
      refine Integrable.mono' hdomint hmeasosc ?_
      filter_upwards [ae_restrict_mem hAm] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact hptw y hy
    have hstep1 : (∫ y in A, |u y - mA| ^ q)
        ≤ 2 ^ q * ((∫ y in A, |u y - c| ^ q) + (volume A).toReal * m ^ q) := by
      have h1 : (∫ y in A, |u y - mA| ^ q)
          ≤ ∫ y in A, 2 ^ q * (|u y - c| ^ q + m ^ q) :=
        setIntegral_mono_on hoscint hdomint hAm hptw
      rw [integral_const_mul, integral_add hpowA
        (integrableOn_const (C := m ^ q) hAfin (by simp)),
        setIntegral_const, Measure.real_def, smul_eq_mul] at h1
      exact h1
    -- Jensen, via Hölder
    have hjensen : (volume A).toReal * m ^ q ≤ ∫ y in A, |u y - c| ^ q := by
      have hH := hholder A (fun y => |u y - c|) q hq1 hAfin (fun y => abs_nonneg _) hwabsA
      have halg : (volume A).toReal⁻¹ * ((∫ y in A, |u y - c| ^ q) ^ (1 / q)
            * (volume A).toReal ^ (1 - 1 / q))
          = ((∫ y in A, |u y - c| ^ q) * (volume A).toReal⁻¹) ^ (1 / q) := by
        rw [Real.mul_rpow hXnn (by positivity), Real.inv_rpow hAtr.le]
        have h1 : (volume A).toReal ^ (1 - 1 / q)
            = (volume A).toReal * ((volume A).toReal ^ (1 / q))⁻¹ := by
          rw [show (1:ℝ) - 1 / q = 1 + -(1 / q) by ring, Real.rpow_add hAtr,
            Real.rpow_one, Real.rpow_neg hAtr.le]
        rw [h1]
        field_simp
      have hm2 : m ≤ ((∫ y in A, |u y - c| ^ q) * (volume A).toReal⁻¹) ^ (1 / q) := by
        rw [hm, ← halg]
        exact mul_le_mul_of_nonneg_left hH (by positivity)
      have hm3 : m ^ q ≤ (∫ y in A, |u y - c| ^ q) * (volume A).toReal⁻¹ := by
        have h4 := Real.rpow_le_rpow hm0 hm2 hq0.le
        rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hq0.ne', Real.rpow_one] at h4
      calc (volume A).toReal * m ^ q
          ≤ (volume A).toReal * ((∫ y in A, |u y - c| ^ q) * (volume A).toReal⁻¹) :=
            mul_le_mul_of_nonneg_left hm3 hAtr.le
        _ = ∫ y in A, |u y - c| ^ q := by field_simp
    rw [← hmA]
    have h2q : (0:ℝ) ≤ 2 ^ q := Real.rpow_nonneg (by norm_num) q
    have hAB' : (∫ y in A, |u y - c| ^ q) ≤ ∫ y in B, |u y - c| ^ q :=
      setIntegral_mono_set hpowB
        (Filter.Eventually.of_forall (fun y => Real.rpow_nonneg (abs_nonneg _) _))
        (Filter.Eventually.of_forall hAB)
    have hfin2 : (2:ℝ) ^ (q + 1) = 2 ^ q * 2 := by
      rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]
    rw [hfin2]
    calc (∫ y in A, |u y - mA| ^ q)
        ≤ 2 ^ q * ((∫ y in A, |u y - c| ^ q) + (volume A).toReal * m ^ q) := hstep1
      _ ≤ 2 ^ q * ((∫ y in A, |u y - c| ^ q) + (∫ y in A, |u y - c| ^ q)) :=
          mul_le_mul_of_nonneg_left (by linarith) h2q
      _ = 2 ^ q * 2 * ∫ y in A, |u y - c| ^ q := by ring
      _ ≤ 2 ^ q * 2 * ∫ y in B, |u y - c| ^ q :=
          mul_le_mul_of_nonneg_left hAB' (by positivity)
  -- Step 2: `u ∈ L^q(Ω'')`, and the Campanato bound.
  refine ⟨huLq.mono_measure (Measure.restrict_mono hsub2 le_rfl), ?_⟩
  intro x₀ hx₀ ρ hρ hρdiam
  have hρdiam' : ρ < Metric.diam Ω' := lt_of_lt_of_le hρdiam hdiam
  have hAopen : IsOpen (Ω'' ∩ Metric.ball x₀ ρ) := hΩ''.inter Metric.isOpen_ball
  have hAm : MeasurableSet (Ω'' ∩ Metric.ball x₀ ρ) := hAopen.measurableSet
  have hApos : 0 < volume (Ω'' ∩ Metric.ball x₀ ρ) :=
    hAopen.measure_pos volume ⟨x₀, hx₀, Metric.mem_ball_self hρ⟩
  have hAΩ' : Ω'' ∩ Metric.ball x₀ ρ ⊆ Ω' := Set.inter_subset_left.trans hsub2
  have hballfin : volume (Metric.ball x₀ ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hNq : (0:ℝ) ≤ 2 ^ ((q + 1) / q) * N * M := by positivity
  rcases lt_or_ge ρ d with hcase | hcase
  · -- Step 3: the regime `ρ < d`
    have hballΩ' : Metric.ball x₀ ρ ⊆ Ω' := by
      intro z hz
      by_contra hzn
      have h1 := hsep x₀ hx₀ z hzn
      rw [Metric.mem_ball, dist_comm] at hz
      linarith
    have hballΩ : Metric.ball x₀ ρ ⊆ Ω := hballΩ'.trans hsub1
    have hclosball : closure (Metric.ball x₀ ρ) ⊆ Ω := (closure_mono hballΩ').trans hcl1
    obtain ⟨hwg1, hLu1, hLg1⟩ :
        MemW1pOn n p (Metric.ball x₀ ρ) u g :=
      (WeakGradientRestrict n p hn1 hp1 Ω (Metric.ball x₀ ρ) u g hΩ Metric.isOpen_ball
          hballΩ).2.2.2 hloc
        (by rw [closure_ball x₀ hρ.ne']; exact isCompact_closedBall x₀ ρ) hclosball
    have hfinball : IsFiniteMeasure (volume.restrict (Metric.ball x₀ ρ)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have hW11 : MemW1pOn n 1 (Metric.ball x₀ ρ) u g := by
      exact ⟨hwg1, hLu1.mono_exponent (ENNReal.ofReal_le_ofReal hp1),
        hLg1.mono_exponent (ENNReal.ofReal_le_ofReal hp1)⟩
    have hSPa := hC6 x₀ ρ hρ u g hW11
    rw [← hq] at hSPa
    have hinvq : ((n:ℝ) - 1) / (n:ℝ) = 1 / q := by
      rw [hq]
      field_simp
    rw [hinvq] at hSPa
    -- the Morrey bound on the gradient, over the full ball
    have hgradbd : (∫ y in Metric.ball x₀ ρ, ‖g y‖ ^ p) ≤ N ^ p * ρ ^ ((n:ℝ) - τ) := by
      have h1 := hMg.2 x₀ (hsub2 hx₀) ρ hρ hρdiam'
      rw [Set.inter_eq_self_of_subset_right hballΩ'] at h1
      simpa only [abs_norm] using h1
    -- Hölder on the ball
    have hgnorm : MemLp (fun y => ‖g y‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ ρ)) := hLg1.norm
    have hH := hholder (Metric.ball x₀ ρ) (fun y => ‖g y‖) p hp hballfin
      (fun y => norm_nonneg _) hgnorm
    have hIg : (0:ℝ) ≤ ∫ y in Metric.ball x₀ ρ, ‖g y‖ :=
      setIntegral_nonneg measurableSet_ball (fun y _ => norm_nonneg _)
    have hgpowmono : (∫ y in Metric.ball x₀ ρ, ‖g y‖ ^ p) ^ (1 / p)
        ≤ (N ^ p * ρ ^ ((n:ℝ) - τ)) ^ (1 / p) :=
      Real.rpow_le_rpow
        (setIntegral_nonneg measurableSet_ball (fun y _ => Real.rpow_nonneg (norm_nonneg _) _))
        hgradbd (by positivity)
    have hrhs : (N ^ p * ρ ^ ((n:ℝ) - τ)) ^ (1 / p) = N * ρ ^ (((n:ℝ) - τ) / p) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hN _) (Real.rpow_nonneg hρ.le _),
        ← Real.rpow_mul hN, ← Real.rpow_mul hρ.le, mul_one_div, div_self hp0.ne',
        Real.rpow_one, mul_one_div]
    have hvol : (volume (Metric.ball x₀ ρ)).toReal ^ (1 - 1 / p)
        = ω ^ (1 - 1 / p) * ρ ^ ((n:ℝ) * (1 - 1 / p)) := by
      rw [hballvol x₀ ρ hρ.le, Real.mul_rpow hω0.le (by positivity),
        ← Real.rpow_natCast ρ n, ← Real.rpow_mul hρ.le]
    have hIgbd : (∫ y in Metric.ball x₀ ρ, ‖g y‖) ≤ ω ^ (1 - 1 / p) * N * ρ ^ ((n:ℝ) - τ / p) := by
      have h1 : (∫ y in Metric.ball x₀ ρ, ‖g y‖)
          ≤ (N * ρ ^ (((n:ℝ) - τ) / p)) * (ω ^ (1 - 1 / p) * ρ ^ ((n:ℝ) * (1 - 1 / p))) := by
        rw [← hrhs, ← hvol]
        exact le_trans hH (mul_le_mul_of_nonneg_right hgpowmono (by positivity))
      have h2 : (N * ρ ^ (((n:ℝ) - τ) / p)) * (ω ^ (1 - 1 / p) * ρ ^ ((n:ℝ) * (1 - 1 / p)))
          = ω ^ (1 - 1 / p) * N * ρ ^ ((n:ℝ) - τ / p) := by
        have he : ((n:ℝ) - τ) / p + (n:ℝ) * (1 - 1 / p) = (n:ℝ) - τ / p := by
          field_simp
          ring
        calc (N * ρ ^ (((n:ℝ) - τ) / p)) * (ω ^ (1 - 1 / p) * ρ ^ ((n:ℝ) * (1 - 1 / p)))
            = ω ^ (1 - 1 / p) * N
                * (ρ ^ (((n:ℝ) - τ) / p) * ρ ^ ((n:ℝ) * (1 - 1 / p))) := by ring
          _ = ω ^ (1 - 1 / p) * N * ρ ^ (((n:ℝ) - τ) / p + (n:ℝ) * (1 - 1 / p)) := by
              rw [← Real.rpow_add hρ]
          _ = ω ^ (1 - 1 / p) * N * ρ ^ ((n:ℝ) - τ / p) := by rw [he]
      linarith [h1, h2.le, h2.ge]
    -- the Sobolev-Poincaré bound on the oscillation over the ball
    have hXball : (∫ y in Metric.ball x₀ ρ,
        |u y - (volume (Metric.ball x₀ ρ)).toReal⁻¹ * ∫ z in Metric.ball x₀ ρ, u z| ^ q)
        ≤ (K * N) ^ q * ρ ^ lam := by
      obtain ⟨X, hX⟩ : ∃ t : ℝ, t = ∫ y in Metric.ball x₀ ρ,
          |u y - (volume (Metric.ball x₀ ρ)).toReal⁻¹ * ∫ z in Metric.ball x₀ ρ, u z| ^ q :=
        ⟨_, rfl⟩
      have hXnn : 0 ≤ X := by
        rw [hX]
        exact setIntegral_nonneg measurableSet_ball
          (fun y _ => Real.rpow_nonneg (abs_nonneg _) _)
      have h1 : X ^ (1 / q) ≤ C * (ω ^ (1 - 1 / p) * N * ρ ^ ((n:ℝ) - τ / p)) := by
        rw [hX]
        exact le_trans hSPa (mul_le_mul_of_nonneg_left hIgbd hC0.le)
      have h2 : X ≤ (C * (ω ^ (1 - 1 / p) * N * ρ ^ ((n:ℝ) - τ / p))) ^ q := by
        have h3 := Real.rpow_le_rpow (Real.rpow_nonneg hXnn _) h1 hq0.le
        rwa [← Real.rpow_mul hXnn, one_div_mul_cancel hq0.ne', Real.rpow_one] at h3
      have h4 : (C * (ω ^ (1 - 1 / p) * N * ρ ^ ((n:ℝ) - τ / p))) ^ q
          = (K * N) ^ q * ρ ^ lam := by
        have he : C * (ω ^ (1 - 1 / p) * N * ρ ^ ((n:ℝ) - τ / p))
            = (K * N) * ρ ^ ((n:ℝ) - τ / p) := by
          rw [hK]; ring
        rw [he, Real.mul_rpow (mul_nonneg hK0.le hN) (Real.rpow_nonneg hρ.le _),
          ← Real.rpow_mul hρ.le, hlam_eq, mul_comm ((n:ℝ) - τ / p) q]
      rw [← hX]
      linarith [h2, h4.le, h4.ge]
    -- combine with the oscillation lemma
    have hoscApp := hosc (Ω'' ∩ Metric.ball x₀ ρ) (Metric.ball x₀ ρ)
      ((volume (Metric.ball x₀ ρ)).toReal⁻¹ * ∫ z in Metric.ball x₀ ρ, u z)
      hAm Set.inter_subset_right hApos hballfin hballΩ'
    have hcombine : (2:ℝ) ^ (q + 1) * ((K * N) ^ q * ρ ^ lam)
        ≤ (2 ^ ((q + 1) / q) * N * M) ^ q * ρ ^ lam := by
      have h1 : (2:ℝ) ^ (q + 1) * (K * N) ^ q = (2 ^ ((q + 1) / q) * K * N) ^ q := by
        rw [show (2:ℝ) ^ ((q + 1) / q) * K * N = 2 ^ ((q + 1) / q) * (K * N) by ring,
          Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (mul_nonneg hK0.le hN),
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), div_mul_cancel₀ _ hq0.ne']
      have h2 : ((2:ℝ) ^ ((q + 1) / q) * K * N) ^ q ≤ (2 ^ ((q + 1) / q) * N * M) ^ q := by
        refine Real.rpow_le_rpow (by positivity) ?_ hq0.le
        have h3 : (2:ℝ) ^ ((q + 1) / q) * K * N = 2 ^ ((q + 1) / q) * N * K := by ring
        rw [h3]
        exact mul_le_mul_of_nonneg_left hKM (by positivity)
      have h4 : (0:ℝ) ≤ ρ ^ lam := Real.rpow_nonneg hρ.le _
      calc (2:ℝ) ^ (q + 1) * ((K * N) ^ q * ρ ^ lam)
          = 2 ^ (q + 1) * (K * N) ^ q * ρ ^ lam := by ring
        _ = ((2:ℝ) ^ ((q + 1) / q) * K * N) ^ q * ρ ^ lam := by rw [h1]
        _ ≤ (2 ^ ((q + 1) / q) * N * M) ^ q * ρ ^ lam := mul_le_mul_of_nonneg_right h2 h4
    calc (∫ y in Ω'' ∩ Metric.ball x₀ ρ,
          |u y - (volume (Ω'' ∩ Metric.ball x₀ ρ)).toReal⁻¹
            * ∫ z in Ω'' ∩ Metric.ball x₀ ρ, u z| ^ q)
        ≤ 2 ^ (q + 1) * ∫ y in Metric.ball x₀ ρ,
            |u y - (volume (Metric.ball x₀ ρ)).toReal⁻¹
              * ∫ z in Metric.ball x₀ ρ, u z| ^ q := hoscApp
      _ ≤ 2 ^ (q + 1) * ((K * N) ^ q * ρ ^ lam) :=
          mul_le_mul_of_nonneg_left hXball (Real.rpow_nonneg (by norm_num) _)
      _ ≤ (2 ^ ((q + 1) / q) * N * M) ^ q * ρ ^ lam := hcombine
  · -- Step 4: the regime `ρ ≥ d`
    have hoscApp := hosc (Ω'' ∩ Metric.ball x₀ ρ) (Ω'' ∩ Metric.ball x₀ ρ) 0
      hAm (le_refl _) hApos
      ((lt_of_le_of_lt (measure_mono hAΩ') (lt_of_le_of_ne le_top hΩ'fin)).ne) hAΩ'
    have hub : (∫ y in Ω'' ∩ Metric.ball x₀ ρ, |u y - 0| ^ q) ≤ N ^ q := by
      have h1 := hMu.2 x₀ (hsub2 hx₀) ρ hρ hρdiam'
      rw [Real.rpow_zero, mul_one] at h1
      have h3 : Ω'' ∩ Metric.ball x₀ ρ ⊆ Ω' ∩ Metric.ball x₀ ρ :=
        Set.inter_subset_inter_left _ hsub2
      have h4 : (∫ y in Ω'' ∩ Metric.ball x₀ ρ, |u y - 0| ^ q)
          ≤ ∫ y in Ω' ∩ Metric.ball x₀ ρ, |u y - 0| ^ q := by
        refine setIntegral_mono_set (hintpow (Ω' ∩ Metric.ball x₀ ρ) 0 Set.inter_subset_left)
          (Filter.Eventually.of_forall (fun y => Real.rpow_nonneg (abs_nonneg _) _))
          (Filter.Eventually.of_forall h3)
      have h5 : (∫ y in Ω' ∩ Metric.ball x₀ ρ, |u y - 0| ^ q)
          = ∫ y in Ω' ∩ Metric.ball x₀ ρ, |u y| ^ q := by
        refine setIntegral_congr_fun (hΩ'.inter Metric.isOpen_ball).measurableSet
          (fun y _ => ?_)
        rw [sub_zero]
      rw [h5] at h4
      linarith
    -- `1 ≤ M^q * ρ^lam`
    have hone : (1:ℝ) ≤ M ^ q * ρ ^ lam := by
      have h1 : (d ^ (-(lam / q))) ^ q = d ^ (-lam) := by
        rw [← Real.rpow_mul hd.le]
        congr 1
        field_simp
      have h2 : d ^ (-lam) ≤ M ^ q := by
        rw [← h1]
        exact Real.rpow_le_rpow (Real.rpow_nonneg hd.le _) hdM hq0.le
      have h3 : d ^ lam ≤ ρ ^ lam := Real.rpow_le_rpow hd.le hcase hlam0.le
      have h4 : d ^ (-lam) * d ^ lam = 1 := by
        rw [← Real.rpow_add hd]
        simp
      have h6 : (0:ℝ) < d ^ lam := Real.rpow_pos_of_pos hd _
      calc (1:ℝ) = d ^ (-lam) * d ^ lam := h4.symm
        _ ≤ M ^ q * ρ ^ lam := mul_le_mul h2 h3 h6.le (Real.rpow_nonneg hM0.le _)
    have hfinal : (2:ℝ) ^ (q + 1) * N ^ q ≤ (2 ^ ((q + 1) / q) * N * M) ^ q * ρ ^ lam := by
      have h1 : ((2:ℝ) ^ ((q + 1) / q) * N * M) ^ q = 2 ^ (q + 1) * N ^ q * M ^ q := by
        rw [Real.mul_rpow (by positivity) hM0.le, Real.mul_rpow (by positivity) hN,
          ← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ hq0.ne']
      rw [h1]
      have h2 : (0:ℝ) ≤ 2 ^ (q + 1) * N ^ q :=
        mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hN _)
      calc (2:ℝ) ^ (q + 1) * N ^ q = 2 ^ (q + 1) * N ^ q * 1 := by ring
        _ ≤ 2 ^ (q + 1) * N ^ q * (M ^ q * ρ ^ lam) :=
            mul_le_mul_of_nonneg_left hone h2
        _ = 2 ^ (q + 1) * N ^ q * M ^ q * ρ ^ lam := by ring
    have h2q : (0:ℝ) ≤ 2 ^ (q + 1) := Real.rpow_nonneg (by norm_num) _
    calc (∫ y in Ω'' ∩ Metric.ball x₀ ρ,
          |u y - (volume (Ω'' ∩ Metric.ball x₀ ρ)).toReal⁻¹
            * ∫ z in Ω'' ∩ Metric.ball x₀ ρ, u z| ^ q)
        ≤ 2 ^ (q + 1) * ∫ y in Ω'' ∩ Metric.ball x₀ ρ, |u y - 0| ^ q := hoscApp
      _ ≤ 2 ^ (q + 1) * N ^ q := mul_le_mul_of_nonneg_left hub h2q
      _ ≤ (2 ^ ((q + 1) / q) * N * M) ^ q * ρ ^ lam := hfinal
