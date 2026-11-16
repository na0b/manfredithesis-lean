import ManfrediThesis.Preamble
import ManfrediThesis.ComparisonSchemeCampanatoBound
import ManfrediThesis.IsBoundedLipschitzDomain
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MorreyBoundOn
import ManfrediThesis.CampanatoBoundOn
import ManfrediThesis.MemHolderOn
import ManfrediThesis.MorreyGradientToCampanato
import ManfrediThesis.MorreyBoundFromBundle
import ManfrediThesis.MeanReplacementLp
import ManfrediThesis.CitedCampanatoEmbedding
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.WeakGradientRestrict
open MeasureTheory

/-- The abstract comparison scheme behind Theorems 3 and 5: from the decay
(4.11) for the comparison maps and the smallness (Lemma 4.1 / Lemma 5.1) of the
remainder, the Morrey bound for `∇u`, the Campanato bound for `u` and the
Hölder representative of `u`, all three on the inner domain `Ω'`.  The scheme
sees the comparison maps only through the two displayed estimates, so it is
shared by the variational and the general setting. -/
theorem ComparisonSchemeMorreyCore :
    ∀ (n : ℕ) (p τ c₀ W M d R₁ : ℝ) (σ₂ : ℝ → ℝ),
      2 ≤ n → 1 < p → 0 < τ → τ < (n : ℝ) → 0 < c₀ → 0 ≤ W → 0 ≤ M → 0 < d →
      0 < R₁ → Continuous σ₂ → Monotone σ₂ → σ₂ 0 = 0 → (∀ t : ℝ, 0 ≤ σ₂ t) →
      CitedSobolevPoincareBall n →
      ∃ N₁ N₂ : ℝ, 0 ≤ N₁ ∧ 0 ≤ N₂ ∧
        ∀ (ε : ℝ) (Ω Ω'' Ω' : Set (EuclideanSpace ℝ (Fin n)))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 ≤ ε → ε ≤ 1 → IsOpen Ω → IsOpen Ω'' → IsOpen Ω' → Ω'.Nonempty →
          Bornology.IsBounded Ω'' → closure Ω' ⊆ Ω'' → closure Ω'' ⊆ Ω →
          (∀ x ∈ Ω', ∀ y, y ∉ Ω'' → d ≤ dist x y) →
          (∀ x ∈ Ω'', ∀ y, y ∉ Ω → d ≤ dist x y) →
          IsBoundedLipschitzDomain n Ω' →
          CitedCampanatoEmbedding n ((n : ℝ) / ((n : ℝ) - 1)) Ω' →
          MemW1pOn n p Ω u g →
          (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
          ((∫ x in Ω, |u x| ^ p) + ∫ x in Ω, ‖g x‖ ^ p) ≤ W ^ p →
          (∀ x₀ ∈ Ω'', ∀ R : ℝ, 0 < R → R ≤ R₁ → Metric.closedBall x₀ R ⊆ Ω →
            ∃ (v : EuclideanSpace ℝ (Fin n) → ℝ)
              (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
              MemW1pOn n p (Metric.ball x₀ R) v gv ∧
              (∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
                (∫ x in Metric.ball x₀ ρ, (ε + ‖gv x‖ ^ 2) ^ (p / 2))
                  ≤ c₀ * (ρ / R) ^ (n : ℝ)
                    * ∫ x in Metric.ball x₀ R, (ε + ‖gv x‖ ^ 2) ^ (p / 2)) ∧
              (∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p)
                ≤ σ₂ R * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2)) →
          MorreyBoundOn n p ((n : ℝ) - τ) Ω' (fun x => ‖g x‖) N₁
          ∧ CampanatoBoundOn n ((n : ℝ) / ((n : ℝ) - 1))
              ((n : ℝ) + (1 - τ / p) * ((n : ℝ) / ((n : ℝ) - 1))) Ω' u N₂
          ∧ (∀ η : ℝ, 0 ≤ η → η < 1 →
              ∃ w : EuclideanSpace ℝ (Fin n) → ℝ,
                (∀ᵐ x ∂(volume.restrict Ω'), u x = w x) ∧
                  MemHolderOn n η (closure Ω') w) := by
  intro n p τ c₀ W M d R₁ σ₂ hn hp hτ hτn hc₀ hW hM hd hR₁ hσc hσm hσ0 hσnn hSP
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  set q : ℝ := (n:ℝ) / ((n:ℝ) - 1) with hqdef
  have hq1 : (1:ℝ) < q := by
    rw [hqdef, lt_div_iff₀ (by linarith)]; linarith
  have hq0 : (0:ℝ) < q := lt_trans one_pos hq1
  have hpart2 : ∀ t : ℝ, 0 < t → t < (n:ℝ) →
      ∃ N : ℝ, 0 ≤ N ∧
        ∀ (ε : ℝ) (Ω Ω'' Ω' : Set (EuclideanSpace ℝ (Fin n)))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          0 ≤ ε → ε ≤ 1 → IsOpen Ω → IsOpen Ω'' → IsOpen Ω' → Ω'.Nonempty →
          Bornology.IsBounded Ω'' → closure Ω' ⊆ Ω'' → closure Ω'' ⊆ Ω →
          (∀ x ∈ Ω', ∀ y, y ∉ Ω'' → d ≤ dist x y) →
          (∀ x ∈ Ω'', ∀ y, y ∉ Ω → d ≤ dist x y) →
          MemW1pOn n p Ω u g →
          (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
          ((∫ x in Ω, |u x| ^ p) + ∫ x in Ω, ‖g x‖ ^ p) ≤ W ^ p →
          (∀ x₀ ∈ Ω'', ∀ R : ℝ, 0 < R → R ≤ R₁ → Metric.closedBall x₀ R ⊆ Ω →
            ∃ (v : EuclideanSpace ℝ (Fin n) → ℝ)
              (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
              MemW1pOn n p (Metric.ball x₀ R) v gv ∧
              (∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
                (∫ x in Metric.ball x₀ ρ, (ε + ‖gv x‖ ^ 2) ^ (p / 2))
                  ≤ c₀ * (ρ / R) ^ (n : ℝ)
                    * ∫ x in Metric.ball x₀ R, (ε + ‖gv x‖ ^ 2) ^ (p / 2)) ∧
              (∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p)
                ≤ σ₂ R * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2)) →
          CampanatoBoundOn n ((n : ℝ) / ((n : ℝ) - 1))
            ((n : ℝ) + (1 - t / p) * ((n : ℝ) / ((n : ℝ) - 1))) Ω' u N :=
    ComparisonSchemeCampanatoBound n p c₀ W M d R₁ σ₂ hn hp hc₀ hW hM hd hR₁
      hσc hσm hσ0 hσnn hSP
  obtain ⟨N₂, hN₂0, hN₂⟩ := hpart2 τ hτ hτn
  obtain ⟨N₁, hN₁0, hmorrey⟩ :=
    MorreyBoundFromBundle n p τ c₀ W d R₁ σ₂ hn hp hτ hτn hc₀ hW hd hR₁ hσc hσm hσ0 hσnn
  refine ⟨N₁, N₂, hN₁0, hN₂0, ?_⟩
  intro ε Ω Ω'' Ω' u g hε0 hε1 hΩ hΩ'' hΩ' hΩ'ne hbdd hclΩ' hclΩ'' hsep1 hsep2 hLip hCE
    hu hMb hWb hbundle
  have hsub : Ω' ⊆ Ω'' := subset_trans subset_closure hclΩ'
  have hΩ''Ω : Ω'' ⊆ Ω := subset_trans subset_closure hclΩ''
  have hpne0 : (ENNReal.ofReal p) ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have hpnet : (ENNReal.ofReal p) ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  have htoR : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hgpΩ : IntegrableOn (fun y => ‖g y‖ ^ p) Ω volume := by
    have h := (hu.2.2).integrable_norm_rpow hpne0 hpnet
    rwa [htoR] at h
  refine ⟨?_, hN₂ ε Ω Ω'' Ω' u g hε0 hε1 hΩ hΩ'' hΩ' hΩ'ne hbdd hclΩ' hclΩ'' hsep1 hsep2
    hu hMb hWb hbundle, ?_⟩
  · -- part (i): restrict the Ω'' bound of MorreyBoundFromBundle to Ω'
    have hmor'' := hmorrey ε Ω Ω'' u g hε0 hε1 hΩ hΩ'' hbdd hclΩ'' hsep2 hu hWb hbundle
    refine ⟨hmor''.1.mono_measure (Measure.restrict_mono hsub le_rfl), ?_⟩
    intro x hx ρ hρ hρd
    have hdiam : Metric.diam Ω' ≤ Metric.diam Ω'' := Metric.diam_mono hsub hbdd
    refine le_trans ?_ (hmor''.2 x (hsub hx) ρ hρ (lt_of_lt_of_le hρd hdiam))
    refine setIntegral_mono_set ?_ ?_ ?_
    · refine (hgpΩ.mono_set ?_).congr_fun ?_ ((hΩ''.measurableSet).inter measurableSet_ball)
      · exact fun y hy => hΩ''Ω hy.1
      · exact fun y _ => by rw [abs_of_nonneg (norm_nonneg _)]
    · exact Filter.Eventually.of_forall fun y => Real.rpow_nonneg (abs_nonneg _) _
    · exact Filter.Eventually.of_forall fun y hy => ⟨hsub hy.1, hy.2⟩
  · -- part (iii): re-run (ii) at a second exponent and feed the Campanato embedding
    intro η hη0 hη1
    set t : ℝ := min (n:ℝ) p * (1 - η) / 2 with htdef
    have hmin0 : (0:ℝ) < min (n:ℝ) p := lt_min (by linarith) hp0
    have h1η : (0:ℝ) < 1 - η := by linarith
    have hmn : min (n:ℝ) p ≤ (n:ℝ) := min_le_left _ _
    have hmp : min (n:ℝ) p ≤ p := min_le_right _ _
    have ht0 : 0 < t := by
      rw [htdef]; exact div_pos (mul_pos hmin0 h1η) two_pos
    have htn : t < (n:ℝ) := by
      rw [htdef]
      have ha : min (n:ℝ) p * (1 - η) ≤ (n:ℝ) * (1 - η) :=
        mul_le_mul_of_nonneg_right hmn h1η.le
      have hb : (n:ℝ) * (1 - η) ≤ (n:ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
    have htp : t < p := by
      rw [htdef]
      have ha : min (n:ℝ) p * (1 - η) ≤ p * (1 - η) :=
        mul_le_mul_of_nonneg_right hmp h1η.le
      have hb : p * (1 - η) ≤ p * 1 := mul_le_mul_of_nonneg_left (by linarith) hp0.le
      linarith
    obtain ⟨Nt, hNt0, hNt⟩ := hpart2 t ht0 htn
    have hcamp := hNt ε Ω Ω'' Ω' u g hε0 hε1 hΩ hΩ'' hΩ' hΩ'ne hbdd hclΩ' hclΩ'' hsep1 hsep2
      hu hMb hWb hbundle
    -- Ω' has finite measure
    obtain ⟨rB, _hrB, hBall⟩ := (hbdd.subset hsub).subset_closedBall_lt 0 0
    have hΩ'fin : volume Ω' ≠ ⊤ :=
      ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hBall)
    have hΩ'R : (0:ℝ) ≤ (volume Ω').toReal := ENNReal.toReal_nonneg
    set N₃ : ℝ := M * (volume Ω').toReal ^ (1/q) with hN₃def
    have hN₃0 : 0 ≤ N₃ := mul_nonneg hM (Real.rpow_nonneg hΩ'R _)
    have hN₃pow : N₃ ^ q = M ^ q * (volume Ω').toReal := by
      rw [hN₃def, Real.mul_rpow hM (Real.rpow_nonneg hΩ'R _), ← Real.rpow_mul hΩ'R,
        one_div, inv_mul_cancel₀ (ne_of_gt hq0), Real.rpow_one]
    -- the λ = 0 Morrey datum for u on Ω'
    have hmor0 : MorreyBoundOn n q 0 Ω' u N₃ := by
      refine ⟨hcamp.1, ?_⟩
      intro x hx ρ hρ _hρd
      rw [Real.rpow_zero, mul_one, hN₃pow]
      have hfin : IsFiniteMeasure (volume.restrict (Ω' ∩ Metric.ball x ρ)) :=
        ⟨by rw [Measure.restrict_apply_univ]
            exact lt_of_le_of_lt (measure_mono Set.inter_subset_left)
              (lt_of_le_of_ne le_top hΩ'fin)⟩
      have hpt : ∀ᵐ y ∂(volume.restrict (Ω' ∩ Metric.ball x ρ)), |u y| ^ q ≤ M ^ q := by
        have hsubΩ : Ω' ∩ Metric.ball x ρ ⊆ Ω := fun y hy => hΩ''Ω (hsub hy.1)
        have h0 := hMb.filter_mono (ae_mono (Measure.restrict_mono hsubΩ le_rfl))
        filter_upwards [h0] with y hy
        exact Real.rpow_le_rpow (abs_nonneg _) hy hq0.le
      have h1 := integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (abs_nonneg _) _)
        (integrable_const (M ^ q)) hpt
      rw [integral_const, Measure.real_def, Measure.restrict_apply_univ, smul_eq_mul] at h1
      refine le_trans h1 ?_
      calc (volume (Ω' ∩ Metric.ball x ρ)).toReal * M ^ q
          ≤ (volume Ω').toReal * M ^ q :=
            mul_le_mul_of_nonneg_right
              (ENNReal.toReal_mono hΩ'fin (measure_mono Set.inter_subset_left))
              (Real.rpow_nonneg hM _)
        _ = M ^ q * (volume Ω').toReal := mul_comm _ _
    -- enlarge both bounds to a common constant
    set N : ℝ := max Nt N₃ with hNdef
    have hN0 : 0 ≤ N := le_trans hNt0 (le_max_left _ _)
    have hcampN : CampanatoBoundOn n q ((n:ℝ) + (1 - t/p) * q) Ω' u N := by
      refine ⟨hcamp.1, fun x hx ρ hρ hρd => le_trans (hcamp.2 x hx ρ hρ hρd) ?_⟩
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hNt0 (le_max_left _ _) hq0.le)
        (Real.rpow_nonneg hρ.le _)
    have hmorN : MorreyBoundOn n q 0 Ω' u N := by
      refine ⟨hmor0.1, fun x hx ρ hρ hρd => le_trans (hmor0.2 x hx ρ hρ hρd) ?_⟩
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hN₃0 (le_max_right _ _) hq0.le)
        (Real.rpow_nonneg hρ.le _)
    -- the cited Campanato embedding
    have htp1 : t / p < 1 := by rw [div_lt_one hp0]; exact htp
    have htp0 : 0 < t / p := div_pos ht0 hp0
    have hlow : (n:ℝ) < (n:ℝ) + (1 - t/p) * q := by
      have h1 : 0 < (1 - t/p) * q := mul_pos (by linarith) hq0
      linarith
    have hhigh : (n:ℝ) + (1 - t/p) * q < (n:ℝ) + q := by
      have h1 : (1 - t/p) * q < 1 * q := mul_lt_mul_of_pos_right (by linarith) hq0
      rw [one_mul] at h1
      linarith
    obtain ⟨Nh, hNh0, hemb⟩ := hCE hLip ((n:ℝ) + (1 - t/p) * q) hlow hhigh N hN0
    obtain ⟨w, hwae, hwhol, hwlip⟩ := hemb u hcampN hmorN
    have hexp : ((n:ℝ) + (1 - t/p) * q - (n:ℝ)) / q = 1 - t/p := by
      rw [add_sub_cancel_left, mul_div_assoc, div_self (ne_of_gt hq0), mul_one]
    rw [hexp] at hwhol hwlip
    -- lower the exponent from 1 - t/p to η
    have hη' : η ≤ 1 - t / p := by
      have ha : min (n:ℝ) p * (1 - η) ≤ p * (1 - η) :=
        mul_le_mul_of_nonneg_right hmp h1η.le
      have hnn : (0:ℝ) ≤ min (n:ℝ) p * (1 - η) := mul_nonneg hmin0.le h1η.le
      have h1 : t ≤ p * (1 - η) := by rw [htdef]; linarith
      have hcm : p * (1 - η) = (1 - η) * p := mul_comm _ _
      have h2 : t / p ≤ 1 - η := by rw [div_le_iff₀ hp0]; linarith
      linarith
    have hbddcl : Bornology.IsBounded (closure Ω') := hbdd.subset hclΩ'
    refine ⟨w, hwae, hwhol.1, ?_⟩
    set Δ : ℝ := Metric.diam (closure Ω') with hΔdef
    have hC0 : (0:ℝ) ≤ Nh * max 1 (Δ ^ (1 - t/p - η)) :=
      mul_nonneg hNh0 (le_trans zero_le_one (le_max_left _ _))
    refine ⟨Nh * max 1 (Δ ^ (1 - t/p - η)), hC0, ?_⟩
    intro x hx y hy
    rcases eq_or_ne x y with rfl | hxy
    · rw [sub_self, abs_zero]
      exact mul_nonneg hC0 (Real.rpow_nonneg dist_nonneg _)
    · have hdpos : 0 < dist x y := dist_pos.2 hxy
      have hdΔ : dist x y ≤ Δ := Metric.dist_le_diam_of_mem hbddcl hx hy
      have hsplit : dist x y ^ (1 - t/p) = dist x y ^ η * dist x y ^ (1 - t/p - η) := by
        rw [← Real.rpow_add hdpos]
        congr 1
        ring
      have hfac : dist x y ^ (1 - t/p - η) ≤ max 1 (Δ ^ (1 - t/p - η)) :=
        le_trans (Real.rpow_le_rpow hdpos.le hdΔ (by linarith)) (le_max_right _ _)
      calc |w x - w y| ≤ Nh * dist x y ^ (1 - t/p) := hwlip x hx y hy
        _ = Nh * (dist x y ^ η * dist x y ^ (1 - t/p - η)) := by rw [hsplit]
        _ ≤ Nh * (dist x y ^ η * max 1 (Δ ^ (1 - t/p - η))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hfac (Real.rpow_nonneg hdpos.le _)) hNh0
        _ = Nh * max 1 (Δ ^ (1 - t/p - η)) * dist x y ^ η := by ring
