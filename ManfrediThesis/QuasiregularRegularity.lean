import ManfrediThesis.Preamble
import ManfrediThesis.IsBoundedLipschitzDomain
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.CitedDirichletW1p
import ManfrediThesis.CitedDirichletHolder
import ManfrediThesis.CitedHolderOscillationMinimum
import ManfrediThesis.CitedCampanatoEmbedding
import ManfrediThesis.IsQuasiregularOn
import ManfrediThesis.IsDistortionMatrix
import ManfrediThesis.ModelQuasiregularIdentity
import ManfrediThesis.CitedQuasiregularBasics
import ManfrediThesis.TauPropertiesQuasiregular
import ManfrediThesis.MemHolderOn
import ManfrediThesis.MemC1HolderOn
import ManfrediThesis.MinimumMorreyRegularity
import ManfrediThesis.MinimumGradientHolder
import ManfrediThesis.QuasiregularConstantCase
import ManfrediThesis.QuasiregularLocalVariationalData
open MeasureTheory

/-- Theorem 7: Hölder and `C^{1+β}` regularity of a quasiregular mapping whose
distortion matrix is continuous, respectively Hölder continuous. -/
theorem QuasiregularRegularity :
    ∀ (n : ℕ) (K δ : ℝ), 2 ≤ n → 1 ≤ K → 0 < δ → δ < 1 →
      CitedSobolevPoincareBall n →
      (∀ (ε' γ₀' γ₁' : ℝ) (Ω₀ : Set (EuclideanSpace ℝ (Fin n)))
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → IsOpen Ω₀ →
        CitedRegularityEpsPos n (n : ℝ) ε' γ₀' γ₁' Ω₀ A') →
      (∀ (ε' γ₀' γ₁' : ℝ)
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → CitedDirichletW1p n (n : ℝ) ε' γ₀' γ₁' A') →
      (∀ (ε' γ₀' γ₁' : ℝ)
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → CitedDirichletHolder n (n : ℝ) ε' γ₀' γ₁' A') →
      CitedHolderOscillationMinimum n (n : ℝ) →
      (∀ (y : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
        CitedCampanatoEmbedding n ((n : ℝ) / ((n : ℝ) - 1)) (Metric.ball y ρ)) →
      ∃ β : ℝ, 0 < β ∧
        ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
          (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (G : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (τ : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ),
          IsOpen Ω → IsConnected Ω →
          IsQuasiregularOn n K Ω F G → IsDistortionMatrix n Ω G τ →
          (∀ Ω₀ : Set (EuclideanSpace ℝ (Fin n)), IsOpen Ω₀ → Ω₀ ⊆ Ω →
            CitedQuasiregularBasics n K Ω₀ F G τ) →
          ((∃ τ' : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ,
              (∀ᵐ x ∂(volume.restrict Ω), τ x = τ' x) ∧
                ∀ i j : Fin n, ContinuousOn (fun x => τ' x i j) Ω) →
            ∀ (Ω' : Set (EuclideanSpace ℝ (Fin n))) (η : ℝ),
              IsOpen Ω' → Ω'.Nonempty → Bornology.IsBounded Ω' → closure Ω' ⊆ Ω →
              IsBoundedLipschitzDomain n Ω' →
              CitedCampanatoEmbedding n (n : ℝ) Ω' →
              CitedCampanatoEmbedding n ((n : ℝ) / ((n : ℝ) - 1)) Ω' →
              0 ≤ η → η < 1 →
              ∀ i : Fin n, ∃ w : EuclideanSpace ℝ (Fin n) → ℝ,
                (∀ᵐ x ∂(volume.restrict Ω'), F x i = w x) ∧
                  MemHolderOn n η (closure Ω') w)
          ∧ ((∃ (τ' : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) (C : ℝ),
              (∀ᵐ x ∂(volume.restrict Ω), τ x = τ' x) ∧ 0 ≤ C ∧
                ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ i j : Fin n,
                  |τ' x i j - τ' y i j| ≤ C * dist x y ^ δ) →
            ∀ Ω' : Set (EuclideanSpace ℝ (Fin n)),
              IsOpen Ω' → Ω'.Nonempty → Bornology.IsBounded Ω' → closure Ω' ⊆ Ω →
              IsBoundedLipschitzDomain n Ω' →
              CitedCampanatoEmbedding n (n : ℝ) Ω' →
              CitedCampanatoEmbedding n ((n : ℝ) / ((n : ℝ) - 1)) Ω' →
              ∀ i : Fin n, ∃ (w : EuclideanSpace ℝ (Fin n) → ℝ)
                (gw : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
                (∀ᵐ x ∂(volume.restrict Ω'), F x i = w x) ∧
                  (∀ᵐ x ∂(volume.restrict Ω'), G i x = gw x) ∧
                    MemC1HolderOn n β Ω' (closure Ω') w gw) := by
  intro n K δ hn hK hδ0 hδ1 hSP hC1 hC2 hC3 hC4 hC5ball
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnp : (1:ℝ) < (n:ℝ) := by linarith
  have hK0 : (0:ℝ) < K := by linarith
  -- (0a)
  obtain ⟨lam, Lam, hlam, hlamLam, hTau⟩ := TauPropertiesQuasiregular n K hn hK
  -- (0b)
  have hKn1 : (1:ℝ) ≤ K ^ ((n:ℝ) - 1) := by
    have h := Real.rpow_le_rpow_of_exponent_le hK (show (0:ℝ) ≤ (n:ℝ) - 1 by linarith)
    rwa [Real.rpow_zero] at h
  have hν₀0 : (0:ℝ) < (n:ℝ) / K := div_pos (by linarith) hK0
  have hν₀le : (n:ℝ) / K ≤ (n:ℝ) := by
    rw [div_le_iff₀ hK0]
    nlinarith
  have hprod1 : (1:ℝ) ≤ ((n:ℝ) - 1) * K ^ ((n:ℝ) - 1) := by
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ ((n:ℝ) - 1) * K ^ ((n:ℝ) - 1) :=
          mul_le_mul (by linarith) hKn1 (by norm_num) (by linarith)
  have hν₁ge : (2:ℝ) * (n:ℝ) ≤ 2 * (n:ℝ) * ((n:ℝ) - 1) * K ^ ((n:ℝ) - 1) := by
    calc (2:ℝ) * (n:ℝ) = 2 * (n:ℝ) * 1 := by ring
      _ ≤ 2 * (n:ℝ) * (((n:ℝ) - 1) * K ^ ((n:ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left hprod1 (by linarith)
      _ = 2 * (n:ℝ) * ((n:ℝ) - 1) * K ^ ((n:ℝ) - 1) := by ring
  have hν₀ν₁ : (n:ℝ) / K < 2 * (n:ℝ) * ((n:ℝ) - 1) * K ^ ((n:ℝ) - 1) := by
    linarith
  have hν₁half : (n:ℝ) * ((n:ℝ) - 1) * K ^ ((n:ℝ) - 1)
      ≤ 2 * (n:ℝ) * ((n:ℝ) - 1) * K ^ ((n:ℝ) - 1) := by
    have h0 : (0:ℝ) ≤ (n:ℝ) * ((n:ℝ) - 1) * K ^ ((n:ℝ) - 1) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (Real.rpow_nonneg hK0.le _)
    linarith
  -- (0c)
  obtain ⟨lam₀, hlam₀0, hlam₀p, hMGH⟩ :=
    MinimumGradientHolder n (n:ℝ) lam Lam 1 ((n:ℝ)/K)
      (2*(n:ℝ)*((n:ℝ)-1)*K^((n:ℝ)-1)) δ hn hnp hlam hlamLam one_pos hν₀0 hν₀ν₁ hδ0
      hSP hC1 hC2 hC3 hC5ball
  refine ⟨lam₀ / (n:ℝ), by positivity, ?_⟩
  intro Ω F G τ hΩ hΩconn hQR hDist hC7
  refine ⟨?_, ?_⟩
  · -- conclusion (i)
    intro hτcont Ω' η hΩ' hΩ'ne hΩ'bd hclΩ' hLip hCampn hCampq hη0 hη1 i
    obtain ⟨τ', hττ', hτ'cont⟩ := hτcont
    have hΩ'Ω : Ω' ⊆ Ω := subset_trans subset_closure hclΩ'
    by_cases hconst : ∃ c : EuclideanSpace ℝ (Fin n),
        ∀ᵐ x ∂(volume.restrict Ω), F x = c
    · -- Part 1: the constant branch
      obtain ⟨c, hc⟩ := hconst
      refine ⟨fun _ => c i, ?_, continuousOn_const, 0, le_rfl, ?_⟩
      · filter_upwards [ae_restrict_of_ae_restrict_of_subset hΩ'Ω hc] with x hx
        rw [hx]
      · intro x _ y _
        simp
    · -- Parts 2, 3 and 4
      have hTauΩ := hTau Ω F G τ hΩ hQR hDist (hC7 Ω hΩ (subset_refl Ω)) hconst
      obtain ⟨Ω'', fdens, σ, M, Wn, d, hΩ''open, hclΩ'Ω'', hclΩ''Ω, hsep, hd0, hM0,
          hWn0, hF123, hW1p, hubd, hWbd, hLM, -⟩ :=
        QuasiregularLocalVariationalData n K lam Lam ((n:ℝ)/K)
          (2*(n:ℝ)*((n:ℝ)-1)*K^((n:ℝ)-1)) hn hK hlam hlamLam hν₀0 le_rfl hν₁half
          Ω Ω' F G τ τ' i hΩ hΩ' hΩ'ne hΩ'bd hclΩ' hQR hDist hC7 hconst hττ' hτ'cont
          hTauΩ
      obtain ⟨N₁, N₂, hN₁, hN₂, hthm3⟩ :=
        MinimumMorreyRegularity n (n:ℝ) ((n:ℝ)/2) lam Lam 1 ((n:ℝ)/K)
          (2*(n:ℝ)*((n:ℝ)-1)*K^((n:ℝ)-1)) d M Wn σ hn hnp (by linarith) (by linarith)
          hlam hlamLam one_pos hν₀0 hν₀ν₁ hd0 hM0 hWn0 hSP hC1 hC2 hC3
      obtain ⟨-, -, hiii⟩ := hthm3 0 Ω'' Ω' fdens (fun x => F x i) (G i) le_rfl
        zero_le_one hΩ''open hΩ' hΩ'ne hΩ'bd hclΩ'Ω'' hLip hsep hCampq hC4 hF123
        hW1p hubd hWbd hLM
      exact hiii η hη0 hη1
  · -- conclusion (ii)
    intro hτhol Ω' hΩ' hΩ'ne hΩ'bd hclΩ' hLip hCampn hCampq i
    obtain ⟨τ', C, hττ', hC0, hτ'hol⟩ := hτhol
    have hΩ'Ω : Ω' ⊆ Ω := subset_trans subset_closure hclΩ'
    by_cases hconst : ∃ c : EuclideanSpace ℝ (Fin n),
        ∀ᵐ x ∂(volume.restrict Ω), F x = c
    · -- Part 1: the constant branch
      obtain ⟨c, hc⟩ := hconst
      have hG0 := QuasiregularConstantCase n K hn Ω F G c hΩ hQR hc i
      refine ⟨fun _ => c i, fun _ => 0, ?_, ?_, ?_, continuousOn_const, 0, le_rfl, ?_⟩
      · filter_upwards [ae_restrict_of_ae_restrict_of_subset hΩ'Ω hc] with x hx
        rw [hx]
      · exact ae_restrict_of_ae_restrict_of_subset hΩ'Ω hG0
      · intro x _
        refine ⟨differentiableAt_const _, ?_⟩
        intro j
        simp
      · intro x _ y _
        simp
    · -- Parts 2, 3 and 5
      have hτ'cont : ∀ j k : Fin n, ContinuousOn (fun x => τ' x j k) Ω := by
        intro j k x hx
        rw [Metric.continuousWithinAt_iff]
        intro e he
        rcases eq_or_lt_of_le hC0 with hC | hC
        · refine ⟨1, one_pos, fun y hy _ => ?_⟩
          have h1 := hτ'hol y hy x hx j k
          rw [← hC, zero_mul] at h1
          rw [Real.dist_eq]
          linarith [abs_nonneg (τ' y j k - τ' x j k)]
        · refine ⟨(e / C) ^ (1/δ), by positivity, fun y hy hd => ?_⟩
          have h1 := hτ'hol y hy x hx j k
          rw [Real.dist_eq]
          refine lt_of_le_of_lt h1 ?_
          have h2 : dist y x ^ δ < e / C := by
            have h3 := Real.rpow_lt_rpow dist_nonneg hd hδ0
            rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hδ0.ne',
              Real.rpow_one] at h3
          calc C * dist y x ^ δ < C * (e / C) :=
                mul_lt_mul_of_pos_left h2 hC
            _ = e := by field_simp
      have hTauΩ := hTau Ω F G τ hΩ hQR hDist (hC7 Ω hΩ (subset_refl Ω)) hconst
      obtain ⟨Ω'', fdens, σ, M, Wn, d, hΩ''open, hclΩ'Ω'', hclΩ''Ω, hsep, hd0, hM0,
          hWn0, hF123, hW1p, hubd, hWbd, hLM, hF4gen⟩ :=
        QuasiregularLocalVariationalData n K lam Lam ((n:ℝ)/K)
          (2*(n:ℝ)*((n:ℝ)-1)*K^((n:ℝ)-1)) hn hK hlam hlamLam hν₀0 le_rfl hν₁half
          Ω Ω' F G τ τ' i hΩ hΩ' hΩ'ne hΩ'bd hclΩ' hQR hDist hC7 hconst hττ' hτ'cont
          hTauΩ
      obtain ⟨cσ, hcσ0, hF4⟩ := hF4gen δ C hδ0 hδ1 hC0 hτ'hol
      obtain ⟨N, hN0, hMGH'⟩ := hMGH cσ d M Wn σ hcσ0 hd0 hM0 hWn0
      obtain ⟨-, hii⟩ := hMGH' 0 Ω'' Ω' fdens (fun x => F x i) (G i) le_rfl zero_le_one
        hΩ''open hΩ' hΩ'ne hΩ'bd hclΩ'Ω'' hLip hsep hCampn hCampq hC4 hF123 hF4
        hW1p hubd hWbd hLM
      obtain ⟨w, gw, hw1, hw2, hw3⟩ := hii
      exact ⟨w, gw, hw1, hw2, hw3⟩
