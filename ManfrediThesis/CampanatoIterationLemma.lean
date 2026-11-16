import ManfrediThesis.Preamble
open MeasureTheory

/-- Lemma 4.3: the iteration lemma of Campanato and Morrey. -/
theorem CampanatoIterationLemma :
    ∀ A α β : ℝ, 0 < A → 0 < α → 0 < β → β < α →
      ∃ δ₀ C : ℝ, 0 < δ₀ ∧ 0 < C ∧
        ∀ (δ B R₀ : ℝ) (φ : ℝ → ℝ), 0 ≤ δ → δ < δ₀ → 0 < B → 0 < R₀ →
          (∀ t : ℝ, 0 ≤ φ t) →
          (∀ s t : ℝ, s ≤ t → φ s ≤ φ t) →
          (∀ ρ R : ℝ, 0 < ρ → ρ ≤ R → R ≤ R₀ →
            φ ρ ≤ A * ((ρ / R) ^ α + δ) * φ R + B * R ^ β) →
          ∀ ρ R : ℝ, 0 < ρ → ρ ≤ R → R ≤ R₀ →
            φ ρ ≤ C * (ρ / R) ^ β * (φ R + B * R ^ β) := by
  intro A α β hA hα hβ hβα
  -- Choice of the parameters: γ = (α+β)/2, κ = min {1/2, (2A)^(-1/(α-γ))}.
  obtain ⟨γ, hγ⟩ : ∃ t : ℝ, t = (α + β) / 2 := ⟨_, rfl⟩
  have hβγ : β < γ := by rw [hγ]; linarith
  have hγα : γ < α := by rw [hγ]; linarith
  have hαγ : 0 < α - γ := by linarith
  have h2A : 0 < 2 * A := by linarith
  obtain ⟨κ, hκ⟩ : ∃ t : ℝ, t = min (1 / 2) ((2 * A) ^ (-(1 / (α - γ)))) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by
    rw [hκ]
    exact lt_min (by norm_num) (Real.rpow_pos_of_pos h2A _)
  have hκ1 : κ < 1 := by
    have h1 : κ ≤ 1 / 2 := by rw [hκ]; exact min_le_left _ _
    linarith
  -- A natural power of κ raised to a real exponent.
  have hκpow : ∀ (s : ℝ) (k : ℕ), (κ ^ k) ^ s = (κ ^ s) ^ k := by
    intro s k
    rw [← Real.rpow_natCast κ k, ← Real.rpow_mul hκ0.le,
      ← Real.rpow_natCast (κ ^ s) k, ← Real.rpow_mul hκ0.le]
    congr 1
    ring
  -- (∗) : 2A κ^α ≤ κ^γ, from κ ≤ (2A)^(-1/(α-γ)).
  have hstar : 2 * A * κ ^ α ≤ κ ^ γ := by
    have hγpos : (0:ℝ) < κ ^ γ := Real.rpow_pos_of_pos hκ0 γ
    have h2 : κ ≤ (2 * A) ^ (-(1 / (α - γ))) := by rw [hκ]; exact min_le_right _ _
    have h3 : κ ^ (α - γ) ≤ ((2 * A) ^ (-(1 / (α - γ)))) ^ (α - γ) :=
      Real.rpow_le_rpow hκ0.le h2 hαγ.le
    rw [← Real.rpow_mul h2A.le, show -(1 / (α - γ)) * (α - γ) = -1 by field_simp,
      Real.rpow_neg_one] at h3
    have h4 : 2 * A * κ ^ (α - γ) ≤ 1 := by
      have h5 := mul_le_mul_of_nonneg_left h3 h2A.le
      rwa [mul_inv_cancel₀ h2A.ne'] at h5
    have h6 : κ ^ α = κ ^ (α - γ) * κ ^ γ := by
      rw [← Real.rpow_add hκ0]
      congr 1
      ring
    rw [h6]
    nlinarith [hγpos, h4]
  -- b = κ^β, c = κ^γ, M = max {1, 1/(b-c)}; then C = M/b is the lemma's constant.
  obtain ⟨b, hb⟩ : ∃ t : ℝ, t = κ ^ β := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ t : ℝ, t = κ ^ γ := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; exact Real.rpow_pos_of_pos hκ0 β
  have hc0 : 0 < c := by rw [hc]; exact Real.rpow_pos_of_pos hκ0 γ
  have hbne : b ≠ 0 := hb0.ne'
  have hcb : c < b := by
    rw [hb, hc]
    exact Real.rpow_lt_rpow_of_exponent_gt hκ0 hκ1 hβγ
  obtain ⟨M, hM⟩ : ∃ t : ℝ, t = max 1 (1 / (b - c)) := ⟨_, rfl⟩
  have hM1 : (1:ℝ) ≤ M := by rw [hM]; exact le_max_left _ _
  have hM0 : (0:ℝ) < M := lt_of_lt_of_le one_pos hM1
  -- The single inequality that drives the induction: (b-c)M ≥ 1.
  have hkey : (1:ℝ) ≤ (b - c) * M := by
    have h1 : 1 / (b - c) ≤ M := by rw [hM]; exact le_max_right _ _
    rw [mul_comm]
    exact (div_le_iff₀ (by linarith)).mp h1
  refine ⟨κ ^ α, M / b, Real.rpow_pos_of_pos hκ0 α, div_pos hM0 hb0, ?_⟩
  intro δ B R₀ φ hδ0 hδ hB hR₀ hφ0 hmono hhyp ρ R hρ hρR hRR₀
  have hR : 0 < R := lt_of_lt_of_le hρ hρR
  have hRβ : (0:ℝ) < R ^ β := Real.rpow_pos_of_pos hR β
  have hRβne : (R:ℝ) ^ β ≠ 0 := hRβ.ne'
  have hDpos : (0:ℝ) < B * R ^ β := mul_pos hB hRβ
  have hsum0 : (0:ℝ) ≤ φ R + B * R ^ β := by linarith [hφ0 R]
  -- Step 1: one step of the iteration, at any admissible radius.
  have hstep : ∀ r : ℝ, 0 < r → r ≤ R₀ → φ (κ * r) ≤ c * φ r + B * r ^ β := by
    intro r hr hrR₀
    have hκr : κ * r ≤ r := by nlinarith
    have h1 := hhyp (κ * r) r (by positivity) hκr hrR₀
    rw [mul_div_assoc, div_self hr.ne', mul_one] at h1
    have h3 : A * (κ ^ α + δ) ≤ c := by
      rw [hc]
      nlinarith [hstar, mul_pos hA (sub_pos.mpr hδ)]
    have h4 := mul_le_mul_of_nonneg_right h3 (hφ0 r)
    linarith
  -- (∗∗) : the one-step estimate along the geometric sequence of radii.
  have hrad : ∀ k : ℕ, κ ^ k * R ≤ R := by
    intro k
    nlinarith [pow_le_one₀ hκ0.le hκ1.le (n := k), hR]
  have hradpos : ∀ k : ℕ, 0 < κ ^ k * R := fun k => mul_pos (pow_pos hκ0 k) hR
  have hrec : ∀ k : ℕ,
      φ (κ ^ (k + 1) * R) ≤ c * φ (κ ^ k * R) + B * R ^ β * b ^ k := by
    intro k
    have h1 := hstep (κ ^ k * R) (hradpos k) (le_trans (hrad k) hRR₀)
    have h2 : κ * (κ ^ k * R) = κ ^ (k + 1) * R := by ring
    have h3 : B * (κ ^ k * R) ^ β = B * R ^ β * b ^ k := by
      rw [Real.mul_rpow (pow_nonneg hκ0.le k) hR.le, hκpow β k, hb]
      ring
    rw [h2, h3] at h1
    exact h1
  -- (‡) : the iterated estimate, by induction on k.
  have hiter : ∀ k : ℕ, φ (κ ^ k * R) ≤ b ^ k * M * (φ R + B * R ^ β) := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, one_mul]
      have h0 : 0 ≤ (M - 1) * (φ R + B * R ^ β) := mul_nonneg (by linarith) hsum0
      linarith [hφ0 R, hDpos]
    | succ k ih =>
      have hbk : (0:ℝ) < b ^ k := pow_pos hb0 k
      have h2 : 0 ≤ ((b - c) * M - 1) * (φ R + B * R ^ β) :=
        mul_nonneg (by linarith) hsum0
      have h3 : B * R ^ β ≤ (b - c) * M * (φ R + B * R ^ β) := by
        linarith [hφ0 R]
      have h4 : B * R ^ β * b ^ k ≤ (b - c) * M * (φ R + B * R ^ β) * b ^ k :=
        mul_le_mul_of_nonneg_right h3 hbk.le
      have h5 : c * φ (κ ^ k * R) ≤ c * (b ^ k * M * (φ R + B * R ^ β)) :=
        mul_le_mul_of_nonneg_left ih hc0.le
      calc φ (κ ^ (k + 1) * R)
          ≤ c * φ (κ ^ k * R) + B * R ^ β * b ^ k := hrec k
        _ ≤ c * (b ^ k * M * (φ R + B * R ^ β))
            + (b - c) * M * (φ R + B * R ^ β) * b ^ k := by linarith
        _ = b ^ (k + 1) * M * (φ R + B * R ^ β) := by ring
  -- Step 3: from the geometric radii to all radii.
  have hex : ∃ k : ℕ, κ ^ (k + 1) * R < ρ := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hρ hR) hκ1
    refine ⟨m, ?_⟩
    have h1 : κ ^ (m + 1) ≤ κ ^ m := by
      rw [pow_succ]
      nlinarith [pow_pos hκ0 m]
    have h2 : κ ^ m * R < ρ := (lt_div_iff₀ hR).mp hm
    nlinarith [hR]
  classical
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, κ ^ (k + 1) * R < ρ ∧ ρ ≤ κ ^ k * R := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, pow_zero, one_mul]
      exact hρR
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
      have h1 := Nat.find_min hex (m := m) (by omega)
      rw [hm]
      exact not_lt.mp h1
  have hbpow : b ^ k ≤ 1 / b * (ρ / R) ^ β := by
    have h1 : κ ^ k < ρ / (κ * R) := by
      rw [lt_div_iff₀ (by positivity)]
      calc κ ^ k * (κ * R) = κ ^ (k + 1) * R := by ring
        _ < ρ := hk1
    have h2 : (κ ^ k) ^ β ≤ (ρ / (κ * R)) ^ β :=
      Real.rpow_le_rpow (by positivity) h1.le hβ.le
    rw [hκpow β k, ← hb] at h2
    have h3 : (ρ / (κ * R)) ^ β = 1 / b * (ρ / R) ^ β := by
      rw [Real.div_rpow hρ.le (by positivity), Real.mul_rpow hκ0.le hR.le,
        Real.div_rpow hρ.le hR.le, ← hb]
      field_simp
    rw [h3] at h2
    exact h2
  calc φ ρ ≤ φ (κ ^ k * R) := hmono ρ (κ ^ k * R) hk2
    _ ≤ b ^ k * M * (φ R + B * R ^ β) := hiter k
    _ ≤ 1 / b * (ρ / R) ^ β * M * (φ R + B * R ^ β) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbpow hM0.le) hsum0
    _ = M / b * (ρ / R) ^ β * (φ R + B * R ^ β) := by ring
