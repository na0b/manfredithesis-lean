import ManfrediThesis.Preamble
import ManfrediThesis.IsQuasiregularOn
import ManfrediThesis.IsDistortionMatrix
import ManfrediThesis.CitedQuasiregularBasics
import Mathlib.Analysis.Matrix.Spectrum
open MeasureTheory

/-- The properties of the distortion matrix `τ(x)` used in Theorem 7: symmetry,
`det τ = 1`, the two-sided eigenvalue bounds, and the resulting growth bounds
for the functional `(τ(x)h, h)^{n/2}`. -/
theorem TauPropertiesQuasiregular :
    ∀ (n : ℕ) (K : ℝ), 2 ≤ n → 1 ≤ K →
      ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
        ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
          (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (G : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (τ : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ),
          IsOpen Ω →
          IsQuasiregularOn n K Ω F G → IsDistortionMatrix n Ω G τ →
          CitedQuasiregularBasics n K Ω F G τ →
          (¬ ∃ c : EuclideanSpace ℝ (Fin n),
            ∀ᵐ x ∂(volume.restrict Ω), F x = c) →
          ∀ᵐ x ∂(volume.restrict Ω),
            (τ x).IsSymm ∧ (τ x).det = 1 ∧
              (∀ ξ : EuclideanSpace ℝ (Fin n),
                K ^ (-(2 : ℝ) / (n : ℝ)) * ‖ξ‖ ^ 2 ≤ ∑ a, ∑ b, τ x a b * ξ a * ξ b ∧
                  (∑ a, ∑ b, τ x a b * ξ a * ξ b)
                    ≤ K ^ (2 * ((n : ℝ) - 1) / (n : ℝ)) * ‖ξ‖ ^ 2) ∧
              (∀ h : EuclideanSpace ℝ (Fin n),
                lam * ‖h‖ ^ (n : ℝ) ≤ (∑ a, ∑ b, τ x a b * h a * h b) ^ ((n : ℝ) / 2) ∧
                  (∑ a, ∑ b, τ x a b * h a * h b) ^ ((n : ℝ) / 2)
                    ≤ Lam * ‖h‖ ^ (n : ℝ)) := by
  open Matrix in
  intro n K hn hK
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hnR2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hrpow2 : ∀ x : ℝ, x ^ ((2 : ℝ)) = x ^ 2 := fun x => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  -- Steps 1-4 of the proof, at a single point `x` where `J > 0` and (5.10) hold.
  -- `M` is `DF(x)`, `T` is `τ(x)` and `J` is the Jacobian `det M`.
  have hcore : ∀ (J : ℝ) (M T : Matrix (Fin n) (Fin n) ℝ), 0 < J → M.det = J →
      T * (Mᵀ * M) = (J ^ ((2 : ℝ) / (n : ℝ))) • (1 : Matrix (Fin n) (Fin n) ℝ) →
      (∀ ξ : EuclideanSpace ℝ (Fin n),
        (∑ i, (∑ j, M i j * ξ j) ^ 2) ^ ((n : ℝ) / 2) ≤ K * J * ‖ξ‖ ^ (n : ℝ)) →
      T.IsSymm ∧ T.det = 1 ∧ ∀ ξ : EuclideanSpace ℝ (Fin n),
        K ^ (-(2 : ℝ) / (n : ℝ)) * ‖ξ‖ ^ 2 ≤ ∑ a, ∑ b, T a b * ξ a * ξ b ∧
          (∑ a, ∑ b, T a b * ξ a * ξ b)
            ≤ K ^ (2 * ((n : ℝ) - 1) / (n : ℝ)) * ‖ξ‖ ^ 2 := by
    intro J M T hJ hdet hTeq h510
    have hKJ : (0 : ℝ) < K * J := mul_pos hK0 hJ
    set c : ℝ := J ^ ((2 : ℝ) / (n : ℝ)) with hcdef
    set S : ℝ := (K * J) ^ ((2 : ℝ) / (n : ℝ)) with hSdef
    have hc : 0 < c := Real.rpow_pos_of_pos hJ _
    -- Step 0 arithmetic: the three exponent identities used below.
    have hKlS : K ^ (-(2 : ℝ) / (n : ℝ)) * S = c := by
      rw [hSdef, Real.mul_rpow hK0.le hJ.le, ← mul_assoc, ← Real.rpow_add hK0,
        show -(2 : ℝ) / (n : ℝ) + (2 : ℝ) / (n : ℝ) = 0 by ring, Real.rpow_zero, one_mul, hcdef]
    have hSn : S ^ (n - 1) = (K * J) ^ ((2 : ℝ) * ((n : ℝ) - 1) / (n : ℝ)) := by
      rw [hSdef, ← Real.rpow_natCast ((K * J) ^ ((2 : ℝ) / (n : ℝ))) (n - 1),
        ← Real.rpow_mul hKJ.le]
      congr 1
      rw [Nat.cast_sub hn1, Nat.cast_one]
      ring
    have hJ2 : J ^ ((2 : ℝ)) = J ^ 2 := hrpow2 J
    have hcSn : c * S ^ (n - 1) = K ^ (2 * ((n : ℝ) - 1) / (n : ℝ)) * J ^ 2 := by
      rw [hSn, Real.mul_rpow hK0.le hJ.le, hcdef,
        mul_comm (K ^ (2 * ((n : ℝ) - 1) / (n : ℝ))) (J ^ (2 * ((n : ℝ) - 1) / (n : ℝ))),
        ← mul_assoc, ← Real.rpow_add hJ,
        show (2 : ℝ) / (n : ℝ) + 2 * ((n : ℝ) - 1) / (n : ℝ) = 2 by field_simp; ring,
        hJ2, mul_comm]
    -- Step 2: `A = MᵀM` is symmetric with `det A = J²`, hence invertible.
    set A : Matrix (Fin n) (Fin n) ℝ := Mᵀ * M with hAdef
    have hAsymm : Aᵀ = A := isSymm_transpose_mul_self M
    have hA : A.IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      exact hAsymm
    have hdetA : A.det = J ^ 2 := by
      rw [hAdef, det_mul, det_transpose, hdet]; ring
    have hAunit : IsUnit A.det := by
      rw [hdetA]; exact isUnit_iff_ne_zero.mpr (by positivity)
    have hcn : c ^ n = J ^ 2 := by
      rw [hcdef, ← Real.rpow_natCast (J ^ ((2 : ℝ) / (n : ℝ))) n, ← Real.rpow_mul hJ.le,
        div_mul_cancel₀ (2 : ℝ) hnne, hJ2]
    -- (T1): `T = J^{2/n} A⁻¹`.
    have hTA : T = c • A⁻¹ := by
      have h1 : T * A * A⁻¹ = T := mul_nonsing_inv_cancel_right A T hAunit
      conv_lhs => rw [← h1]
      rw [hTeq]
      simp
    refine ⟨?_, ?_, ?_⟩
    · show Tᵀ = T
      rw [hTA, transpose_smul, transpose_nonsing_inv, hAsymm]
    · have hAinvdet : A⁻¹.det = (J ^ 2)⁻¹ := by
        have hmd := det_nonsing_inv_mul_det A hAunit
        rw [hdetA] at hmd
        field_simp at hmd ⊢
        linarith [hmd]
      rw [hTA, det_smul, Fintype.card_fin, hcn, hAinvdet]
      field_simp
    · -- Steps 3-4: the quadratic form bounds.
      have hdd : ∀ (B : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)),
          ∑ a, ∑ b, B a b * v a * v b = (⇑v : Fin n → ℝ) ⬝ᵥ (B *ᵥ (⇑v)) := by
        intro B v
        simp only [dotProduct, mulVec, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => by ring
      have hnsq : ∀ v : EuclideanSpace ℝ (Fin n), (⇑v : Fin n → ℝ) ⬝ᵥ (⇑v) = ‖v‖ ^ 2 := by
        intro v
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
        simp [dotProduct, sq]
      have hquad : ∀ w : Fin n → ℝ, w ⬝ᵥ (A *ᵥ w) = ∑ i, (∑ j, M i j * w j) ^ 2 := by
        intro w
        rw [hAdef, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
        simp [dotProduct, mulVec, sq]
      have hquad_nonneg : ∀ w : Fin n → ℝ, 0 ≤ w ⬝ᵥ (A *ᵥ w) := by
        intro w; rw [hquad]; positivity
      -- (5.10) in the form `(Aw, w) ≤ (KJ)^{2/n} |w|²`.
      have hSb : ∀ w : Fin n → ℝ, w ⬝ᵥ (A *ᵥ w) ≤ S * (w ⬝ᵥ w) := by
        intro w
        have hv : (⇑(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) = w := rfl
        have h1 := h510 (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin n))
        rw [show (∑ i, (∑ j, M i j * (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin n)) j) ^ 2)
              = w ⬝ᵥ (A *ᵥ w) from by rw [hquad, hv]] at h1
        have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (hquad_nonneg w) _) h1
          (div_pos two_pos hnR).le
        rw [← Real.rpow_mul (hquad_nonneg w),
          show (n : ℝ) / 2 * ((2 : ℝ) / (n : ℝ)) = 1 by field_simp, Real.rpow_one,
          Real.mul_rpow hKJ.le (by positivity), ← Real.rpow_mul (norm_nonneg _),
          show (n : ℝ) * ((2 : ℝ) / (n : ℝ)) = 2 by field_simp, hrpow2, ← hSdef, ← hnsq, hv] at h2
        exact h2
      -- Step 3: the orthonormal eigenbasis of `A`, with its eigenvalues `ev`.
      obtain ⟨fv, ev, hAf, hfn, hprod, hcomp⟩ :
          ∃ (fv : Fin n → (Fin n → ℝ)) (ev : Fin n → ℝ),
            (∀ i, A *ᵥ fv i = ev i • fv i) ∧ (∀ i, fv i ⬝ᵥ fv i = 1) ∧
              (∏ i, ev i = J ^ 2) ∧
              (∀ w : Fin n → ℝ, w = ∑ i, (fv i ⬝ᵥ w) • fv i) := by
        refine ⟨fun i => (⇑(hA.eigenvectorBasis i) : Fin n → ℝ), hA.eigenvalues,
          fun i => hA.mulVec_eigenvectorBasis i, fun i => ?_, ?_, ?_⟩
        · rw [hnsq, hA.eigenvectorBasis.orthonormal.1 i, one_pow]
        · rw [← hdetA]; simpa using hA.det_eq_prod_eigenvalues.symm
        · intro w
          have h := hA.eigenvectorBasis.sum_repr (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin n))
          have h2 : ∀ i, hA.eigenvectorBasis.repr (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin n)) i
              = (⇑(hA.eigenvectorBasis i) : Fin n → ℝ) ⬝ᵥ w := by
            intro i
            rw [hA.eigenvectorBasis.repr_apply_apply]
            simp [dotProduct, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
          simp only [h2] at h
          ext j
          conv_lhs =>
            rw [show w = (⇑(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) from rfl, ← h]
          simp
      -- each eigenvalue lies in `(0, (KJ)^{2/n}]`
      have hev_nonneg : ∀ i, 0 ≤ ev i := by
        intro i
        have h := hquad_nonneg (fv i)
        rwa [hAf i, dotProduct_smul, smul_eq_mul, hfn i, mul_one] at h
      have hev_le : ∀ i, ev i ≤ S := by
        intro i
        have h := hSb (fv i)
        rwa [hAf i, dotProduct_smul, smul_eq_mul, hfn i, mul_one, mul_one] at h
      have hev_pos : ∀ i, 0 < ev i := by
        intro i
        rcases (hev_nonneg i).lt_or_eq with h | h
        · exact h
        · exfalso
          have hz : ∏ k, ev k = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h.symm
          rw [hprod] at hz
          exact absurd hz (by positivity)
      -- Step 4: the eigenvalues `c / ev i` of `T` lie in `[K^{-2/n}, K^{2(n-1)/n}]`.
      have hmu_ge : ∀ i, K ^ (-(2 : ℝ) / (n : ℝ)) ≤ c / ev i := by
        intro i
        rw [le_div_iff₀ (hev_pos i), ← hKlS]
        exact mul_le_mul_of_nonneg_left (hev_le i) (Real.rpow_nonneg hK0.le _)
      have hmu_le : ∀ i, c / ev i ≤ K ^ (2 * ((n : ℝ) - 1) / (n : ℝ)) := by
        intro i
        rw [div_le_iff₀ (hev_pos i)]
        have hP : 0 < ∏ k ∈ Finset.univ.erase i, ev k :=
          Finset.prod_pos fun k _ => hev_pos k
        have hPle : (∏ k ∈ Finset.univ.erase i, ev k) ≤ S ^ (n - 1) := by
          calc (∏ k ∈ Finset.univ.erase i, ev k) ≤ ∏ _k ∈ Finset.univ.erase i, S :=
                Finset.prod_le_prod (fun k _ => hev_nonneg k) (fun k _ => hev_le k)
            _ = S ^ (n - 1) := by
                rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
                  Finset.card_univ, Fintype.card_fin]
        have hsplit : ev i * (∏ k ∈ Finset.univ.erase i, ev k) = J ^ 2 := by
          rw [Finset.mul_prod_erase Finset.univ ev (Finset.mem_univ i)]; exact hprod
        have h1 : c * (∏ k ∈ Finset.univ.erase i, ev k)
            ≤ (K ^ (2 * ((n : ℝ) - 1) / (n : ℝ)) * ev i)
              * (∏ k ∈ Finset.univ.erase i, ev k) := by
          rw [mul_assoc, hsplit, ← hcSn]
          exact mul_le_mul_of_nonneg_left hPle hc.le
        exact le_of_mul_le_mul_right h1 hP
      -- (T3): the eigenbasis of `A` diagonalises `T`.
      have hTf : ∀ i, T *ᵥ fv i = (c / ev i) • fv i := by
        intro i
        have h0 : A⁻¹ *ᵥ (A *ᵥ fv i) = fv i := by
          rw [mulVec_mulVec, nonsing_inv_mul A hAunit, one_mulVec]
        rw [hAf i, mulVec_smul] at h0
        have hinv : A⁻¹ *ᵥ fv i = (ev i)⁻¹ • fv i := by
          have h1 := congrArg (fun v : Fin n → ℝ => (ev i)⁻¹ • v) h0
          simpa [smul_smul, inv_mul_cancel₀ (hev_pos i).ne'] using h1
        rw [hTA, smul_mulVec, hinv, smul_smul, div_eq_mul_inv]
      -- expand in the eigenbasis and bound coefficientwise
      intro ξ
      have hw := hcomp (⇑ξ : Fin n → ℝ)
      have hQ : ∑ a, ∑ b, T a b * ξ a * ξ b
          = ∑ i, (c / ev i) * (fv i ⬝ᵥ (⇑ξ : Fin n → ℝ)) ^ 2 := by
        rw [hdd T ξ]
        nth_rewrite 2 [hw]
        rw [mulVec_sum, dotProduct_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mulVec_smul, hTf i, smul_smul, dotProduct_smul, smul_eq_mul,
          dotProduct_comm (⇑ξ : Fin n → ℝ) (fv i)]
        ring
      have hN : ‖ξ‖ ^ 2 = ∑ i, (fv i ⬝ᵥ (⇑ξ : Fin n → ℝ)) ^ 2 := by
        rw [← hnsq ξ]
        nth_rewrite 2 [hw]
        rw [dotProduct_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [dotProduct_smul, smul_eq_mul, dotProduct_comm (⇑ξ : Fin n → ℝ) (fv i)]
        ring
      rw [hQ, hN, Finset.mul_sum, Finset.mul_sum]
      refine ⟨Finset.sum_le_sum fun i _ => ?_, Finset.sum_le_sum fun i _ => ?_⟩
      · exact mul_le_mul_of_nonneg_right (hmu_ge i) (sq_nonneg _)
      · exact mul_le_mul_of_nonneg_right (hmu_le i) (sq_nonneg _)
  -- Step 5: raising the bounds of part (2) to the power `n/2`.
  have hpow : ∀ (Q : ℝ) (v : EuclideanSpace ℝ (Fin n)),
      K ^ (-(2 : ℝ) / (n : ℝ)) * ‖v‖ ^ 2 ≤ Q →
      Q ≤ K ^ (2 * ((n : ℝ) - 1) / (n : ℝ)) * ‖v‖ ^ 2 →
      K⁻¹ * ‖v‖ ^ (n : ℝ) ≤ Q ^ ((n : ℝ) / 2) ∧
        Q ^ ((n : ℝ) / 2) ≤ K ^ ((n : ℝ) - 1) * ‖v‖ ^ (n : ℝ) := by
    intro Q v hlo hhi
    have hn2 : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
    have key : ∀ r : ℝ,
        (K ^ r * ‖v‖ ^ 2) ^ ((n : ℝ) / 2) = K ^ (r * ((n : ℝ) / 2)) * ‖v‖ ^ (n : ℝ) := by
      intro r
      rw [Real.mul_rpow (Real.rpow_nonneg hK0.le _) (by positivity), ← Real.rpow_mul hK0.le,
        ← hrpow2 ‖v‖, ← Real.rpow_mul (norm_nonneg _),
        show (2 : ℝ) * ((n : ℝ) / 2) = (n : ℝ) by ring]
    constructor
    · have h1 := Real.rpow_le_rpow (by positivity) hlo hn2
      rw [key, show (-(2 : ℝ) / (n : ℝ)) * ((n : ℝ) / 2) = -1 by field_simp,
        Real.rpow_neg_one] at h1
      exact h1
    · have h1 := Real.rpow_le_rpow (le_trans (by positivity) hlo) hhi hn2
      rw [key, show (2 * ((n : ℝ) - 1) / (n : ℝ)) * ((n : ℝ) / 2) = (n : ℝ) - 1 by
        field_simp] at h1
      exact h1
  -- Step 0: the constants, chosen before the data.
  refine ⟨K⁻¹, K ^ ((n : ℝ) - 1), inv_pos.mpr hK0, ?_, ?_⟩
  · have h1 : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
    have h2 : (1 : ℝ) ≤ K ^ ((n : ℝ) - 1) := by
      calc (1 : ℝ) = K ^ (0 : ℝ) := (Real.rpow_zero K).symm
        _ ≤ K ^ ((n : ℝ) - 1) := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
    linarith
  -- Step 1: the full-measure set on which the argument runs.
  intro Ω F G τ hΩ hqr hdist hC7 hnc
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hJae := (hC7 hqr hdist).2.1 hnc
  have h510ae := hqr.2
  rw [← ae_restrict_iff' hΩm] at hJae h510ae
  filter_upwards [hJae, h510ae, ae_restrict_mem hΩm] with x hJx h510x hxΩ
  obtain ⟨hsym, hdet1, hbd⟩ := hcore ((Matrix.of fun i j => G i x j).det)
    (Matrix.of fun i j => G i x j) (τ x) hJx rfl ((hdist x hxΩ).1 hJx) h510x
  exact ⟨hsym, hdet1, hbd, fun v => hpow _ v (hbd v).1 (hbd v).2⟩
