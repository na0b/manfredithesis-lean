import ManfrediThesis.Preamble

/-- Three elementary facts about `EuclideanSpace ℝ (Fin n)`, true for every
`n` and independent of any further data: the norm is dominated by the sum of
the absolute values of the coordinates, each coordinate is dominated by the
norm, and a continuous linear endomorphism whose matrix entries are bounded by
`B ≥ 0` has operator bound `n²B`, i.e. `‖Lv‖ ≤ ((n : ℝ) * n) * B * ‖v‖` for
every `v`.

Conventions, restated here because a helper inherits none of its parent's.
`w i` is the `i`-th coordinate of `w`, `‖·‖` the Euclidean norm, and the
matrix entries of `L` are `L (EuclideanSpace.single j 1) i`, the `i`-th
coordinate of the image of the `j`-th standard basis vector — so the
hypothesis is a bound on every entry, not on the columns or on the operator.
The constant is written `((n : ℝ) * n)`, the product of two casts of the same
natural number, exactly as the conclusion prints it.  No hypothesis on `n` is
needed: all three statements hold for `n = 0` as well, vacuously or trivially.

The route.  The first expands `w = ∑ i, w i · e_i` and applies the triangle
inequality, with `‖w i · e_i‖ = |w i|` since `‖e_i‖ = 1`.  The second is
monotonicity of the square root applied to `|w i|^2 ≤ ∑_l|w l|^2`.  The third
bounds each column by `‖Le_j‖ ≤ ∑_i|(Le_j)_i| ≤ nB` using the first fact, then
expands `v` in the basis and uses linearity, the triangle inequality and
`|v j| ≤ ‖v‖` from the second fact to get `∑_j‖v‖(nB) = n^2B‖v‖`. -/
theorem EuclideanCoordinateOperatorBounds :
    ∀ n : ℕ,
      (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ ∑ i, |w i|)
      ∧ (∀ (w : EuclideanSpace ℝ (Fin n)) (i : Fin n), |w i| ≤ ‖w‖)
      ∧ (∀ (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (B : ℝ),
          0 ≤ B → (∀ i j : Fin n, |L (EuclideanSpace.single j (1 : ℝ)) i| ≤ B) →
          ∀ v : EuclideanSpace ℝ (Fin n), ‖L v‖ ≤ ((n : ℝ) * n) * B * ‖v‖) := by
  intro n
  have hl1 : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ ∑ i, |w i| := by
    intro w
    have he : (∑ i, (w i) • EuclideanSpace.single i (1 : ℝ)) = w := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq]
    calc ‖w‖ = ‖∑ i, (w i) • EuclideanSpace.single i (1 : ℝ)‖ := by rw [he]
      _ ≤ ∑ i, ‖(w i) • EuclideanSpace.single i (1 : ℝ)‖ := norm_sum_le _ _
      _ = ∑ i, |w i| := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
          simp
  have hcoord : ∀ (w : EuclideanSpace ℝ (Fin n)) (i : Fin n), |w i| ≤ ‖w‖ := by
    intro w i
    rw [EuclideanSpace.norm_eq,
      show |w i| = Real.sqrt (|w i| ^ 2) by rw [Real.sqrt_sq (abs_nonneg _)]]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (f := fun l => |w l| ^ 2) (fun l _ => sq_nonneg _)
        (Finset.mem_univ i))
  refine ⟨hl1, hcoord, ?_⟩
  intro L B hB hL v
  have hcol : ∀ j : Fin n, ‖L (EuclideanSpace.single j (1 : ℝ))‖ ≤ (n : ℝ) * B := by
    intro j
    calc ‖L (EuclideanSpace.single j (1 : ℝ))‖
        ≤ ∑ i, |L (EuclideanSpace.single j (1 : ℝ)) i| := hl1 _
      _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum fun i _ => hL i j
      _ = (n : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have he : (∑ j, (v j) • EuclideanSpace.single j (1 : ℝ)) = v := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq]
  calc ‖L v‖ = ‖L (∑ j, (v j) • EuclideanSpace.single j (1 : ℝ))‖ := by rw [he]
    _ = ‖∑ j, (v j) • L (EuclideanSpace.single j (1 : ℝ))‖ := by
        rw [map_sum]
        simp only [map_smul]
    _ ≤ ∑ j, ‖(v j) • L (EuclideanSpace.single j (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ j, |v j| * ‖L (EuclideanSpace.single j (1 : ℝ))‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ _j : Fin n, ‖v‖ * ((n : ℝ) * B) := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul (hcoord v j) (hcol j) (norm_nonneg _) (norm_nonneg _)
    _ = ((n : ℝ) * n) * B * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
