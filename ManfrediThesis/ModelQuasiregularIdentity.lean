import ManfrediThesis.Preamble
import ManfrediThesis.IsDistortionMatrix
import ManfrediThesis.WeakGradientOfC1
open MeasureTheory

/-- The identity map of `ℝⁿ` is `1`-quasiregular on every open set, with weak
gradient field `G i x = eᵢ`, and the constant identity matrix is its distortion
matrix.

This is an inhabitation witness for the data hypotheses of §5, and that is its
purpose: the Note for the formalization requires at l. 258 that the cited
results "must not be vacuous (each must be a true statement for the operators to
which it is applied)", and `QuasiregularRegularity` (Theorem 7) is conditioned on
`IsQuasiregularOn` together with `IsDistortionMatrix`, so without a witness those
hypotheses could be satisfied by nothing and the theorem would be vacuously true.
The identity map at `K = 1` is the paper's own trivial instance: l. 1582 defines
`K`-quasiregular as `F ∈ W^{1,n}_loc(Ω)` together with (5.10)
`|DF(x)|^n ≤ K J_F(x)` a.e., and for `F = id` both sides equal `‖ξ‖^n`, so (5.10)
holds with equality at `K = 1`.

Being Lean-closed is not available here: the first conjunct of
`IsQuasiregularOn` is a `W^{1,n}_loc` membership, which the tablet obtains from
`WeakGradientOfC1`, itself still `sorry`-bearing. -/
theorem ModelQuasiregularIdentity :
    ∀ (n : ℕ), 2 ≤ n →
      ∀ Ω : Set (EuclideanSpace ℝ (Fin n)), IsOpen Ω →
        IsQuasiregularOn n 1 Ω (fun x => x)
            (fun (i : Fin n) (_ : EuclideanSpace ℝ (Fin n)) =>
              EuclideanSpace.single i (1 : ℝ))
          ∧ IsDistortionMatrix n Ω
              (fun (i : Fin n) (_ : EuclideanSpace ℝ (Fin n)) =>
                EuclideanSpace.single i (1 : ℝ))
              (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  intro n hn Ω hΩ
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  -- the gradient matrix of the identity is the identity matrix
  have hmat : (Matrix.of fun (i j : Fin n) => (EuclideanSpace.single i (1:ℝ)) j)
      = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Matrix.one_apply, eq_comm]
  have hdet : (Matrix.of fun (i j : Fin n) => (EuclideanSpace.single i (1:ℝ)) j).det = 1 := by
    rw [hmat, Matrix.det_one]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- each coordinate function lies in `W^{1,n}_loc` with the constant gradient `eᵢ`
    intro i
    obtain ⟨P, hP⟩ : ∃ P : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
        ∀ v : EuclideanSpace ℝ (Fin n), P v = v i :=
      ⟨EuclideanSpace.proj i, fun v => rfl⟩
    have hfun : (fun y : EuclideanSpace ℝ (Fin n) => y i) = ⇑P := by
      funext y
      rw [hP]
    refine WeakGradientOfC1 n (n : ℝ) hn1 hnR Ω (fun x => x i)
      (fun _ => EuclideanSpace.single i (1:ℝ)) hΩ ?_ continuousOn_const
    intro x _
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact P.differentiableAt
    · intro j
      rw [hfun, (P.hasFDerivAt (x := x)).fderiv, hP]
      simp [eq_comm]
  · -- the distortion inequality, which holds with equality at `K = 1`
    refine Filter.Eventually.of_forall (fun x _ ξ => ?_)
    have h1 : ∀ i : Fin n, (∑ j, (EuclideanSpace.single i (1:ℝ)) j * ξ j) = ξ i := by
      intro i
      simp [ite_mul]
    have h2 : (∑ i, (∑ j, (EuclideanSpace.single i (1:ℝ)) j * ξ j) ^ 2) = ‖ξ‖ ^ 2 := by
      simp only [h1]
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      exact Finset.sum_congr rfl (fun i _ => (sq_abs (ξ i)).symm)
    have h3 : ((‖ξ‖ : ℝ) ^ 2) ^ ((n : ℝ) / 2) = ‖ξ‖ ^ (n : ℝ) := by
      rw [← Real.rpow_natCast ‖ξ‖ 2, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      push_cast
      ring
    rw [h2, h3, hdet]
    norm_num
  · -- the constant identity matrix is the distortion matrix
    intro x _
    refine ⟨fun _ => ?_, fun hc => absurd ?_ hc⟩
    · rw [hmat, Matrix.transpose_one, Matrix.one_mul, Matrix.one_mul, Matrix.det_one,
        Real.one_rpow, one_smul]
    · rw [hdet]
      norm_num
