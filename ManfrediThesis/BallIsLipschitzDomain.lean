import ManfrediThesis.Preamble
import ManfrediThesis.IsBoundedLipschitzDomain
open MeasureTheory

/-- Every open ball of positive radius is a bounded Lipschitz domain.  This is
what the proofs of §4 and §5 need in order to apply the cited result (C5), and
Theorems 3 and 5, at the balls they construct: after the `Ω'`-Lipschitz
hypothesis of l. 264, l. 1274, l. 1431 and l. 1551 is carried in the tablet,
every instantiation of those statements at a ball has to discharge it. -/
theorem BallIsLipschitzDomain :
    ∀ (n : ℕ), 1 ≤ n →
      ∀ (z : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
        IsBoundedLipschitzDomain n (Metric.ball z ρ) := by
  intro n hn z ρ hρ
  refine ⟨Metric.isOpen_ball,
    ⟨⟨z, Metric.mem_ball_self hρ⟩, (convex_ball z ρ).isPreconnected⟩,
    Metric.isBounded_ball, ?_⟩
  intro x hx
  -- the coordinate sum is the inner product
  have hinner : ∀ v w : EuclideanSpace ℝ (Fin n), ∑ i, v i * w i = inner ℝ v w := by
    intro v w
    rw [PiLp.inner_apply]
    simp [RCLike.inner_apply, mul_comm]
  -- a boundary point lies on the sphere
  have hxz : dist x z = ρ := by
    have hx' : x ∈ closure (Metric.ball z ρ) \ interior (Metric.ball z ρ) := hx
    rw [Metric.isOpen_ball.interior_eq] at hx'
    have h3 : dist x z ≤ ρ := by
      have h4 := closure_minimal
        (Metric.ball_subset_closedBall (x := z) (ε := ρ)) Metric.isClosed_closedBall hx'.1
      exact Metric.mem_closedBall.mp h4
    have h5 : ¬ dist x z < ρ := fun hc => hx'.2 (Metric.mem_ball.mpr hc)
    rw [not_lt] at h5
    linarith
  have hzx : ‖z - x‖ = ρ := by
    rw [← dist_eq_norm, dist_comm]
    exact hxz
  -- the inward unit normal
  obtain ⟨ν, hν⟩ : ∃ v : EuclideanSpace ℝ (Fin n), v = ρ⁻¹ • (z - x) := ⟨_, rfl⟩
  have hνnorm : ‖ν‖ = 1 := by
    rw [hν, norm_smul, hzx, norm_inv, Real.norm_eq_abs, abs_of_pos hρ,
      inv_mul_cancel₀ hρ.ne']
  have hνν : (inner ℝ ν ν : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hνnorm]
    norm_num
  have hzxν : z - x = ρ • ν := by
    rw [hν, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
  -- the projection onto the orthogonal complement of `ν`
  obtain ⟨P, hP⟩ : ∃ f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      f = fun y => y - (inner ℝ y ν : ℝ) • ν := ⟨_, rfl⟩
  have hPsq : ∀ y : EuclideanSpace ℝ (Fin n),
      ‖P y‖ ^ 2 = ‖y‖ ^ 2 - (inner ℝ y ν : ℝ) ^ 2 := by
    intro y
    rw [← real_inner_self_eq_norm_sq, hP]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_comm ν y]
    simp only [real_inner_self_eq_norm_sq, hνnorm]
    ring
  have hPle : ∀ y : EuclideanSpace ℝ (Fin n), ‖P y‖ ≤ ‖y‖ := by
    intro y
    have h1 := hPsq y
    have h2 : ‖P y‖ ^ 2 ≤ ‖y‖ ^ 2 := by nlinarith [sq_nonneg (inner ℝ y ν : ℝ)]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
  have hPsub : ∀ y y' : EuclideanSpace ℝ (Fin n), P y - P y' = P (y - y') := by
    intro y y'
    simp only [hP, inner_sub_left, sub_smul]
    abel
  have hPlip : LipschitzWith 1 (fun y : EuclideanSpace ℝ (Fin n) => ‖P y‖) := by
    refine LipschitzWith.of_dist_le_mul (fun y y' => ?_)
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
    calc |‖P y‖ - ‖P y'‖| ≤ ‖P y - P y'‖ := abs_norm_sub_norm_le _ _
      _ = ‖P (y - y')‖ := by rw [hPsub]
      _ ≤ ‖y - y'‖ := hPle _
  -- the graph function
  obtain ⟨φ, hφ⟩ : ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
      f = fun y => ρ - Real.sqrt (ρ ^ 2 - min ‖P y‖ (ρ / 2) ^ 2) := ⟨_, rfl⟩
  have hmin0 : ∀ y : EuclideanSpace ℝ (Fin n), 0 ≤ min ‖P y‖ (ρ / 2) :=
    fun y => le_min (norm_nonneg _) (by linarith)
  have hminle : ∀ y : EuclideanSpace ℝ (Fin n), min ‖P y‖ (ρ / 2) ≤ ρ / 2 :=
    fun y => min_le_right _ _
  have hsqrtge : ∀ y : EuclideanSpace ℝ (Fin n),
      ρ / 2 ≤ Real.sqrt (ρ ^ 2 - min ‖P y‖ (ρ / 2) ^ 2) := by
    intro y
    have h1 : (ρ / 2) ^ 2 ≤ ρ ^ 2 - min ‖P y‖ (ρ / 2) ^ 2 := by
      nlinarith [hmin0 y, hminle y]
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by linarith)] at h2
  have hφlip : LipschitzWith (Real.toNNReal 1) φ := by
    rw [Real.toNNReal_one]
    refine LipschitzWith.of_dist_le_mul (fun y y' => ?_)
    rw [Real.dist_eq, NNReal.coe_one, one_mul]
    obtain ⟨t, ht⟩ : ∃ c : ℝ, c = min ‖P y‖ (ρ / 2) := ⟨_, rfl⟩
    obtain ⟨t', ht'⟩ : ∃ c : ℝ, c = min ‖P y'‖ (ρ / 2) := ⟨_, rfl⟩
    have hA0 : (0:ℝ) ≤ ρ ^ 2 - t ^ 2 := by
      rw [ht]; nlinarith [hmin0 y, hminle y]
    have hB0 : (0:ℝ) ≤ ρ ^ 2 - t' ^ 2 := by
      rw [ht']; nlinarith [hmin0 y', hminle y']
    have hsa : ρ / 2 ≤ Real.sqrt (ρ ^ 2 - t ^ 2) := by rw [ht]; exact hsqrtge y
    have hsb : ρ / 2 ≤ Real.sqrt (ρ ^ 2 - t' ^ 2) := by rw [ht']; exact hsqrtge y'
    have hprod : (Real.sqrt (ρ ^ 2 - t ^ 2) - Real.sqrt (ρ ^ 2 - t' ^ 2))
        * (Real.sqrt (ρ ^ 2 - t ^ 2) + Real.sqrt (ρ ^ 2 - t' ^ 2)) = t' ^ 2 - t ^ 2 := by
      have e1 : Real.sqrt (ρ ^ 2 - t ^ 2) ^ 2 = ρ ^ 2 - t ^ 2 := Real.sq_sqrt hA0
      have e2 : Real.sqrt (ρ ^ 2 - t' ^ 2) ^ 2 = ρ ^ 2 - t' ^ 2 := Real.sq_sqrt hB0
      nlinarith [e1, e2]
    have hminlip : ∀ a b c : ℝ, |min a c - min b c| ≤ |a - b| := by
      intro a b c
      rcases le_total a c with h1 | h1 <;> rcases le_total b c with h2 | h2
      · rw [min_eq_left h1, min_eq_left h2]
      · rw [min_eq_left h1, min_eq_right h2, abs_of_nonpos (by linarith),
          abs_of_nonpos (by linarith)]
        linarith
      · rw [min_eq_right h1, min_eq_left h2, abs_of_nonneg (by linarith),
          abs_of_nonneg (by linarith)]
        linarith
      · rw [min_eq_right h1, min_eq_right h2, sub_self, abs_zero]
        exact abs_nonneg _
    have htt' : |t - t'| ≤ dist y y' := by
      have h1 := hPlip.dist_le_mul y y'
      rw [NNReal.coe_one, one_mul, Real.dist_eq] at h1
      rw [ht, ht']
      exact le_trans (hminlip _ _ _) h1
    have hdiff : |t' ^ 2 - t ^ 2| ≤ |t - t'| * ρ := by
      have h1 : t' ^ 2 - t ^ 2 = (t' - t) * (t' + t) := by ring
      rw [h1, abs_mul]
      have h2 : |t' + t| ≤ ρ := by
        rw [abs_of_nonneg (by rw [ht, ht']; linarith [hmin0 y, hmin0 y'])]
        rw [ht, ht']
        linarith [hminle y, hminle y']
      have h3 : |t' - t| = |t - t'| := abs_sub_comm _ _
      rw [h3]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    have hkey : |Real.sqrt (ρ ^ 2 - t ^ 2) - Real.sqrt (ρ ^ 2 - t' ^ 2)| * ρ
        ≤ |t - t'| * ρ := by
      have h1 : |Real.sqrt (ρ ^ 2 - t ^ 2) - Real.sqrt (ρ ^ 2 - t' ^ 2)|
          * (Real.sqrt (ρ ^ 2 - t ^ 2) + Real.sqrt (ρ ^ 2 - t' ^ 2))
          = |t' ^ 2 - t ^ 2| := by
        rw [← abs_of_nonneg (show (0:ℝ) ≤ Real.sqrt (ρ ^ 2 - t ^ 2)
            + Real.sqrt (ρ ^ 2 - t' ^ 2) by positivity), ← abs_mul, hprod]
      have h2 : ρ ≤ Real.sqrt (ρ ^ 2 - t ^ 2) + Real.sqrt (ρ ^ 2 - t' ^ 2) := by linarith
      calc |Real.sqrt (ρ ^ 2 - t ^ 2) - Real.sqrt (ρ ^ 2 - t' ^ 2)| * ρ
          ≤ |Real.sqrt (ρ ^ 2 - t ^ 2) - Real.sqrt (ρ ^ 2 - t' ^ 2)|
            * (Real.sqrt (ρ ^ 2 - t ^ 2) + Real.sqrt (ρ ^ 2 - t' ^ 2)) :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = |t' ^ 2 - t ^ 2| := h1
        _ ≤ |t - t'| * ρ := hdiff
    have hfin : |Real.sqrt (ρ ^ 2 - t ^ 2) - Real.sqrt (ρ ^ 2 - t' ^ 2)| ≤ |t - t'| := by
      have := hkey
      nlinarith [abs_nonneg (Real.sqrt (ρ ^ 2 - t ^ 2) - Real.sqrt (ρ ^ 2 - t' ^ 2)),
        abs_nonneg (t - t')]
    have hφy : φ y - φ y' = Real.sqrt (ρ ^ 2 - t' ^ 2) - Real.sqrt (ρ ^ 2 - t ^ 2) := by
      simp only [hφ, ← ht, ← ht']
      ring
    rw [hφy, abs_sub_comm]
    exact le_trans hfin htt'
  -- invariance in the direction `ν`
  have hPinv : ∀ (y : EuclideanSpace ℝ (Fin n)) (c : ℝ), P (y + c • ν) = P y := by
    intro y c
    simp only [hP]
    rw [inner_add_left, real_inner_smul_left, hνν, mul_one, add_smul]
    abel
  have hφinv : ∀ (y : EuclideanSpace ℝ (Fin n)) (c : ℝ), φ (y + c • ν) = φ y := by
    intro y c
    simp only [hφ, hPinv y c]
  refine ⟨ρ / 2, 1, ν, φ, by linarith, by norm_num, hνnorm, hφlip, hφinv, ?_⟩
  -- the graph description on `B_{ρ/2}(x)`
  intro y hy
  have hyx : ‖y - x‖ < ρ / 2 := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hy
  obtain ⟨w, hw⟩ : ∃ v : EuclideanSpace ℝ (Fin n), v = P (y - x) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ c : ℝ, c = (inner ℝ (y - x) ν : ℝ) := ⟨_, rfl⟩
  have hwnorm : ‖w‖ < ρ / 2 := lt_of_le_of_lt (by rw [hw]; exact hPle _) hyx
  have hsabs : |s| < ρ / 2 := by
    rw [hs]
    have h1 := abs_real_inner_le_norm (y - x) ν
    rw [hνnorm, mul_one] at h1
    linarith
  have hyxw : y - x = w + s • ν := by
    rw [hw, hs, hP]
    simp only []
    abel
  have hwν : (inner ℝ w ν : ℝ) = 0 := by
    rw [hw, hP]
    simp only []
    rw [inner_sub_left, real_inner_smul_left, hνν, mul_one, sub_self]
  have hyz : y - z = w + (s - ρ) • ν := by
    have h1 : y - z = (y - x) - (z - x) := by abel
    rw [h1, hyxw, hzxν, sub_smul]
    abel
  have hwν' : (inner ℝ ν w : ℝ) = 0 := by
    rw [real_inner_comm]
    exact hwν
  have hyznorm : ‖y - z‖ ^ 2 = ‖w‖ ^ 2 + (s - ρ) ^ 2 := by
    rw [hyz, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hwν, hwν']
    simp only [real_inner_self_eq_norm_sq, hνnorm]
    ring
  have hmineq : min ‖P (y - x)‖ (ρ / 2) = ‖w‖ := by
    rw [← hw]
    exact min_eq_left (le_of_lt hwnorm)
  have hφval : φ (y - x) = ρ - Real.sqrt (ρ ^ 2 - ‖w‖ ^ 2) := by
    simp only [hφ, hmineq]
  have hw2 : ‖w‖ ^ 2 < ρ ^ 2 := by nlinarith [norm_nonneg w]
  have hrhs : ∑ i, (y - x) i * ν i = s := by rw [hinner, hs]
  rw [hφval, hrhs]
  constructor
  · intro hmem
    have h1 : ‖y - z‖ < ρ := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hmem
    have h2 : ‖y - z‖ ^ 2 < ρ ^ 2 := (sq_lt_sq₀ (norm_nonneg _) (by linarith)).mpr h1
    rw [hyznorm] at h2
    have h3 : (ρ - s) ^ 2 < ρ ^ 2 - ‖w‖ ^ 2 := by nlinarith
    have h4 : ρ - s < Real.sqrt (ρ ^ 2 - ‖w‖ ^ 2) := by
      refine (Real.lt_sqrt (by linarith [abs_lt.mp hsabs])).mpr h3
    linarith
  · intro hlt
    have h4 : ρ - s < Real.sqrt (ρ ^ 2 - ‖w‖ ^ 2) := by linarith
    have h3 : (ρ - s) ^ 2 < ρ ^ 2 - ‖w‖ ^ 2 :=
      (Real.lt_sqrt (by linarith [abs_lt.mp hsabs])).mp h4
    have h2 : ‖y - z‖ ^ 2 < ρ ^ 2 := by
      rw [hyznorm]
      nlinarith
    have h1 : ‖y - z‖ < ρ := (sq_lt_sq₀ (norm_nonneg _) (by linarith)).mp h2
    rw [Metric.mem_ball, dist_eq_norm]
    exact h1
