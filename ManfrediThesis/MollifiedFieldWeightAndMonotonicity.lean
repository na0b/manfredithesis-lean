import ManfrediThesis.Preamble
set_option maxHeartbeats 1600000
open MeasureTheory

/-- The uniform-in-`e` weight bound for the mollified field, and the
monotonicity constant it produces.

Conventions, restated here because a helper inherits none of its parent's.
`supp` is the CLOSED support.  `ρ` is a nonnegative probability density
supported in the closed unit ball, and
`A_e(h) = ∫ ρ(z)A(h + √e z)dz - ∫ ρ(z)A(√e z)dz` is the mollification of the
degenerate field `A` at the parameter `e`.  All powers of positive reals are
real powers, written exactly as the structure conditions (Q1)/(Q2) print them,
and the exponent `p/2 - 1` carries no sign assumption: the argument works for
`p` on either side of `2`.

Two conclusions, produced together.  First, with `c_w` the absolute constant of
the hypotheses, for every `0 < e ≤ 1` and all `a ≠ b`,
`c_w(e+‖a‖²+‖b‖²)^{p/2-1} ≤ ∫ρ(z)(‖a+√e z‖²+‖b+√e z‖²)^{p/2-1}dz`.
Second, there is `c₃ > 0` with
`c₃(e+‖a‖²+‖b‖²)^{p/2-1}‖a-b‖² ≤ ⟨A_e(a)-A_e(b), a-b⟩`
for every `0 < e ≤ 1` and all `a, b`.  They are one lemma because the first is
consumed INSIDE the proof of the second and nowhere else, while the second is
what the consumer needs; separating them would strand the first.

The route for the first: the weight sandwich at a single point gives
`c₁(e+‖h‖²)^{p/2-1} ≤ ∫(‖h+√e z‖²)^{p/2-1}ρ(z)dz`, and the two-point weight
`‖a+√e z‖²+‖b+√e z‖²` is comparable to `e+‖a‖²+‖b‖²` up to the absolute
factors `2^{-(p/2-1)}` and `4^{p/2-1}` that bound `c_w`, using
`‖x+y‖² ≤ 2‖x‖²+2‖y‖²`, the support bound `‖z‖ ≤ 1` on `supp ρ`, and
`√e ≤ 1`; averaging against `ρ`, a probability density, transports the
pointwise comparison to the integral.  The route for the second: the
monotonicity bound for the UNMOLLIFIED field,
`C_M γ₀(0+‖a‖²+‖b‖²)^{p/2-1}‖a-b‖² ≤ ⟨A(a)-A(b), a-b⟩`, holds at every pair;
translating `a, b` by `√e z` and averaging against `ρ` turns its left-hand side
into `C_M γ₀‖a-b‖²∫ρ(z)(‖a+√e z‖²+‖b+√e z‖²)^{p/2-1}dz`, which the first
conclusion bounds below by `C_M γ₀ c_w(e+‖a‖²+‖b‖²)^{p/2-1}‖a-b‖²`; and its
right-hand side averages exactly to `⟨A_e(a)-A_e(b), a-b⟩`, the two constant
subtractions in the definition of `A_e` cancelling in the difference.  So
`c₃ = C_M γ₀ c_w`.  The case `a = b` is trivial, both sides vanishing. -/
theorem MollifiedFieldWeightAndMonotonicity :
    ∀ (n : ℕ) (p : ℝ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ z, 0 ≤ ρ z) →
      (∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Continuous f →
        Integrable (fun z => ρ z * f z) volume) →
      (∀ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), Continuous F →
        Integrable (fun z => ρ z • F z) volume) →
      (∀ z ∈ tsupport ρ, ‖z‖ ≤ 1) →
      (∀ (f : EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ), Continuous f →
        (∀ z ∈ tsupport ρ, C ≤ f z) → C ≤ ∫ z, ρ z * f z) →
    ∀ (γ₀ : ℝ) (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      0 < γ₀ → Continuous A →
    ∀ Ae : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      (∀ e h, Ae e h = (∫ z, ρ z • A (h + Real.sqrt e • z))
          - ∫ z, ρ z • A (Real.sqrt e • z)) →
    ∀ CM : ℝ, 0 < CM →
      (∀ a b : EuclideanSpace ℝ (Fin n),
        CM * γ₀ * (0 + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2
          ≤ ∑ i, (A a i - A b i) * (a i - b i)) →
      (∀ v w : EuclideanSpace ℝ (Fin n), (∑ i, v i * w i) = (innerSL ℝ w) v) →
      (∀ x y : EuclideanSpace ℝ (Fin n), ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) →
      (∀ a b w : EuclideanSpace ℝ (Fin n), a ≠ b →
        (0:ℝ) < ‖a + w‖ ^ 2 + ‖b + w‖ ^ 2) →
    ∀ c₁ C₂w : ℝ, 0 < c₁ →
      (∀ (h : EuclideanSpace ℝ (Fin n)) (e : ℝ), 0 < e →
        c₁ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)
            ≤ ∫ z, (‖h + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ρ z
          ∧ (∫ z, (‖h + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ρ z)
            ≤ C₂w * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)) →
    ∀ cw : ℝ, 0 < cw →
      cw ≤ min c₁ 1 * (2:ℝ) ^ (-(p / 2 - 1)) →
      cw ≤ (4:ℝ) ^ (p / 2 - 1) →
      (∀ e : ℝ, 0 < e → e ≤ 1 →
          ∀ a b : EuclideanSpace ℝ (Fin n), a ≠ b →
            cw * (e + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1)
              ≤ ∫ z, ρ z * (‖a + Real.sqrt e • z‖ ^ 2
                  + ‖b + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1))
        ∧ (∃ c₃ : ℝ, 0 < c₃ ∧
          ∀ e : ℝ, 0 < e → e ≤ 1 → ∀ a b : EuclideanSpace ℝ (Fin n),
            c₃ * (e + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2
              ≤ ∑ i, (Ae e a i - Ae e b i) * (a i - b i)) := by
  intro n p ρ hρ0 hρfint hρFint hsuppz hρavg' γ₀ A hγ₀ hAcont Ae hAeeq CM hCM0
    hMA hIP hsq2 hWposg c₁ C₂w hc₁0 hsw cw hcw0 hcwa hcwb
  have hWbd : ∀ e : ℝ, 0 < e → e ≤ 1 →
      ∀ a b : EuclideanSpace ℝ (Fin n), a ≠ b →
        cw * (e + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1)
          ≤ ∫ z, ρ z * (‖a + Real.sqrt e • z‖ ^ 2
              + ‖b + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) := by
    intro e he0 he1 a b hab
    have hte0 : 0 ≤ Real.sqrt e := Real.sqrt_nonneg e
    have hte : Real.sqrt e ≤ 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt he1
    have htsq : Real.sqrt e ^ 2 = e := Real.sq_sqrt he0.le
    have hV0 : (0:ℝ) < e + ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
      nlinarith [sq_nonneg ‖a‖, sq_nonneg ‖b‖]
    have habn : (0:ℝ) < ‖a - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hab)
    have hWpos : ∀ w : EuclideanSpace ℝ (Fin n),
        (0:ℝ) < ‖a + w‖ ^ 2 + ‖b + w‖ ^ 2 := fun w => hWposg a b w hab
    have hWcont : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
        ‖a + Real.sqrt e • z‖ ^ 2 + ‖b + Real.sqrt e • z‖ ^ 2) := by fun_prop
    have hWqcont : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
        (‖a + Real.sqrt e • z‖ ^ 2 + ‖b + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)) :=
      hWcont.rpow_const (fun z => Or.inl (ne_of_gt (hWpos _)))
    rcases le_or_gt 0 (p / 2 - 1) with hq | hq
    · -- the exponent is nonnegative: the parallelogram identity and the sandwich
      obtain ⟨s, hsdef⟩ : ∃ s : EuclideanSpace ℝ (Fin n),
        s = (1/2 : ℝ) • (a + b) := ⟨_, rfl⟩
      obtain ⟨d, hddef⟩ : ∃ d : EuclideanSpace ℝ (Fin n),
        d = (1/2 : ℝ) • (a - b) := ⟨_, rfl⟩
      have hpar : ∀ w : EuclideanSpace ℝ (Fin n),
          ‖a + w‖ ^ 2 + ‖b + w‖ ^ 2 = 2 * ‖s + w‖ ^ 2 + 2 * ‖d‖ ^ 2 := by
        intro w
        have h1 := parallelogram_law_with_norm ℝ (a + w) (b + w)
        have h2 : (a + w) + (b + w) = (2:ℝ) • (s + w) := by rw [hsdef]; module
        have h3 : (a + w) - (b + w) = (2:ℝ) • d := by rw [hddef]; module
        rw [h2, h3, norm_smul, norm_smul] at h1
        simp only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h1
        simp only [pow_two]
        linarith [h1]
      have hpar0 : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 2 * ‖s‖ ^ 2 + 2 * ‖d‖ ^ 2 := by
        have := hpar 0
        simpa using this
      have hUV : e + ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ 2 * ((e + ‖s‖ ^ 2) + ‖d‖ ^ 2) := by
        rw [show e + ‖a‖ ^ 2 + ‖b‖ ^ 2 = e + (‖a‖ ^ 2 + ‖b‖ ^ 2) by ring, hpar0]
        linarith [he0.le]
      -- the two lower bounds, and their combination
      have hq2pos : (0:ℝ) < (2:ℝ) ^ (p / 2 - 1) := Real.rpow_pos_of_pos (by norm_num) _
      have hscont : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
          (‖s + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)) :=
        (by fun_prop : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
          ‖s + Real.sqrt e • z‖ ^ 2)).rpow_const (fun z => Or.inr hq)
      have hJ1 : (2:ℝ) ^ (p / 2 - 1) * (c₁ * (e + ‖s‖ ^ 2) ^ (p / 2 - 1))
          ≤ ∫ z, ρ z * (‖a + Real.sqrt e • z‖ ^ 2
              + ‖b + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) := by
        have hsw1 : c₁ * (e + ‖s‖ ^ 2) ^ (p / 2 - 1)
            ≤ ∫ z, ρ z * (‖s + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) := by
          have h := (hsw s e he0).1
          have hcomm : (∫ z, (‖s + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ρ z)
              = ∫ z, ρ z * (‖s + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) :=
            integral_congr_ae (Filter.Eventually.of_forall fun z => by
              show (‖s + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ρ z
                = ρ z * (‖s + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)
              ring)
          rwa [hcomm] at h
        have hsub : (∫ z, ρ z * ((2:ℝ) ^ (p / 2 - 1)
              * (‖s + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)))
            ≤ ∫ z, ρ z * (‖a + Real.sqrt e • z‖ ^ 2
                + ‖b + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) := by
          refine integral_mono (hρfint _ (continuous_const.mul hscont))
            (hρfint _ hWqcont) ?_
          intro z
          show ρ z * _ ≤ ρ z * _
          refine mul_le_mul_of_nonneg_left ?_ (hρ0 z)
          rw [hpar (Real.sqrt e • z), ← Real.mul_rpow (by norm_num) (sq_nonneg _)]
          refine Real.rpow_le_rpow (by positivity) ?_ hq
          nlinarith [sq_nonneg ‖d‖]
        have heqint : (∫ z, ρ z * ((2:ℝ) ^ (p / 2 - 1)
              * (‖s + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)))
            = (2:ℝ) ^ (p / 2 - 1) * ∫ z, ρ z
              * (‖s + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          show ρ z * ((2:ℝ) ^ (p / 2 - 1)
              * (‖s + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1))
            = (2:ℝ) ^ (p / 2 - 1)
              * (ρ z * (‖s + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1))
          ring
        calc (2:ℝ) ^ (p / 2 - 1) * (c₁ * (e + ‖s‖ ^ 2) ^ (p / 2 - 1))
            ≤ (2:ℝ) ^ (p / 2 - 1) * ∫ z, ρ z
                * (‖s + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) :=
              mul_le_mul_of_nonneg_left hsw1 hq2pos.le
          _ = ∫ z, ρ z * ((2:ℝ) ^ (p / 2 - 1)
                * (‖s + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)) := heqint.symm
          _ ≤ _ := hsub
      have hJ2 : (2:ℝ) ^ (p / 2 - 1) * (‖d‖ ^ 2) ^ (p / 2 - 1)
          ≤ ∫ z, ρ z * (‖a + Real.sqrt e • z‖ ^ 2
              + ‖b + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) := by
        refine hρavg' _ _ hWqcont ?_
        intro z _
        rw [hpar (Real.sqrt e • z), ← Real.mul_rpow (by norm_num) (sq_nonneg _)]
        refine Real.rpow_le_rpow (by positivity) ?_ hq
        nlinarith [sq_nonneg ‖s + Real.sqrt e • z‖]
      have ht2 : (2:ℝ) ^ (-(p / 2 - 1)) * (2:ℝ) ^ (p / 2 - 1) = 1 := by
        rw [← Real.rpow_add (by norm_num)]
        simp
      have hcm0 : (0:ℝ) < min c₁ 1 := lt_min hc₁0 (by norm_num)
      have hstep : ∀ X : ℝ, (min c₁ 1 * (2:ℝ) ^ (-(p / 2 - 1)))
          * ((2:ℝ) ^ (p / 2 - 1) * X) = min c₁ 1 * X := by
        intro X
        calc (min c₁ 1 * (2:ℝ) ^ (-(p / 2 - 1))) * ((2:ℝ) ^ (p / 2 - 1) * X)
            = min c₁ 1 * ((2:ℝ) ^ (-(p / 2 - 1)) * (2:ℝ) ^ (p / 2 - 1)) * X := by ring
          _ = min c₁ 1 * X := by rw [ht2, mul_one]
      have hUVq : (e + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1)
          ≤ (2:ℝ) ^ (p / 2 - 1) * ((e + ‖s‖ ^ 2) + ‖d‖ ^ 2) ^ (p / 2 - 1) := by
        rw [← Real.mul_rpow (by norm_num) (by positivity)]
        exact Real.rpow_le_rpow (by positivity) hUV hq
      have hfirst : cw * (e + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1)
          ≤ min c₁ 1 * ((e + ‖s‖ ^ 2) + ‖d‖ ^ 2) ^ (p / 2 - 1) := by
        calc cw * (e + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1)
            ≤ (min c₁ 1 * (2:ℝ) ^ (-(p / 2 - 1)))
                * ((2:ℝ) ^ (p / 2 - 1) * ((e + ‖s‖ ^ 2) + ‖d‖ ^ 2) ^ (p / 2 - 1)) :=
              mul_le_mul hcwa hUVq (Real.rpow_nonneg (by positivity) _) (by positivity)
          _ = min c₁ 1 * ((e + ‖s‖ ^ 2) + ‖d‖ ^ 2) ^ (p / 2 - 1) := hstep _
      rcases le_total (e + ‖s‖ ^ 2) (‖d‖ ^ 2) with hcase | hcase
      · have hb : ((e + ‖s‖ ^ 2) + ‖d‖ ^ 2) ^ (p / 2 - 1)
            ≤ (2:ℝ) ^ (p / 2 - 1) * (‖d‖ ^ 2) ^ (p / 2 - 1) := by
          rw [← Real.mul_rpow (by norm_num) (sq_nonneg _)]
          exact Real.rpow_le_rpow (by positivity) (by linarith) hq
        calc cw * (e + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1)
            ≤ min c₁ 1 * ((e + ‖s‖ ^ 2) + ‖d‖ ^ 2) ^ (p / 2 - 1) := hfirst
          _ ≤ min c₁ 1 * ((2:ℝ) ^ (p / 2 - 1) * (‖d‖ ^ 2) ^ (p / 2 - 1)) :=
              mul_le_mul_of_nonneg_left hb hcm0.le
          _ ≤ 1 * ((2:ℝ) ^ (p / 2 - 1) * (‖d‖ ^ 2) ^ (p / 2 - 1)) :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
          _ = (2:ℝ) ^ (p / 2 - 1) * (‖d‖ ^ 2) ^ (p / 2 - 1) := one_mul _
          _ ≤ _ := hJ2
      · have hb : ((e + ‖s‖ ^ 2) + ‖d‖ ^ 2) ^ (p / 2 - 1)
            ≤ (2:ℝ) ^ (p / 2 - 1) * (e + ‖s‖ ^ 2) ^ (p / 2 - 1) := by
          rw [← Real.mul_rpow (by norm_num) (by positivity)]
          exact Real.rpow_le_rpow (by positivity) (by linarith) hq
        calc cw * (e + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1)
            ≤ min c₁ 1 * ((e + ‖s‖ ^ 2) + ‖d‖ ^ 2) ^ (p / 2 - 1) := hfirst
          _ ≤ min c₁ 1 * ((2:ℝ) ^ (p / 2 - 1) * (e + ‖s‖ ^ 2) ^ (p / 2 - 1)) :=
              mul_le_mul_of_nonneg_left hb hcm0.le
          _ ≤ c₁ * ((2:ℝ) ^ (p / 2 - 1) * (e + ‖s‖ ^ 2) ^ (p / 2 - 1)) :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
          _ = (2:ℝ) ^ (p / 2 - 1) * (c₁ * (e + ‖s‖ ^ 2) ^ (p / 2 - 1)) := by ring
          _ ≤ _ := hJ1
    · -- the exponent is negative: a pointwise bound suffices
      have hbd : ∀ z ∈ tsupport ρ,
          (4:ℝ) ^ (p / 2 - 1) * (e + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1)
            ≤ (‖a + Real.sqrt e • z‖ ^ 2
              + ‖b + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) := by
        intro z hz
        have hzn := hsuppz z hz
        have hwn : ‖(Real.sqrt e • z : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ e := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hte0, mul_pow, htsq]
          have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z, hzn]
          calc e * ‖z‖ ^ 2 ≤ e * 1 := mul_le_mul_of_nonneg_left hz2 he0.le
            _ = e := mul_one e
        have hle : ‖a + Real.sqrt e • z‖ ^ 2 + ‖b + Real.sqrt e • z‖ ^ 2
            ≤ 4 * (e + ‖a‖ ^ 2 + ‖b‖ ^ 2) := by
          have h1 := hsq2 a (Real.sqrt e • z)
          have h2 := hsq2 b (Real.sqrt e • z)
          nlinarith [hwn, h1, h2]
        rw [← Real.mul_rpow (by norm_num) hV0.le]
        exact Real.rpow_le_rpow_of_nonpos (hWpos _) hle hq.le
      refine le_trans ?_ (hρavg' _ _ hWqcont hbd)
      have h4 : (0:ℝ) < (e + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1) :=
        Real.rpow_pos_of_pos hV0 _
      exact mul_le_mul_of_nonneg_right hcwb h4.le
  obtain ⟨c₃, hc₃0, hM⟩ : ∃ c₃ : ℝ, 0 < c₃ ∧
      ∀ e : ℝ, 0 < e → e ≤ 1 → ∀ a b : EuclideanSpace ℝ (Fin n),
        c₃ * (e + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2
          ≤ ∑ i, (Ae e a i - Ae e b i) * (a i - b i) := by
    refine ⟨CM * γ₀ * cw, by positivity, ?_⟩
    intro e he0 he1 a b
    by_cases hab : a = b
    · subst hab
      simp
    · have hV0 : (0:ℝ) < e + ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
        nlinarith [sq_nonneg ‖a‖, sq_nonneg ‖b‖]
      have hWqcont : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
          (‖a + Real.sqrt e • z‖ ^ 2 + ‖b + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)) :=
        (by fun_prop : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
          ‖a + Real.sqrt e • z‖ ^ 2
            + ‖b + Real.sqrt e • z‖ ^ 2)).rpow_const
          (fun z => Or.inl (ne_of_gt (hWposg a b _ hab)))
      have hca : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
          A (a + Real.sqrt e • z)) :=
        hAcont.comp (continuous_const.add (continuous_const_smul _))
      have hcb : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
          A (b + Real.sqrt e • z)) :=
        hAcont.comp (continuous_const.add (continuous_const_smul _))
      have hScont : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
          ∑ i, (A (a + Real.sqrt e • z) i - A (b + Real.sqrt e • z) i)
            * (a i - b i)) := by
        refine continuous_finsetSum _ (fun i _ => ?_)
        exact (((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hca).sub
          ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hcb)).mul continuous_const
      -- the difference of the mollified field, under the integral
      have hdiff : Ae e a - Ae e b
          = ∫ z, ρ z • (A (a + Real.sqrt e • z) - A (b + Real.sqrt e • z)) := by
        rw [hAeeq e a, hAeeq e b,
          show ((∫ z, ρ z • A (a + Real.sqrt e • z))
              - ∫ z, ρ z • A (Real.sqrt e • z))
            - ((∫ z, ρ z • A (b + Real.sqrt e • z))
              - ∫ z, ρ z • A (Real.sqrt e • z))
            = (∫ z, ρ z • A (a + Real.sqrt e • z))
              - ∫ z, ρ z • A (b + Real.sqrt e • z) from by abel,
          ← integral_sub (hρFint _ hca) (hρFint _ hcb)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        show ρ z • A (a + Real.sqrt e • z) - ρ z • A (b + Real.sqrt e • z)
          = ρ z • (A (a + Real.sqrt e • z) - A (b + Real.sqrt e • z))
        rw [smul_sub]
      have hsum : (∑ i, (Ae e a i - Ae e b i) * (a i - b i))
          = ∫ z, ρ z * ∑ i, (A (a + Real.sqrt e • z) i
              - A (b + Real.sqrt e • z) i) * (a i - b i) := by
        have h0 : (∑ i, (Ae e a i - Ae e b i) * (a i - b i))
            = (innerSL ℝ (a - b)) (Ae e a - Ae e b) := by
          refine Eq.trans ?_ (hIP (Ae e a - Ae e b) (a - b))
          exact Finset.sum_congr rfl fun i _ => rfl
        have hint : Integrable (fun z : EuclideanSpace ℝ (Fin n) => ρ z •
            (A (a + Real.sqrt e • z) - A (b + Real.sqrt e • z))) volume :=
          hρFint (fun z => A (a + Real.sqrt e • z) - A (b + Real.sqrt e • z))
            (hca.sub hcb)
        rw [h0, hdiff, ← ContinuousLinearMap.integral_comp_comm
          (innerSL ℝ (a - b)) hint]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        show (innerSL ℝ (a - b))
            (ρ z • (A (a + Real.sqrt e • z) - A (b + Real.sqrt e • z)))
          = ρ z * ∑ i, (A (a + Real.sqrt e • z) i
              - A (b + Real.sqrt e • z) i) * (a i - b i)
        rw [map_smul, smul_eq_mul]
        refine congrArg (fun t => ρ z * t) ?_
        refine Eq.trans (hIP (A (a + Real.sqrt e • z)
          - A (b + Real.sqrt e • z)) (a - b)).symm ?_
        exact Finset.sum_congr rfl fun i _ => rfl
      rw [hsum]
      -- the pointwise monotonicity bound of `A`, integrated
      have hptw : ∀ z : EuclideanSpace ℝ (Fin n),
          ρ z * (CM * γ₀ * ‖a - b‖ ^ 2
            * (‖a + Real.sqrt e • z‖ ^ 2 + ‖b + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1))
            ≤ ρ z * ∑ i, (A (a + Real.sqrt e • z) i
                - A (b + Real.sqrt e • z) i) * (a i - b i) := by
        intro z
        refine mul_le_mul_of_nonneg_left ?_ (hρ0 z)
        have h1 := hMA (a + Real.sqrt e • z) (b + Real.sqrt e • z)
        have h2 : (a + Real.sqrt e • z) - (b + Real.sqrt e • z) = a - b := by abel
        have h3 : ∀ i : Fin n, (a + Real.sqrt e • z) i - (b + Real.sqrt e • z) i
            = a i - b i := by
          intro i
          show (a i + (Real.sqrt e • z) i) - (b i + (Real.sqrt e • z) i) = a i - b i
          ring
        rw [h2, zero_add] at h1
        rw [Finset.sum_congr rfl (fun i _ => by rw [h3 i])] at h1
        calc CM * γ₀ * ‖a - b‖ ^ 2
              * (‖a + Real.sqrt e • z‖ ^ 2 + ‖b + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)
            = CM * γ₀ * (‖a + Real.sqrt e • z‖ ^ 2
                + ‖b + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2 := by ring
          _ ≤ _ := h1
      have hmono : (∫ z, ρ z * (CM * γ₀ * ‖a - b‖ ^ 2
            * (‖a + Real.sqrt e • z‖ ^ 2
              + ‖b + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)))
          ≤ ∫ z, ρ z * ∑ i, (A (a + Real.sqrt e • z) i
              - A (b + Real.sqrt e • z) i) * (a i - b i) :=
        integral_mono (hρfint _ (continuous_const.mul hWqcont))
          (hρfint _ hScont) hptw
      have hconst : (∫ z, ρ z * (CM * γ₀ * ‖a - b‖ ^ 2
            * (‖a + Real.sqrt e • z‖ ^ 2
              + ‖b + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1)))
          = CM * γ₀ * ‖a - b‖ ^ 2 * ∫ z, ρ z
            * (‖a + Real.sqrt e • z‖ ^ 2
              + ‖b + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        show ρ z * (CM * γ₀ * ‖a - b‖ ^ 2 * _)
          = CM * γ₀ * ‖a - b‖ ^ 2 * (ρ z * _)
        ring
      rw [hconst] at hmono
      refine le_trans ?_ hmono
      have hw := hWbd e he0 he1 a b hab
      calc CM * γ₀ * cw * (e + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2
          = CM * γ₀ * ‖a - b‖ ^ 2 * (cw * (e + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1)) := by
            ring
        _ ≤ CM * γ₀ * ‖a - b‖ ^ 2 * ∫ z, ρ z
              * (‖a + Real.sqrt e • z‖ ^ 2
                + ‖b + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) :=
            mul_le_mul_of_nonneg_left hw (by positivity)
  exact ⟨hWbd, c₃, hc₃0, hM⟩
