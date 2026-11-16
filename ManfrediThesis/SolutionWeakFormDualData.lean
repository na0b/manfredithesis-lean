import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.EllipticStructureQ345
open MeasureTheory

/-- The two integrability facts that make the weak form of
`div A(x,u,∇u) = B(x,u,∇u)` a pairing one may split and pass to limits in: the
field evaluated along the solution lies in the dual Lebesgue class
`L^{p'}`, and the right-hand side evaluated along the solution lies in `L¹`.
Both are read off the same clause family of `EllipticStructureQ345` -- (Q4) for
the field and (Q5) for the right-hand side -- against the same Carathéodory
measurability argument, which is why they are one node and not two.  They are
used wherever (5.4) splits an integral or (5.8) bounds the `B`-term.

Unlike `FrozenFieldDualMemLp`, which is stated for a field constant in `x` and
`z` and needs only the normalised (Q1)-(Q2) bundle, the unfrozen field carries
no normalisation, so the value at `h = 0` has to be supplied: that is clause
(Q4) of `EllipticStructureQ345`, read at `h = 0`, where
`(1 + |0|²)^{(p-1)/2} = 1` and each component is bounded by `γ₃`.  Measurability
of `x ↦ A x (u x) (g x)` is likewise not automatic here and comes from the two
Carathéodory clauses `meas_x` and `cont_zh` of `EllipticStructureQ12` together
with the measurability of `u` and `g`; the same argument run on `measB_x` and
`contB_zh` of `EllipticStructureQ345` gives it for `x ↦ B x (u x) (g x)`. -/
theorem SolutionWeakFormDualData :
    ∀ (n : ℕ) (p ε μ γ₀ γ₁ γ₂ γ₃ γ₄ : ℝ), 2 ≤ n → 1 < p → 0 ≤ ε → ε ≤ 1 →
      0 < γ₀ → 0 < γ₁ → 0 < γ₃ → 0 < γ₄ →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n))
        (B : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (S : Set (EuclideanSpace ℝ (Fin n))),
        EllipticStructureQ12 n p ε γ₀ γ₁ Ω A →
        EllipticStructureQ345 n p ε μ γ₂ γ₃ γ₄ Ω A B →
        MeasurableSet S → S ⊆ Ω → volume S ≠ ⊤ →
        MemLp u (ENNReal.ofReal p) (volume.restrict S) →
        MemLp g (ENNReal.ofReal p) (volume.restrict S) →
        MemLp (fun x => A x (u x) (g x)) (ENNReal.ofReal (p / (p - 1)))
            (volume.restrict S)
          ∧ IntegrableOn (fun x => B x (u x) (g x)) S volume := by
  intro n p ε μ γ₀ γ₁ γ₂ γ₃ γ₄ hn hp hε hε1 hγ₀ hγ₁ hγ₃ hγ₄ Ω A B u g S hQ12 hQ345
    hSms hSsub hSfin huLp hgLp
  have hp0 : (0:ℝ) < p := by linarith
  have hp1 : (0:ℝ) < p - 1 := by linarith
  have hfin : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hSfin⟩
  have htoR : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hne0 : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hgp : Integrable (fun x => ‖g x‖ ^ p) (volume.restrict S) := by
    simpa [htoR] using hgLp.integrable_norm_rpow hne0 (by simp)
  -- Step 1: both superpositions are a.e. strongly measurable on `S`
  have hUA : Measurable (Function.uncurry
      (fun (q : ℝ × EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) =>
        A x q.1 q.2)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun x => hQ12.cont_zh x) (fun q => hQ12.meas_x q.1 q.2)
  have hUB : Measurable (Function.uncurry
      (fun (q : ℝ × EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) =>
        B x q.1 q.2)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun x => hQ345.contB_zh x) (fun q => hQ345.measB_x q.1 q.2)
  obtain ⟨u', hu'm, hu'e⟩ := huLp.aestronglyMeasurable
  obtain ⟨g', hg'm, hg'e⟩ := hgLp.aestronglyMeasurable
  have hAmeas : AEStronglyMeasurable (fun x => A x (u x) (g x)) (volume.restrict S) := by
    refine ⟨fun x => A x (u' x) (g' x), ?_, ?_⟩
    · exact Measurable.stronglyMeasurable
        (hUA.comp ((hu'm.measurable.prodMk hg'm.measurable).prodMk measurable_id))
    · filter_upwards [hu'e, hg'e] with x h1 h2
      rw [h1, h2]
  have hBmeas : AEStronglyMeasurable (fun x => B x (u x) (g x)) (volume.restrict S) := by
    refine ⟨fun x => B x (u' x) (g' x), ?_, ?_⟩
    · exact Measurable.stronglyMeasurable
        (hUB.comp ((hu'm.measurable.prodMk hg'm.measurable).prodMk measurable_id))
    · filter_upwards [hu'e, hg'e] with x h1 h2
      rw [h1, h2]
  -- Step 2: the elementary bound, used at both exponents
  have helem : ∀ s q : ℝ, 0 ≤ s → 0 ≤ q →
      (1 + s ^ 2) ^ q ≤ (2:ℝ) ^ q * (1 + s ^ (2 * q)) := by
    intro s q hs hq
    have h20 : (0:ℝ) < (2:ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) _
    have hsq : (0:ℝ) ≤ s ^ (2 * q) := Real.rpow_nonneg hs _
    rcases le_total s 1 with h | h
    · have h1 : (1:ℝ) + s ^ 2 ≤ 2 := by nlinarith
      have h2 : (1 + s ^ 2) ^ q ≤ (2:ℝ) ^ q :=
        Real.rpow_le_rpow (by positivity) h1 hq
      nlinarith [h2, h20.le, hsq]
    · have hs0 : (0:ℝ) < s := lt_of_lt_of_le one_pos h
      have h1 : (1:ℝ) + s ^ 2 ≤ 2 * s ^ 2 := by nlinarith
      have h2 : (1 + s ^ 2) ^ q ≤ (2 * s ^ 2) ^ q :=
        Real.rpow_le_rpow (by positivity) h1 hq
      have h3 : (2 * s ^ 2) ^ q = (2:ℝ) ^ q * s ^ (2 * q) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        congr 1
        rw [show s ^ 2 = s ^ (2:ℝ) by
              rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast],
          ← Real.rpow_mul hs]
      rw [h3] at h2
      nlinarith [h2, h20.le]
  have hQae : AEMeasurable (fun x => 1 + ‖g x‖ ^ 2) (volume.restrict S) :=
    (hgLp.aestronglyMeasurable.aemeasurable.norm.pow_const 2).const_add 1
  have hhalfint : Integrable (fun x => (1 + ‖g x‖ ^ 2) ^ (p / 2))
      (volume.restrict S) := by
    refine ((integrable_const ((2:ℝ) ^ (p/2))).mul_const 1 |>.add
      (hgp.const_mul ((2:ℝ) ^ (p/2)))).mono'
      ((hQae.pow_const (p/2)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    have h := helem ‖g x‖ (p/2) (norm_nonneg _) (by positivity)
    rw [show 2 * (p/2) = p by ring] at h
    calc (1 + ‖g x‖ ^ 2) ^ (p/2)
        ≤ (2:ℝ) ^ (p/2) * (1 + ‖g x‖ ^ p) := h
      _ = (2:ℝ) ^ (p/2) * 1 + (2:ℝ) ^ (p/2) * ‖g x‖ ^ p := by ring
  -- Step 3: the componentwise bound gives a norm bound
  have hnormle : ∀ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ), 0 ≤ c →
      (∀ i, |v i| ≤ c) → ‖v‖ ≤ Real.sqrt n * c := by
    intro v c hc hvc
    rw [EuclideanSpace.norm_eq]
    have h1 : ∑ i, ‖v i‖ ^ 2 ≤ (n : ℝ) * c ^ 2 := by
      have hpt : ∀ i : Fin n, ‖v i‖ ^ 2 ≤ c ^ 2 := by
        intro i
        rw [Real.norm_eq_abs]
        nlinarith [hvc i, abs_nonneg (v i)]
      calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin n, c ^ 2 :=
            Finset.sum_le_sum fun i _ => hpt i
        _ = (n : ℝ) * c ^ 2 := by simp [mul_comm]
    calc Real.sqrt (∑ i, ‖v i‖ ^ 2) ≤ Real.sqrt ((n : ℝ) * c ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt n * c := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hc]
  have hQ4 := hQ345.Q4
  have hAbd : ∀ᵐ x ∂(volume.restrict S),
      ‖A x (u x) (g x)‖
        ≤ Real.sqrt n * γ₃ * (1 + ‖g x‖ ^ 2) ^ ((p - 1) / 2) := by
    filter_upwards [ae_restrict_of_ae hQ4, ae_restrict_mem hSms] with x h1 h2
    have hxΩ : x ∈ Ω := hSsub h2
    have hc0 : (0:ℝ) ≤ γ₃ * (1 + ‖g x‖ ^ 2) ^ ((p - 1) / 2) := by
      have : (0:ℝ) ≤ (1 + ‖g x‖ ^ 2) ^ ((p - 1) / 2) :=
        Real.rpow_nonneg (by positivity) _
      positivity
    have h := hnormle (A x (u x) (g x)) _ hc0 fun i => h1 hxΩ (u x) (g x) i
    calc ‖A x (u x) (g x)‖
        ≤ Real.sqrt n * (γ₃ * (1 + ‖g x‖ ^ 2) ^ ((p - 1) / 2)) := h
      _ = Real.sqrt n * γ₃ * (1 + ‖g x‖ ^ 2) ^ ((p - 1) / 2) := by ring
  -- the dual membership
  have hAmem : MemLp (fun x => A x (u x) (g x))
      (ENNReal.ofReal (p / (p - 1))) (volume.restrict S) := by
    have hne0' : ENNReal.ofReal (p / (p - 1)) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    rw [← integrable_norm_rpow_iff hAmeas hne0' (by simp),
      ENNReal.toReal_ofReal (by positivity)]
    refine (hhalfint.const_mul ((Real.sqrt n * γ₃) ^ (p / (p - 1)))).mono'
      (hAmeas.norm.aemeasurable.pow_const _ |>.aestronglyMeasurable) ?_
    filter_upwards [hAbd] with x h
    have hc0 : (0:ℝ) ≤ Real.sqrt n * γ₃ := by positivity
    have hb0 : (0:ℝ) ≤ (1 + ‖g x‖ ^ 2) ^ ((p - 1) / 2) :=
      Real.rpow_nonneg (by positivity) _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc ‖A x (u x) (g x)‖ ^ (p / (p - 1))
        ≤ (Real.sqrt n * γ₃ * (1 + ‖g x‖ ^ 2) ^ ((p - 1) / 2)) ^ (p / (p - 1)) :=
          Real.rpow_le_rpow (norm_nonneg _) h (by positivity)
      _ = (Real.sqrt n * γ₃) ^ (p / (p - 1)) * (1 + ‖g x‖ ^ 2) ^ (p / 2) := by
          rw [Real.mul_rpow (by positivity) hb0, ← Real.rpow_mul (by positivity)]
          congr 2
          field_simp
  -- the right-hand side is integrable
  have hQ5 := hQ345.Q5
  have hBint : IntegrableOn (fun x => B x (u x) (g x)) S volume := by
    refine (hhalfint.const_mul γ₄).mono' hBmeas ?_
    filter_upwards [ae_restrict_of_ae hQ5, ae_restrict_mem hSms] with x h1 h2
    rw [Real.norm_eq_abs]
    exact h1 (hSsub h2) (u x) (g x)
  exact ⟨hAmem, hBint⟩
