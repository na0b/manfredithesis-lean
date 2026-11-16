import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pZeroOn
import ManfrediThesis.CitedDirichletW1p
import ManfrediThesis.StructureMonotonicityBound
import ManfrediThesis.StructureGrowthBound
import ManfrediThesis.SmoothCompactSupportMemW1p
import ManfrediThesis.MollifiedFieldStructure
import ManfrediThesis.WeakSolutionZeroTest
import ManfrediThesis.MollifiedSolutionGradientLpConvergence
import ManfrediThesis.MollifiedFieldWeightAndMonotonicity
open MeasureTheory
set_option maxHeartbeats 1400000

/-- The approximation of the degenerate case `ε = 0` by the nondegenerate cases
`ε > 0`, along a sequence `eₘ → 0` and with the structure ratio of the
approximating problems bounded by a constant depending only on `p` and the
original ratio bound `r`. -/
theorem DegenerateLimitTransfer :
    ∀ (n : ℕ) (p r : ℝ), 2 ≤ n → 1 < p → 0 < r →
      ∃ r' : ℝ, 0 < r' ∧
        ∀ (γ₀ γ₁ : ℝ), 0 < γ₀ → γ₁ ≤ r * γ₀ →
          ∀ (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)), A 0 = 0 →
            EllipticStructureQ12 n p 0 γ₀ γ₁ Set.univ (fun _ _ h => A h) →
            (∀ (ε γ₀' γ₁' : ℝ)
              (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
              0 < γ₀' → 0 < γ₁' → CitedDirichletW1p n p ε γ₀' γ₁' A') →
            ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
              (u : EuclideanSpace ℝ (Fin n) → ℝ)
              (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
              0 < R →
              MemW1pOn n p (Metric.ball x₀ R) u g →
              IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h)
                (fun _ _ _ => 0) u g →
              ∃ (em : ℕ → ℝ)
                (Ae : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
                (ue : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
                (ge : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
                (∀ m : ℕ, 0 < em m) ∧
                Filter.Tendsto em Filter.atTop (nhds 0) ∧
                (∀ m : ℕ, Ae m 0 = 0 ∧
                  ∃ γ₀' γ₁' : ℝ, 0 < γ₀' ∧ γ₁' ≤ r' * γ₀' ∧
                    EllipticStructureQ12 n p (em m) γ₀' γ₁' Set.univ
                      (fun _ _ h => Ae m h)) ∧
                (∀ m : ℕ,
                  IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => Ae m h)
                    (fun _ _ _ => 0) (ue m) (ge m)) ∧
                (∀ m : ℕ,
                  MemW1pZeroOn n p (Metric.ball x₀ R)
                    (fun x => ue m x - u x) (fun x => ge m x - g x)) ∧
                Filter.Tendsto
                  (fun m => ∫ x in Metric.ball x₀ R, ‖ge m x - g x‖ ^ p)
                  Filter.atTop (nhds 0) ∧
                (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
                  Filter.Tendsto (fun m => ge m x) Filter.atTop (nhds (g x))) := by
  intro n p r hn hp hr
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  -- the mollifier of the Preamble, with the six properties used below
  obtain ⟨ρ, hρsm, hρ0, hρsupp, hρint, hρκ⟩ :
      ∃ ρ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) ρ ∧ (∀ z, 0 ≤ ρ z) ∧
        tsupport ρ ⊆ Metric.closedBall 0 1 ∧ (∫ z, ρ z) = 1 ∧
        (∃ κ : ℝ, 0 < κ ∧
          ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (7 / 8), κ ≤ ρ z) := by
    set B : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
      ⟨7 / 8, 1, by norm_num, by norm_num⟩ with hBdef
    refine ⟨B.normed volume, B.contDiff_normed, fun z => B.nonneg_normed z, ?_,
      B.integral_normed, ?_⟩
    · have h := B.tsupport_normed_eq (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      rw [h]
    · have hpos : (0 : ℝ) < ∫ x, B x := B.integral_pos (μ := volume)
      refine ⟨1 / ∫ x, B x, by positivity, fun z hz => ?_⟩
      have h1 : B z = 1 := B.one_of_mem_closedBall (by simpa [hBdef] using hz)
      rw [ContDiffBump.normed_def, h1]
  -- the construction: the mollified family and its structure constants
  obtain ⟨r', hr'0, hfam⟩ :=
    MollifiedFieldStructure n p r ρ hn hp hr hρsm hρ0 hρsupp hρint hρκ
  refine ⟨r', hr'0, ?_⟩
  intro γ₀ γ₁ hγ₀ hγ₁r A hA0 hQ hC2 x₀ R u g hR hu hsol
  obtain ⟨Ae, hAedef⟩ :
      ∃ Ae : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Ae = fun e h => (∫ z, ρ z • A (h + Real.sqrt e • z))
          - ∫ z, ρ z • A (Real.sqrt e • z) := ⟨_, rfl⟩
  have hAeeq : ∀ e h, Ae e h = (∫ z, ρ z • A (h + Real.sqrt e • z))
      - ∫ z, ρ z • A (Real.sqrt e • z) := fun e h => by rw [hAedef]
  have hAe0 : ∀ e, Ae e 0 = 0 := by
    intro e
    rw [hAeeq e 0]
    simp
  -- clause (1), at every admissible parameter
  have hAeQ : ∀ e : ℝ, 0 < e → e ≤ 1 →
      ∃ γ₀' γ₁' : ℝ, 0 < γ₀' ∧ γ₁' ≤ r' * γ₀' ∧
        EllipticStructureQ12 n p e γ₀' γ₁' Set.univ (fun _ _ h => Ae e h) := by
    intro e he0 he1
    obtain ⟨γ₀', γ₁', h1, h2, h3⟩ := hfam γ₀ γ₁ A hγ₀ hγ₁r hQ e he0 he1
    refine ⟨γ₀', γ₁', h1, h2, ?_⟩
    rw [hAedef]
    exact h3
  -- Step 1: the structure constants of an `x`-independent field are ordered
  have hposgamma : ∀ (ε' γ₀' γ₁' : ℝ)
      (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      0 ≤ ε' → EllipticStructureQ12 n p ε' γ₀' γ₁' Set.univ (fun _ _ h => A' h) →
      γ₀' ≤ γ₁' := by
    intro ε' γ₀' γ₁' A' hε' hQ'
    obtain ⟨i0⟩ : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
    obtain ⟨e1, he1def⟩ : ∃ e1 : EuclideanSpace ℝ (Fin n),
        e1 = EuclideanSpace.single i0 (1 : ℝ) := ⟨_, rfl⟩
    have hen : ‖e1‖ = 1 := by rw [he1def]; simp
    have hen2 : ‖e1‖ ^ 2 = 1 := by rw [hen]; norm_num
    have hguard : ε' + ‖e1‖ ^ 2 ≠ 0 := by
      rw [hen2]
      exact ne_of_gt (by linarith)
    have hneb : Filter.NeBot (ae (volume.restrict (Set.univ :
        Set (EuclideanSpace ℝ (Fin n))))) := by
      refine ae_neBot.2 ?_
      simp only [ne_eq, Measure.restrict_eq_zero]
      exact (isOpen_univ.measure_pos volume ⟨0, trivial⟩).ne'
    obtain ⟨x, ⟨hx1, hx2⟩, hxΩ⟩ :=
      ((ae_restrict_of_ae (hQ'.Q1.and hQ'.Q2)).and
        (ae_restrict_mem MeasurableSet.univ)).exists
    have hQ1 := hx1 hxΩ 0 e1 e1 hguard
    have hQ2 := hx2 hxΩ 0 e1 i0 i0 hguard
    have hsum : (∑ i, (fderiv ℝ (fun h => A' h) e1 e1) i * e1 i)
        = (fderiv ℝ (fun h => A' h) e1 e1) i0 := by
      rw [he1def]
      simp
    rw [hsum, hen2, mul_one] at hQ1
    rw [← he1def, hen2] at hQ2
    have hpow : (0 : ℝ) < (ε' + 1) ^ (p / 2 - 1) :=
      Real.rpow_pos_of_pos (by linarith) _
    have hle : (fderiv ℝ (fun h => A' h) e1 e1) i0 ≤ γ₁' * (ε' + 1) ^ (p / 2 - 1) :=
      le_trans (le_abs_self _) hQ2
    exact le_of_mul_le_mul_right (by linarith) hpow
  -- Step 3: clauses (2) and (3), from the cited result (C2)
  have hstep3 : ∀ e : ℝ, 0 < e → e ≤ 1 →
      ∃ (ue : EuclideanSpace ℝ (Fin n) → ℝ)
        (ge : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => Ae e h)
            (fun _ _ _ => 0) ue ge ∧
          MemW1pZeroOn n p (Metric.ball x₀ R)
            (fun x => ue x - u x) (fun x => ge x - g x) := by
    intro e he0 he1
    obtain ⟨γ₀', γ₁', hγ₀', hγ₁'r, hQe⟩ := hAeQ e he0 he1
    have hγ₁'0 : 0 < γ₁' :=
      lt_of_lt_of_le hγ₀' (hposgamma e γ₀' γ₁' (Ae e) he0.le hQe)
    exact hC2 e γ₀' γ₁' (Ae e) hγ₀' hγ₁'0 hQe he0.le (hAe0 e) x₀ R hR u g hu
  -- the sequence `ẽ_m = 1/(m+1)` of Step 9, and the solutions it carries
  have hem0 : ∀ m : ℕ, (0 : ℝ) < 1 / ((m : ℝ) + 1) := by
    intro m
    have : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    positivity
  have hem1 : ∀ m : ℕ, (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 := by
    intro m
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  choose U G hUsol hUzero using
    fun m : ℕ => hstep3 (1 / ((m : ℝ) + 1)) (hem0 m) (hem1 m)
  -- Mollifier toolkit: integrability, the norm bound and the averaging bound.
  have hρcs : HasCompactSupport ρ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 1) isClosed_closure hρsupp
  have hρc : Continuous ρ := hρsm.continuous
  have hρfint : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Continuous f →
      Integrable (fun z => ρ z * f z) volume := by
    intro f hf
    refine Continuous.integrable_of_hasCompactSupport (hρc.mul hf) ?_
    refine HasCompactSupport.intro hρcs ?_
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hρFint : ∀ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      Continuous F → Integrable (fun z => ρ z • F z) volume := by
    intro F hF
    refine Continuous.integrable_of_hasCompactSupport (hρc.smul hF) ?_
    refine HasCompactSupport.intro hρcs ?_
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
  have hρavg : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ), Continuous f →
      (∀ z ∈ tsupport ρ, f z ≤ C) → (∫ z, ρ z * f z) ≤ C := by
    intro f C hf hbd
    have h1 : (∫ z, ρ z * f z) ≤ ∫ z, ρ z * C := by
      refine integral_mono (hρfint f hf) (hρfint _ continuous_const) ?_
      intro z
      show ρ z * f z ≤ ρ z * C
      by_cases hz : z ∈ tsupport ρ
      · exact mul_le_mul_of_nonneg_left (hbd z hz) (hρ0 z)
      · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, zero_mul]
    have h2 : (∫ z, ρ z * C) = C := by
      rw [integral_mul_const, hρint, one_mul]
    rw [h2] at h1
    exact h1
  have hρnorm : ∀ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      Continuous F → ‖∫ z, ρ z • F z‖ ≤ ∫ z, ρ z * ‖F z‖ := by
    intro F hF
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show ‖ρ z • F z‖ = ρ z * ‖F z‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ0 z)]
  -- the growth bound (G), uniform in the parameter
  have hγ₁0 : 0 < γ₁ := lt_of_lt_of_le hγ₀ (hposgamma 0 γ₀ γ₁ A le_rfl hQ)
  have hAcont : Continuous A := hQ.hcont 0 (Set.mem_univ 0) 0
  obtain ⟨cG, hcG0, hcG⟩ := StructureGrowthBound n p hn hp
  have hAgrow : ∀ h : EuclideanSpace ℝ (Fin n),
      ‖A h‖ ≤ cG * γ₁ * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2) := by
    have hae := hcG 0 γ₀ γ₁ Set.univ (fun _ _ h => A h) le_rfl hγ₀ hγ₁0 hQ
    have hneb : Filter.NeBot (ae (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
      refine ae_neBot.2 (fun hc => ?_)
      have hpos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))) Set.univ :=
        isOpen_univ.measure_pos volume ⟨0, trivial⟩
      rw [hc] at hpos
      simp at hpos
    obtain ⟨x, hx⟩ := hae.exists
    intro h
    have h1 := hx (Set.mem_univ x) 0 h
    show ‖A h‖ ≤ cG * γ₁ * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2)
    have hA00 : ‖A 0‖ = 0 := by rw [hA0]; simp
    rw [hA00, zero_add, zero_add] at h1
    have hmon : (‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖ ≤ (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2) := by
      by_cases hh : h = 0
      · rw [hh]
        simp only [norm_zero, mul_zero]
        exact Real.rpow_nonneg (by norm_num) _
      · have hn0 : 0 < ‖h‖ := norm_pos_iff.2 hh
        have he1 : (‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖ = (‖h‖ ^ 2) ^ ((p - 1) / 2) := by
          have hc : (‖h‖ : ℝ) ^ (2 : ℝ) = ‖h‖ ^ 2 := by
            rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
          rw [← hc]
          simp only [← Real.rpow_mul hn0.le]
          rw [show 2 * ((p - 1) / 2) = 2 * (p / 2 - 1) + 1 by ring,
            Real.rpow_add hn0, Real.rpow_one]
        rw [he1]
        refine Real.rpow_le_rpow (sq_nonneg _) (by linarith) (by linarith)
    calc ‖A h‖ ≤ cG * γ₁ * (‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖ := h1
      _ = cG * γ₁ * ((‖h‖ ^ 2) ^ (p / 2 - 1) * ‖h‖) := by ring
      _ ≤ cG * γ₁ * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2) :=
          mul_le_mul_of_nonneg_left hmon (by positivity)
  have hq'0 : (0:ℝ) < (p - 1) / 2 := by linarith
  have hone : ∀ c : ℝ, 1 ≤ c → (1:ℝ) ≤ c ^ ((p - 1) / 2) := by
    intro c hc
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hc hq'0.le
    rwa [Real.one_rpow] at h
  have hWone : ∀ h : EuclideanSpace ℝ (Fin n),
      (1:ℝ) ≤ (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2) :=
    fun h => hone _ (by nlinarith [sq_nonneg ‖h‖])
  have hsuppz : ∀ z ∈ tsupport ρ, ‖z‖ ≤ 1 := by
    intro z hz
    have := hρsupp hz
    rwa [mem_closedBall_zero_iff] at this
  obtain ⟨Γ, hΓ0, hΓA, hΓAe⟩ : ∃ Γ : ℝ, 0 < Γ ∧
      (∀ h : EuclideanSpace ℝ (Fin n), ‖A h‖ ≤ Γ * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2)) ∧
      ∀ e : ℝ, 0 < e → e ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin n),
        ‖Ae e h‖ ≤ Γ * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2) := by
    refine ⟨cG * γ₁ * ((3:ℝ) ^ ((p - 1) / 2) + (2:ℝ) ^ ((p - 1) / 2)),
      by positivity, ?_, ?_⟩
    · intro h
      refine le_trans (hAgrow h) (mul_le_mul_of_nonneg_right ?_
        (Real.rpow_nonneg (by nlinarith [sq_nonneg ‖h‖]) _))
      have hcg : (0:ℝ) ≤ cG * γ₁ := by positivity
      have hsum : (1:ℝ) ≤ (3:ℝ) ^ ((p - 1) / 2) + (2:ℝ) ^ ((p - 1) / 2) := by
        linarith [hone 3 (by norm_num), hone 2 (by norm_num)]
      calc cG * γ₁ = cG * γ₁ * 1 := by ring
        _ ≤ cG * γ₁ * ((3:ℝ) ^ ((p - 1) / 2) + (2:ℝ) ^ ((p - 1) / 2)) :=
            mul_le_mul_of_nonneg_left hsum hcg
    · intro e he0 he1 h
      have hte : Real.sqrt e ≤ 1 := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt he1
      have hte0 : 0 ≤ Real.sqrt e := Real.sqrt_nonneg e
      have hc1 : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
          A (h + Real.sqrt e • z)) :=
        hAcont.comp (continuous_const.add (continuous_const_smul _))
      have hc2 : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
          A (Real.sqrt e • z)) := hAcont.comp (continuous_const_smul _)
      have hb1 : (∫ z, ρ z * ‖A (h + Real.sqrt e • z)‖)
          ≤ cG * γ₁ * (3:ℝ) ^ ((p - 1) / 2) * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2) := by
        refine hρavg _ _ (continuous_norm.comp hc1) ?_
        intro z hz
        have hzn := hsuppz z hz
        have hnm : ‖h + Real.sqrt e • z‖ ≤ ‖h‖ + 1 := by
          have h1 : ‖(Real.sqrt e • z : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hte0]
            nlinarith [norm_nonneg z]
          calc ‖h + Real.sqrt e • z‖ ≤ ‖h‖ + ‖(Real.sqrt e • z : EuclideanSpace ℝ (Fin n))‖ :=
              norm_add_le _ _
            _ ≤ ‖h‖ + 1 := by linarith
        have hbase : 1 + ‖h + Real.sqrt e • z‖ ^ 2 ≤ 3 * (1 + ‖h‖ ^ 2) := by
          nlinarith [norm_nonneg (h + Real.sqrt e • z), norm_nonneg h, sq_nonneg (‖h‖ - 1)]
        calc ‖A (h + Real.sqrt e • z)‖
            ≤ cG * γ₁ * (1 + ‖h + Real.sqrt e • z‖ ^ 2) ^ ((p - 1) / 2) := hAgrow _
          _ ≤ cG * γ₁ * (3 * (1 + ‖h‖ ^ 2)) ^ ((p - 1) / 2) := by
              refine mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (by positivity) hbase hq'0.le) (by positivity)
          _ = cG * γ₁ * (3:ℝ) ^ ((p - 1) / 2) * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2) := by
              rw [Real.mul_rpow (by norm_num) (by positivity)]
              ring
      have hb2 : (∫ z, ρ z * ‖A (Real.sqrt e • z)‖)
          ≤ cG * γ₁ * (2:ℝ) ^ ((p - 1) / 2) * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2) := by
        refine hρavg _ _ (continuous_norm.comp hc2) ?_
        intro z hz
        have hzn := hsuppz z hz
        have h1 : ‖(Real.sqrt e • z : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hte0]
          nlinarith [norm_nonneg z]
        have hbase : 1 + ‖(Real.sqrt e • z : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ 2 := by
          nlinarith [norm_nonneg (Real.sqrt e • z : EuclideanSpace ℝ (Fin n))]
        calc ‖A (Real.sqrt e • z)‖
            ≤ cG * γ₁ * (1 + ‖(Real.sqrt e • z : EuclideanSpace ℝ (Fin n))‖ ^ 2)
                ^ ((p - 1) / 2) := hAgrow _
          _ ≤ cG * γ₁ * (2:ℝ) ^ ((p - 1) / 2) := by
              refine mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (by positivity) hbase hq'0.le) (by positivity)
          _ ≤ cG * γ₁ * (2:ℝ) ^ ((p - 1) / 2) * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2) := by
              have hc0 : (0:ℝ) ≤ cG * γ₁ * (2:ℝ) ^ ((p - 1) / 2) := by positivity
              calc cG * γ₁ * (2:ℝ) ^ ((p - 1) / 2)
                  = cG * γ₁ * (2:ℝ) ^ ((p - 1) / 2) * 1 := by ring
                _ ≤ _ := mul_le_mul_of_nonneg_left (hWone h) hc0
      rw [hAeeq e h]
      calc ‖(∫ z, ρ z • A (h + Real.sqrt e • z))
              - ∫ z, ρ z • A (Real.sqrt e • z)‖
          ≤ ‖∫ z, ρ z • A (h + Real.sqrt e • z)‖
            + ‖∫ z, ρ z • A (Real.sqrt e • z)‖ := norm_sub_le _ _
        _ ≤ (∫ z, ρ z * ‖A (h + Real.sqrt e • z)‖)
            + ∫ z, ρ z * ‖A (Real.sqrt e • z)‖ :=
            add_le_add (hρnorm _ hc1) (hρnorm _ hc2)
        _ ≤ cG * γ₁ * ((3:ℝ) ^ ((p - 1) / 2) + (2:ℝ) ^ ((p - 1) / 2))
              * (1 + ‖h‖ ^ 2) ^ ((p - 1) / 2) := by
            have hadd := add_le_add hb1 hb2
            linarith [hadd]
  have hsq2 : ∀ x y : EuclideanSpace ℝ (Fin n),
      ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    intro x y
    have h1 := norm_add_le x y
    nlinarith [h1, norm_nonneg x, norm_nonneg y, norm_nonneg (x + y),
      sq_nonneg (‖x‖ - ‖y‖)]
  have hρavg' : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ), Continuous f →
      (∀ z ∈ tsupport ρ, C ≤ f z) → C ≤ ∫ z, ρ z * f z := by
    intro f C hf hbd
    have h1 : (∫ z, ρ z * C) ≤ ∫ z, ρ z * f z := by
      refine integral_mono (hρfint _ continuous_const) (hρfint f hf) ?_
      intro z
      show ρ z * C ≤ ρ z * f z
      by_cases hz : z ∈ tsupport ρ
      · exact mul_le_mul_of_nonneg_left (hbd z hz) (hρ0 z)
      · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, zero_mul]
    have h2 : (∫ z, ρ z * C) = C := by
      rw [integral_mul_const, hρint, one_mul]
    rw [h2] at h1
    exact h1
  -- the monotonicity bound (M), uniform in the parameter
  have hneb : Filter.NeBot (ae (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    refine ae_neBot.2 (fun hc => ?_)
    have hpos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))) Set.univ :=
      isOpen_univ.measure_pos volume ⟨0, trivial⟩
    rw [hc] at hpos
    simp at hpos
  obtain ⟨CM, hCM0, hCMb⟩ := StructureMonotonicityBound n p r hn hp hr
  have hMA : ∀ a b : EuclideanSpace ℝ (Fin n),
      CM * γ₀ * (0 + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2
        ≤ ∑ i, (A a i - A b i) * (a i - b i) := by
    obtain ⟨x, hx⟩ :=
      (hCMb 0 γ₀ γ₁ Set.univ (fun _ _ h => A h) le_rfl hγ₀ hγ₁r hQ).exists
    intro a b
    exact hx (Set.mem_univ x) 0 a b
  have hIP : ∀ v w : EuclideanSpace ℝ (Fin n), (∑ i, v i * w i) = (innerSL ℝ w) v := by
    intro v w
    show (∑ i, v i * w i) = inner ℝ w v
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => by simp
  obtain ⟨c₁, C₂w, hc₁0, hc₁C₂, hsw⟩ :=
    WeightSandwich n p ρ hn hp hρsm hρ0 hρsupp hρint hρκ
  obtain ⟨cw, hcw0, hcwa, hcwb⟩ : ∃ cw : ℝ, 0 < cw ∧
      cw ≤ min c₁ 1 * (2:ℝ) ^ (-(p / 2 - 1)) ∧ cw ≤ (4:ℝ) ^ (p / 2 - 1) := by
    refine ⟨min (min c₁ 1 * (2:ℝ) ^ (-(p / 2 - 1))) ((4:ℝ) ^ (p / 2 - 1)),
      lt_min (by positivity) (Real.rpow_pos_of_pos (by norm_num) _),
      min_le_left _ _, min_le_right _ _⟩
  have hWposg : ∀ a b w : EuclideanSpace ℝ (Fin n), a ≠ b →
      (0:ℝ) < ‖a + w‖ ^ 2 + ‖b + w‖ ^ 2 := by
    intro a b w hab
    have habn : (0:ℝ) < ‖a - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hab)
    have h1 : ‖a - b‖ ≤ ‖a + w‖ + ‖b + w‖ := by
      calc ‖a - b‖ = ‖(a + w) - (b + w)‖ := by congr 1; abel
        _ ≤ ‖a + w‖ + ‖b + w‖ := norm_sub_le _ _
    have h2 : ‖a - b‖ ^ 2 ≤ 2 * (‖a + w‖ ^ 2 + ‖b + w‖ ^ 2) := by
      nlinarith [h1, norm_nonneg (a + w), norm_nonneg (b + w), norm_nonneg (a - b),
        sq_nonneg (‖a + w‖ - ‖b + w‖)]
    nlinarith [h2, habn]
  -- the uniform-in-`e` weight bound and the monotonicity constant it produces.
  -- This is `MollifiedFieldWeightAndMonotonicity`, whose docstring records the
  -- route (the weight sandwich at a single point, the two-point comparison up
  -- to the absolute factors bounding `cw`, then the unmollified monotonicity
  -- bound translated by `√e z` and averaged against `ρ`).  The two conclusions
  -- come together because the first is consumed inside the proof of the second.
  obtain ⟨hWbd, c₃, hc₃0, hM⟩ := MollifiedFieldWeightAndMonotonicity n p ρ hρ0
    hρfint hρFint hsuppz hρavg' γ₀ A hγ₀ hAcont Ae hAeeq CM hCM0 hMA hIP hsq2
    hWposg c₁ C₂w hc₁0 hsw cw hcw0 hcwa hcwb
  -- Steps 4-8: the gradients converge in `L^p(B_R)`.  This is
  -- `MollifiedSolutionGradientLpConvergence`, whose docstring records the route
  -- (the two energy identities (E), the uniform bound (5a) on `Y_e`, the
  -- difference estimate (6), `δ_e → 0` by dominated convergence, and the two
  -- Hoelder cases of Step 8) and the facts it consumes.
  have hLp := MollifiedSolutionGradientLpConvergence n p r' hn hp ρ hρ0 hρint
    hρfint hρFint hsuppz A hA0 hAcont Ae hAeeq hAe0 hAeQ x₀ R u g hR hu hsol
    Γ hΓ0 hΓA hΓAe c₃ hc₃0 hM U G hUsol hUzero
  -- Step 9: an almost everywhere convergent subsequence, by the Preamble item on
  -- extracting one out of `L^q` convergence, at the exponent `p` on `B_R(x₀)`.
  have hgm : AEStronglyMeasurable g (volume.restrict (Metric.ball x₀ R)) :=
    hu.2.2.aestronglyMeasurable
  have hdm : ∀ m : ℕ, MemLp (fun x => G m x - g x) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) := fun m => (hUzero m).1.2.2
  obtain ⟨φ, hφmono, hφae⟩ : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
        Filter.Tendsto (fun j => G (φ j) x) Filter.atTop (nhds (g x)) := by
    have hp0 : (0 : ℝ) < p := by linarith
    have hpne : (ENNReal.ofReal p) ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le, hp0]
    have hptop : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hptoReal : (ENNReal.ofReal p).toReal = p := by
      rw [ENNReal.toReal_ofReal hp0.le]
    have heq : ∀ m : ℕ,
        eLpNorm (fun x => G m x - g x) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R))
          = (ENNReal.ofReal (∫ x in Metric.ball x₀ R, ‖G m x - g x‖ ^ p)) ^ (1 / p) := by
      intro m
      have hint : Integrable (fun x => ‖G m x - g x‖ ^ p)
          (volume.restrict (Metric.ball x₀ R)) := by
        have h := (hdm m).integrable_norm_rpow hpne hptop
        rwa [hptoReal] at h
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hptop, hptoReal,
        ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun x => by positivity)]
      congr 1
      refine lintegral_congr fun x => ?_
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ofReal_norm]
    have hofr : Filter.Tendsto
        (fun m : ℕ => ENNReal.ofReal (∫ x in Metric.ball x₀ R, ‖G m x - g x‖ ^ p))
        Filter.atTop (nhds 0) := by
      have h := (ENNReal.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto.comp hLp
      rw [ENNReal.ofReal_zero] at h
      exact h.congr fun m => rfl
    have help : Filter.Tendsto
        (fun m : ℕ => eLpNorm (fun x => G m x - g x) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R))) Filter.atTop (nhds 0) := by
      simp only [heq]
      have h := ((ENNReal.continuous_rpow_const (y := 1 / p)).continuousAt
        (x := (0 : ENNReal))).tendsto.comp hofr
      rw [ENNReal.zero_rpow_of_pos (by positivity : (0 : ℝ) < 1 / p)] at h
      exact h.congr fun m => rfl
    have hGm : ∀ m, AEStronglyMeasurable (G m) (volume.restrict (Metric.ball x₀ R)) := by
      intro m
      have h := (hdm m).aestronglyMeasurable.add hgm
      exact h.congr (Filter.Eventually.of_forall fun x => by simp)
    have hmeas : TendstoInMeasure (volume.restrict (Metric.ball x₀ R)) G
        Filter.atTop g :=
      tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top hpne hptop hGm hgm
        (help.congr fun m => rfl)
    exact hmeas.exists_seq_tendsto_ae
  have hφtop : Filter.Tendsto φ Filter.atTop Filter.atTop := hφmono.tendsto_atTop
  refine ⟨fun j => 1 / ((φ j : ℝ) + 1), fun j => Ae (1 / ((φ j : ℝ) + 1)),
    fun j => U (φ j), fun j => G (φ j), fun j => hem0 (φ j), ?_, ?_,
    fun j => hUsol (φ j), fun j => hUzero (φ j), ?_, hφae⟩
  · have h1 : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact h1.comp hφtop
  · exact fun j => ⟨hAe0 _, hAeQ _ (hem0 (φ j)) (hem1 (φ j))⟩
  · exact hLp.comp hφtop
