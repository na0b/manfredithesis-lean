import ManfrediThesis.Preamble
import ManfrediThesis.MollifiedFieldIncrementBound
import ManfrediThesis.EllipticStructureQ12
set_option maxHeartbeats 400000
open MeasureTheory

/-- The condition (Q2) for the mollified field at the nondegenerate parameter.

Conventions, restated here because a helper inherits none of its parent's.
`ρ` is the mollifying kernel: smooth, nonnegative and compactly supported,
`supp ρ` meaning its CLOSED support.  For `e > 0` the mollified field is
`A_e(h) = ∫ ρ(z) A(h + √e z) dz − ∫ ρ(z) A(√e z) dz`,
the subtracted constant being the normalisation `A_e(0) = 0`; this is the live
route to the structure conditions at `ε = e`, and it is *not* the perturbation
`A(h) + e^{p/2-1}h`, which does not preserve `γ₀, γ₁`.  The weight is the
`Real.rpow` power `(e + ‖h‖²)^{p/2-1}`, written exactly as (Q1)/(Q2) print it
and never rewritten as an integer power.  `c₁ ≤ C₂` are the two constants of the
weight sandwich for the scalar kernel
`K(h,e) = ∫ (‖h + √e z‖²)^{p/2-1} ρ(z) dz`, taken here as a hypothesis, and
`γ₁' = C₂γ₁` is the (Q2) constant the parent chooses for `A_e`.

The conclusion is the (Q2) field of `EllipticStructureQ12 n p e γ₀' γ₁' univ A_e`
verbatim, and in particular it is an almost-everywhere statement in `x`: (Q1)
and (Q2) are a.e.-`x` clauses while the continuity and `C¹` clauses are
everywhere-`x`, and that distinction is load-bearing.  Here `A_e` does not
depend on `x` at all, so the a.e. quantifier is discharged by
`Filter.Eventually.of_forall`; it is kept in the statement so that the parent
can supply this lemma as that field without reshaping it.

The route is the paper's segment-increment argument.  (Q2) for `A` gives
`|dA(y)e_j|_i ≤ γ₁(‖y‖²)^{p/2-1}` at every `y ≠ 0`, and `A` is `C¹` away from
the origin, so for `h' ≠ h''` whose segment misses the origin the fundamental
theorem of calculus along the segment gives
`|A(h'') − A(h')| ≤ γ₁ |h'' − h'| sup` of the weight along it; integrating that
against `ρ` and using Fubini, the symmetric difference quotient of `A_e` at `h`
in the direction `e_j` is bounded by `γ₁ C₂ (e + ‖h + s e_j‖²)^{p/2-1}` for all
small `s > 0`, the factor `C₂` coming from the weight sandwich.  Letting
`s → 0⁺` and using that `A_e` is differentiable (a hypothesis here, since it is
proved once in the parent for both arms) turns that into the asserted bound at
`h`.  The segments through `h` in the direction `e_j` that meet the origin form
a null set of parameters, which is why the increment bound is taken on an
almost-every segment and the limit is still valid. -/
theorem MollifiedFieldQ2Bound :
    ∀ (n : ℕ) (p : ℝ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ), 2 ≤ n →
      ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) → HasCompactSupport ρ →
      ∀ c₁ C₂ : ℝ, 0 < c₁ → 0 < C₂ →
        (∀ (h : EuclideanSpace ℝ (Fin n)) (e : ℝ), 0 < e →
          c₁ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)
              ≤ ∫ z, (‖h + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ρ z
            ∧ (∫ z, (‖h + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ρ z)
              ≤ C₂ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)) →
      ∀ (γ₀ γ₁ : ℝ) (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        EllipticStructureQ12 n p 0 γ₀ γ₁ Set.univ (fun _ _ h => A h) →
      ∀ e : ℝ, 0 < e →
        ContDiff ℝ (⊤ : ℕ∞) (fun h : EuclideanSpace ℝ (Fin n) =>
          (∫ z, ρ z • A (h + Real.sqrt e • z))
            - ∫ z, ρ z • A (Real.sqrt e • z)) →
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) →
            ∀ (zz : ℝ) (h : EuclideanSpace ℝ (Fin n)) (i j : Fin n),
              e + ‖h‖ ^ 2 ≠ 0 →
              |(fderiv ℝ (fun h' : EuclideanSpace ℝ (Fin n) =>
                  (∫ z, ρ z • A (h' + Real.sqrt e • z))
                    - ∫ z, ρ z • A (Real.sqrt e • z)) h
                (EuclideanSpace.single j (1 : ℝ))) i|
                ≤ C₂ * γ₁ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1) := by
  intro n p ρ hn hρsm hρ0 hρcs c₁ C₂ hc₁0 hC₂0 hsw γ₀ γ₁ A hQ e he0 hsmooth
  have hAcont : Continuous A := hQ.hcont 0 (Set.mem_univ 0) 0
  refine Filter.Eventually.of_forall (fun x _ zz h i j _ => ?_)
  show |(fderiv ℝ (fun h' : EuclideanSpace ℝ (Fin n) =>
        (∫ z, ρ z • A (h' + Real.sqrt e • z))
          - ∫ z, ρ z • A (Real.sqrt e • z)) h
      (EuclideanSpace.single j (1 : ℝ))) i|
    ≤ C₂ * γ₁ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)
  set Ae : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun h' : EuclideanSpace ℝ (Fin n) =>
      (∫ z, ρ z • A (h' + Real.sqrt e • z))
        - ∫ z, ρ z • A (Real.sqrt e • z) with hAedef
  set u : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j (1 : ℝ) with hudef
  have ht0 : 0 < Real.sqrt e := Real.sqrt_pos.2 he0
  have htsq : Real.sqrt e ^ 2 = e := Real.sq_sqrt he0.le
  have hW0 : (0 : ℝ) < e + ‖h‖ ^ 2 := by nlinarith [sq_nonneg ‖h‖]
  have hu0 : (u : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
    intro hc
    have hcc := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v j) hc
    rw [hudef] at hcc
    simp at hcc
  have hneb : Filter.NeBot (ae (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    refine ae_neBot.2 (fun hc => ?_)
    have hpos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))) Set.univ :=
      isOpen_univ.measure_pos volume ⟨0, trivial⟩
    rw [hc] at hpos
    simp at hpos
  -- (Q2) for `A`, read at every point, and its `C¹` regularity off the origin
  obtain ⟨x₁, hx₁⟩ := hQ.Q2.exists
  have hQ2A : ∀ (y : EuclideanSpace ℝ (Fin n)) (i' j' : Fin n), y ≠ 0 →
      |(fderiv ℝ A y (EuclideanSpace.single j' (1 : ℝ))) i'|
        ≤ γ₁ * (0 + ‖y‖ ^ 2) ^ (p / 2 - 1) := by
    intro y i' j' hy
    refine hx₁ (Set.mem_univ x₁) 0 y i' j' ?_
    have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy
    nlinarith
  have hSeq : {y : EuclideanSpace ℝ (Fin n) | (0 : ℝ) + ‖y‖ ^ 2 ≠ 0}
      = {(0 : EuclideanSpace ℝ (Fin n))}ᶜ := by
    ext y
    show (0 : ℝ) + ‖y‖ ^ 2 ≠ 0 ↔ y ∉ ({0} : Set (EuclideanSpace ℝ (Fin n)))
    rw [Set.mem_singleton_iff, zero_add]
    constructor
    · intro hy hc
      exact hy (by rw [hc]; simp)
    · intro hy hc
      exact hy (norm_eq_zero.1 (sq_eq_zero_iff.1 hc))
  have hSopen : IsOpen {y : EuclideanSpace ℝ (Fin n) | (0 : ℝ) + ‖y‖ ^ 2 ≠ 0} := by
    rw [hSeq]
    exact isOpen_compl_singleton
  have hSmem : ∀ y : EuclideanSpace ℝ (Fin n), y ≠ 0 →
      y ∈ {y : EuclideanSpace ℝ (Fin n) | (0 : ℝ) + ‖y‖ ^ 2 ≠ 0} := by
    intro y hy
    rw [hSeq]
    exact hy
  have hAC1 : ContDiffOn ℝ 1 A {y : EuclideanSpace ℝ (Fin n) | (0 : ℝ) + ‖y‖ ^ 2 ≠ 0} :=
    hQ.hdiff 0 (Set.mem_univ 0) 0
  have hAdiff : ∀ y : EuclideanSpace ℝ (Fin n), y ≠ 0 →
      HasFDerivAt A (fderiv ℝ A y) y := by
    intro y hy
    have h1 := (hAC1.differentiableOn (by norm_num)) y (hSmem y hy)
    exact (h1.differentiableAt (hSopen.mem_nhds (hSmem y hy))).hasFDerivAt
  have hAfd : ContinuousOn (fun y => fderiv ℝ A y)
      {y : EuclideanSpace ℝ (Fin n) | (0 : ℝ) + ‖y‖ ^ 2 ≠ 0} := by
    have h1 := hAC1.continuousOn_fderivWithin hSopen.uniqueDiffOn le_rfl
    refine h1.congr (fun y hy => ?_)
    exact (fderivWithin_of_isOpen hSopen hy).symm
  -- the segment increment bound for `A`
  have hIA : ∀ (t : ℝ) (b : EuclideanSpace ℝ (Fin n)),
      (∀ ς ∈ Set.Icc (0 : ℝ) 1, b + (ς * t) • u ≠ 0) →
      |A (b + t • u) i - A b i|
        ≤ |t| * γ₁ * ∫ ς in Set.Ioc (0 : ℝ) 1,
            (‖b + (ς * t) • u‖ ^ 2) ^ (p / 2 - 1) := by
    intro t b hseg
    have hγd : ∀ ς : ℝ, HasDerivAt (fun s : ℝ => b + (s * t) • u) (t • u) ς := by
      intro ς
      have h1 : HasDerivAt (fun s : ℝ => (s * t) • u) ((1 * t) • u) ς :=
        ((hasDerivAt_id ς).mul_const t).smul_const u
      rw [one_mul] at h1
      exact h1.const_add b
    have hφd : ∀ ς ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => A (b + (s * t) • u) i)
          (t * (fderiv ℝ A (b + (ς * t) • u) u) i) ς := by
      intro ς hς
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hς
      have hne := hseg ς hς
      have h2 := (hAdiff _ hne).comp_hasDerivAt ς (hγd ς)
      have h3 := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt).comp_hasDerivAt ς h2
      refine h3.congr_deriv ?_
      show ((EuclideanSpace.proj (𝕜 := ℝ) i) ((fderiv ℝ A (b + (ς * t) • u)) (t • u)))
        = t * (fderiv ℝ A (b + (ς * t) • u) u) i
      rw [map_smul]
      simp
    have hcont : ContinuousOn (fun ς : ℝ =>
        t * (fderiv ℝ A (b + (ς * t) • u) u) i) (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      refine ContinuousOn.mul continuousOn_const ?_
      refine ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn
        (((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) u).continuous).comp_continuousOn ?_))
      refine hAfd.comp (by fun_prop) (fun ς hς => hSmem _ (hseg ς hς))
    have hφint : IntervalIntegrable
        (fun ς : ℝ => t * (fderiv ℝ A (b + (ς * t) • u) u) i) volume 0 1 :=
      hcont.intervalIntegrable
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hφd hφint
    have hmaj : ∀ ς ∈ Set.Icc (0 : ℝ) 1,
        |t * (fderiv ℝ A (b + (ς * t) • u) u) i|
          ≤ |t| * γ₁ * (‖b + (ς * t) • u‖ ^ 2) ^ (p / 2 - 1) := by
      intro ς hς
      rw [abs_mul]
      have h1 := hQ2A (b + (ς * t) • u) i j (hseg ς hς)
      rw [← hudef] at h1
      rw [zero_add] at h1
      calc |t| * |(fderiv ℝ A (b + (ς * t) • u) u) i|
          ≤ |t| * (γ₁ * (‖b + (ς * t) • u‖ ^ 2) ^ (p / 2 - 1)) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg t)
        _ = |t| * γ₁ * (‖b + (ς * t) • u‖ ^ 2) ^ (p / 2 - 1) := by ring
    have hmajint : IntervalIntegrable
        (fun ς : ℝ => |t| * γ₁ * (‖b + (ς * t) • u‖ ^ 2) ^ (p / 2 - 1)) volume 0 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.rpow_const (by fun_prop) (fun ς hς => Or.inl ?_)
      have hne := hseg ς hς
      have : 0 < ‖b + (ς * t) • u‖ := norm_pos_iff.2 hne
      positivity
    calc |A (b + t • u) i - A b i|
        = |∫ ς in (0:ℝ)..1, t * (fderiv ℝ A (b + (ς * t) • u) u) i| := by
          rw [hftc]
          simp
      _ ≤ ∫ ς in (0:ℝ)..1, |t * (fderiv ℝ A (b + (ς * t) • u) u) i| := by
          exact intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ ς in (0:ℝ)..1, |t| * γ₁ * (‖b + (ς * t) • u‖ ^ 2) ^ (p / 2 - 1) :=
          intervalIntegral.integral_mono_on (by norm_num) hφint.abs hmajint hmaj
      _ = |t| * γ₁ * ∫ ς in Set.Ioc (0:ℝ) 1,
            (‖b + (ς * t) • u‖ ^ 2) ^ (p / 2 - 1) := by
          rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
            ← integral_const_mul]
  -- `u` is a unit vector
  have hunorm : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    rw [hudef, PiLp.norm_single]
    exact norm_one
  have hρc : Continuous ρ := hρsm.continuous
  have hγ₁0 : (0 : ℝ) ≤ γ₁ := by
    have h1 := hQ2A u i j hu0
    have h2 : (0 : ℝ) < (0 + ‖(u : EuclideanSpace ℝ (Fin n))‖ ^ 2) ^ (p / 2 - 1) := by
      refine Real.rpow_pos_of_pos ?_ _
      rw [hunorm]
      norm_num
    have h3 : (0 : ℝ) ≤ γ₁ * (0 + ‖(u : EuclideanSpace ℝ (Fin n))‖ ^ 2) ^ (p / 2 - 1) :=
      le_trans (abs_nonneg _) h1
    nlinarith [h2, h3]
  -- the kernel is integrable, free from the sandwich's own lower bound
  have hker : ∀ h' : EuclideanSpace ℝ (Fin n),
      Integrable (fun z => (‖h' + Real.sqrt e • z‖ ^ 2) ^ (p / 2 - 1) * ρ z) volume := by
    intro h'
    by_contra hcon
    have hlow := (hsw h' e he0).1
    rw [integral_undef hcon] at hlow
    have hW0' : (0 : ℝ) < e + ‖h'‖ ^ 2 :=
      add_pos_of_pos_of_nonneg he0 (sq_nonneg _)
    have hWq : (0 : ℝ) < (e + ‖h'‖ ^ 2) ^ (p / 2 - 1) := Real.rpow_pos_of_pos hW0' _
    exact absurd hlow (not_le.2 (mul_pos hc₁0 hWq))
  -- the segment through the origin meets only a null set of `z`
  have hbad : ∀ s : ℝ, s ≠ 0 → ∀ᵐ z : EuclideanSpace ℝ (Fin n),
      ∀ ς ∈ Set.Icc (0 : ℝ) 1, h + Real.sqrt e • z + (ς * s) • u ≠ 0 := by
    intro s hs
    have hne : (ℝ ∙ u) ≠ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := by
      intro hc
      have h1 : Module.finrank ℝ (ℝ ∙ u) = 1 := finrank_span_singleton hu0
      rw [hc] at h1
      have h2 : Module.finrank ℝ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
          = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := finrank_top _ _
      have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
      omega
    have hnull : volume ((fun z : EuclideanSpace ℝ (Fin n) =>
        z + (Real.sqrt e)⁻¹ • h) ⁻¹'
        ((ℝ ∙ u : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
          Set (EuclideanSpace ℝ (Fin n)))) = 0 := by
      rw [measure_preimage_add_right]
      exact Measure.addHaar_submodule volume _ hne
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz ς _ hc
    refine hz ?_
    show z + (Real.sqrt e)⁻¹ • h ∈ (ℝ ∙ u : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    have hsc := congrArg (fun v : EuclideanSpace ℝ (Fin n) => (Real.sqrt e)⁻¹ • v) hc
    simp only [smul_add, smul_zero, smul_smul,
      inv_smul_smul₀ (ne_of_gt ht0)] at hsc
    have h7 : z + (Real.sqrt e)⁻¹ • h + ((Real.sqrt e)⁻¹ * (ς * s)) • u = 0 := by
      have hab : (Real.sqrt e)⁻¹ • h + z + ((Real.sqrt e)⁻¹ * (ς * s)) • u
          = z + (Real.sqrt e)⁻¹ • h + ((Real.sqrt e)⁻¹ * (ς * s)) • u := by abel
      rw [← hab]
      exact hsc
    have h4 : z + (Real.sqrt e)⁻¹ • h
        = (-((Real.sqrt e)⁻¹ * (ς * s))) • u := by
      rw [neg_smul, eq_neg_iff_add_eq_zero]
      exact h7
    rw [h4]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  -- integrability of the mollified field and of its coordinates
  have hAint : ∀ h' : EuclideanSpace ℝ (Fin n),
      Integrable (fun z => ρ z • A (h' + Real.sqrt e • z)) volume := by
    intro h'
    refine Continuous.integrable_of_hasCompactSupport
      (hρc.smul (hAcont.comp (continuous_const.add (continuous_const_smul _)))) ?_
    refine HasCompactSupport.intro hρcs ?_
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
  have hAcoord : ∀ h' : EuclideanSpace ℝ (Fin n),
      Integrable (fun z => ρ z * A (h' + Real.sqrt e • z) i) volume := by
    intro h'
    have hc1 : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
        A (h' + Real.sqrt e • z) i) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
        (hAcont.comp (continuous_const.add (continuous_const_smul _)))
    refine Continuous.integrable_of_hasCompactSupport (hρc.mul hc1) ?_
    refine HasCompactSupport.intro hρcs ?_
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hproj : ∀ h' : EuclideanSpace ℝ (Fin n),
      (∫ z, ρ z • A (h' + Real.sqrt e • z)) i
        = ∫ z, ρ z * A (h' + Real.sqrt e • z) i := by
    intro h'
    exact (ContinuousLinearMap.integral_comp_comm
      (EuclideanSpace.proj (𝕜 := ℝ) i) (hAint h')).symm
  have hdif : ∀ h₁ h₂ : EuclideanSpace ℝ (Fin n),
      (Ae h₁ - Ae h₂) i
        = ∫ z, ρ z * (A (h₁ + Real.sqrt e • z) i - A (h₂ + Real.sqrt e • z) i) := by
    intro h₁ h₂
    have hsub : Ae h₁ - Ae h₂
        = (∫ z, ρ z • A (h₁ + Real.sqrt e • z))
          - ∫ z, ρ z • A (h₂ + Real.sqrt e • z) := by
      simp only [hAedef]
      abel
    rw [hsub]
    have hpi : ((∫ z, ρ z • A (h₁ + Real.sqrt e • z))
          - ∫ z, ρ z • A (h₂ + Real.sqrt e • z)) i
        = (∫ z, ρ z • A (h₁ + Real.sqrt e • z)) i
          - (∫ z, ρ z • A (h₂ + Real.sqrt e • z)) i := rfl
    rw [hpi, hproj, hproj, ← integral_sub (hAcoord h₁) (hAcoord h₂)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  -- the majorant of the weight along the segment
  obtain ⟨Mb, hMbdef⟩ : ∃ f : ℝ → ℝ, f = fun s : ℝ =>
      max ((e + (‖h‖ + s) ^ 2) ^ (p / 2 - 1))
          ((e + (max (‖h‖ - s) 0) ^ 2) ^ (p / 2 - 1)) := ⟨_, rfl⟩
  have hMb : ∀ t s : ℝ, 0 < t → |s| ≤ t →
      (e + ‖h + s • u‖ ^ 2) ^ (p / 2 - 1) ≤ Mb t := by
    intro t s ht hs
    have hsu : ‖(s • u : EuclideanSpace ℝ (Fin n))‖ = |s| := by
      rw [norm_smul, hunorm, mul_one]
      exact Real.norm_eq_abs s
    have hub : ‖h + s • u‖ ≤ ‖h‖ + t := by
      have h8 := norm_add_le h (s • u)
      rw [hsu] at h8
      linarith
    have hlb : max (‖h‖ - t) 0 ≤ ‖h + s • u‖ := by
      refine max_le ?_ (norm_nonneg _)
      have h9 : ‖h‖ ≤ ‖h + s • u‖ + ‖(s • u : EuclideanSpace ℝ (Fin n))‖ := by
        calc ‖h‖ = ‖h + s • u - s • u‖ := by rw [add_sub_cancel_right]
          _ ≤ ‖h + s • u‖ + ‖(s • u : EuclideanSpace ℝ (Fin n))‖ := norm_sub_le _ _
      rw [hsu] at h9
      linarith
    have hA1 : e + (max (‖h‖ - t) 0) ^ 2 ≤ e + ‖h + s • u‖ ^ 2 := by
      have h10 := pow_le_pow_left₀ (le_max_right (‖h‖ - t) 0) hlb 2
      linarith
    have hA2 : e + ‖h + s • u‖ ^ 2 ≤ e + (‖h‖ + t) ^ 2 := by
      have h11 := pow_le_pow_left₀ (norm_nonneg (h + s • u)) hub 2
      linarith
    have hA0 : (0 : ℝ) < e + (max (‖h‖ - t) 0) ^ 2 := by
      nlinarith [sq_nonneg (max (‖h‖ - t) 0)]
    simp only [hMbdef]
    rcases le_or_gt 0 (p / 2 - 1) with hq | hq
    · exact le_trans (Real.rpow_le_rpow (by nlinarith [sq_nonneg ‖h + s • u‖]) hA2 hq)
        (le_max_left _ _)
    · exact le_trans (Real.rpow_le_rpow_of_nonpos hA0 hA1 hq.le) (le_max_right _ _)
  -- the increment bound for the mollified field
  have hbound : ∀ t : ℝ, 0 < t →
      |(Ae (h + t • u) - Ae h) i| ≤ t * (γ₁ * (C₂ * Mb t)) :=
    MollifiedFieldIncrementBound n p c₁ C₂ γ₁ e ρ A Ae h u i Mb hρ0 hρcs hρc
      hAcont hC₂0 hγ₁0 he0 hsw hIA hker hbad hdif hMb
  -- pass to the limit `t → 0⁺`
  have hAediff : HasFDerivAt Ae (fderiv ℝ Ae h) h :=
    (hsmooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hpath : HasDerivAt (fun s : ℝ => h + s • u) u (0 : ℝ) := by
    have h1 : HasDerivAt (fun s : ℝ => s • u) u (0 : ℝ) := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
    simpa using h1.const_add h
  have hg1 : HasDerivAt (fun s : ℝ => Ae (h + s • u)) (fderiv ℝ Ae h u) (0 : ℝ) := by
    have hd' : HasFDerivAt Ae (fderiv ℝ Ae h) ((fun s : ℝ => h + s • u) 0) := by
      simpa using hAediff
    exact hd'.comp_hasDerivAt 0 hpath
  have hslope : Filter.Tendsto
      (fun s : ℝ => s⁻¹ • (Ae (h + s • u) - Ae h))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (fderiv ℝ Ae h u)) := by
    have h0 := hasDerivAt_iff_tendsto_slope.1 hg1
    have h1 : Filter.Tendsto (fun s : ℝ => s⁻¹ • (Ae (h + s • u) - Ae h))
        (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (fderiv ℝ Ae h u)) := by
      refine h0.congr fun s => ?_
      rw [slope_def_module]
      simp
    exact h1.mono_left (nhdsWithin_mono _ (fun y hy => ne_of_gt hy))
  have hcoord : Filter.Tendsto
      (fun s : ℝ => |(s⁻¹ • (Ae (h + s • u) - Ae h)) i|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds |(fderiv ℝ Ae h u) i|) := by
    have hq1 : Filter.Tendsto (fun s : ℝ => (s⁻¹ • (Ae (h + s • u) - Ae h)) i)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((fderiv ℝ Ae h u) i)) :=
      (((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.tendsto
        (fderiv ℝ Ae h u)).comp hslope).congr fun s => rfl
    exact ((continuous_abs.tendsto _).comp hq1).congr fun s => rfl
  have hMlim : Filter.Tendsto (fun t : ℝ => γ₁ * (C₂ * Mb t))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (γ₁ * (C₂ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)))) := by
    have hf1 : ContinuousAt (fun s : ℝ => (e + (‖h‖ + s) ^ 2) ^ (p / 2 - 1)) 0 := by
      refine ContinuousAt.rpow_const (by fun_prop) (Or.inl ?_)
      have hpos : (0 : ℝ) < e + (‖h‖ + (0 : ℝ)) ^ 2 := by
        nlinarith [sq_nonneg (‖h‖ + (0 : ℝ))]
      exact ne_of_gt hpos
    have hf2 : ContinuousAt
        (fun s : ℝ => (e + (max (‖h‖ - s) 0) ^ 2) ^ (p / 2 - 1)) 0 := by
      refine ContinuousAt.rpow_const (by fun_prop) (Or.inl ?_)
      have hpos : (0 : ℝ) < e + (max (‖h‖ - (0 : ℝ)) 0) ^ 2 := by
        nlinarith [sq_nonneg (max (‖h‖ - (0 : ℝ)) 0)]
      exact ne_of_gt hpos
    have hM0 : ContinuousAt Mb 0 := by
      rw [hMbdef]
      exact hf1.max hf2
    have hval : Mb 0 = (e + ‖h‖ ^ 2) ^ (p / 2 - 1) := by
      simp only [hMbdef]
      rw [add_zero, sub_zero, max_eq_left (norm_nonneg h), max_self]
    have h1 : Filter.Tendsto Mb (nhds (0 : ℝ))
        (nhds ((e + ‖h‖ ^ 2) ^ (p / 2 - 1))) := by
      rw [← hval]
      exact hM0
    exact ((h1.const_mul C₂).const_mul γ₁).mono_left nhdsWithin_le_nhds
  have hfin : |(fderiv ℝ Ae h u) i|
      ≤ γ₁ * (C₂ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)) := by
    refine le_of_tendsto_of_tendsto hcoord hMlim ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (0 : ℝ) < s := hs
    have h1 := hbound s hs'
    have h2 : |(s⁻¹ • (Ae (h + s • u) - Ae h)) i|
        = s⁻¹ * |(Ae (h + s • u) - Ae h) i| := by
      show |s⁻¹ * (Ae (h + s • u) - Ae h) i| = _
      rw [abs_mul, abs_of_pos (inv_pos.2 hs')]
    rw [h2]
    calc s⁻¹ * |(Ae (h + s • u) - Ae h) i|
        ≤ s⁻¹ * (s * (γ₁ * (C₂ * Mb s))) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.2 hs'))
      _ = γ₁ * (C₂ * Mb s) := by field_simp
  have hcomm : C₂ * γ₁ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)
      = γ₁ * (C₂ * (e + ‖h‖ ^ 2) ^ (p / 2 - 1)) := by ring
  rw [hcomm]
  exact hfin
