import ManfrediThesis.Preamble
import ManfrediThesis.VariationalStructureF123
import ManfrediThesis.FrozenGradientOperator
import ManfrediThesis.EllipticStructureQ12
open MeasureTheory

/-- The frozen operator of a density satisfying (F1)-(F3) satisfies (Q1)-(Q2)
after the normalisation `A ↦ A - A 0` of thesis l. 542, with the structure
constants `γ₀ = ν₀`, `γ₁ = ν₁` undegraded.  This is the step by which §4 and §5
hand their variational data to the nodes of §3, all of which are stated for a
field satisfying `EllipticStructureQ12` on `Set.univ`. -/
theorem FrozenOperatorStructureQ12 :
    ∀ (n : ℕ) (p ε lam Lam a ν₀ ν₁ : ℝ),
      2 ≤ n → 1 < p → 0 ≤ ε → ε ≤ 1 → 0 < lam → lam ≤ Lam → 0 < a →
      0 < ν₀ → ν₀ < ν₁ →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
        (σ : ℝ → ℝ) (x₁ : EuclideanSpace ℝ (Fin n)) (z₁ : ℝ),
        IsOpen Ω → x₁ ∈ Ω →
        VariationalStructureF123 n p ε lam Lam a ν₀ ν₁ Ω fdens σ →
        EllipticStructureQ12 n p ε ν₀ ν₁ Set.univ
          (fun _ _ h => FrozenGradientOperator n fdens x₁ z₁ h
                          - FrozenGradientOperator n fdens x₁ z₁ 0) := by
  intro n p ε lam Lam a ν₀ ν₁ hn hp hε hε1 hlam hlamLam ha hν₀ hν₁ Ω fdens σ x₁ z₁ hΩ hx₁ hF
  have hν₁0 : 0 < ν₁ := lt_trans hν₀ hν₁
  -- the nondegeneracy set is open
  have hDopen : IsOpen {h : EuclideanSpace ℝ (Fin n) | ε + ‖h‖ ^ 2 ≠ 0} := by
    have hc : Continuous fun h : EuclideanSpace ℝ (Fin n) => ε + ‖h‖ ^ 2 :=
      continuous_const.add (continuous_norm.pow 2)
    exact isOpen_ne.preimage hc
  -- the frozen density is `C¹` on `ℝⁿ` and `C²` on the nondegeneracy set
  have hf1 : ContDiff ℝ 1 (fdens x₁ z₁) := hF.F2_diff x₁ hx₁ z₁
  have hf2 : ContDiffOn ℝ 2 (fdens x₁ z₁) {h : EuclideanSpace ℝ (Fin n) | ε + ‖h‖ ^ 2 ≠ 0} :=
    hF.F2_diff2 x₁ hx₁ z₁
  have hTcont : Continuous (fderiv ℝ (fdens x₁ z₁)) := hf1.continuous_fderiv (by norm_num)
  have hTcd : ContDiffOn ℝ 1 (fderiv ℝ (fdens x₁ z₁))
      {h : EuclideanSpace ℝ (Fin n) | ε + ‖h‖ ^ 2 ≠ 0} := by
    refine (hf2.fderivWithin (m := 1) hDopen.uniqueDiffOn (by norm_num)).congr
      (fun x hx => ?_)
    exact (fderivWithin_of_isOpen hDopen hx).symm
  -- hence the frozen operator is continuous, and `C¹` on the nondegeneracy set
  have hA0cont : Continuous (FrozenGradientOperator n fdens x₁ z₁) := by
    have hcd : ContDiff ℝ 0 (FrozenGradientOperator n fdens x₁ z₁) := by
      rw [contDiff_euclidean]
      intro i
      have h1 : Continuous fun y : EuclideanSpace ℝ (Fin n) =>
          fderiv ℝ (fdens x₁ z₁) y (EuclideanSpace.single i (1:ℝ)) :=
        (ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single i (1:ℝ))).continuous.comp hTcont
      rw [contDiff_zero]
      exact h1
    exact contDiff_zero.mp hcd
  have hA0cd : ContDiffOn ℝ 1 (FrozenGradientOperator n fdens x₁ z₁)
      {h : EuclideanSpace ℝ (Fin n) | ε + ‖h‖ ^ 2 ≠ 0} := by
    rw [contDiffOn_euclidean]
    intro i
    have h1 : ContDiffOn ℝ 1 (fun y : EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ (fdens x₁ z₁) y (EuclideanSpace.single i (1:ℝ)))
        {h : EuclideanSpace ℝ (Fin n) | ε + ‖h‖ ^ 2 ≠ 0} :=
      (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single i (1:ℝ))).contDiff.comp_contDiffOn hTcd
    exact h1
  -- expansion of a functional in the standard basis
  have hbasis : ∀ (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (ξ : EuclideanSpace ℝ (Fin n)),
      ∑ i, L (EuclideanSpace.single i (1:ℝ)) * ξ i = L ξ := by
    intro L ξ
    have hb : ∑ i, ξ i • EuclideanSpace.single i (1:ℝ) = ξ := by
      have h := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr ξ
      simpa using h
    have h2 : L ξ = ∑ i, L (EuclideanSpace.single i (1:ℝ)) * ξ i := by
      conv_lhs => rw [← hb]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [map_smul, smul_eq_mul]
      ring
    exact h2.symm
  -- the three second-derivative identities at a point of the nondegeneracy set
  have hsecond : ∀ h : EuclideanSpace ℝ (Fin n), ε + ‖h‖ ^ 2 ≠ 0 →
      (∀ (ζ ξ : EuclideanSpace ℝ (Fin n)),
          fderiv ℝ (fun h' => fderiv ℝ (fdens x₁ z₁) h' ζ) h ξ
            = (fderiv ℝ (fderiv ℝ (fdens x₁ z₁)) h ξ) ζ)
        ∧ (∀ (ξ : EuclideanSpace ℝ (Fin n)) (i : Fin n),
          (fderiv ℝ (FrozenGradientOperator n fdens x₁ z₁) h ξ) i
            = (fderiv ℝ (fderiv ℝ (fdens x₁ z₁)) h ξ) (EuclideanSpace.single i (1:ℝ)))
        ∧ (∀ (ζ ξ : EuclideanSpace ℝ (Fin n)),
          (fderiv ℝ (fderiv ℝ (fdens x₁ z₁)) h ξ) ζ
            = (fderiv ℝ (fderiv ℝ (fdens x₁ z₁)) h ζ) ξ) := by
    intro h hh
    have hCD : ContDiffAt ℝ 2 (fdens x₁ z₁) h := hf2.contDiffAt (hDopen.mem_nhds hh)
    have hdT : DifferentiableAt ℝ (fderiv ℝ (fdens x₁ z₁)) h :=
      (hCD.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hcomp : ∀ (ζ ξ : EuclideanSpace ℝ (Fin n)),
        fderiv ℝ (fun h' => fderiv ℝ (fdens x₁ z₁) h' ζ) h ξ
          = (fderiv ℝ (fderiv ℝ (fdens x₁ z₁)) h ξ) ζ := by
      intro ζ ξ
      have hL : HasFDerivAt (fun h' => fderiv ℝ (fdens x₁ z₁) h' ζ)
          ((ContinuousLinearMap.apply ℝ ℝ ζ).comp
            (fderiv ℝ (fderiv ℝ (fdens x₁ z₁)) h)) h :=
        ((ContinuousLinearMap.apply ℝ ℝ ζ).hasFDerivAt
          (x := fderiv ℝ (fdens x₁ z₁) h)).comp h hdT.hasFDerivAt
      rw [hL.fderiv]
      rfl
    refine ⟨hcomp, ?_, ?_⟩
    · intro ξ i
      have hA0diff : DifferentiableAt ℝ (FrozenGradientOperator n fdens x₁ z₁) h := by
        rw [differentiableAt_euclidean]
        intro j
        have he : (fun y => (FrozenGradientOperator n fdens x₁ z₁ y).ofLp j)
            = fun y => fderiv ℝ (fdens x₁ z₁) y (EuclideanSpace.single j (1:ℝ)) := rfl
        rw [he]
        exact (ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single j (1:ℝ))).differentiableAt.comp h hdT
      obtain ⟨P, hP⟩ : ∃ P : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
          ∀ v : EuclideanSpace ℝ (Fin n), P v = v i :=
        ⟨EuclideanSpace.proj i, fun v => rfl⟩
      have hL0 : HasFDerivAt (fun y => P (FrozenGradientOperator n fdens x₁ z₁ y))
          (P.comp (fderiv ℝ (FrozenGradientOperator n fdens x₁ z₁) h)) h :=
        (P.hasFDerivAt (x := FrozenGradientOperator n fdens x₁ z₁ h)).comp h
          hA0diff.hasFDerivAt
      have h1 : (fderiv ℝ (FrozenGradientOperator n fdens x₁ z₁) h ξ) i
          = fderiv ℝ (fun y => P (FrozenGradientOperator n fdens x₁ z₁ y)) h ξ := by
        rw [hL0.fderiv]
        simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hP]
      have h2 : (fun y => P (FrozenGradientOperator n fdens x₁ z₁ y))
          = fun y => fderiv ℝ (fdens x₁ z₁) y (EuclideanSpace.single i (1:ℝ)) := by
        funext y
        rw [hP]
        rfl
      rw [h1, h2, hcomp]
    · intro ζ ξ
      exact hCD.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) ξ ζ
  -- the derivative of the normalised field is the derivative of the frozen operator
  have hfdsub : ∀ h : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fun h' => FrozenGradientOperator n fdens x₁ z₁ h'
          - FrozenGradientOperator n fdens x₁ z₁ 0) h
        = fderiv ℝ (FrozenGradientOperator n fdens x₁ z₁) h :=
    fun h => fderiv_sub_const _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun z h => measurable_const
  · exact fun x => (hA0cont.sub continuous_const).comp continuous_snd
  · exact fun x _ z => hA0cont.sub continuous_const
  · exact fun x _ z => hA0cd.sub contDiffOn_const
  · -- (Q1)
    refine Filter.Eventually.of_forall (fun x _ z h ξ hh => ?_)
    obtain ⟨hcomp, hAcomp, hsymm⟩ := hsecond h hh
    have hF2 := (hF.F2 x₁ hx₁ z₁ h ξ hh).1
    rw [hcomp ξ ξ] at hF2
    calc ν₀ * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖ξ‖ ^ 2
        ≤ (fderiv ℝ (fderiv ℝ (fdens x₁ z₁)) h ξ) ξ := hF2
      _ = ∑ i, (fderiv ℝ (FrozenGradientOperator n fdens x₁ z₁) h ξ) i * ξ i := by
          rw [← hbasis (fderiv ℝ (fderiv ℝ (fdens x₁ z₁)) h ξ) ξ]
          exact (Finset.sum_congr rfl (fun i _ => by rw [hAcomp ξ i])).symm
      _ = ∑ i, (fderiv ℝ (fun h' => FrozenGradientOperator n fdens x₁ z₁ h'
              - FrozenGradientOperator n fdens x₁ z₁ 0) h ξ) i * ξ i := by
          rw [hfdsub h]
  · -- (Q2)
    refine Filter.Eventually.of_forall (fun x _ z h i j hh => ?_)
    obtain ⟨hcomp, hAcomp, hsymm⟩ := hsecond h hh
    obtain ⟨W, hW⟩ : ∃ t : ℝ, t = (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) := ⟨_, rfl⟩
    have hW0 : 0 ≤ W := by
      rw [hW]
      exact Real.rpow_nonneg (by positivity) _
    obtain ⟨B, hB⟩ : ∃ B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ,
        B = fun ζ ξ => (fderiv ℝ (fderiv ℝ (fdens x₁ z₁)) h ξ) ζ := ⟨_, rfl⟩
    have hBnn : ∀ v : EuclideanSpace ℝ (Fin n), 0 ≤ B v v := by
      intro v
      have h1 := (hF.F2 x₁ hx₁ z₁ h v hh).1
      rw [hcomp v v] at h1
      simp only [hB]
      refine le_trans ?_ h1
      positivity
    have hBub : ∀ v : EuclideanSpace ℝ (Fin n), B v v ≤ ν₁ * W * ‖v‖ ^ 2 := by
      intro v
      have h1 := (hF.F2 x₁ hx₁ z₁ h v hh).2
      rw [hcomp v v] at h1
      simp only [hB, hW]
      exact h1
    have hBsymm : ∀ v w : EuclideanSpace ℝ (Fin n), B v w = B w v := by
      intro v w
      simp only [hB]
      exact hsymm v w
    have hBadd : ∀ (v w : EuclideanSpace ℝ (Fin n)) (t : ℝ),
        B (v + t • w) (v + t • w) = B v v + 2 * t * B v w + t ^ 2 * B w w := by
      intro v w t
      have hs : (fderiv ℝ (fderiv ℝ (fdens x₁ z₁)) h v) w
          = (fderiv ℝ (fderiv ℝ (fdens x₁ z₁)) h w) v := hsymm w v
      simp only [hB, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      linear_combination t * hs
    have hCS : ∀ v w : EuclideanSpace ℝ (Fin n), (B v w) ^ 2 ≤ B v v * B w w := by
      intro v w
      have hdisc : discrim (B w w) (2 * B v w) (B v v) ≤ 0 := by
        refine discrim_le_zero (fun t => ?_)
        have h1 := hBnn (v + t • w)
        rw [hBadd v w t] at h1
        linarith
      rw [discrim] at hdisc
      linarith
    have hone : ∀ k : Fin n, B (EuclideanSpace.single k (1:ℝ))
        (EuclideanSpace.single k (1:ℝ)) ≤ ν₁ * W := by
      intro k
      have h1 := hBub (EuclideanSpace.single k (1:ℝ))
      have h2 : ‖EuclideanSpace.single k (1:ℝ)‖ ^ 2 = 1 := by simp
      rw [h2, mul_one] at h1
      exact h1
    have hsq : (B (EuclideanSpace.single i (1:ℝ)) (EuclideanSpace.single j (1:ℝ))) ^ 2
        ≤ (ν₁ * W) ^ 2 := by
      have h1 := hCS (EuclideanSpace.single i (1:ℝ)) (EuclideanSpace.single j (1:ℝ))
      have h2 : B (EuclideanSpace.single i (1:ℝ)) (EuclideanSpace.single i (1:ℝ))
          * B (EuclideanSpace.single j (1:ℝ)) (EuclideanSpace.single j (1:ℝ))
          ≤ (ν₁ * W) * (ν₁ * W) :=
        mul_le_mul (hone i) (hone j) (hBnn _) (by positivity)
      calc (B (EuclideanSpace.single i (1:ℝ)) (EuclideanSpace.single j (1:ℝ))) ^ 2
          ≤ B (EuclideanSpace.single i (1:ℝ)) (EuclideanSpace.single i (1:ℝ))
            * B (EuclideanSpace.single j (1:ℝ)) (EuclideanSpace.single j (1:ℝ)) := h1
        _ ≤ (ν₁ * W) * (ν₁ * W) := h2
        _ = (ν₁ * W) ^ 2 := by ring
    have hval : (fderiv ℝ (fun h' => FrozenGradientOperator n fdens x₁ z₁ h'
            - FrozenGradientOperator n fdens x₁ z₁ 0) h
          (EuclideanSpace.single j (1:ℝ))) i
        = B (EuclideanSpace.single i (1:ℝ)) (EuclideanSpace.single j (1:ℝ)) := by
      rw [hfdsub h, hB]
      exact hAcomp (EuclideanSpace.single j (1:ℝ)) i
    rw [hval, ← hW]
    exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (by positivity))
