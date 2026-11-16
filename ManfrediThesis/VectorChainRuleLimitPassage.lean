import ManfrediThesis.Preamble
set_option maxHeartbeats 800000
open MeasureTheory

/-- The limit passage in the mollified approximation for the chain rule of a
`C¹` function of several arguments.

Fix a `C¹` function `F : ℝᵐ → ℝ`, a `C^∞` test function `φ` on `ℝⁿ` with
compact support, and a direction `i`.  Suppose a family `G : ℝᵐ`-valued and a
candidate directional derivative family `DGi` are given on `tsupport φ`, with
`‖G(x)‖ ≤ Lb` there, and suppose smooth families `U l`, `W l` satisfy the
integration-by-parts identity
`∫ F(U l) D_i φ = -∫ (Σ_j (D_j F)(U l) · W l j) φ`
on `tsupport φ` for every `l`, with `‖U l(x)‖ ≤ Lb` on `tsupport φ`,
`W l j → DGi j` in `L¹(tsupport φ)` and `U l → G` almost everywhere there.
Then the identity passes to the limit:
`∫ F(G) D_i φ = -∫ (Σ_j (D_j F)(G) · DGi j) φ`.

The two bounds `|F| ≤ C` and `|(D_j F)| ≤ C` on the ball `‖y‖ ≤ Lb` are what
makes the passage uniform: on the left `F` is bounded and continuous, so
dominated convergence applies to `F(U l) D_i φ` against the majorant
`C|D_i φ|`; on the right each `(D_j F)(U l)` is uniformly bounded by `C` and
converges almost everywhere to `(D_j F)(G)`, so the product
`(D_j F)(U l) · W l j · φ` converges in `L¹(tsupport φ)` once `W l j → DGi j`
there, the difference being split as
`((D_j F)(U l) - (D_j F)(G))·W l j·φ + (D_j F)(G)·(W l j - DGi j)·φ`.

This is the vector-argument chain rule's limit passage, and it is genuinely not
an instance of the scalar one: `F` is a function of the whole family
`(G 1, …, G m)` and the identity pairs each partial derivative `(D_j F)` with
its own field `DGi j`, so the sum over `j` -- not a single composition -- is
what has to survive the limit. -/
theorem VectorChainRuleLimitPassage :
    ∀ (n m : ℕ) (F : (Fin m → ℝ) → ℝ), ContDiff ℝ 1 F →
      ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∀ i : Fin n,
      ∀ Lb C : ℝ, 0 ≤ C →
    (∀ y : Fin m → ℝ, ‖y‖ ≤ Lb → |F y| ≤ C) →
    (∀ y : Fin m → ℝ, ‖y‖ ≤ Lb → ∀ j,
      |fderiv ℝ F y (Pi.single j (1 : ℝ))| ≤ C) →
    ∀ (G : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
      (DGi : Fin m → EuclideanSpace ℝ (Fin n) → ℝ),
    AEStronglyMeasurable (fun x => (fun j => G j x : Fin m → ℝ))
      (volume.restrict (tsupport φ)) →
    (∀ j, IntegrableOn (DGi j) (tsupport φ) volume) →
    (∀ x ∈ tsupport φ, ‖(fun j => G j x : Fin m → ℝ)‖ ≤ Lb) →
    ∀ U W : ℕ → Fin m → EuclideanSpace ℝ (Fin n) → ℝ,
    (∀ l j, Continuous (U l j)) → (∀ l j, Continuous (W l j)) →
    (∀ l, ∀ x ∈ tsupport φ, ‖(fun j => U l j x : Fin m → ℝ)‖ ≤ Lb) →
    (∀ j, Filter.Tendsto
      (fun l => ∫ x in tsupport φ, |W l j x - DGi j x|) Filter.atTop (nhds 0)) →
    (∀ᵐ x ∂(volume.restrict (tsupport φ)),
      Filter.Tendsto (fun l => (fun j => U l j x : Fin m → ℝ)) Filter.atTop
        (nhds (fun j => G j x))) →
    (∀ l, (∫ x in tsupport φ,
        F (fun j => U l j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
      = -∫ x in tsupport φ,
          (∑ j, (fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) * W l j x) * φ x) →
    (∫ x in tsupport φ,
        F (fun j => G j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
      = -∫ x in tsupport φ,
          (∑ j, (fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x) * φ x := by
  intro n m F hF φ hφ hφcs i Lb C hC0 hCF hCD G DGi hGmeas hDGi hVbd U W hUc hWc hUbd hL1W hae h10
  have hFc : Continuous F := hF.continuous
  have hFd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hφc : Continuous φ := hφ.continuous
  have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφcs : HasCompactSupport
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) := hφcs.fderiv_apply ℝ _
  obtain ⟨Λ, hΛ⟩ := hdφcs.exists_bound_of_continuous hdφ
  obtain ⟨Λ', hΛ'⟩ := hφcs.exists_bound_of_continuous hφc
  have hΛ0 : 0 ≤ Λ := le_trans (norm_nonneg _) (hΛ 0)
  have hΛ'0 : 0 ≤ Λ' := le_trans (norm_nonneg _) (hΛ' 0)
  have hKcpt : IsCompact (tsupport φ) := hφcs
  have hKm : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
  have hfinK : IsFiniteMeasure (volume.restrict (tsupport φ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hKcpt.measure_lt_top⟩
  have hintC : ∀ h : EuclideanSpace ℝ (Fin n) → ℝ, Continuous h →
      IntegrableOn h (tsupport φ) volume :=
    fun h hh => hh.continuousOn.integrableOn_compact hKcpt
  have hVUc : ∀ l, Continuous (fun x => (fun j => U l j x : Fin m → ℝ)) :=
    fun l => continuous_pi fun j => hUc l j
  have hcl : ∀ l j, Continuous
      (fun x => fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) :=
    fun l j => ((ContinuousLinearMap.apply ℝ ℝ
      (Pi.single j (1 : ℝ) : Fin m → ℝ)).continuous.comp hFd).comp (hVUc l)
  have hcmeas : ∀ j, AEStronglyMeasurable
      (fun x => fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ)))
      (volume.restrict (tsupport φ)) := by
    intro j
    have h := ((ContinuousLinearMap.apply ℝ ℝ
      (Pi.single j (1 : ℝ) : Fin m → ℝ)).continuous.comp hFd).comp_aestronglyMeasurable hGmeas
    simpa [Function.comp_def] using h
  -- (L) the left-hand side
  have hLlim : Filter.Tendsto
      (fun l => ∫ x in tsupport φ,
        F (fun j => U l j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
      Filter.atTop
      (nhds (∫ x in tsupport φ,
        F (fun j => G j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C * Λ)
      (fun l => ((hFc.comp (hVUc l)).mul hdφ).aestronglyMeasurable)
      (integrable_const _)
      (fun l => ae_restrict_of_forall_mem hKm fun x hx => ?_)
      ?_
    · calc ‖F (fun j => U l j x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))‖
          = |F (fun j => U l j x)| *
            ‖fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))‖ := by
            rw [norm_mul, Real.norm_eq_abs]
        _ ≤ C * Λ := mul_le_mul (hCF _ (hUbd l x hx)) (hΛ x) (norm_nonneg _) hC0
    · filter_upwards [hae] with x hx
      exact ((hFc.tendsto _).comp hx).mul_const _
  -- the three-term split of the right-hand side, one `j` at a time
  have hWK : ∀ l j, IntegrableOn (W l j) (tsupport φ) volume :=
    fun l j => hintC _ (hWc l j)
  have hIA : ∀ l j, IntegrableOn
      (fun x => (fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) * W l j x * φ x)
      (tsupport φ) volume :=
    fun l j => hintC _ (((hcl l j).mul (hWc l j)).mul hφc)
  have hIB : ∀ l j, IntegrableOn
      (fun x => (fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) * DGi j x * φ x)
      (tsupport φ) volume := by
    intro l j
    refine Integrable.mono' (g := fun x => (C * Λ') * |DGi j x|)
      ((hDGi j).abs.const_mul _)
      ((((hcl l j).aestronglyMeasurable).mul (hDGi j).1).mul hφc.aestronglyMeasurable)
      (ae_restrict_of_forall_mem hKm fun x hx => ?_)
    calc ‖(fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) * DGi j x * φ x‖
        = |fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))| * |DGi j x| * ‖φ x‖ := by
          rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ C * |DGi j x| * Λ' := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (hCD _ (hUbd l x hx) j)
            (abs_nonneg _)) (hΛ' x) (norm_nonneg _) (by positivity)
      _ = C * Λ' * |DGi j x| := by ring
  have hIC : ∀ j, IntegrableOn
      (fun x => (fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x * φ x)
      (tsupport φ) volume := by
    intro j
    refine Integrable.mono' (g := fun x => (C * Λ') * |DGi j x|)
      ((hDGi j).abs.const_mul _)
      (((hcmeas j).mul (hDGi j).1).mul hφc.aestronglyMeasurable)
      (ae_restrict_of_forall_mem hKm fun x hx => ?_)
    calc ‖(fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x * φ x‖
        = |fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))| * |DGi j x| * ‖φ x‖ := by
          rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ C * |DGi j x| * Λ' := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (hCD _ (hVbd x hx) j)
            (abs_nonneg _)) (hΛ' x) (norm_nonneg _) (by positivity)
      _ = C * Λ' * |DGi j x| := by ring
  -- (R1)
  have hR1 : ∀ j, Filter.Tendsto
      (fun l => ∫ x in tsupport φ,
        ((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) *
          (W l j x - DGi j x)) * φ x) Filter.atTop (nhds 0) := by
    intro j
    refine squeeze_zero_norm
      (a := fun l => (C * Λ') * ∫ x in tsupport φ, |W l j x - DGi j x|)
      (fun l => ?_) ?_
    · have hI : IntegrableOn (fun x =>
          ((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) *
            (W l j x - DGi j x)) * φ x) (tsupport φ) volume := by
        have he : (fun x => ((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) *
              (W l j x - DGi j x)) * φ x)
            = fun x => (fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) * W l j x * φ x
              - (fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) * DGi j x * φ x := by
          funext x; ring
        rw [he]; exact (hIA l j).sub (hIB l j)
      calc ‖∫ x in tsupport φ, ((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) *
              (W l j x - DGi j x)) * φ x‖
          ≤ ∫ x in tsupport φ, |((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) *
              (W l j x - DGi j x)) * φ x| := by
            rw [Real.norm_eq_abs]; exact abs_integral_le_integral_abs
        _ ≤ ∫ x in tsupport φ, (C * Λ') * |W l j x - DGi j x| := by
            refine integral_mono_ae hI.abs
              (((hWK l j).sub (hDGi j)).abs.const_mul _)
              (ae_restrict_of_forall_mem hKm fun x hx => ?_)
            calc |((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) *
                  (W l j x - DGi j x)) * φ x|
                = |fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))| *
                  |W l j x - DGi j x| * |φ x| := by rw [abs_mul, abs_mul]
              _ ≤ C * |W l j x - DGi j x| * Λ' := by
                  refine mul_le_mul (mul_le_mul_of_nonneg_right
                    (hCD _ (hUbd l x hx) j) (abs_nonneg _))
                    (by simpa [Real.norm_eq_abs] using hΛ' x) (abs_nonneg _) (by positivity)
              _ = (C * Λ') * |W l j x - DGi j x| := by ring
        _ = (C * Λ') * ∫ x in tsupport φ, |W l j x - DGi j x| := integral_const_mul _ _
    · simpa using (hL1W j).const_mul (C * Λ')
  -- (R2) dominated convergence for the derivative factor
  have hR2 : ∀ j, Filter.Tendsto
      (fun l => ∫ x in tsupport φ,
        ((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))
          - fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x) * φ x)
      Filter.atTop (nhds 0) := by
    intro j
    have hmeas : ∀ l, AEStronglyMeasurable
        (fun x => ((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))
          - fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x) * φ x)
        (volume.restrict (tsupport φ)) :=
      fun l => ((((hcl l j).aestronglyMeasurable).sub (hcmeas j)).mul (hDGi j).1).mul
        hφc.aestronglyMeasurable
    have hbd : ∀ l, ∀ᵐ x ∂(volume.restrict (tsupport φ)),
        ‖((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))
          - fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x) * φ x‖
          ≤ (2 * C * Λ') * |DGi j x| := by
      intro l
      refine ae_restrict_of_forall_mem hKm fun x hx => ?_
      have hb1 := hCD _ (hUbd l x hx) j
      have hb2 := hCD _ (hVbd x hx) j
      have hdiff : |fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))
          - fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))| ≤ 2 * C := by
        rcases abs_le.1 hb1 with ⟨a1, b1⟩
        rcases abs_le.1 hb2 with ⟨a2, b2⟩
        exact abs_le.2 ⟨by linarith, by linarith⟩
      calc ‖((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))
              - fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x) * φ x‖
          = |fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))
              - fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))| *
            |DGi j x| * ‖φ x‖ := by
            rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ (2 * C) * |DGi j x| * Λ' := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hdiff (abs_nonneg _))
              (hΛ' x) (norm_nonneg _) (by positivity)
        _ = (2 * C * Λ') * |DGi j x| := by ring
    have hlim : ∀ᵐ x ∂(volume.restrict (tsupport φ)),
        Filter.Tendsto (fun l => ((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))
          - fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x) * φ x)
          Filter.atTop (nhds 0) := by
      filter_upwards [hae] with x hx
      have h1 : Filter.Tendsto
          (fun l => fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ)))
          Filter.atTop (nhds (fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ)))) := by
        have h := (((ContinuousLinearMap.apply ℝ ℝ
          (Pi.single j (1 : ℝ) : Fin m → ℝ)).continuous.comp hFd).tendsto
            (fun j => G j x)).comp hx
        simpa [Function.comp_def] using h
      have h0 : Filter.Tendsto
          (fun l => fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))
            - fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ)))
          Filter.atTop (nhds 0) := by
        simpa using h1.sub_const (fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ)))
      simpa using (h0.mul_const (DGi j x)).mul_const (φ x)
    have hd := tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (tsupport φ))
      (F := fun l (x : EuclideanSpace ℝ (Fin n)) =>
        ((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))
          - fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x) * φ x)
      (f := fun _ => (0 : ℝ))
      (bound := fun x => (2 * C * Λ') * |DGi j x|)
      hmeas ((hDGi j).abs.const_mul _) hbd hlim
    simpa using hd
  -- combine the three terms, one `j` at a time
  have hRj : ∀ j, Filter.Tendsto
      (fun l => ∫ x in tsupport φ,
        (fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) * W l j x * φ x)
      Filter.atTop
      (nhds (∫ x in tsupport φ,
        (fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x * φ x)) := by
    intro j
    have hsplit : ∀ l, (∫ x in tsupport φ,
          (fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) * W l j x * φ x)
        = (∫ x in tsupport φ, ((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) *
              (W l j x - DGi j x)) * φ x)
          + ((∫ x in tsupport φ, ((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))
                - fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x) * φ x)
            + (∫ x in tsupport φ,
                (fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x * φ x)) := by
      intro l
      have hI1 : IntegrableOn (fun x =>
          ((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) *
            (W l j x - DGi j x)) * φ x) (tsupport φ) volume := by
        have he : (fun x => ((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) *
              (W l j x - DGi j x)) * φ x)
            = fun x => (fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) * W l j x * φ x
              - (fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) * DGi j x * φ x := by
          funext x; ring
        rw [he]; exact (hIA l j).sub (hIB l j)
      have hI2 : IntegrableOn (fun x =>
          ((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))
            - fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x) * φ x)
          (tsupport φ) volume := by
        have he : (fun x => ((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))
              - fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x) * φ x)
            = fun x => (fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) * DGi j x * φ x
              - (fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x * φ x := by
          funext x; ring
        rw [he]; exact (hIB l j).sub (hIC j)
      have hIBC : IntegrableOn (fun x =>
          ((fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))
            - fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x) * φ x
          + (fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x * φ x)
          (tsupport φ) volume := hI2.add (hIC j)
      rw [← integral_add hI2 (hIC j), ← integral_add hI1 hIBC]
      refine setIntegral_congr_fun hKm fun x _ => ?_
      ring
    simp only [hsplit]
    simpa using (hR1 j).add ((hR2 j).add
      (tendsto_const_nhds (x := ∫ x in tsupport φ,
        (fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x * φ x)
        (f := Filter.atTop (α := ℕ))))
  -- sum over `j`
  have hRsum : Filter.Tendsto
      (fun l => ∫ x in tsupport φ,
        (∑ j, (fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) * W l j x) * φ x)
      Filter.atTop
      (nhds (∫ x in tsupport φ,
        (∑ j, (fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x) * φ x)) := by
    have heU : ∀ (l : ℕ) (x : EuclideanSpace ℝ (Fin n)),
        (∑ j, (fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) * W l j x) * φ x
        = ∑ j, (fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) * W l j x * φ x :=
      fun l x => by rw [Finset.sum_mul]
    have heG : ∀ x : EuclideanSpace ℝ (Fin n),
        (∑ j, (fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x) * φ x
        = ∑ j, (fderiv ℝ F (fun j => G j x) (Pi.single j (1 : ℝ))) * DGi j x * φ x :=
      fun x => by rw [Finset.sum_mul]
    simp only [heU, heG]
    rw [integral_finsetSum _ (fun j _ => hIC j)]
    have hexp : ∀ l, (∫ x in tsupport φ,
          ∑ j, (fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) * W l j x * φ x)
        = ∑ j, ∫ x in tsupport φ,
            (fderiv ℝ F (fun j => U l j x) (Pi.single j (1 : ℝ))) * W l j x * φ x :=
      fun l => integral_finsetSum _ (fun j _ => hIA l j)
    simp only [hexp]
    exact tendsto_finsetSum _ fun j _ => hRj j
  refine tendsto_nhds_unique hLlim ?_
  simp only [h10]
  exact hRsum.neg
