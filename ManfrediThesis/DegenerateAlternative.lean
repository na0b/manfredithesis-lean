import ManfrediThesis.Preamble
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.CaccioppoliLevelWeight
import ManfrediThesis.LevelTruncationMaximumPrinciple
import ManfrediThesis.LevelSetMeasureImprovement
import ManfrediThesis.PinchedCaccioppoliLevelBound
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.SignedPowerGradientEstimate
open MeasureTheory

/-- Lemma 3.2: the alternative for the partial derivatives of a solution of
(3.1) on a ball. -/
theorem DegenerateAlternative :
    ∀ (n : ℕ) (p r : ℝ), 2 ≤ n → 1 < p → 0 < r →
      CitedSobolevPoincareBall n →
      ∃ θ₂ ν : ℝ, θ₂ ∈ Set.Ioo (0 : ℝ) 1 ∧ ν ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∀ (ε γ₀ γ₁ μ : ℝ) (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ),
          0 < ε → 0 < γ₀ → γ₁ ≤ r * γ₀ → 0 < R →
          EllipticStructureQ12 n p ε γ₀ γ₁ (Metric.ball x₀ R) (fun _ _ h => A h) →
          CitedRegularityEpsPos n p ε γ₀ γ₁ (Metric.ball x₀ R) A →
          IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h)
            (fun _ _ _ => 0) u g →
          (∀ i : Fin n, MemW1pLocOn n 2 (Metric.ball x₀ R) (fun x => g x i) (Dg i)) →
          (∀ k : Fin n, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), |g x k| ≤ μ) →
          (∀ m : ℝ, (∀ k : Fin n, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
              |g x k| ≤ m) → μ ≤ m) →
          (∀ k : Fin n,
              (θ₂ * (volume (Metric.ball x₀ R)).toReal
                  ≤ (volume (Metric.ball x₀ R ∩ {y | μ / 2 < g y k})).toReal ∨
                θ₂ * (volume (Metric.ball x₀ R)).toReal
                  ≤ (volume (Metric.ball x₀ R ∩ {y | g y k < -(μ / 2)})).toReal) →
            ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))),
              min (1 / 16) ((2 : ℝ) ^ (-1 - 4 / p)) * μ ≤ |g x k|)
          ∧ ((¬ ∃ k : Fin n,
              θ₂ * (volume (Metric.ball x₀ R)).toReal
                  ≤ (volume (Metric.ball x₀ R ∩ {y | μ / 2 < g y k})).toReal ∨
                θ₂ * (volume (Metric.ball x₀ R)).toReal
                  ≤ (volume (Metric.ball x₀ R ∩ {y | g y k < -(μ / 2)})).toReal) →
            ∀ k : Fin n, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))),
              |g x k| ≤ ν * μ) := by
  intro n p r hn hp hr hSP
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  -- Step 1's constant `c₄`
  obtain ⟨c₄, hc₄0, hCacc⟩ := CaccioppoliLevelWeight n p r hn hp hr
  -- Steps 2-3's constant `γ₉`
  have hK1 : (1:ℝ) ≤ 1 + 4 * (n : ℝ) := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  obtain ⟨γ₉, hγ₉0, hPinch⟩ :=
    PinchedCaccioppoliLevelBound n (p / 2 - 1) (1 + 4 * (n : ℝ)) c₄ hn1 hK1 hc₄0
  -- Step 4's constant `C₁₂`
  obtain ⟨C₁₂, hC₁₂0, hSPGE⟩ := SignedPowerGradientEstimate n p r hn hp hr
  obtain ⟨γs, hγsdef⟩ : ∃ t : ℝ, t = max γ₉ (16 * C₁₂) := ⟨_, rfl⟩
  have hγs0 : 0 < γs := by rw [hγsdef]; exact lt_of_lt_of_le hγ₉0 (le_max_left _ _)
  -- Step 5: the constants `θ₂` and `ν`
  have h23 : (2:ℝ) / 3 ∈ Set.Ioo (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h34 : (3:ℝ) / 4 ∈ Set.Ioo (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨P, hPdef⟩ : ∃ t : ℝ, t = (2:ℝ) ^ (p / 2) := ⟨_, rfl⟩
  have hP1 : 1 < P := by
    rw [hPdef]
    exact Real.one_lt_rpow_iff_of_pos (by norm_num) |>.2 (Or.inl ⟨by norm_num, by linarith⟩)
  have hP0 : 0 < P := lt_trans one_pos hP1
  obtain ⟨lam02, hlam02def⟩ : ∃ t : ℝ, t = (P + 1 / 2) / (P + 1) := ⟨_, rfl⟩
  have hlam02 : lam02 ∈ Set.Ioo (0:ℝ) 1 := by
    rw [hlam02def]
    constructor
    · positivity
    · rw [div_lt_one (by linarith)]
      linarith
  obtain ⟨θa, hθa0, hLTa⟩ :=
    LevelTruncationMaximumPrinciple n γs (3 / 4) (2 / 3) hn hγs0 h34 h23 hSP
  obtain ⟨θb, hθb0, hLTb⟩ :=
    LevelTruncationMaximumPrinciple n γs lam02 (2 / 3) hn hγs0 hlam02 h23 hSP
  obtain ⟨θ0s, hθ0sdef⟩ : ∃ t : ℝ, t = min (min θa θb) 1 := ⟨_, rfl⟩
  have hθ0s0 : 0 < θ0s := by
    rw [hθ0sdef]; exact lt_min (lt_min hθa0 hθb0) one_pos
  have hθ0s1 : θ0s ≤ 1 := by rw [hθ0sdef]; exact min_le_right _ _
  have h34n : (0:ℝ) < (3 / 4 : ℝ) ^ n := by positivity
  have h34n1 : ((3:ℝ) / 4) ^ n < 1 := by
    refine pow_lt_one₀ (by norm_num) (by norm_num) ?_
    omega
  obtain ⟨θ₂, hθ₂def⟩ : ∃ t : ℝ, t = 1 - θ0s * (3 / 4 : ℝ) ^ n := ⟨_, rfl⟩
  have hθ₂0 : 0 < θ₂ := by
    rw [hθ₂def]
    nlinarith
  have hθ₂1 : θ₂ < 1 := by
    rw [hθ₂def]
    nlinarith
  -- the second family of radii
  obtain ⟨t, htdef⟩ : ∃ s : ℝ, s = ((1 + θ₂) / 2) ^ ((n : ℝ)⁻¹) := ⟨_, rfl⟩
  have hbase0 : (0:ℝ) < (1 + θ₂) / 2 := by linarith
  have hbase1 : (1 + θ₂) / 2 < 1 := by linarith
  have hnR0 : (0:ℝ) < (n : ℝ) := by
    have : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have ht0 : 0 < t := by rw [htdef]; exact Real.rpow_pos_of_pos hbase0 _
  have ht1 : t < 1 := by
    rw [htdef]
    exact Real.rpow_lt_one hbase0.le hbase1 (by positivity)
  have htn : t ^ n = (1 + θ₂) / 2 := by
    rw [htdef, ← Real.rpow_natCast (((1 + θ₂) / 2) ^ ((n : ℝ)⁻¹)) n,
      ← Real.rpow_mul hbase0.le, inv_mul_cancel₀ (ne_of_gt hnR0), Real.rpow_one]
  have ht12 : 1 / 2 < t := by
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : t ^ n ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ ht0.le hcon n
    have h2 : ((1:ℝ) / 2) ^ n ≤ 1 / 2 := by
      calc ((1:ℝ) / 2) ^ n ≤ ((1:ℝ) / 2) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hn1
        _ = 1 / 2 := pow_one _
    rw [htn] at h1
    linarith
  obtain ⟨lam1, hlam1def⟩ : ∃ s : ℝ, s = 2 * t / (1 + t) := ⟨_, rfl⟩
  have hlam1 : lam1 ∈ Set.Ioo (0:ℝ) 1 := by
    rw [hlam1def]
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one (by linarith)]
    linarith
  obtain ⟨c₀, hc₀def⟩ : ∃ s : ℝ, s = 2 * θ₂ / (1 + θ₂) := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀def]; positivity
  have hc₀1 : c₀ < 1 := by
    rw [hc₀def, div_lt_one (by linarith)]
    linarith
  obtain ⟨lam1'', hlam1''def⟩ : ∃ s : ℝ, s = 1 / (2 * t) := ⟨_, rfl⟩
  have hlam1'' : lam1'' ∈ Set.Ioo (0:ℝ) 1 := by
    rw [hlam1''def]
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one (by linarith)]
    linarith
  obtain ⟨θc, hθc0, hLTc⟩ :=
    LevelTruncationMaximumPrinciple n γs (1 / 2) lam1'' hn hγs0
      ⟨by norm_num, by norm_num⟩ hlam1'' hSP
  obtain ⟨θ₁c, hθ₁cdef⟩ : ∃ s : ℝ, s = min θc (1 / 2) := ⟨_, rfl⟩
  have hθ₁c : θ₁c ∈ Set.Ioo (0:ℝ) 1 := by
    rw [hθ₁cdef]
    exact ⟨lt_min hθc0 (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
  obtain ⟨lam₂, hlam₂, hLSMI⟩ :=
    LevelSetMeasureImprovement n γs lam1 c₀ θ₁c hn hγs0 hlam1 hc₀0 hc₀1 hθ₁c hSP
  obtain ⟨hlam₂0, hlam₂1⟩ := hlam₂
  obtain ⟨ν, hνdef⟩ : ∃ s : ℝ, s = 1 - lam₂ / 4 := ⟨_, rfl⟩
  have hν0 : 0 < ν := by rw [hνdef]; linarith
  have hν1 : ν < 1 := by rw [hνdef]; linarith
  refine ⟨θ₂, ν, ⟨hθ₂0, hθ₂1⟩, ⟨hν0, hν1⟩, ?_⟩
  intro ε γ₀ γ₁ μ A u g Dg x₀ R hε hγ₀ hγ₁ hR hQ hC1 hsol hDg hbd hleast
  -- `μ ≥ 0`, and the degenerate case `μ = 0` of Step 0(0a)
  have hNBR : Filter.NeBot (ae (volume.restrict (Metric.ball x₀ R))) := by
    rw [ae_neBot]
    intro hcc
    rw [← Measure.measure_univ_eq_zero, Measure.restrict_apply_univ] at hcc
    exact (Metric.measure_ball_pos volume x₀ hR).ne' hcc
  have hμ0 : 0 ≤ μ := by
    obtain ⟨x, hx⟩ := (hbd ⟨0, lt_of_lt_of_le (by norm_num) hn⟩).exists
    exact le_trans (abs_nonneg _) hx
  have hsubhalf : Metric.ball x₀ (R / 2) ⊆ Metric.ball x₀ R :=
    Metric.ball_subset_ball (by linarith)
  rcases eq_or_lt_of_le hμ0 with hμeq | hμpos
  · -- `μ = 0`: both parts hold for any `θ₂, ν`
    refine ⟨fun k _ => ?_, fun _ k => ?_⟩
    · filter_upwards with x
      rw [← hμeq]
      simp
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsubhalf (hbd k)] with x hx
      rw [← hμeq] at hx ⊢
      simpa using hx
  · -- `μ > 0`
    -- ------------------------------------------------------------------
    -- Steps 0(0b), 1, 2 and 3, HOISTED: they are shared verbatim by Step 6
    -- (part (a)) and Step 7 (part (b)), and only the index `k` is bound inside
    -- the branches, so the whole block is one `have` quantified over `k`.
    -- ------------------------------------------------------------------
    -- (0b) A GLOBALLY MEASURABLE representative of `g` on `B_R`.  The `.tex`
    -- uses the CONTINUOUS representative `g'` of (C1) and then has to prove
    -- that `{|g'^i| > μ}` is an open null set, hence empty, to get an
    -- EVERYWHERE bound on the weight.  That is not needed: every hypothesis
    -- and conclusion of `PinchedCaccioppoliLevelBound` that reads the weight
    -- reads it almost everywhere or under an integral, so an almost-everywhere
    -- representative suffices -- and `AEStronglyMeasurable.mk` supplies one
    -- that is measurable on ALL of the space, which is exactly the global
    -- measurability that node asks of its weight.
    have hballU : Metric.ball x₀ R
        = ⋃ m : ℕ, Metric.closedBall x₀ (R - R / (m + 2)) := by
      ext z
      constructor
      · intro hz
        have hd : dist z x₀ < R := Metric.mem_ball.1 hz
        have h1 : (0:ℝ) < R - dist z x₀ := by linarith only [hd]
        obtain ⟨m, hm⟩ := exists_nat_gt (R / (R - dist z x₀))
        have h2 : (0:ℝ) < (m:ℝ) + 2 := by positivity
        have h3 : R / (R - dist z x₀) < (m:ℝ) + 2 := by linarith only [hm]
        rw [div_lt_iff₀ h1] at h3
        refine Set.mem_iUnion.2 ⟨m, Metric.mem_closedBall.2 ?_⟩
        have h4 : R / ((m:ℝ) + 2) ≤ R - dist z x₀ := by
          rw [div_le_iff₀ h2]
          nlinarith only [h3]
        linarith only [h4]
      · intro hz
        obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hz
        have h2 : (0:ℝ) < (m:ℝ) + 2 := by positivity
        have h5 : 0 < R / ((m:ℝ) + 2) := by positivity
        exact Metric.mem_ball.2
          (lt_of_le_of_lt (Metric.mem_closedBall.1 hm) (by linarith only [h5]))
    have hcbcpt : ∀ m : ℕ, IsCompact (Metric.closedBall x₀ (R - R / (m + 2))) :=
      fun m => isCompact_closedBall _ _
    have hcbsub : ∀ m : ℕ,
        Metric.closedBall x₀ (R - R / (m + 2)) ⊆ Metric.ball x₀ R := by
      intro m
      rw [hballU]
      exact Set.subset_iUnion
        (fun j : ℕ => Metric.closedBall x₀ (R - R / ((j:ℝ) + 2))) m
    have hgR : AEStronglyMeasurable g (volume.restrict (Metric.ball x₀ R)) := by
      rw [hballU]
      exact aestronglyMeasurable_iUnion_iff.2 fun m =>
        (hsol.1.2 _ (hcbcpt m) (hcbsub m)).2.1
    obtain ⟨gh, hghm, hghae⟩ := hgR
    -- the weight, measurable on all of the space
    obtain ⟨wt, hwtdef⟩ : ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
      f = fun x => ε + ‖gh x‖ ^ 2 := ⟨_, rfl⟩
    have hwteq : ∀ x, wt x = ε + ‖gh x‖ ^ 2 := fun x => by rw [hwtdef]
    have hwtmeas : Measurable wt := by
      rw [hwtdef]
      exact ((hghm.measurable.norm).pow_const 2).const_add ε
    have hwtae : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
        wt x = ε + ‖g x‖ ^ 2 := by
      filter_upwards [hghae] with x hx
      rw [hwteq x, hx]
    have hwtlow : ∀ x : EuclideanSpace ℝ (Fin n), ε ≤ wt x := by
      intro x
      rw [hwteq x]
      have := sq_nonneg ‖gh x‖
      linarith only [this]
    -- (0.1): the upper half of the two-sided bound
    have hwtup : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
        wt x ≤ ε + 4 * (n:ℝ) * (μ / 2) ^ 2 := by
      have hbdall : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), ∀ i : Fin n,
          |g x i| ≤ μ := ae_all_iff.2 hbd
      filter_upwards [hbdall, hghae] with x hx hx2
      have hterm : ∀ i : Fin n, (gh x i) ^ 2 ≤ μ ^ 2 := by
        intro i
        have h1 : |gh x i| ≤ μ := by rw [← hx2]; exact hx i
        nlinarith only [h1, abs_nonneg (gh x i), sq_abs (gh x i)]
      have hsum : ‖gh x‖ ^ 2 ≤ (n:ℝ) * μ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        calc ∑ i, (gh x i) ^ 2 ≤ ∑ _i : Fin n, μ ^ 2 :=
              Finset.sum_le_sum fun i _ => hterm i
          _ = (n:ℝ) * μ ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              simp [nsmul_eq_mul]
      rw [hwteq x]
      nlinarith only [hsum]
    -- the coordinate bound, used for the level-set pinch of Step 2(ii)
    have hcoordsq : ∀ (y : EuclideanSpace ℝ (Fin n)) (i : Fin n),
        (y i) ^ 2 ≤ ‖y‖ ^ 2 := by
      intro y i
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (f := fun m => (y m) ^ 2)
        (fun m _ => sq_nonneg _) (Finset.mem_univ i)
    -- `DeGiorgiLevelBound` is weakened by increasing `γ`, so one constant
    -- serves every instance below
    have hDGmono : ∀ (γ γ' : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
        (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (ℓ ρ₀ ρ₁ : ℝ), 0 < ρ₁ → γ ≤ γ' → ρ₀ < ρ₁ →
        DeGiorgiLevelBound n γ f G x₀ ℓ ρ₀ ρ₁ →
        DeGiorgiLevelBound n γ' f G x₀ ℓ ρ₀ ρ₁ := by
      intro γ γ' f G ℓ ρ₀ ρ₁ hρ1 hγ hρ01 hDGB
      obtain ⟨⟨C, hC⟩, hineq⟩ := hDGB
      refine ⟨⟨C, hC⟩, le_trans hineq ?_⟩
      have hNB : Filter.NeBot (ae (volume.restrict (Metric.ball x₀ ρ₁))) := by
        rw [ae_neBot]
        intro hcc
        rw [← Measure.measure_univ_eq_zero, Measure.restrict_apply_univ] at hcc
        exact (Metric.measure_ball_pos volume x₀ hρ1).ne' hcc
      have hbdd : Filter.IsBoundedUnder (· ≤ ·)
          (ae (volume.restrict (Metric.ball x₀ ρ₁)))
          (fun x => max (f x - ℓ) 0 ^ 2) := by
        refine ⟨max C 0 ^ 2, ?_⟩
        rw [Filter.eventually_map]
        filter_upwards [hC] with x hx
        have h0 : (0:ℝ) ≤ max (f x - ℓ) 0 := le_max_right _ _
        exact pow_le_pow_left₀ h0 (le_trans hx (le_max_left _ _)) 2
      have hes0 : (0:ℝ)
          ≤ essSup (fun x => max (f x - ℓ) 0 ^ 2)
              (volume.restrict (Metric.ball x₀ ρ₁)) := by
        obtain ⟨x, hx⟩ := (ae_le_essSup hbdd).exists
        exact le_trans (sq_nonneg _) hx
      have hvol0 : (0:ℝ)
          ≤ (volume (Metric.ball x₀ ρ₁ ∩ {y | ℓ < f y})).toReal :=
        ENNReal.toReal_nonneg
      have hd0 : (0:ℝ) < (ρ₁ - ρ₀) ^ 2 := by
        have : (0:ℝ) < ρ₁ - ρ₀ := by linarith only [hρ01]
        positivity
      have hstep : γ / (ρ₁ - ρ₀) ^ 2 ≤ γ' / (ρ₁ - ρ₀) ^ 2 := by
        rw [div_le_div_iff₀ hd0 hd0]
        exact mul_le_mul_of_nonneg_right hγ hd0.le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hstep hes0) hvol0
    have hgaev : ∀ᵐ x ∂volume, x ∈ Metric.ball x₀ R → g x = gh x :=
      (ae_restrict_iff' measurableSet_ball).1 hghae
    have hghk : ∀ k : Fin n,
        Measurable (fun y : EuclideanSpace ℝ (Fin n) => gh y k) := fun k =>
      ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous.measurable).comp hghm.measurable
    -- Steps 1, 2 and 3: the two `DeGiorgiLevelBound` families, at every `k`.
    -- Step 2(i) makes both available at EVERY level when `ε ≥ λ²`; Step 2(ii)
    -- makes the `+` one available for `ℓ ∈ [μ/2, μ]` and the `−` one for
    -- `ℓ ∈ [-μ, -μ/2]` when `ε < λ²`.  Those are exactly the families Steps 6
    -- and 7 consume.  `γ_♯ = max γ₉ (16 C₁₂)` serves every instance because
    -- `DeGiorgiLevelBound` is weakened by increasing `γ` (`hDGmono`).
    have hDG : ∀ (k : Fin n) (ℓ ρ₀ ρ₁ : ℝ), 0 < ρ₀ → ρ₀ < ρ₁ → ρ₁ < R →
        (((μ / 2) ^ 2 ≤ ε ∨ (μ / 2 ≤ ℓ ∧ ℓ ≤ μ)) →
          DeGiorgiLevelBound n γs (fun x => g x k) (Dg k) x₀ ℓ ρ₀ ρ₁)
        ∧ (((μ / 2) ^ 2 ≤ ε ∨ (-μ ≤ ℓ ∧ ℓ ≤ -(μ / 2))) →
          DeGiorgiLevelBound n γs (fun x => -(g x k)) (fun x => -(Dg k x)) x₀ (-ℓ)
            ρ₀ ρ₁) := by
      intro k ℓ ρ₀ ρ₁ hρ₀ hρ01 hρ1R
      have hρ10 : 0 < ρ₁ := lt_trans hρ₀ hρ01
      have hγ9s : γ₉ ≤ γs := by rw [hγsdef]; exact le_max_left _ _
      have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      -- Step 1, transported to the weight `wt`
      have hCac : ∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
          tsupport ζ ⊆ Metric.ball x₀ R →
          ((∫ x in Metric.ball x₀ R ∩ {y | ℓ < g y k},
                wt x ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
              ≤ c₄ * ∫ x in Metric.ball x₀ R, wt x ^ (p / 2 - 1)
                  * max (g x k - ℓ) 0 ^ 2
                  * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2)
            ∧ ((∫ x in Metric.ball x₀ R ∩ {y | g y k < ℓ},
                wt x ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
              ≤ c₄ * ∫ x in Metric.ball x₀ R, wt x ^ (p / 2 - 1)
                  * max (ℓ - g x k) 0 ^ 2
                  * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) := by
        intro ζ hζsm hζcs hζts
        obtain ⟨h1, h2⟩ := hCacc ε γ₀ γ₁ (Metric.ball x₀ R) A u g Dg ζ k ℓ
          hε hγ₀ hγ₁ Metric.isOpen_ball hQ hC1 hsol hDg hζsm hζcs hζts
        have e1 : (∫ x in Metric.ball x₀ R ∩ {y | ℓ < g y k},
              wt x ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
            = ∫ x in Metric.ball x₀ R ∩ {y | ℓ < g y k},
              (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset
            Set.inter_subset_left hwtae] with x hx
          rw [hx]
        have e2 : (∫ x in Metric.ball x₀ R ∩ {y | g y k < ℓ},
              wt x ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
            = ∫ x in Metric.ball x₀ R ∩ {y | g y k < ℓ},
              (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset
            Set.inter_subset_left hwtae] with x hx
          rw [hx]
        have e3 : (∫ x in Metric.ball x₀ R, wt x ^ (p / 2 - 1)
              * max (g x k - ℓ) 0 ^ 2
              * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2)
            = ∫ x in Metric.ball x₀ R, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
              * max (g x k - ℓ) 0 ^ 2
              * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [hwtae] with x hx
          rw [hx]
        have e4 : (∫ x in Metric.ball x₀ R, wt x ^ (p / 2 - 1)
              * max (ℓ - g x k) 0 ^ 2
              * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2)
            = ∫ x in Metric.ball x₀ R, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
              * max (ℓ - g x k) 0 ^ 2
              * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [hwtae] with x hx
          rw [hx]
        rw [e1, e2, e3, e4]
        exact ⟨h1, h2⟩
      -- Step 3: the node, at a pinch pair
      have hmk : ∀ κ₁ κ₂ : ℝ, 0 < κ₁ → κ₂ ≤ (1 + 4 * (n:ℝ)) * κ₁ →
          ((∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R ∩ {y | ℓ < g y k})),
              κ₁ ≤ wt x ∧ wt x ≤ κ₂) →
            DeGiorgiLevelBound n γs (fun x => g x k) (Dg k) x₀ ℓ ρ₀ ρ₁)
          ∧ ((∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R ∩ {y | g y k < ℓ})),
              κ₁ ≤ wt x ∧ wt x ≤ κ₂) →
            DeGiorgiLevelBound n γs (fun x => -(g x k)) (fun x => -(Dg k x)) x₀
              (-ℓ) ρ₀ ρ₁) := by
        intro κ₁ κ₂ hκ1 hκ2
        obtain ⟨hp1, hp2⟩ := hPinch x₀ R μ ℓ κ₁ κ₂ (fun x => g x k) (Dg k) wt
          hR hκ1 hκ2 hwtmeas (hDg k) (hbd k) ρ₀ ρ₁ hρ₀ hρ01 hρ1R
        refine ⟨fun hpin => ?_, fun hpin => ?_⟩
        · exact hDGmono γ₉ γs _ _ ℓ ρ₀ ρ₁ hρ10 hγ9s hρ01
            (hp1 hpin (fun ζ h1 h2 h3 => (hCac ζ h1 h2 h3).1))
        · exact hDGmono γ₉ γs _ _ (-ℓ) ρ₀ ρ₁ hρ10 hγ9s hρ01
            (hp2 hpin (fun ζ h1 h2 h3 => (hCac ζ h1 h2 h3).2))
      -- Step 2(i): the regime `ε ≥ λ²`, both sides at every level
      have hreg1 : (μ / 2) ^ 2 ≤ ε →
          ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
            ε ≤ wt x ∧ wt x ≤ (1 + 4 * (n:ℝ)) * ε := by
        intro hA
        filter_upwards [hwtup] with x hx
        refine ⟨hwtlow x, ?_⟩
        nlinarith only [hx, hA, hn0]
      refine ⟨fun hreg => ?_, fun hreg => ?_⟩
      · rcases le_or_gt ((μ / 2) ^ 2) ε with hA | hA
        · refine (hmk ε ((1 + 4 * (n:ℝ)) * ε) hε le_rfl).1 ?_
          exact ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left
            (hreg1 hA)
        · rcases hreg with hcon | ⟨hℓ1, hℓ2⟩
          · exact absurd hcon (not_le.2 hA)
          · refine (hmk ((μ / 2) ^ 2) ((1 + 4 * (n:ℝ)) * (μ / 2) ^ 2)
              (by positivity) le_rfl).1 ?_
            have hset : volume.restrict (Metric.ball x₀ R ∩ {y | ℓ < g y k})
                = volume.restrict (Metric.ball x₀ R ∩ {y | ℓ < gh y k}) := by
              refine Measure.restrict_congr_set (Filter.eventuallyEq_set.2 ?_)
              filter_upwards [hgaev] with x hx
              constructor
              · rintro ⟨h1, h2⟩
                exact ⟨h1, by show ℓ < gh x k; rw [← hx h1]; exact h2⟩
              · rintro ⟨h1, h2⟩
                exact ⟨h1, by show ℓ < g x k; rw [hx h1]; exact h2⟩
            have hms : MeasurableSet (Metric.ball x₀ R ∩ {y | ℓ < gh y k}) :=
              measurableSet_ball.inter (measurableSet_lt measurable_const (hghk k))
            rw [hset]
            filter_upwards [ae_restrict_mem hms,
              ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hwtup]
              with x hx hx2
            obtain ⟨-, hxl⟩ := hx
            have hxl' : ℓ < gh x k := hxl
            have hsq : (μ / 2) ^ 2 ≤ (gh x k) ^ 2 := by
              nlinarith only [hxl', hℓ1, hμpos]
            refine ⟨?_, by nlinarith only [hx2, hA, hn0]⟩
            rw [hwteq x]
            nlinarith only [hsq, hcoordsq (gh x) k, hε.le]
      · rcases le_or_gt ((μ / 2) ^ 2) ε with hA | hA
        · refine (hmk ε ((1 + 4 * (n:ℝ)) * ε) hε le_rfl).2 ?_
          exact ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left
            (hreg1 hA)
        · rcases hreg with hcon | ⟨hℓ1, hℓ2⟩
          · exact absurd hcon (not_le.2 hA)
          · refine (hmk ((μ / 2) ^ 2) ((1 + 4 * (n:ℝ)) * (μ / 2) ^ 2)
              (by positivity) le_rfl).2 ?_
            have hset : volume.restrict (Metric.ball x₀ R ∩ {y | g y k < ℓ})
                = volume.restrict (Metric.ball x₀ R ∩ {y | gh y k < ℓ}) := by
              refine Measure.restrict_congr_set (Filter.eventuallyEq_set.2 ?_)
              filter_upwards [hgaev] with x hx
              constructor
              · rintro ⟨h1, h2⟩
                exact ⟨h1, by show gh x k < ℓ; rw [← hx h1]; exact h2⟩
              · rintro ⟨h1, h2⟩
                exact ⟨h1, by show g x k < ℓ; rw [hx h1]; exact h2⟩
            have hms : MeasurableSet (Metric.ball x₀ R ∩ {y | gh y k < ℓ}) :=
              measurableSet_ball.inter (measurableSet_lt (hghk k) measurable_const)
            rw [hset]
            filter_upwards [ae_restrict_mem hms,
              ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hwtup]
              with x hx hx2
            obtain ⟨-, hxl⟩ := hx
            have hxl' : gh x k < ℓ := hxl
            have hsq : (μ / 2) ^ 2 ≤ (gh x k) ^ 2 := by
              nlinarith only [hxl', hℓ2, hμpos]
            refine ⟨?_, by nlinarith only [hx2, hA, hn0]⟩
            rw [hwteq x]
            nlinarith only [hsq, hcoordsq (gh x) k, hε.le]
    -- the volume of a ball, in the form Steps 6 and 7 both need (the idiom is
    -- `LevelTruncationMaximumPrinciple`'s, l. 98-105)
    have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hntriv : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
      refine ⟨⟨0, EuclideanSpace.single ⟨0, hnpos⟩ (1 : ℝ), ?_⟩⟩
      intro hc
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hnpos⟩) hc
      simp at h
    have hωn : (0:ℝ)
        < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
      refine ENNReal.toReal_pos ?_ measure_ball_lt_top.ne
      exact (Metric.isOpen_ball.measure_pos volume
        ⟨0, Metric.mem_ball_self one_pos⟩).ne'
    obtain ⟨ωn, hωndef⟩ : ∃ w : ℝ,
      w = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := ⟨_, rfl⟩
    rw [← hωndef] at hωn
    have hballvol : ∀ σ : ℝ, 0 ≤ σ →
        (volume (Metric.ball x₀ σ)).toReal = ωn * σ ^ n := by
      intro σ hσ
      rw [Measure.addHaar_ball volume x₀ hσ, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity),
        show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n by simp, hωndef]
      ring
    -- the level sets of `g^k` have the same measure as those of `gh^k`
    have hswapgt : ∀ (k : Fin n) (ρ c : ℝ), ρ ≤ R →
        volume (Metric.ball x₀ ρ ∩ {y | c < g y k})
          = volume (Metric.ball x₀ ρ ∩ {y | c < gh y k}) := by
      intro k ρ c hρ
      refine measure_congr (Filter.eventuallyEq_set.2 ?_)
      filter_upwards [hgaev] with x hx
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        show c < gh x k
        rw [← hx (Metric.ball_subset_ball hρ h1)]
        exact h2
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        show c < g x k
        rw [hx (Metric.ball_subset_ball hρ h1)]
        exact h2
    have hswaplt : ∀ (k : Fin n) (ρ c : ℝ), ρ ≤ R →
        volume (Metric.ball x₀ ρ ∩ {y | g y k < c})
          = volume (Metric.ball x₀ ρ ∩ {y | gh y k < c}) := by
      intro k ρ c hρ
      refine measure_congr (Filter.eventuallyEq_set.2 ?_)
      filter_upwards [hgaev] with x hx
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        show gh x k < c
        rw [← hx (Metric.ball_subset_ball hρ h1)]
        exact h2
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        show g x k < c
        rw [hx (Metric.ball_subset_ball hρ h1)]
        exact h2
    -- (6.1)/(3.21): the complement of a large level set is small
    have hdisj61 : ∀ (ρ : ℝ) (A B : Set (EuclideanSpace ℝ (Fin n))), ρ ≤ R →
        MeasurableSet A → MeasurableSet B → Disjoint A B →
        θ₂ * (volume (Metric.ball x₀ R)).toReal
            ≤ (volume (Metric.ball x₀ R ∩ A)).toReal →
        (volume (Metric.ball x₀ ρ ∩ B)).toReal
          ≤ (1 - θ₂) * (volume (Metric.ball x₀ R)).toReal := by
      intro ρ A B hρ hA hB hAB hle
      have hfinR : volume (Metric.ball x₀ R) ≠ ⊤ := measure_ball_lt_top.ne
      have hfinA : volume (Metric.ball x₀ R ∩ A) ≠ ⊤ :=
        ne_top_of_le_ne_top hfinR (measure_mono Set.inter_subset_left)
      have hfinB : volume (Metric.ball x₀ R ∩ B) ≠ ⊤ :=
        ne_top_of_le_ne_top hfinR (measure_mono Set.inter_subset_left)
      have hadd : volume (Metric.ball x₀ R ∩ A) + volume (Metric.ball x₀ R ∩ B)
          ≤ volume (Metric.ball x₀ R) := by
        rw [← measure_union
          (hAB.mono Set.inter_subset_right Set.inter_subset_right)
          (measurableSet_ball.inter hB)]
        refine measure_mono ?_
        intro x hx
        rcases hx with h | h
        · exact h.1
        · exact h.1
      have hadd' : (volume (Metric.ball x₀ R ∩ A)).toReal
          + (volume (Metric.ball x₀ R ∩ B)).toReal
          ≤ (volume (Metric.ball x₀ R)).toReal := by
        rw [← ENNReal.toReal_add hfinA hfinB]
        exact ENNReal.toReal_mono hfinR hadd
      have hmono : (volume (Metric.ball x₀ ρ ∩ B)).toReal
          ≤ (volume (Metric.ball x₀ R ∩ B)).toReal :=
        ENNReal.toReal_mono hfinB
          (measure_mono (Set.inter_subset_inter_left _
            (Metric.ball_subset_ball hρ)))
      linarith only [hle, hadd', hmono]
    refine ⟨fun k hk => ?_, fun hno k => ?_⟩
    · -- STEP 6, part (a).  Steps 0(0b), 1, 2 and 3 are DONE above and shared
      -- with part (b); what is left of the `.tex` here is Step 6 alone
      -- (l. 833-943).  In scope, besides Step 5's constants
      -- (`c₄, hCacc`; `γ₉, hPinch`; `C₁₂, hSPGE`; `γs`; `θa/θb/θ0s/θ₂`;
      -- `t, lam1, c₀, lam1'', θc, θ₁c, lam₂, ν`, with `hLTa, hLTb, hLTc,
      -- hLSMI`) and the data `ε γ₀ γ₁ μ A u g Dg x₀ R` with
      -- `hε hγ₀ hγ₁ hR hQ hC1 hsol hDg hbd hleast`, `hμpos`, `hNBR`,
      -- `hsubhalf`, the index `k` and the hypothesis `hk` of (a):
      --   * `hDG k ℓ ρ₀ ρ₁ hρ₀ hρ01 hρ1R` -- the two `DeGiorgiLevelBound`
      --     families of Step 3, at `γs`.  `.1` is the `g^k` family, available
      --     at EVERY `ℓ` when `(μ/2)^2 ≤ ε` and for `ℓ ∈ [μ/2, μ]` otherwise;
      --     `.2` is the `-g^k` family at level `-ℓ`, available at every `ℓ`
      --     in the first regime and for `ℓ ∈ [-μ, -μ/2]` in the second.  To
      --     feed `hLTa`/`hLTb` at a level `l`, take `ℓ = -l` in `.2` and
      --     rewrite `- -l = l` with `neg_neg`.
      --   * `hDGmono` -- `DeGiorgiLevelBound` is weakened by increasing `γ`.
      --   * `gh`, `hghm`, `hghae`, `hgaev`, `hghk` -- a GLOBALLY measurable
      --     representative of `g` on `B_R`.  Step 6 needs the MEASURES of the
      --     level sets `B_R ∩ {μ/2 < g^k}` etc., which are only null
      --     measurable; `measure_congr` against the `gh` version (the sets are
      --     a.e. equal by `hgaev`, and the `gh` version is measurable by
      --     `hghk`) is the same move `hDG` makes with
      --     `Measure.restrict_congr_set`.
      --   * `wt`, `hwteq`, `hwtmeas`, `hwtae`, `hwtlow`, `hwtup` -- the weight
      --     and its two-sided bound (0.1), if Step 6 needs them again.
      -- STILL TO DO: (6.1), the measure inequality, which needs the scaling
      -- `|B_{cR}| = c^n |B_R|` to turn `(1-θ₂)|B_R|` into `θ0s|B_S|` with
      -- `S = 3R/4`; (6a) the case `(μ/2)^2 ≤ ε`, an `hLTa` instance at
      -- `S = 3R/4`, `κ = -μ/2`, `f = -g^k`, whose `MemW1pOn n 2 (B_S)` comes
      -- from `hDg k` by clause (4) of `WeakGradientRestrict` and clause (2)
      -- of `WeakGradientLinear` (both already in the transitive cone, so no
      -- import is needed); and (6b) the case `(μ/2)^2 > ε`, which consumes
      -- `hSPGE` at this `k` for Step 4's `v`, `V`, `h₀` and then runs `hLTb`.
      -- the outer radius `S = 3R/4` of Step 5, and `λ₁' S = R/2`
      obtain ⟨S, hSdef⟩ : ∃ s : ℝ, s = 3 * R / 4 := ⟨_, rfl⟩
      have hS0 : 0 < S := by rw [hSdef]; linarith only [hR]
      have hSR : S < R := by rw [hSdef]; linarith only [hR]
      have hSsub : Metric.ball x₀ S ⊆ Metric.ball x₀ R :=
        Metric.ball_subset_ball hSR.le
      have h23S : 2 / 3 * S = R / 2 := by rw [hSdef]; ring
      have hhalfS : R / 2 < S := by rw [hSdef]; linarith only [hR]
      have hhalfsub : Metric.ball x₀ (R / 2) ⊆ Metric.ball x₀ S :=
        Metric.ball_subset_ball hhalfS.le
      have hvolS : (volume (Metric.ball x₀ S)).toReal
          = (3 / 4 : ℝ) ^ n * (volume (Metric.ball x₀ R)).toReal := by
        rw [hballvol S hS0.le, hballvol R hR.le, hSdef,
          show (3 * R / 4 : ℝ) = (3 / 4) * R from by ring, mul_pow]
        ring
      have hvolSnn : (0:ℝ) ≤ (volume (Metric.ball x₀ S)).toReal :=
        ENNReal.toReal_nonneg
      have h1θ₂ : (1 - θ₂) * (volume (Metric.ball x₀ R)).toReal
          = θ0s * (volume (Metric.ball x₀ S)).toReal := by
        rw [hvolS, hθ₂def]
        ring
      have hθ0sa : θ0s ≤ θa := by
        rw [hθ0sdef]
        exact le_trans (min_le_left _ _) (min_le_left _ _)
      -- the `W^{1,2}(B_S)` pair, by (0.3)
      have hclcpt : IsCompact (closure (Metric.ball x₀ S)) :=
        (isCompact_closedBall x₀ S).of_isClosed_subset isClosed_closure
          Metric.closure_ball_subset_closedBall
      have hclsub : closure (Metric.ball x₀ S) ⊆ Metric.ball x₀ R :=
        subset_trans Metric.closure_ball_subset_closedBall
          (Metric.closedBall_subset_ball hSR)
      have hWS : MemW1pOn n 2 (Metric.ball x₀ S) (fun x => g x k) (Dg k) :=
        (WeakGradientRestrict n 2 hn1 (by norm_num) (Metric.ball x₀ R)
          (Metric.ball x₀ S) (fun x => g x k) (Dg k) Metric.isOpen_ball
          Metric.isOpen_ball hSsub).2.2.2 (hDg k) hclcpt hclsub
      have hWSneg : MemW1pOn n 2 (Metric.ball x₀ S) (fun x => -(g x k))
          (fun x => -(Dg k x)) := by
        have hsrc := (WeakGradientLinear n 2 hn1 (by norm_num) (Metric.ball x₀ S)
          (fun x => g x k) (fun x => g x k) (Dg k) (Dg k) (-1) 0 0
          Metric.isOpen_ball).2.1 hWS hWS
        have e1 : (fun x : EuclideanSpace ℝ (Fin n) =>
              (-1 : ℝ) * g x k + (0 : ℝ) * g x k)
            = fun x : EuclideanSpace ℝ (Fin n) => -(g x k) := by
          funext x; ring
        have e2 : (fun x : EuclideanSpace ℝ (Fin n) =>
              (-1 : ℝ) • Dg k x + (0 : ℝ) • Dg k x)
            = fun x : EuclideanSpace ℝ (Fin n) => -(Dg k x) := by
          funext x
          rw [neg_smul, one_smul, zero_smul, add_zero]
        rw [e1, e2] at hsrc
        exact hsrc
      -- the maximum-principle step, written once for both alternatives
      have hLTapply : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ)
          (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          MemW1pOn n 2 (Metric.ball x₀ S) f G →
          (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ S)), f x ≤ μ) →
          (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ S)), -μ ≤ f x) →
          (∀ l ρ₀ ρ₁ : ℝ, 0 < ρ₀ → ρ₀ < ρ₁ → ρ₁ ≤ S →
              DeGiorgiLevelBound n γs f G x₀ l ρ₀ ρ₁) →
          (volume (Metric.ball x₀ S ∩ {y | -(μ / 2) < f y})).toReal
            ≤ θ0s * (volume (Metric.ball x₀ S)).toReal →
          ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))), f x ≤ -(μ / 8) := by
        intro f G hW hbdS hlowS hfam hmeas
        obtain ⟨M, hMdef⟩ : ∃ m : ℝ,
          m = essSup f (volume.restrict (Metric.ball x₀ S)) := ⟨_, rfl⟩
        have hneb : (ae (volume.restrict (Metric.ball x₀ S))).NeBot := by
          refine ae_neBot.2 ?_
          simp only [ne_eq, Measure.restrict_eq_zero]
          exact (Metric.isOpen_ball.measure_pos volume
            ⟨x₀, Metric.mem_ball_self hS0⟩).ne'
        have hcob : Filter.IsCoboundedUnder (· ≤ ·)
            (ae (volume.restrict (Metric.ball x₀ S))) f :=
          Filter.isCoboundedUnder_le_of_eventually_le _ hlowS
        have hbddS : Filter.IsBoundedUnder (· ≤ ·)
            (ae (volume.restrict (Metric.ball x₀ S))) f := by
          refine ⟨μ, ?_⟩
          rw [Filter.eventually_map]
          exact hbdS
        have hMle : M ≤ μ := by
          rw [hMdef]
          exact essSup_le_of_ae_le μ hbdS hcob
        rcases le_or_gt M (-(μ / 2)) with hMsmall | hMbig
        · have h1 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ S)),
              f x ≤ -(μ / 2) := by
            filter_upwards [ae_le_essSup hbddS] with x hx
            rw [← hMdef] at hx
            linarith only [hx, hMsmall]
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hhalfsub h1] with x hx
          linarith only [hx, hμpos]
        · have hconc := hLTa x₀ S (-(μ / 2)) M f G hS0 hW ⟨μ, hbdS⟩ hMdef hMbig
            (fun l ρ₀ ρ₁ _ hρ₀ hρ₁ hlt =>
              hfam l ρ₀ ρ₁
                (by
                  have := hρ₀.1
                  rw [h23S] at this
                  linarith only [this, hR])
                hlt hρ₁.2)
            (le_trans hmeas (mul_le_mul_of_nonneg_right hθ0sa hvolSnn))
          rw [h23S] at hconc
          filter_upwards [hconc] with x hx
          linarith only [hx, hMle, hμpos]
      -- `min {1/16, 2^{-1-4/p}} ≤ 1/8`
      have hcst8 : min (1 / 16 : ℝ) ((2:ℝ) ^ (-1 - 4 / p)) ≤ 1 / 8 :=
        le_trans (min_le_left _ _) (by norm_num)
      rcases le_or_gt ((μ / 2) ^ 2) ε with hreg | hreg
      · -- (6a) the case `ε ≥ λ²`: Step 2(i) supplies every level
        rcases hk with halt | halt
        · -- the first alternative, run on `-g^k`
          have hfam : ∀ l ρ₀ ρ₁ : ℝ, 0 < ρ₀ → ρ₀ < ρ₁ → ρ₁ ≤ S →
              DeGiorgiLevelBound n γs (fun x => -(g x k)) (fun x => -(Dg k x))
                x₀ l ρ₀ ρ₁ := by
            intro l ρ₀ ρ₁ h0 h01 h1S
            have h := (hDG k (-l) ρ₀ ρ₁ h0 h01
              (lt_of_le_of_lt h1S hSR)).2 (Or.inl hreg)
            rwa [neg_neg] at h
          have hbdS : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ S)),
              -(g x k) ≤ μ := by
            filter_upwards [ae_restrict_of_ae_restrict_of_subset hSsub (hbd k)]
              with x hx
            have := neg_abs_le (g x k)
            linarith only [hx, this]
          have hset : {y : EuclideanSpace ℝ (Fin n) | -(μ / 2) < -(g y k)}
              = {y | g y k < μ / 2} := by
            ext y
            constructor
            · intro hy
              have h1 : -(μ / 2) < -(g y k) := hy
              show g y k < μ / 2
              linarith only [h1]
            · intro hy
              have h1 : g y k < μ / 2 := hy
              show -(μ / 2) < -(g y k)
              linarith only [h1]
          have hmeas : (volume (Metric.ball x₀ S ∩ {y | -(μ / 2) < -(g y k)})).toReal
              ≤ θ0s * (volume (Metric.ball x₀ S)).toReal := by
            rw [hset, hswaplt k S (μ / 2) hSR.le, ← h1θ₂]
            refine hdisj61 S {y | μ / 2 < gh y k} {y | gh y k < μ / 2} hSR.le
              (measurableSet_lt measurable_const (hghk k))
              (measurableSet_lt (hghk k) measurable_const) ?_ ?_
            · refine Set.disjoint_left.2 fun x hx hx' => ?_
              have h1 : μ / 2 < gh x k := hx
              have h2 : gh x k < μ / 2 := hx'
              linarith only [h1, h2]
            · rw [← hswapgt k R (μ / 2) le_rfl]
              exact halt
          have hlowS : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ S)),
              -μ ≤ -(g x k) := by
            filter_upwards [ae_restrict_of_ae_restrict_of_subset hSsub (hbd k)]
              with x hx
            have := le_abs_self (g x k)
            linarith only [hx, this]
          filter_upwards [hLTapply _ _ hWSneg hbdS hlowS hfam hmeas] with x hx
          have hgk : μ / 8 ≤ |g x k| := by
            rw [abs_of_nonneg (by linarith only [hx, hμpos] : (0:ℝ) ≤ g x k)]
            linarith only [hx]
          nlinarith only [hgk, hcst8, hμpos]
        · -- the second alternative, run on `g^k`
          have hfam : ∀ l ρ₀ ρ₁ : ℝ, 0 < ρ₀ → ρ₀ < ρ₁ → ρ₁ ≤ S →
              DeGiorgiLevelBound n γs (fun x => g x k) (Dg k) x₀ l ρ₀ ρ₁ := by
            intro l ρ₀ ρ₁ h0 h01 h1S
            exact (hDG k l ρ₀ ρ₁ h0 h01 (lt_of_le_of_lt h1S hSR)).1 (Or.inl hreg)
          have hbdS : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ S)),
              g x k ≤ μ := by
            filter_upwards [ae_restrict_of_ae_restrict_of_subset hSsub (hbd k)]
              with x hx
            exact le_trans (le_abs_self _) hx
          have hmeas : (volume (Metric.ball x₀ S ∩ {y | -(μ / 2) < g y k})).toReal
              ≤ θ0s * (volume (Metric.ball x₀ S)).toReal := by
            rw [hswapgt k S (-(μ / 2)) hSR.le, ← h1θ₂]
            refine hdisj61 S {y | gh y k < -(μ / 2)} {y | -(μ / 2) < gh y k}
              hSR.le (measurableSet_lt (hghk k) measurable_const)
              (measurableSet_lt measurable_const (hghk k)) ?_ ?_
            · refine Set.disjoint_left.2 fun x hx hx' => ?_
              have h1 : gh x k < -(μ / 2) := hx
              have h2 : -(μ / 2) < gh x k := hx'
              linarith only [h1, h2]
            · rw [← hswaplt k R (-(μ / 2)) le_rfl]
              exact halt
          have hlowS : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ S)),
              -μ ≤ g x k := by
            filter_upwards [ae_restrict_of_ae_restrict_of_subset hSsub (hbd k)]
              with x hx
            have := neg_abs_le (g x k)
            linarith only [hx, this]
          filter_upwards [hLTapply _ _ hWS hbdS hlowS hfam hmeas] with x hx
          have hgk : μ / 8 ≤ |g x k| := by
            rw [abs_of_nonpos (by linarith only [hx, hμpos] : g x k ≤ 0)]
            linarith only [hx]
          nlinarith only [hgk, hcst8, hμpos]
      · -- (6b) the case `ε < λ²`
        -- (6b) the case `ε < λ²`: Step 4 supplies `v`, `V` and `h₀`
        have hp20 : (0:ℝ) < p / 2 := by linarith only [hp]
        have hpne : p ≠ 0 := ne_of_gt (by linarith only [hp])
        obtain ⟨h0, hh0def⟩ : ∃ s : ℝ, s = (μ / 2) ^ (p / 2) := ⟨_, rfl⟩
        have hh00 : 0 < h0 := by
          rw [hh0def]; exact Real.rpow_pos_of_pos (by linarith only [hμpos]) _
        obtain ⟨hv1, hv2⟩ := hSPGE ε γ₀ γ₁ μ A u g Dg x₀ R k hε hγ₀ hγ₁ hR hμpos
          hreg hQ hC1 hsol hDg hbd
        have hθ0sb : θ0s ≤ θb := by
          rw [hθ0sdef]
          exact le_trans (min_le_left _ _) (min_le_right _ _)
        -- `|v| = |g^k|^{p/2}` and `|v| ≤ 2^{p/2} h₀`
        have hvabs : ∀ t : ℝ, |(|t| ^ (p / 2 - 1) * t)| = |t| ^ (p / 2) := by
          intro t
          rcases eq_or_ne t 0 with ht | ht
          · subst ht
            rw [mul_zero, abs_zero, Real.zero_rpow (ne_of_gt hp20)]
          · have hta : 0 < |t| := abs_pos.2 ht
            rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _),
              ← Real.rpow_add_one (ne_of_gt hta) (p / 2 - 1)]
            congr 1
            ring
        -- the common conclusion of both branches
        have hfinal : ∀ x : EuclideanSpace ℝ (Fin n), h0 / 4 ≤ |g x k| ^ (p / 2) →
            min (1 / 16 : ℝ) ((2:ℝ) ^ (-1 - 4 / p)) * μ ≤ |g x k| := by
          intro x hgk
          have h4 : (2:ℝ) ^ (-2 : ℝ) = 1 / 4 := by
            rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) from by norm_num, Real.rpow_intCast]
            norm_num
          have hpe : (-1 - 4 / p) * (p / 2) = -(p / 2) + (-2) := by
            field_simp
            ring
          have hcpow : ((2:ℝ) ^ (-1 - 4 / p) * μ) ^ (p / 2) = h0 / 4 := by
            rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) hμpos.le,
              ← Real.rpow_mul (by norm_num), hpe, Real.rpow_add (by norm_num),
              Real.rpow_neg (by norm_num), h4, hh0def,
              show (μ / 2 : ℝ) = μ * 2⁻¹ from by ring,
              Real.mul_rpow hμpos.le (by norm_num), Real.inv_rpow (by norm_num)]
            ring
          have hstep : (2:ℝ) ^ (-1 - 4 / p) * μ ≤ |g x k| := by
            by_contra hcon
            push_neg at hcon
            have h1 : |g x k| ^ (p / 2)
                < ((2:ℝ) ^ (-1 - 4 / p) * μ) ^ (p / 2) :=
              Real.rpow_lt_rpow (abs_nonneg _) hcon hp20
            rw [hcpow] at h1
            linarith only [h1, hgk]
          have hcm : min (1 / 16 : ℝ) ((2:ℝ) ^ (-1 - 4 / p))
              ≤ (2:ℝ) ^ (-1 - 4 / p) := min_le_right _ _
          nlinarith only [hstep, hcm, hμpos]
        -- the sign-free core of (6b)
        have hstep6b : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ)
            (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
            MemW1pOn n 2 (Metric.ball x₀ S) f G →
            (∀ x, |f x| = |g x k| ^ (p / 2)) →
            (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
              |f x| ≤ (2:ℝ) ^ (p / 2) * h0) →
            (∀ l ρ₀ ρ₁ : ℝ, -h0 ≤ l → R / 2 ≤ ρ₀ → ρ₀ < ρ₁ → ρ₁ ≤ S →
                (∫ x in Metric.ball x₀ ρ₀ ∩ {y | l < f y}, ‖G x‖ ^ 2)
                  ≤ C₁₂ * h0 ^ 2 / (ρ₁ - ρ₀) ^ 2
                    * (volume (Metric.ball x₀ ρ₁ ∩ {y | l < f y})).toReal) →
            (volume (Metric.ball x₀ S ∩ {y | -h0 < f y})).toReal
              ≤ θ0s * (volume (Metric.ball x₀ S)).toReal →
            ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))),
              min (1 / 16 : ℝ) ((2:ℝ) ^ (-1 - 4 / p)) * μ ≤ |g x k| := by
          intro f G hW habs hfbd hfam hmeas
          have hP0 : (0:ℝ) < (2:ℝ) ^ (p / 2) := Real.rpow_pos_of_pos (by norm_num) _
          have hbdS : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ S)),
              f x ≤ (2:ℝ) ^ (p / 2) * h0 := by
            filter_upwards [ae_restrict_of_ae_restrict_of_subset hSsub hfbd] with x hx
            exact le_trans (le_abs_self _) hx
          have hlowS : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ S)),
              -((2:ℝ) ^ (p / 2) * h0) ≤ f x := by
            filter_upwards [ae_restrict_of_ae_restrict_of_subset hSsub hfbd] with x hx
            have := neg_abs_le (f x)
            linarith only [hx, this]
          have hhalf0 : (0:ℝ) < R / 2 := by linarith only [hR]
          have hnebh : (ae (volume.restrict (Metric.ball x₀ (R / 2)))).NeBot := by
            refine ae_neBot.2 ?_
            simp only [ne_eq, Measure.restrict_eq_zero]
            exact (Metric.isOpen_ball.measure_pos volume
              ⟨x₀, Metric.mem_ball_self hhalf0⟩).ne'
          have hbdh : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))),
              f x ≤ (2:ℝ) ^ (p / 2) * h0 :=
            ae_restrict_of_ae_restrict_of_subset hhalfsub hbdS
          have hlowh : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))),
              -((2:ℝ) ^ (p / 2) * h0) ≤ f x :=
            ae_restrict_of_ae_restrict_of_subset hhalfsub hlowS
          obtain ⟨Mk, hMkdef⟩ : ∃ m : ℝ,
            m = essSup f (volume.restrict (Metric.ball x₀ (R / 2))) := ⟨_, rfl⟩
          have hbddh : Filter.IsBoundedUnder (· ≤ ·)
              (ae (volume.restrict (Metric.ball x₀ (R / 2)))) f := by
            refine ⟨(2:ℝ) ^ (p / 2) * h0, ?_⟩
            rw [Filter.eventually_map]
            exact hbdh
          by_cases hbr1 : Mk < -(h0 / 4)
          · -- Branch 1
            filter_upwards [ae_le_essSup hbddh] with x hx
            rw [← hMkdef] at hx
            have hfx : f x < -(h0 / 4) := lt_of_le_of_lt hx hbr1
            have hge : h0 / 4 ≤ |f x| := by
              rw [abs_of_nonpos (by linarith only [hfx, hh00])]
              linarith only [hfx]
            exact hfinal x (by rw [← habs x]; exact hge)
          · -- Branch 2
            have hbr2 : -(h0 / 4) ≤ Mk := not_lt.1 hbr1
            have hconc : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))),
                f x ≤ -(h0 / 2) := by
              obtain ⟨M, hMdef⟩ : ∃ m : ℝ,
                m = essSup f (volume.restrict (Metric.ball x₀ S)) := ⟨_, rfl⟩
              have hnebS : (ae (volume.restrict (Metric.ball x₀ S))).NeBot := by
                refine ae_neBot.2 ?_
                simp only [ne_eq, Measure.restrict_eq_zero]
                exact (Metric.isOpen_ball.measure_pos volume
                  ⟨x₀, Metric.mem_ball_self hS0⟩).ne'
              have hcobS : Filter.IsCoboundedUnder (· ≤ ·)
                  (ae (volume.restrict (Metric.ball x₀ S))) f :=
                Filter.isCoboundedUnder_le_of_eventually_le _ hlowS
              have hMle : M ≤ (2:ℝ) ^ (p / 2) * h0 := by
                rw [hMdef]
                exact essSup_le_of_ae_le _ hbdS hcobS
              rcases le_or_gt M (-h0) with hMsmall | hMbig
              · have hbddS : Filter.IsBoundedUnder (· ≤ ·)
                    (ae (volume.restrict (Metric.ball x₀ S))) f := by
                  refine ⟨(2:ℝ) ^ (p / 2) * h0, ?_⟩
                  rw [Filter.eventually_map]
                  exact hbdS
                have h1 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ S)),
                    f x ≤ -h0 := by
                  filter_upwards [ae_le_essSup hbddS] with x hx
                  rw [← hMdef] at hx
                  linarith only [hx, hMsmall]
                filter_upwards [ae_restrict_of_ae_restrict_of_subset hhalfsub h1]
                  with x hx
                linarith only [hx, hh00]
              · -- the De Giorgi family at the levels the node asks for
                have hfamDG : ∀ l ρ₀ ρ₁ : ℝ,
                    l ∈ Set.Icc (-h0) (lam02 * (-h0) + (1 - lam02) * M) →
                    ρ₀ ∈ Set.Icc (2 / 3 * S) S → ρ₁ ∈ Set.Icc (2 / 3 * S) S →
                    ρ₀ < ρ₁ → DeGiorgiLevelBound n γs f G x₀ l ρ₀ ρ₁ := by
                  intro l ρ₀ ρ₁ hl hρ₀ hρ₁ hlt
                  have hρ₀h : R / 2 ≤ ρ₀ := by
                    have := hρ₀.1; rw [h23S] at this; exact this
                  have hρ₁h : R / 2 ≤ ρ₁ := by
                    have := hρ₁.1; rw [h23S] at this; exact this
                  have hρ₁S : ρ₁ ≤ S := hρ₁.2
                  have hρ₁0 : 0 < ρ₁ := by linarith only [hρ₁h, hR]
                  have hlup : l ≤ -(h0 / 2) := by
                    have h1 : (0:ℝ) ≤ 1 - lam02 := by linarith only [hlam02.2]
                    have h2 : lam02 * (-h0) + (1 - lam02) * M
                        ≤ lam02 * (-h0) + (1 - lam02) * ((2:ℝ) ^ (p / 2) * h0) :=
                      by nlinarith only [h1, hMle]
                    have h3 : lam02 * (-h0)
                        + (1 - lam02) * ((2:ℝ) ^ (p / 2) * h0) = -(h0 / 2) := by
                      rw [hlam02def, ← hPdef]
                      field_simp
                      ring
                    linarith only [hl.2, h2, h3]
                  -- boundedness of the truncation on `B_{ρ₁}`
                  have hsubρ : Metric.ball x₀ ρ₁ ⊆ Metric.ball x₀ R :=
                    Metric.ball_subset_ball (le_trans hρ₁S hSR.le)
                  have hbdρ : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ₁)),
                      f x ≤ (2:ℝ) ^ (p / 2) * h0 := by
                    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsubρ hfbd]
                      with x hx
                    exact le_trans (le_abs_self _) hx
                  have hCbd : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ₁)),
                      max (f x - l) 0 ≤ (2:ℝ) ^ (p / 2) * h0 - l := by
                    filter_upwards [hbdρ] with x hx
                    refine max_le (by linarith only [hx]) ?_
                    have : (0:ℝ) < (2:ℝ) ^ (p / 2) * h0 := mul_pos hP0 hh00
                    linarith only [this, hlup, hh00]
                  refine ⟨⟨(2:ℝ) ^ (p / 2) * h0 - l, hCbd⟩, ?_⟩
                  -- `h₀² ≤ 16 ess sup ((f-l)^+)²` in this branch
                  have hnebρ : (ae (volume.restrict (Metric.ball x₀ ρ₁))).NeBot := by
                    refine ae_neBot.2 ?_
                    simp only [ne_eq, Measure.restrict_eq_zero]
                    exact (Metric.isOpen_ball.measure_pos volume
                      ⟨x₀, Metric.mem_ball_self hρ₁0⟩).ne'
                  have hbddρ : Filter.IsBoundedUnder (· ≤ ·)
                      (ae (volume.restrict (Metric.ball x₀ ρ₁)))
                      (fun x => max (f x - l) 0) := by
                    refine ⟨(2:ℝ) ^ (p / 2) * h0 - l, ?_⟩
                    rw [Filter.eventually_map]
                    exact hCbd
                  have hbdd2 : Filter.IsBoundedUnder (· ≤ ·)
                      (ae (volume.restrict (Metric.ball x₀ ρ₁)))
                      (fun x => max (f x - l) 0 ^ 2) := by
                    refine ⟨((2:ℝ) ^ (p / 2) * h0 - l) ^ 2, ?_⟩
                    rw [Filter.eventually_map]
                    filter_upwards [hCbd] with x hx
                    exact pow_le_pow_left₀ (le_max_right _ _) hx 2
                  have hcobρ : Filter.IsCoboundedUnder (· ≤ ·)
                      (ae (volume.restrict (Metric.ball x₀ ρ₁)))
                      (fun x => max (f x - l) 0) :=
                    Filter.isCoboundedUnder_le_of_le _ (fun x => le_max_right _ _)
                  have hsubhρ : Metric.ball x₀ (R / 2) ⊆ Metric.ball x₀ ρ₁ :=
                    Metric.ball_subset_ball hρ₁h
                  have hcobh : Filter.IsCoboundedUnder (· ≤ ·)
                      (ae (volume.restrict (Metric.ball x₀ (R / 2)))) f :=
                    Filter.isCoboundedUnder_le_of_eventually_le _ hlowh
                  have hMkle : Mk ≤ essSup (fun x => max (f x - l) 0)
                      (volume.restrict (Metric.ball x₀ ρ₁)) + l := by
                    rw [hMkdef]
                    refine essSup_le_of_ae_le _ ?_ hcobh
                    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsubhρ
                      (ae_le_essSup hbddρ)] with x hx
                    have h1 : f x - l ≤ max (f x - l) 0 := le_max_left _ _
                    linarith only [hx, h1]
                  have hE4 : h0 / 4 ≤ essSup (fun x => max (f x - l) 0)
                      (volume.restrict (Metric.ball x₀ ρ₁)) := by
                    linarith only [hMkle, hbr2, hlup]
                  have hsq0 : (0:ℝ) ≤ essSup (fun x => max (f x - l) 0 ^ 2)
                      (volume.restrict (Metric.ball x₀ ρ₁)) := by
                    obtain ⟨z, hz⟩ := (ae_le_essSup hbdd2).exists
                    exact le_trans (sq_nonneg _) hz
                  have hES : essSup (fun x => max (f x - l) 0)
                      (volume.restrict (Metric.ball x₀ ρ₁))
                      ≤ Real.sqrt (essSup (fun x => max (f x - l) 0 ^ 2)
                        (volume.restrict (Metric.ball x₀ ρ₁))) := by
                    refine essSup_le_of_ae_le _ ?_ hcobρ
                    filter_upwards [ae_le_essSup hbdd2] with x hx
                    rw [show max (f x - l) 0
                        = Real.sqrt (max (f x - l) 0 ^ 2) from
                      (Real.sqrt_sq (le_max_right _ _)).symm]
                    exact Real.sqrt_le_sqrt hx
                  have hE0 : (0:ℝ) ≤ essSup (fun x => max (f x - l) 0)
                      (volume.restrict (Metric.ball x₀ ρ₁)) := by
                    linarith only [hE4, hh00]
                  have hE2 : (essSup (fun x => max (f x - l) 0)
                        (volume.restrict (Metric.ball x₀ ρ₁))) ^ 2
                      ≤ essSup (fun x => max (f x - l) 0 ^ 2)
                        (volume.restrict (Metric.ball x₀ ρ₁)) := by
                    calc (essSup (fun x => max (f x - l) 0)
                          (volume.restrict (Metric.ball x₀ ρ₁))) ^ 2
                        ≤ (Real.sqrt (essSup (fun x => max (f x - l) 0 ^ 2)
                            (volume.restrict (Metric.ball x₀ ρ₁)))) ^ 2 :=
                          pow_le_pow_left₀ hE0 hES 2
                      _ = essSup (fun x => max (f x - l) 0 ^ 2)
                            (volume.restrict (Metric.ball x₀ ρ₁)) :=
                          Real.sq_sqrt hsq0
                  have hes16 : h0 ^ 2
                      ≤ 16 * essSup (fun x => max (f x - l) 0 ^ 2)
                        (volume.restrict (Metric.ball x₀ ρ₁)) := by
                    nlinarith only [hE4, hE2, hh00, hE0]
                  -- and the integral inequality
                  have hγs16 : 16 * C₁₂ ≤ γs := by
                    rw [hγsdef]; exact le_max_right _ _
                  have hvol0 : (0:ℝ)
                      ≤ (volume (Metric.ball x₀ ρ₁ ∩ {y | l < f y})).toReal :=
                    ENNReal.toReal_nonneg
                  have hd0 : (0:ℝ) < (ρ₁ - ρ₀) ^ 2 := by
                    have h1 : (0:ℝ) < ρ₁ - ρ₀ := by linarith only [hlt]
                    positivity
                  have hnum : C₁₂ * h0 ^ 2
                      ≤ γs * essSup (fun x => max (f x - l) 0 ^ 2)
                        (volume.restrict (Metric.ball x₀ ρ₁)) := by
                    nlinarith only [hes16, hγs16, hsq0, hC₁₂0]
                  refine le_trans (hfam l ρ₀ ρ₁ hl.1 hρ₀h hlt hρ₁S) ?_
                  refine mul_le_mul_of_nonneg_right ?_ hvol0
                  rw [div_mul_eq_mul_div, div_le_div_iff₀ hd0 hd0]
                  nlinarith only [hnum, hd0]
                have hLT := hLTb x₀ S (-h0) M f G hS0 hW
                  ⟨(2:ℝ) ^ (p / 2) * h0, hbdS⟩ hMdef hMbig hfamDG
                  (le_trans hmeas (mul_le_mul_of_nonneg_right hθ0sb hvolSnn))
                rw [h23S] at hLT
                filter_upwards [hLT] with x hx
                have h1 : (0:ℝ) ≤ 1 - lam02 := by linarith only [hlam02.2]
                have h2 : lam02 * (-h0) + (1 - lam02) * M
                    ≤ lam02 * (-h0) + (1 - lam02) * ((2:ℝ) ^ (p / 2) * h0) :=
                  by nlinarith only [h1, hMle]
                have h3 : lam02 * (-h0)
                    + (1 - lam02) * ((2:ℝ) ^ (p / 2) * h0) = -(h0 / 2) := by
                  rw [hlam02def, ← hPdef]
                  field_simp
                  ring
                linarith only [hx, h2, h3]
            filter_upwards [hconc] with x hx
            have hge : h0 / 4 ≤ |f x| := by
              rw [abs_of_nonpos (by linarith only [hx, hh00])]
              linarith only [hx, hh00]
            exact hfinal x (by rw [← habs x]; exact hge)
        -- (4.1): `v` is strictly increasing, with `v(±μ/2) = ±h₀`
        have hvstrict : StrictMono (fun t : ℝ => |t| ^ (p / 2 - 1) * t) := by
          have hpos : ∀ t : ℝ, 0 < t → |t| ^ (p / 2 - 1) * t = t ^ (p / 2) := by
            intro t ht
            rw [abs_of_pos ht, ← Real.rpow_add_one (ne_of_gt ht) (p / 2 - 1)]
            congr 1
            ring
          have hneg : ∀ t : ℝ, t < 0 →
              |t| ^ (p / 2 - 1) * t = -((-t) ^ (p / 2)) := by
            intro t ht
            have h1 : (0:ℝ) < -t := by linarith only [ht]
            rw [abs_of_neg ht,
              show ((-t) ^ (p / 2) : ℝ) = (-t) ^ (p / 2 - 1) * (-t) from by
                rw [← Real.rpow_add_one (ne_of_gt h1) (p / 2 - 1)]; congr 1; ring]
            ring
          have hz : |(0:ℝ)| ^ (p / 2 - 1) * (0:ℝ) = 0 := by ring
          intro s t hst
          show |s| ^ (p / 2 - 1) * s < |t| ^ (p / 2 - 1) * t
          rcases lt_trichotomy s 0 with hs | hs | hs
          · rcases lt_trichotomy t 0 with ht | ht | ht
            · rw [hneg s hs, hneg t ht]
              have h1 : (0:ℝ) < -t := by linarith only [ht]
              have h2 : -t < -s := by linarith only [hst]
              have := Real.rpow_lt_rpow h1.le h2 hp20
              linarith only [this]
            · rw [hneg s hs, ht, hz]
              have h1 : (0:ℝ) < -s := by linarith only [hs]
              have := Real.rpow_pos_of_pos h1 (p / 2)
              linarith only [this]
            · rw [hneg s hs, hpos t ht]
              have h1 : (0:ℝ) < -s := by linarith only [hs]
              have h2 := Real.rpow_pos_of_pos h1 (p / 2)
              have h3 := Real.rpow_pos_of_pos ht (p / 2)
              linarith only [h2, h3]
          · rw [hs, hz]
            have ht : 0 < t := by linarith only [hst, hs]
            rw [hpos t ht]
            exact Real.rpow_pos_of_pos ht (p / 2)
          · have ht : 0 < t := by linarith only [hst, hs]
            rw [hpos s hs, hpos t ht]
            exact Real.rpow_lt_rpow hs.le hst hp20
        have hvmu : |(μ / 2 : ℝ)| ^ (p / 2 - 1) * (μ / 2) = h0 := by
          have h1 : (0:ℝ) < μ / 2 := by linarith only [hμpos]
          rw [hh0def, abs_of_pos h1, ← Real.rpow_add_one (ne_of_gt h1) (p / 2 - 1)]
          congr 1
          ring
        have hvmun : |(-(μ / 2) : ℝ)| ^ (p / 2 - 1) * (-(μ / 2)) = -h0 := by
          have h1 : (0:ℝ) < μ / 2 := by linarith only [hμpos]
          rw [abs_neg, abs_of_pos h1, ← hvmu, abs_of_pos h1]
          ring
        have hvbdR : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
            |(|g x k| ^ (p / 2 - 1) * g x k)| ≤ (2:ℝ) ^ (p / 2) * h0 := by
          filter_upwards [hbd k] with x hx
          rw [hvabs (g x k), hh0def,
            ← Real.mul_rpow (by norm_num) (by linarith only [hμpos])]
          refine Real.rpow_le_rpow (abs_nonneg _) ?_ hp20.le
          linarith only [hx]
        -- the (3.12) halves, in the shape `hstep6b` consumes
        have hρeq : ∀ ρ₀ ρ₁ : ℝ, 0 < ρ₁ → ρ₀ < ρ₁ →
            ρ₁ - (ρ₁ - ρ₀) / ρ₁ * ρ₁ = ρ₀ ∧ (ρ₁ - ρ₀) / ρ₁ * ρ₁ = ρ₁ - ρ₀ := by
          intro ρ₀ ρ₁ h1 h2
          have h3 : (ρ₁ - ρ₀) / ρ₁ * ρ₁ = ρ₁ - ρ₀ := by
            field_simp
          exact ⟨by rw [h3]; ring, h3⟩
        rcases hk with halt | halt
        · -- the first alternative, run on `-v`
          have hWneg : MemW1pOn n 2 (Metric.ball x₀ S)
              (fun x => -(|g x k| ^ (p / 2 - 1) * g x k))
              (fun x => -((p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x)) := by
            have hsrc := (WeakGradientLinear n 2 hn1 (by norm_num)
              (Metric.ball x₀ S) (fun x => |g x k| ^ (p / 2 - 1) * g x k)
              (fun x => |g x k| ^ (p / 2 - 1) * g x k)
              (fun x => (p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x)
              (fun x => (p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x) (-1) 0 0
              Metric.isOpen_ball).2.1 (hv1 S hS0 hSR) (hv1 S hS0 hSR)
            have e1 : (fun x : EuclideanSpace ℝ (Fin n) =>
                  (-1 : ℝ) * (|g x k| ^ (p / 2 - 1) * g x k)
                    + (0 : ℝ) * (|g x k| ^ (p / 2 - 1) * g x k))
                = fun x : EuclideanSpace ℝ (Fin n) =>
                  -(|g x k| ^ (p / 2 - 1) * g x k) := by
              funext x; ring
            have e2 : (fun x : EuclideanSpace ℝ (Fin n) =>
                  (-1 : ℝ) • ((p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x)
                    + (0 : ℝ) • ((p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x))
                = fun x : EuclideanSpace ℝ (Fin n) =>
                  -((p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x) := by
              funext x
              rw [neg_smul, one_smul, zero_smul, add_zero]
            rw [e1, e2] at hsrc
            exact hsrc
          refine hstep6b _ _ hWneg (fun x => by rw [abs_neg]; exact hvabs (g x k))
            (by filter_upwards [hvbdR] with x hx; rwa [abs_neg]) ?_ ?_
          · intro l ρ₀ ρ₁ hl hρ₀ hlt hρ₁S
            have hρ₁0 : 0 < ρ₁ := by linarith only [hρ₀, hlt, hR]
            obtain ⟨e1, e2⟩ := hρeq ρ₀ ρ₁ hρ₁0 hlt
            have hσ0 : 0 < (ρ₁ - ρ₀) / ρ₁ := by
              apply div_pos (by linarith only [hlt]) hρ₁0
            have hσ1 : (ρ₁ - ρ₀) / ρ₁ < 1 := by
              rw [div_lt_one hρ₁0]
              linarith only [hρ₀, hR]
            have hmain := (hv2 ρ₁ ((ρ₁ - ρ₀) / ρ₁) (-l) hρ₁0
              (le_trans hρ₁S hSR.le) hσ0 hσ1).2 (by rw [← hh0def]; linarith only [hl])
            rw [e1, e2, ← hh0def] at hmain
            have hset : ∀ ρ : ℝ,
                Metric.ball x₀ ρ ∩ {y | l < -(|g y k| ^ (p / 2 - 1) * g y k)}
                  = Metric.ball x₀ ρ ∩ {y | |g y k| ^ (p / 2 - 1) * g y k < -l} := by
              intro ρ
              ext y
              constructor
              · rintro ⟨h1, h2⟩
                exact ⟨h1, by
                  have h3 : l < -(|g y k| ^ (p / 2 - 1) * g y k) := h2
                  show |g y k| ^ (p / 2 - 1) * g y k < -l
                  linarith only [h3]⟩
              · rintro ⟨h1, h2⟩
                exact ⟨h1, by
                  have h3 : |g y k| ^ (p / 2 - 1) * g y k < -l := h2
                  show l < -(|g y k| ^ (p / 2 - 1) * g y k)
                  linarith only [h3]⟩
            rw [hset ρ₀, hset ρ₁]
            refine le_trans (le_of_eq ?_) hmain
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            show ‖-((p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x)‖ ^ 2
                = ‖(p / 2 * |g x k| ^ (p / 2 - 1)) • Dg k x‖ ^ 2
            rw [norm_neg]
          · have hset : Metric.ball x₀ S
                  ∩ {y | -h0 < -(|g y k| ^ (p / 2 - 1) * g y k)}
                = Metric.ball x₀ S ∩ {y | g y k < μ / 2} := by
              ext y
              simp only [Set.inter_def, Set.mem_setOf_eq]
              constructor
              · rintro ⟨h1, h2⟩
                refine ⟨h1, ?_⟩
                have h3 : |g y k| ^ (p / 2 - 1) * g y k < h0 := by linarith only [h2]
                rw [← hvmu] at h3
                exact hvstrict.lt_iff_lt.1 h3
              · rintro ⟨h1, h2⟩
                refine ⟨h1, ?_⟩
                have h3 : |g y k| ^ (p / 2 - 1) * g y k
                    < |(μ / 2 : ℝ)| ^ (p / 2 - 1) * (μ / 2) := hvstrict h2
                rw [hvmu] at h3
                linarith only [h3]
            rw [hset, hswaplt k S (μ / 2) hSR.le, ← h1θ₂]
            refine hdisj61 S {y | μ / 2 < gh y k} {y | gh y k < μ / 2} hSR.le
              (measurableSet_lt measurable_const (hghk k))
              (measurableSet_lt (hghk k) measurable_const) ?_ ?_
            · refine Set.disjoint_left.2 fun x hx hx' => ?_
              have h1 : μ / 2 < gh x k := hx
              have h2 : gh x k < μ / 2 := hx'
              linarith only [h1, h2]
            · rw [← hswapgt k R (μ / 2) le_rfl]
              exact halt
        · -- the second alternative, run on `v`
          refine hstep6b _ _ (hv1 S hS0 hSR) (fun x => hvabs (g x k)) hvbdR ?_ ?_
          · intro l ρ₀ ρ₁ hl hρ₀ hlt hρ₁S
            have hρ₁0 : 0 < ρ₁ := by linarith only [hρ₀, hlt, hR]
            obtain ⟨e1, e2⟩ := hρeq ρ₀ ρ₁ hρ₁0 hlt
            have hσ0 : 0 < (ρ₁ - ρ₀) / ρ₁ := by
              apply div_pos (by linarith only [hlt]) hρ₁0
            have hσ1 : (ρ₁ - ρ₀) / ρ₁ < 1 := by
              rw [div_lt_one hρ₁0]
              linarith only [hρ₀, hR]
            have hmain := (hv2 ρ₁ ((ρ₁ - ρ₀) / ρ₁) l hρ₁0
              (le_trans hρ₁S hSR.le) hσ0 hσ1).1 (by rw [← hh0def]; linarith only [hl])
            rw [e1, e2, ← hh0def] at hmain
            exact hmain
          · have hset : Metric.ball x₀ S
                  ∩ {y | -h0 < |g y k| ^ (p / 2 - 1) * g y k}
                = Metric.ball x₀ S ∩ {y | -(μ / 2) < g y k} := by
              ext y
              simp only [Set.inter_def, Set.mem_setOf_eq]
              constructor
              · rintro ⟨h1, h2⟩
                refine ⟨h1, ?_⟩
                rw [← hvmun] at h2
                exact hvstrict.lt_iff_lt.1 h2
              · rintro ⟨h1, h2⟩
                refine ⟨h1, ?_⟩
                have h3 : |(-(μ / 2) : ℝ)| ^ (p / 2 - 1) * (-(μ / 2))
                    < |g y k| ^ (p / 2 - 1) * g y k := hvstrict h2
                rw [hvmun] at h3
                exact h3
            rw [hset, hswapgt k S (-(μ / 2)) hSR.le, ← h1θ₂]
            refine hdisj61 S {y | gh y k < -(μ / 2)} {y | -(μ / 2) < gh y k}
              hSR.le (measurableSet_lt (hghk k) measurable_const)
              (measurableSet_lt measurable_const (hghk k)) ?_ ?_
            · refine Set.disjoint_left.2 fun x hx hx' => ?_
              have h1 : gh x k < -(μ / 2) := hx
              have h2 : -(μ / 2) < gh x k := hx'
              linarith only [h1, h2]
            · rw [← hswaplt k R (-(μ / 2)) le_rfl]
              exact halt
    · -- STEP 7, part (b).  This is the ONLY remaining hole: the shared Steps
      -- 0(0b), 1, 2 and 3 are above, and Step 6 (part (a)) is now complete, so
      -- what is left of the `.tex` is Step 7 alone, l. 944-1036.  In scope,
      -- besides everything Step 6 used (`hDG k`, `hDGmono`, `hballvol`,
      -- `hswapgt`/`hswaplt`, `hdisj61`, `gh`/`hghk`/`hgaev`, `wt` and its
      -- bounds), the data with `hμpos`, `hNBR`, `hsubhalf`, `hno` -- the
      -- negation of (a)'s hypothesis AT EVERY INDEX -- and the index `k`.
      -- THE ROUTE, with the radii of Step 5 already named in the Lean:
      --   `t` (`htn : t ^ n = (1 + θ₂)/2`, `ht12 : 1/2 < t`, `ht1 : t < 1`),
      --   `S_b = (1+t)/2 * R`, `lam1 = 2t/(1+t)` so `lam1 * S_b = t * R`,
      --   `c₀ = 2θ₂/(1+θ₂)` with `hc₀0`/`hc₀1`, `lam1'' = 1/(2t)` so
      --   `lam1'' * (t*R) = R/2`, and `θ₁c = min θc (1/2)`.
      --   (7a) (3.21)/(3.22): `|B_{tR} ∩ {μ/2 < g^k}| ≤ |B_R ∩ {μ/2 < g^k}|
      --        < θ₂|B_R| = (θ₂/t^n)|B_{tR}| = c₀|B_{tR}|`, using `hballvol`
      --        for `|B_{tR}| = t^n |B_R|` and `htn` for `θ₂/t^n = c₀`.  Note
      --        this needs only MONOTONICITY in the radius, NOT `hdisj61`:
      --        `hno` already bounds the level set itself from above.  Push
      --        `hno` through `hswapgt`/`hswaplt` first, as Step 6 does.
      --   (7b) `hLSMI` at the centre `x₀`, radius `S_b`, level `μ/2`,
      --        `f = g^k`, `G = Dg k`, `M = essSup g^k (restrict B_{S_b})`.
      --        `MemW1pOn n 2 (B_{S_b})` comes from `hDg k` by clause (4) of
      --        `WeakGradientRestrict` exactly as `hWS` does at `S = 3R/4`.
      --        Its `(2.1)` family is wanted only at levels `l ∈ [μ/2, M]`
      --        with `M ≤ μ` and at the SINGLE pair `(lam1*S_b, S_b)`, which
      --        is why Step 2(ii)'s level-set pinch suffices: feed it
      --        `(hDG k l _ _ _ _ _).1 (Or.inr ⟨_, _⟩)` with `μ/2 ≤ l ≤ μ`.
      --        The `M ≤ μ/2` branch exits early, since `ν ≥ 3/4 ≥ 1/2`.
      --        Then (3.24') by `M ≤ μ`: `{κ₂ < g^k} ⊆ {λ₂μ/2 + (1-λ₂)M < g^k}`
      --        with `κ₂ = μ(1 - λ₂/2)`.
      --   (7c) `hLTc` (the instance at `lam₀ = 1/2`, `lam₁ = lam1''`) at the
      --        radius `t*R`, level `κ₂`, `f = g^k`, whose measure hypothesis
      --        is (3.24') and whose `θ₀` is `θc ≥ θ₁c`.  Its conclusion lands
      --        on `B_{lam1''*(t*R)} = B_{R/2}` and reads
      --        `g^k ≤ κ₂/2 + M/2 ≤ μ(1 - λ₂/4) = ν μ`.
      --   Then `-g^k` by the same four steps, from `hno`'s second half, with
      --        the negated pair of `WeakGradientLinear` as in Step 6's
      --        `hWSneg`; together they give `|g^k| ≤ ν μ`.
      -- Everything Step 6 needed that is radius-specific (`S`, `hvolS`,
      -- `h1θ₂`, `hLTapply`) was introduced INSIDE part (a)'s bullet, so it is
      -- not in scope here; the radius-independent facts above are.
      -- the radii of Step 5's second family: `S_b`, `λ₁S_b = tR`, `λ₁''·tR = R/2`
      obtain ⟨Sb, hSbdef⟩ : ∃ s : ℝ, s = (1 + t) / 2 * R := ⟨_, rfl⟩
      have hSb0 : 0 < Sb := by rw [hSbdef]; nlinarith only [ht0, hR]
      have hSbR : Sb < R := by rw [hSbdef]; nlinarith only [ht1, hR]
      have htR0 : 0 < t * R := mul_pos ht0 hR
      have htRSb : t * R < Sb := by rw [hSbdef]; nlinarith only [ht1, hR]
      have htRR : t * R < R := lt_trans htRSb hSbR
      have hlam1Sb : lam1 * Sb = t * R := by
        rw [hlam1def, hSbdef]
        have h1 : (1:ℝ) + t ≠ 0 := by positivity
        field_simp
      have hhalftR : R / 2 < t * R := by nlinarith only [ht12, hR]
      have hlam1''tR : lam1'' * (t * R) = R / 2 := by
        rw [hlam1''def]
        field_simp
      have hhalfsubtR : Metric.ball x₀ (R / 2) ⊆ Metric.ball x₀ (t * R) :=
        Metric.ball_subset_ball hhalftR.le
      have hhalfsubSb : Metric.ball x₀ (R / 2) ⊆ Metric.ball x₀ Sb :=
        Metric.ball_subset_ball (le_trans hhalftR.le htRSb.le)
      have htRsubR : Metric.ball x₀ (t * R) ⊆ Metric.ball x₀ R :=
        Metric.ball_subset_ball htRR.le
      -- `|B_{tR}| = t^n |B_R|` and `θ₂ = c₀ t^n`
      have hvoltR : (volume (Metric.ball x₀ (t * R))).toReal
          = t ^ n * (volume (Metric.ball x₀ R)).toReal := by
        rw [hballvol (t * R) htR0.le, hballvol R hR.le, mul_pow]
        ring
      have hc₀tn : θ₂ = c₀ * t ^ n := by
        rw [hc₀def, htn]
        have h1 : (1:ℝ) + θ₂ ≠ 0 := by positivity
        field_simp
      have hvoltR0 : (0:ℝ) ≤ (volume (Metric.ball x₀ (t * R))).toReal :=
        ENNReal.toReal_nonneg
      -- `W^{1,2}` on every smaller ball, by (0.3)
      have hWfam : ∀ T : ℝ, 0 < T → T < R →
          MemW1pOn n 2 (Metric.ball x₀ T) (fun x => g x k) (Dg k) := by
        intro T hT0 hTR
        exact (WeakGradientRestrict n 2 hn1 (by norm_num) (Metric.ball x₀ R)
          (Metric.ball x₀ T) (fun x => g x k) (Dg k) Metric.isOpen_ball
          Metric.isOpen_ball (Metric.ball_subset_ball hTR.le)).2.2.2 (hDg k)
          ((isCompact_closedBall x₀ T).of_isClosed_subset isClosed_closure
            Metric.closure_ball_subset_closedBall)
          (subset_trans Metric.closure_ball_subset_closedBall
            (Metric.closedBall_subset_ball hTR))
      have hWfamneg : ∀ T : ℝ, 0 < T → T < R →
          MemW1pOn n 2 (Metric.ball x₀ T) (fun x => -(g x k))
            (fun x => -(Dg k x)) := by
        intro T hT0 hTR
        have hsrc := (WeakGradientLinear n 2 hn1 (by norm_num) (Metric.ball x₀ T)
          (fun x => g x k) (fun x => g x k) (Dg k) (Dg k) (-1) 0 0
          Metric.isOpen_ball).2.1 (hWfam T hT0 hTR) (hWfam T hT0 hTR)
        have e1 : (fun x : EuclideanSpace ℝ (Fin n) =>
              (-1 : ℝ) * g x k + (0 : ℝ) * g x k)
            = fun x : EuclideanSpace ℝ (Fin n) => -(g x k) := by
          funext x; ring
        have e2 : (fun x : EuclideanSpace ℝ (Fin n) =>
              (-1 : ℝ) • Dg k x + (0 : ℝ) • Dg k x)
            = fun x : EuclideanSpace ℝ (Fin n) => -(Dg k x) := by
          funext x
          rw [neg_smul, one_smul, zero_smul, add_zero]
        rw [e1, e2] at hsrc
        exact hsrc
      have hν12 : (1:ℝ) / 2 ≤ ν := by rw [hνdef]; linarith only [hlam₂1]
      -- the sign-free core of Step 7
      have hstep7 : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ)
          (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          (∀ T : ℝ, 0 < T → T < R → MemW1pOn n 2 (Metric.ball x₀ T) f G) →
          (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), f x ≤ μ) →
          (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), -μ ≤ f x) →
          (∀ l ρ₀ ρ₁ : ℝ, μ / 2 ≤ l → l ≤ μ → 0 < ρ₀ → ρ₀ < ρ₁ → ρ₁ < R →
              DeGiorgiLevelBound n γs f G x₀ l ρ₀ ρ₁) →
          (volume (Metric.ball x₀ R ∩ {y | μ / 2 < f y})).toReal
            < θ₂ * (volume (Metric.ball x₀ R)).toReal →
          ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))), f x ≤ ν * μ := by
        intro f G hW hbdR hlowR hfam hsmall
        -- (7a) inequality (3.21)
        have h7a : (volume (Metric.ball x₀ (t * R) ∩ {y | μ / 2 < f y})).toReal
            ≤ c₀ * (volume (Metric.ball x₀ (t * R))).toReal := by
          have hfinR : volume (Metric.ball x₀ R) ≠ ⊤ := measure_ball_lt_top.ne
          have hmono : (volume (Metric.ball x₀ (t * R) ∩ {y | μ / 2 < f y})).toReal
              ≤ (volume (Metric.ball x₀ R ∩ {y | μ / 2 < f y})).toReal :=
            ENNReal.toReal_mono
              (ne_top_of_le_ne_top hfinR (measure_mono Set.inter_subset_left))
              (measure_mono (Set.inter_subset_inter_left _ htRsubR))
          have heq : θ₂ * (volume (Metric.ball x₀ R)).toReal
              = c₀ * (t ^ n * (volume (Metric.ball x₀ R)).toReal) := by
            rw [hc₀tn]; ring
          rw [hvoltR, ← heq]
          linarith only [hmono, hsmall]
        -- (7b) the measure improvement
        have hbdSb : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ Sb)), f x ≤ μ :=
          ae_restrict_of_ae_restrict_of_subset
            (Metric.ball_subset_ball hSbR.le) hbdR
        have hlowSb : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ Sb)), -μ ≤ f x :=
          ae_restrict_of_ae_restrict_of_subset
            (Metric.ball_subset_ball hSbR.le) hlowR
        have hnebSb : (ae (volume.restrict (Metric.ball x₀ Sb))).NeBot := by
          refine ae_neBot.2 ?_
          simp only [ne_eq, Measure.restrict_eq_zero]
          exact (Metric.isOpen_ball.measure_pos volume
            ⟨x₀, Metric.mem_ball_self hSb0⟩).ne'
        have hcobSb : Filter.IsCoboundedUnder (· ≤ ·)
            (ae (volume.restrict (Metric.ball x₀ Sb))) f :=
          Filter.isCoboundedUnder_le_of_eventually_le _ hlowSb
        have hbddSb : Filter.IsBoundedUnder (· ≤ ·)
            (ae (volume.restrict (Metric.ball x₀ Sb))) f := by
          refine ⟨μ, ?_⟩
          rw [Filter.eventually_map]
          exact hbdSb
        obtain ⟨M, hMdef⟩ : ∃ m : ℝ,
          m = essSup f (volume.restrict (Metric.ball x₀ Sb)) := ⟨_, rfl⟩
        have hMle : M ≤ μ := by
          rw [hMdef]; exact essSup_le_of_ae_le μ hbdSb hcobSb
        obtain ⟨κ₂, hκ₂def⟩ : ∃ s : ℝ, s = μ * (1 - lam₂ / 2) := ⟨_, rfl⟩
        have hκ₂half : μ / 2 ≤ κ₂ := by
          rw [hκ₂def]; nlinarith only [hlam₂1, hμpos]
        have hκ₂μ : κ₂ ≤ μ := by
          rw [hκ₂def]; nlinarith only [hlam₂0, hμpos]
        have h324 : (volume (Metric.ball x₀ (t * R) ∩ {y | κ₂ < f y})).toReal
            ≤ θ₁c * (volume (Metric.ball x₀ (t * R))).toReal := by
          rcases le_or_gt M (μ / 2) with hMsmall | hMbig
          · -- the superlevel set at `κ₂ ≥ μ/2 ≥ M` is null up to the essSup
            have h1 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ Sb)), f x ≤ κ₂ := by
              filter_upwards [ae_le_essSup hbddSb] with x hx
              rw [← hMdef] at hx
              linarith only [hx, hMsmall, hκ₂half]
            have h2 : volume (Metric.ball x₀ (t * R) ∩ {y | κ₂ < f y}) = 0 := by
              have h3 : ∀ᵐ x ∂volume, x ∈ Metric.ball x₀ Sb → f x ≤ κ₂ :=
                (ae_restrict_iff' measurableSet_ball).1 h1
              refine measure_mono_null ?_ (ae_iff.1 h3)
              intro x hx
              refine fun hc => ?_
              exact absurd (hc (Metric.ball_subset_ball htRSb.le hx.1))
                (not_le.2 hx.2)
            rw [h2]
            simp only [ENNReal.toReal_zero]
            exact mul_nonneg (le_of_lt hθ₁c.1) hvoltR0
          · have hfamSb : ∀ l : ℝ, l ∈ Set.Icc (μ / 2) M →
                DeGiorgiLevelBound n γs f G x₀ l (lam1 * Sb) Sb := by
              intro l hl
              rw [hlam1Sb]
              exact hfam l (t * R) Sb hl.1 (le_trans hl.2 hMle) htR0 htRSb hSbR
            have hmeasSb : (volume (Metric.ball x₀ (lam1 * Sb)
                  ∩ {y | μ / 2 < f y})).toReal
                ≤ c₀ * (volume (Metric.ball x₀ (lam1 * Sb))).toReal := by
              rw [hlam1Sb]; exact h7a
            have hLS := hLSMI x₀ Sb (μ / 2) M f G hSb0 (hW Sb hSb0 hSbR)
              ⟨μ, hbdSb⟩ hMdef hMbig hfamSb hmeasSb
            rw [hlam1Sb] at hLS
            refine le_trans (le_trans ?_ hLS) le_rfl
            refine ENNReal.toReal_mono
              (ne_top_of_le_ne_top measure_ball_lt_top.ne
                (measure_mono Set.inter_subset_left)) ?_
            refine measure_mono (Set.inter_subset_inter_right _ ?_)
            intro y hy
            have h1 : κ₂ < f y := hy
            have h2 : lam₂ * (μ / 2) + (1 - lam₂) * M ≤ κ₂ := by
              rw [hκ₂def]; nlinarith only [hMle, hlam₂0, hlam₂1, hμpos]
            show lam₂ * (μ / 2) + (1 - lam₂) * M < f y
            linarith only [h1, h2]
        -- (7c) the maximum principle on `B_{tR}`
        have hbdtR : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (t * R))), f x ≤ μ :=
          ae_restrict_of_ae_restrict_of_subset htRsubR hbdR
        have hlowtR : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (t * R))),
            -μ ≤ f x := ae_restrict_of_ae_restrict_of_subset htRsubR hlowR
        have hnebtR : (ae (volume.restrict (Metric.ball x₀ (t * R)))).NeBot := by
          refine ae_neBot.2 ?_
          simp only [ne_eq, Measure.restrict_eq_zero]
          exact (Metric.isOpen_ball.measure_pos volume
            ⟨x₀, Metric.mem_ball_self htR0⟩).ne'
        have hcobtR : Filter.IsCoboundedUnder (· ≤ ·)
            (ae (volume.restrict (Metric.ball x₀ (t * R)))) f :=
          Filter.isCoboundedUnder_le_of_eventually_le _ hlowtR
        have hbddtR : Filter.IsBoundedUnder (· ≤ ·)
            (ae (volume.restrict (Metric.ball x₀ (t * R)))) f := by
          refine ⟨μ, ?_⟩
          rw [Filter.eventually_map]
          exact hbdtR
        obtain ⟨M', hM'def⟩ : ∃ m : ℝ,
          m = essSup f (volume.restrict (Metric.ball x₀ (t * R))) := ⟨_, rfl⟩
        have hM'le : M' ≤ μ := by
          rw [hM'def]; exact essSup_le_of_ae_le μ hbdtR hcobtR
        rcases le_or_gt M' κ₂ with hM'small | hM'big
        · have h1 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (t * R))),
              f x ≤ κ₂ := by
            filter_upwards [ae_le_essSup hbddtR] with x hx
            rw [← hM'def] at hx
            linarith only [hx, hM'small]
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hhalfsubtR h1]
            with x hx
          have h2 : κ₂ ≤ ν * μ := by
            rw [hκ₂def, hνdef]; nlinarith only [hlam₂0, hμpos]
          linarith only [hx, h2]
        · have hfamtR : ∀ l ρ₀ ρ₁ : ℝ,
              l ∈ Set.Icc κ₂ (1 / 2 * κ₂ + (1 - 1 / 2) * M') →
              ρ₀ ∈ Set.Icc (lam1'' * (t * R)) (t * R) →
              ρ₁ ∈ Set.Icc (lam1'' * (t * R)) (t * R) → ρ₀ < ρ₁ →
              DeGiorgiLevelBound n γs f G x₀ l ρ₀ ρ₁ := by
            intro l ρ₀ ρ₁ hl hρ₀ hρ₁ hlt
            have hρ₀0 : 0 < ρ₀ := by
              have := hρ₀.1
              rw [hlam1''tR] at this
              linarith only [this, hR]
            have hρ₁R : ρ₁ < R := lt_of_le_of_lt hρ₁.2 htRR
            refine hfam l ρ₀ ρ₁ ?_ ?_ hρ₀0 hlt hρ₁R
            · linarith only [hl.1, hκ₂half]
            · have := hl.2
              linarith only [this, hM'le, hκ₂μ]
          have hmeastR : (volume (Metric.ball x₀ (t * R) ∩ {y | κ₂ < f y})).toReal
              ≤ θc * (volume (Metric.ball x₀ (t * R))).toReal := by
            refine le_trans h324 (mul_le_mul_of_nonneg_right ?_ hvoltR0)
            rw [hθ₁cdef]
            exact min_le_left _ _
          have hLT := hLTc x₀ (t * R) κ₂ M' f G htR0 (hW (t * R) htR0 htRR)
            ⟨μ, hbdtR⟩ hM'def hM'big hfamtR hmeastR
          rw [hlam1''tR] at hLT
          filter_upwards [hLT] with x hx
          have h2 : 1 / 2 * κ₂ + (1 - 1 / 2) * M' ≤ ν * μ := by
            rw [hκ₂def, hνdef]
            nlinarith only [hM'le, hlam₂0, hμpos]
          linarith only [hx, h2]
      -- the hypothesis of (b) at this index
      have hnok := hno
      push_neg at hnok
      obtain ⟨hA, hB⟩ := hnok k
      have hpos := hstep7 (fun x => g x k) (Dg k) hWfam
        (by
          filter_upwards [hbd k] with x hx
          exact le_trans (le_abs_self _) hx)
        (by
          filter_upwards [hbd k] with x hx
          have h1 := neg_abs_le (g x k)
          linarith only [hx, h1])
        (fun l ρ₀ ρ₁ h1 h2 h3 h4 h5 =>
          (hDG k l ρ₀ ρ₁ h3 h4 h5).1 (Or.inr ⟨h1, h2⟩))
        hA
      have hsetneg : {y : EuclideanSpace ℝ (Fin n) | μ / 2 < -(g y k)}
          = {y | g y k < -(μ / 2)} := by
        ext y
        constructor
        · intro hy
          have h1 : μ / 2 < -(g y k) := hy
          show g y k < -(μ / 2)
          linarith only [h1]
        · intro hy
          have h1 : g y k < -(μ / 2) := hy
          show μ / 2 < -(g y k)
          linarith only [h1]
      have hneg := hstep7 (fun x => -(g x k)) (fun x => -(Dg k x)) hWfamneg
        (by
          filter_upwards [hbd k] with x hx
          have h1 := neg_abs_le (g x k)
          linarith only [hx, h1])
        (by
          filter_upwards [hbd k] with x hx
          have h1 := le_abs_self (g x k)
          linarith only [hx, h1])
        (fun l ρ₀ ρ₁ h1 h2 h3 h4 h5 => by
          have h := (hDG k (-l) ρ₀ ρ₁ h3 h4 h5).2
            (Or.inr ⟨by linarith only [h2], by linarith only [h1]⟩)
          rwa [neg_neg] at h)
        (by rw [hsetneg]; exact hB)
      filter_upwards [hpos, hneg] with x h1 h2
      exact abs_le.2 ⟨by linarith only [h2], h1⟩
