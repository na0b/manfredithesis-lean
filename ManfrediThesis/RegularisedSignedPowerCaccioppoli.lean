import ManfrediThesis.Preamble
import ManfrediThesis.RegularisedSignedPowerCaccioppoliCore
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.DifferentiatedEquationWeak
import ManfrediThesis.WeakGradientPositivePart
import ManfrediThesis.WeakGradientSmoothMul
import ManfrediThesis.WeakGradientLinear
set_option maxHeartbeats 800000
open MeasureTheory

/-- Inequality (D.5): the Caccioppoli estimate for the **regularised** signed
power at the level `η`, on the superlevel and sublevel sets of
`ψ_η = π_η(g^k)`, for an arbitrary level `ℓ` and an arbitrary cut-off `ζ`
compactly supported in `B_R(x₀)`.

In the subquadratic regime `1 < p < 2` the map `s ↦ |s|^{p/2-1}s` is not `C¹`
at `0`, so the thesis runs an `η`-regularisation: `π_η(s) = (|s|+η)^{p-2}s`
with derivative `π'_η`, which here is the function `Dpi`.  Only the clauses of
(D.1) that the argument actually consumes appear as hypotheses: the positivity
`0 < |s|+η`, the lower bound `π'_η(s) ≥ (p-1)(|s|+η)^{p-2}`, the uniform bound
`|π'_η(s)| ≤ η^{p-2}`, continuity of `π'_η`, `π_η ∈ C¹`, and the Sobolev
regularity of `ψ_η` on every smaller ball, `ψ_η ∈ W^{1,2}(B_T)` with weak
gradient `π'_η(g^k) · Dg^k` for `0 < T < R`.  Nothing else about the pair
`(π_η, π'_η)` is used, so the lemma is stated for a pair with those properties;
`SignedPowerGradientEstimateSubquadratic` instantiates it at the thesis' own
`π_η`.

Stating it once, for an arbitrary cut-off and an arbitrary level, is what lets
both of the parent's conclusions consume it -- (D5) for conclusion (1) and (D6)
for inequality (3.17) -- and it also removes the need for any
reparametrisation: the `.tex` states (D.5) for `ζ_{ρ-σρ,ρ}` and uses it in (D5)
at `ζ_{T,T'}`, and an arbitrary `ζ` covers both.

The proof follows `CaccioppoliLevelWeight`'s proof of (3.4) step for step --
the same `M`, `W`, `hposloc`, `key (T, sg, v, Z)` skeleton -- with three
changes, each noted at the point where it is made:

* the truncation is of `ψ_η = π_η(g^k)`, not of `g^k`, so the weak gradient of
  the test function carries the extra factor `π'_η(g^k)`, and `key` takes
  `Z = (sg * π'_η(g^k)) • Dg^k` on `T` rather than `Z = sg • Dg^k`.  The lower
  bound of Step 7 then uses the lower half of (D.1),
  `π'_η ≥ (p-1)(|g^k|+η)^{p-2}`, next to `Q1`.
* (A.2'), the converse localisation, is cheaper here than in the `.tex`
  because `Ω` is a ball, so `hradius` produces the intermediate `T` directly
  and no `exists_compact_between` is needed.  `WeakGradientZeroExtend` is NOT
  used.
* the Cauchy-Schwarz pairing of (D4) splits the weight differently:
  `F = sqrt(w^{p/2-1}(|g^k|+η)^{p-2})|ζ|‖Dg^k‖` against
  `G = (ψ_η-ℓ)^±|∇ζ|`, leaving NO weight on the right-hand side.  The bridge is
  `hWroot`, `w^{p/2-1} ≤ 2^{1-p/2} sqrt(w^{p/2-1}b^{p-2})`, which is (D4)'s
  `|g^k|+η ≤ 2 sqrt(w)` and is the ONLY place where the hypothesis `η² < ε` is
  used.

The first conjunct of the conclusion is the finiteness that (D4) establishes in
its own words, in order to divide by the left Cauchy-Schwarz factor; it is
`hXΩ2` rescaled by `p²/4`. -/
theorem RegularisedSignedPowerCaccioppoli :
    ∀ (n : ℕ) (p r : ℝ), 2 ≤ n → 1 < p → p < 2 → 0 < r →
      ∀ C₁ C₂ : ℝ,
        C₁ = 2 / p * (2:ℝ) ^ (1 - p / 2) →
        C₂ = (2 * (n:ℝ) * r * C₁ * p ^ 2 / (4 * (p - 1))) ^ 2 →
      ∀ Dpi pie : ℝ → ℝ → ℝ,
        (∀ (η : ℝ), 0 < η → ∀ s : ℝ, 0 < |s| + η) →
        (∀ (η : ℝ), 0 < η → ∀ s : ℝ,
          (p - 1) * (|s| + η) ^ (p - 2) ≤ Dpi η s) →
        (∀ (η : ℝ), 0 < η → ∀ s : ℝ, |Dpi η s| ≤ η ^ (p - 2)) →
        (∀ (η : ℝ), 0 < η → Continuous (Dpi η)) →
        (∀ (η : ℝ), 0 < η → ContDiff ℝ 1 (pie η)) →
      ∀ (ε γ₀ γ₁ : ℝ)
        (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ) (k : Fin n),
        0 < ε → 0 < γ₀ → γ₁ ≤ r * γ₀ → γ₀ ≤ γ₁ → 0 < R →
        EllipticStructureQ12 n p ε γ₀ γ₁ (Metric.ball x₀ R) (fun _ _ h => A h) →
        CitedRegularityEpsPos n p ε γ₀ γ₁ (Metric.ball x₀ R) A →
        IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h)
          (fun _ _ _ => 0) u g →
        (∀ i : Fin n, MemW1pLocOn n 2 (Metric.ball x₀ R) (fun x => g x i) (Dg i)) →
        (∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
            (f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ)
            (G₁ G₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
            MemW1pOn n 2 Ω f₁ G₁ →
            (∀ᵐ x ∂(volume.restrict Ω), f₁ x = f₂ x) →
            (∀ᵐ x ∂(volume.restrict Ω), G₁ x = G₂ x) →
            MemW1pOn n 2 Ω f₂ G₂) →
        (∀ (η : ℝ), 0 < η → ∀ T : ℝ, 0 < T → T < R →
            MemW1pOn n 2 (Metric.ball x₀ T) (fun x => pie η (g x k))
              (fun x => Dpi η (g x k) • Dg k x)) →
      ∀ (η : ℝ), 0 < η → η ^ 2 < ε →
        ∀ (ℓ : ℝ) (ζ : EuclideanSpace ℝ (Fin n) → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
          tsupport ζ ⊆ Metric.ball x₀ R →
          IntegrableOn (fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
                * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
              (Metric.ball x₀ R) volume
            ∧ ((∫ x in Metric.ball x₀ R ∩ {y | ℓ < pie η (g y k)},
                  (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
                    * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
                ≤ C₂ * (∫ x in Metric.ball x₀ R,
                    max (pie η (g x k) - ℓ) 0 ^ 2
                      * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)))
            ∧ ((∫ x in Metric.ball x₀ R ∩ {y | pie η (g y k) < ℓ},
                  (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
                    * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
                ≤ C₂ * (∫ x in Metric.ball x₀ R,
                    max (ℓ - pie η (g x k)) 0 ^ 2
                      * (∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2))) := by
  intro n p r hn hp hp2 hr C₁ C₂ hC₁def hC₂def Dpi pie hbase hDpilow hDpibd
    hDpicont hpieC1 ε γ₀ γ₁ A u g Dg x₀ R k hε hγ₀ hγ₁ hγ01 hR hQ hC1 hsol hDg
    htransport hpsiW
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR0 : (0:ℝ) < (n:ℝ) := by
    have : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hp0 : (0:ℝ) < p := by linarith
  have hp10 : (0:ℝ) < p - 1 := by linarith
  have hp2n : p - 2 < 0 := by linarith
  have hwlow : ∀ x : EuclideanSpace ℝ (Fin n), ε ≤ ε + ‖g x‖ ^ 2 := by
    intro x
    have := sq_nonneg ‖g x‖
    linarith
  intro η hη hηε ℓ ζ hζsm hζcs hζΩ
  -- This is (D3)+(D4).  It follows `CaccioppoliLevelWeight`'s proof of (3.4)
  -- step for step; the two differences are that the test function truncates
  -- `ψ_η = π_η(g^k)` rather than `g^k`, so the weak gradient of the
  -- truncation carries the extra factor `π'_η(g^k)`, and that the
  -- Cauchy-Schwarz pairing of (D4) splits the weight differently, leaving
  -- no weight at all on the right-hand side.
  have hΩ : IsOpen (Metric.ball x₀ R) := Metric.isOpen_ball
  have hγ₁p : (0:ℝ) < γ₁ := lt_of_lt_of_le hγ₀ hγ01
  -- a radius `T < R` whose ball contains a given compact subset of `B_R`
  have hradius : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      K ⊆ Metric.ball x₀ R → ∃ T : ℝ, 0 < T ∧ T < R ∧ K ⊆ Metric.ball x₀ T := by
    intro K hK hKR
    rcases Set.eq_empty_or_nonempty K with he | hne
    · exact ⟨R / 2, by linarith only [hR], by linarith only [hR],
        by rw [he]; exact Set.empty_subset _⟩
    · obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn
        (f := fun z : EuclideanSpace ℝ (Fin n) => dist z x₀) hne
        (Continuous.continuousOn (continuous_id.dist continuous_const))
      have hyR : dist y x₀ < R := Metric.mem_ball.1 (hKR hy)
      have hy0 : (0:ℝ) ≤ dist y x₀ := dist_nonneg
      refine ⟨(dist y x₀ + R) / 2, by linarith only [hy0, hR],
        by linarith only [hyR], fun z hz => ?_⟩
      have hzy : dist z x₀ ≤ dist y x₀ := hmax hz
      exact Metric.mem_ball.2 (by linarith only [hzy, hyR])
  -- transfer of an integral from an intermediate ball to `B_R`
  have htrans : ∀ (V B : Set (EuclideanSpace ℝ (Fin n)))
      (F : EuclideanSpace ℝ (Fin n) → ℝ),
      MeasurableSet V → V ⊆ Metric.ball x₀ R → B ⊆ V →
      (∀ x, x ∉ B → F x = 0) →
      (∫ x in V, F x) = ∫ x in Metric.ball x₀ R, F x := by
    intro V B F hVm hVΩ hBV hF
    rw [← integral_indicator hVm, ← integral_indicator hΩ.measurableSet]
    congr 1
    funext x
    by_cases hxV : x ∈ V
    · rw [Set.indicator_of_mem hxV, Set.indicator_of_mem (hVΩ hxV)]
    · rw [Set.indicator_of_notMem hxV]
      by_cases hxΩ : x ∈ Metric.ball x₀ R
      · rw [Set.indicator_of_mem hxΩ, hF x (fun hc => hxV (hBV hc))]
      · rw [Set.indicator_of_notMem hxΩ]
  -- (A.2'): `W^{1,2}` of every smaller ball gives `W^{1,2}_loc` of `B_R`
  have hliftloc : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      (∀ T : ℝ, 0 < T → T < R → MemW1pOn n 2 (Metric.ball x₀ T) f G) →
      MemW1pLocOn n 2 (Metric.ball x₀ R) f G := by
    intro f G hf
    constructor
    · intro θ hθsm hθcs hθΩ i
      obtain ⟨T, hT0, hTR, hTsub⟩ := hradius (tsupport θ) hθcs hθΩ
      have hid := (hf T hT0 hTR).1 θ hθsm hθcs hTsub i
      have e1 : (∫ x in Metric.ball x₀ T,
            f x * fderiv ℝ θ x (EuclideanSpace.single i (1:ℝ)))
          = ∫ x in Metric.ball x₀ R,
            f x * fderiv ℝ θ x (EuclideanSpace.single i (1:ℝ)) := by
        refine htrans _ (tsupport θ) _ measurableSet_ball
          (Metric.ball_subset_ball hTR.le) hTsub (fun x hx => ?_)
        rw [fderiv_of_notMem_tsupport ℝ hx]
        simp
      have e2 : (∫ x in Metric.ball x₀ T, G x i * θ x)
          = ∫ x in Metric.ball x₀ R, G x i * θ x := by
        refine htrans _ (tsupport θ) _ measurableSet_ball
          (Metric.ball_subset_ball hTR.le) hTsub (fun x hx => ?_)
        rw [image_eq_zero_of_notMem_tsupport hx]
        ring
      rw [← e1, ← e2]
      exact hid
    · intro K hK hKΩ
      obtain ⟨T, hT0, hTR, hTsub⟩ := hradius K hK hKΩ
      exact ⟨(hf T hT0 hTR).2.1.mono_measure (Measure.restrict_mono hTsub le_rfl),
        (hf T hT0 hTR).2.2.mono_measure (Measure.restrict_mono hTsub le_rfl)⟩
  -- the two truncated test pairs, on all of `B_R`
  have hplusloc : MemW1pLocOn n 2 (Metric.ball x₀ R)
      (fun x => max (pie η (g x k) - ℓ) 0)
      (fun x => if ℓ < pie η (g x k) then Dpi η (g x k) • Dg k x else 0) :=
    hliftloc _ _ (fun T h1 h2 =>
      WeakGradientPositivePart n 2 ℓ hn1 (by norm_num) (Metric.ball x₀ T) _ _
        Metric.isOpen_ball measure_ball_lt_top.ne (hpsiW η hη T h1 h2))
  have hminusloc : MemW1pLocOn n 2 (Metric.ball x₀ R)
      (fun x => max (ℓ - pie η (g x k)) 0)
      (fun x => if pie η (g x k) < ℓ then -(Dpi η (g x k) • Dg k x) else 0) := by
    refine hliftloc _ _ (fun T h1 h2 => ?_)
    have hneg : MemW1pOn n 2 (Metric.ball x₀ T) (fun x => -(pie η (g x k)))
        (fun x => -(Dpi η (g x k) • Dg k x)) := by
      have hsrc := (WeakGradientLinear n 2 hn1 (by norm_num) (Metric.ball x₀ T)
        (fun x => pie η (g x k)) (fun x => pie η (g x k))
        (fun x => Dpi η (g x k) • Dg k x) (fun x => Dpi η (g x k) • Dg k x)
        (-1) 0 0 Metric.isOpen_ball).2.1 (hpsiW η hη T h1 h2) (hpsiW η hη T h1 h2)
      refine htransport _ _ _ _ _ hsrc
        (Filter.Eventually.of_forall fun x => by ring)
        (Filter.Eventually.of_forall fun x => ?_)
      show (-1:ℝ) • (Dpi η (g x k) • Dg k x) + (0:ℝ) • (Dpi η (g x k) • Dg k x)
          = -(Dpi η (g x k) • Dg k x)
      rw [neg_smul, one_smul, zero_smul, add_zero]
    have hsrc := WeakGradientPositivePart n 2 (-ℓ) hn1 (by norm_num)
      (Metric.ball x₀ T) _ _ Metric.isOpen_ball measure_ball_lt_top.ne hneg
    refine htransport _ _ _ _ _ hsrc
      (Filter.Eventually.of_forall fun x => by ring_nf)
      (Filter.Eventually.of_forall fun x => ?_)
    show (if (-ℓ:ℝ) < -(pie η (g x k)) then -(Dpi η (g x k) • Dg k x) else 0)
        = if pie η (g x k) < ℓ then -(Dpi η (g x k) • Dg k x) else 0
    by_cases hx : pie η (g x k) < ℓ
    · rw [if_pos (by linarith only [hx] : (-ℓ:ℝ) < -(pie η (g x k))), if_pos hx]
    · rw [if_neg (not_lt.2 (by have := not_lt.1 hx; linarith only [this])),
        if_neg hx]
  -- the weight, written as in `CaccioppoliLevelWeight`
  obtain ⟨W, hWdef⟩ : ∃ W : EuclideanSpace ℝ (Fin n) → ℝ,
      W = fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) := ⟨_, rfl⟩
  have hWeq : ∀ x, W x = (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) := fun x => by rw [hWdef]
  have hwp : ∀ x : EuclideanSpace ℝ (Fin n), 0 < ε + ‖g x‖ ^ 2 :=
    fun x => lt_of_lt_of_le hε (hwlow x)
  have hWpos : ∀ x, 0 < W x := fun x => by
    rw [hWeq x]; exact Real.rpow_pos_of_pos (hwp x) _
  -- the continuous representative supplied by (C1)
  obtain ⟨-, g', hg'cont, hg'ae, -⟩ := hC1 hε hQ u g hsol
  have hw'pos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < ε + ‖g' x‖ ^ 2 :=
    fun x => by have := sq_nonneg ‖g' x‖; linarith only [hε, this]
  have hw'cont : ContinuousOn (fun x => ε + ‖g' x‖ ^ 2) (Metric.ball x₀ R) :=
    continuousOn_const.add (hg'cont.norm.pow 2)
  have hWae : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      W x = (ε + ‖g' x‖ ^ 2) ^ (p / 2 - 1) := by
    filter_upwards [hg'ae] with x hx
    rw [hWeq x, hx]
  have hwpowbd : ∀ (s : ℝ) (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K →
      K ⊆ Metric.ball x₀ R → ∃ L : ℝ, 0 ≤ L ∧
        ∀ x ∈ K, (ε + ‖g' x‖ ^ 2) ^ s ≤ L := by
    intro s K hK hKΩ
    have hc : ContinuousOn (fun x => (ε + ‖g' x‖ ^ 2) ^ s) K := by
      refine ContinuousOn.rpow_const (hw'cont.mono hKΩ) ?_
      intro x hx
      exact Or.inl (ne_of_gt (hw'pos x))
    obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn hc
    refine ⟨max L 0, le_max_right _ _, fun x hx => ?_⟩
    refine le_trans ?_ (le_max_left L 0)
    exact le_trans (le_abs_self _) (by simpa using hL x hx)
  -- `A` is `C¹`, because `ε > 0`
  have hAcd : ContDiff ℝ 1 (fun h : EuclideanSpace ℝ (Fin n) => A h) := by
    have h1 := hQ.hdiff x₀ (Metric.mem_ball_self hR) 0
    have h2 : {h : EuclideanSpace ℝ (Fin n) | ε + ‖h‖ ^ 2 ≠ 0} = Set.univ := by
      ext h
      constructor
      · intro _; trivial
      · intro _
        have h3 : (0:ℝ) ≤ ‖h‖ ^ 2 := sq_nonneg _
        exact ne_of_gt (by linarith only [hε, h3])
    rw [h2] at h1
    exact contDiffOn_univ.1 h1
  -- the coefficient field of (3.2)
  obtain ⟨M, hMdef⟩ : ∃ M : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ,
      M = fun x i j =>
        (fderiv ℝ A (g x) (EuclideanSpace.single j (1:ℝ))) i := ⟨_, rfl⟩
  have hMeq : ∀ x i j, M x i j
      = (fderiv ℝ A (g x) (EuclideanSpace.single j (1:ℝ))) i :=
    fun x i j => by rw [hMdef]
  have hdecomp : ∀ ξ : EuclideanSpace ℝ (Fin n),
      ξ = ∑ j, ξ j • EuclideanSpace.single j (1:ℝ) := by
    intro ξ
    refine PiLp.ext fun i => ?_
    simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq]
  have hlin : ∀ (x ξ : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      (fderiv ℝ A (g x) ξ) i = ∑ j, M x i j * ξ j := by
    intro x ξ i
    conv_lhs => rw [hdecomp ξ]
    rw [map_sum]
    simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
      Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [hMeq x i j]; ring
  have hQ1b : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      ∀ ξ : EuclideanSpace ℝ (Fin n),
        γ₀ * W x * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, M x i j * ξ j * ξ i := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet,
      ae_restrict_of_ae hQ.Q1] with x hxΩ hxQ1
    intro ξ
    have h1 := hxQ1 hxΩ 0 (g x) ξ (ne_of_gt (hwp x))
    rw [← hWeq x] at h1
    refine le_trans h1 (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => by rw [hlin x ξ i, Finset.sum_mul]
  have hQ2b : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), ∀ i j : Fin n,
      |M x i j| ≤ γ₁ * W x := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet,
      ae_restrict_of_ae hQ.Q2] with x hxΩ hxQ2
    intro i j
    have h1 := hxQ2 hxΩ 0 (g x) i j (ne_of_gt (hwp x))
    rw [← hMeq x i j, ← hWeq x] at h1
    exact h1
  -- the cut-off's support and the bounds on it
  have hKcpt : IsCompact (tsupport ζ) := hζcs
  have hKmeas : MeasurableSet (tsupport ζ) := hKcpt.measurableSet
  have hζ0 : ∀ x, x ∉ tsupport ζ → ζ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport hx
  have hDζ0 : ∀ x, x ∉ tsupport ζ → ∀ i : Fin n,
      fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ)) = 0 := by
    intro x hx i
    rw [fderiv_of_notMem_tsupport ℝ hx]
    simp
  have hextend : ∀ F : EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ x, x ∉ tsupport ζ → F x = 0) →
      IntegrableOn F (tsupport ζ) volume →
      IntegrableOn F (Metric.ball x₀ R) volume := by
    intro F hF0 hFK
    have hsplit : Metric.ball x₀ R
        = tsupport ζ ∪ (Metric.ball x₀ R \ tsupport ζ) := by
      rw [Set.union_sdiff_cancel hζΩ]
    rw [hsplit]
    refine IntegrableOn.union hFK ?_
    exact IntegrableOn.congr_fun integrableOn_zero (fun x hx => (hF0 x hx.2).symm)
      (hΩ.measurableSet.diff hKmeas)
  have hgK : AEStronglyMeasurable g (volume.restrict (tsupport ζ)) :=
    (hsol.1.2 (tsupport ζ) hKcpt hζΩ).2.1
  have hWm : AEMeasurable W (volume.restrict (tsupport ζ)) := by
    have heq : ∀ x, W x
        = Real.exp (Real.log (ε + ‖g x‖ ^ 2) * (p / 2 - 1)) := by
      intro x
      rw [hWeq x]
      exact Real.rpow_def_of_pos (hwp x) _
    have h0 : AEMeasurable (fun x => ε + ‖g x‖ ^ 2)
        (volume.restrict (tsupport ζ)) :=
      (hgK.aemeasurable.norm.pow_const 2).const_add ε
    have h1 : AEMeasurable
        (fun x => Real.exp (Real.log (ε + ‖g x‖ ^ 2) * (p / 2 - 1)))
        (volume.restrict (tsupport ζ)) := (h0.log.mul_const _).exp
    exact h1.congr (Filter.Eventually.of_forall fun x => (heq x).symm)
  have hMm : ∀ i j : Fin n, AEMeasurable (fun x => M x i j)
      (volume.restrict (tsupport ζ)) := by
    intro i j
    have hc : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ (fun h : EuclideanSpace ℝ (Fin n) => A h) y
          (EuclideanSpace.single j (1:ℝ))) i) := by
      have h1 : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
          fderiv ℝ (fun h : EuclideanSpace ℝ (Fin n) => A h) y) :=
        hAcd.continuous_fderiv (by norm_num)
      exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
        (h1.clm_apply continuous_const)
    have h2 : AEStronglyMeasurable
        (fun x => (fderiv ℝ (fun h : EuclideanSpace ℝ (Fin n) => A h) (g x)
          (EuclideanSpace.single j (1:ℝ))) i) (volume.restrict (tsupport ζ)) :=
      hc.comp_aestronglyMeasurable hgK
    exact h2.aemeasurable.congr
      (Filter.Eventually.of_forall fun x => (hMeq x i j).symm)
  have hDgcm : ∀ j : Fin n, AEMeasurable (fun x => Dg k x j)
      (volume.restrict (tsupport ζ)) := by
    intro j
    have h1 := ((hDg k).2 (tsupport ζ) hKcpt hζΩ).2.1.aemeasurable
    exact ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable).comp_aemeasurable h1
  have hζm : AEMeasurable ζ (volume.restrict (tsupport ζ)) :=
    hζsm.continuous.measurable.aemeasurable
  have hDζm : ∀ i : Fin n, AEMeasurable
      (fun x => fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ)))
      (volume.restrict (tsupport ζ)) := fun i =>
    (((hζsm.continuous_fderiv (by simp)).clm_apply
      continuous_const).measurable).aemeasurable
  have haemul : ∀ f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ,
      AEMeasurable f₁ (volume.restrict (tsupport ζ)) →
      AEMeasurable f₂ (volume.restrict (tsupport ζ)) →
      AEMeasurable (fun x => f₁ x * f₂ x) (volume.restrict (tsupport ζ)) := by
    intro f₁ f₂ h1 h2
    exact (h1.mul h2).congr (Filter.Eventually.of_forall fun x => by simp)
  have haesum : ∀ f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ i, AEMeasurable (f i) (volume.restrict (tsupport ζ))) →
      AEMeasurable (fun x => ∑ i, f i x) (volume.restrict (tsupport ζ)) := by
    intro f hf
    have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin n))
      (fun i (_ : i ∈ Finset.univ) => hf i)
    exact h.congr (Filter.Eventually.of_forall fun x => by simp)
  have hMint : IntegrableOn (fun x => ‖Dg k x‖ ^ 2) (tsupport ζ) volume := by
    have hmem := ((hDg k).2 (tsupport ζ) hKcpt hζΩ).2
    have h1 : Integrable (fun x => ‖Dg k x‖ ^ (ENNReal.ofReal 2).toReal)
        (volume.restrict (tsupport ζ)) :=
      hmem.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
    rw [show (ENNReal.ofReal 2).toReal = 2 from by simp] at h1
    refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
    show ‖Dg k x‖ ^ (2:ℝ) = ‖Dg k x‖ ^ 2
    rw [← Real.rpow_natCast ‖Dg k x‖ 2]
    norm_num
  obtain ⟨Lζ, hLζ0, hLζ⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ x, ζ x ^ 2 ≤ L := by
    obtain ⟨L, hL⟩ := hζcs.exists_bound_of_continuousOn hζsm.continuous.continuousOn
    refine ⟨max L 0 ^ 2, by positivity, fun x => ?_⟩
    by_cases hx : x ∈ tsupport ζ
    · have h1 : |ζ x| ≤ max L 0 := le_trans (by simpa using hL x hx) (le_max_left _ _)
      calc ζ x ^ 2 = |ζ x| ^ 2 := (sq_abs _).symm
        _ ≤ max L 0 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    · rw [hζ0 x hx]
      have h0 : (0:ℝ) ^ 2 = 0 := by norm_num
      rw [h0]
      positivity
  obtain ⟨LDζ, hLDζ0, hLDζ⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ x,
      ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 ≤ L := by
    have hcont : Continuous (fun x => ∑ i, (fderiv ℝ ζ x
        (EuclideanSpace.single i (1:ℝ))) ^ 2) := by
      refine continuous_finsetSum _ fun i _ => ?_
      exact ((hζsm.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2
    obtain ⟨L, hL⟩ := hζcs.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max L 0, le_max_right _ _, fun x => ?_⟩
    by_cases hx : x ∈ tsupport ζ
    · exact le_trans (le_trans (le_abs_self _) (by simpa using hL x hx))
        (le_max_left _ _)
    · have hz : ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hDζ0 x hx i]; ring
      rw [hz]
      exact le_max_right _ _
  obtain ⟨LW, hLW0, hLW'⟩ := hwpowbd (p / 2 - 1) (tsupport ζ) hζcs hζΩ
  have hLW : ∀ᵐ x ∂(volume.restrict (tsupport ζ)), W x ≤ LW := by
    filter_upwards [ae_restrict_mem hKmeas,
      ae_restrict_of_ae_restrict_of_subset hζΩ hWae] with x hxK hxW
    rw [hxW]
    exact hLW' x hxK
  have hsumbd : ∀ (f : Fin n → ℝ) (Mb : ℝ), (∀ i, |f i| ≤ Mb) →
      |∑ i, f i| ≤ (n:ℝ) * Mb := by
    intro f Mb hM
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ i, |f i| ≤ ∑ _i : Fin n, Mb := Finset.sum_le_sum fun i _ => hM i
      _ = (n:ℝ) * Mb := by simp [mul_comm]
  have habs2 : ∀ a b : ℝ, |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    intro a b
    have h1 : (0:ℝ) ≤ (|a| - |b|) ^ 2 := sq_nonneg _
    have h2 : (|a| - |b|) ^ 2 = a ^ 2 - 2 * (|a| * |b|) + b ^ 2 := by
      rw [sub_sq, sq_abs, sq_abs]; ring
    linarith [h1, h2]
  have hDgns : ∀ x : EuclideanSpace ℝ (Fin n),
      ∑ m, (Dg k x m) ^ 2 = ‖Dg k x‖ ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact (Finset.sum_congr rfl fun m _ => by rw [Real.norm_eq_abs, sq_abs]).symm
  have hDgb : ∀ (x : EuclideanSpace ℝ (Fin n)) (j : Fin n),
      |Dg k x j| ≤ ‖Dg k x‖ := by
    intro x j
    have h1 : (Dg k x j) ^ 2 ≤ ‖Dg k x‖ ^ 2 := by
      rw [← hDgns x]
      exact Finset.single_le_sum (f := fun m => (Dg k x m) ^ 2)
        (fun m _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg _)] at h2
  have hpull2 : ∀ (cc : ℝ) (f : Fin n → Fin n → ℝ),
      (∑ i, ∑ j, cc * f i j) = cc * ∑ i, ∑ j, f i j := by
    intro cc f
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hcsn : ∀ f : Fin n → ℝ, ∑ j, |f j| ≤ Real.sqrt ((n:ℝ) * ∑ j, (f j) ^ 2) := by
    intro f
    have h1 : (∑ j, |f j|) ^ 2 ≤ (n:ℝ) * ∑ j, (f j) ^ 2 := by
      have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : Fin n => (1:ℝ)) (fun j => |f j|)
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, sq_abs] at h2
      exact h2
    have h3 : (0:ℝ) ≤ ∑ j, |f j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have h4 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq h3] at h4
  -- the regularisation's pointwise data
  have hbpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < |g x k| + η :=
    fun x => hbase η hη (g x k)
  have hbbd : ∀ x : EuclideanSpace ℝ (Fin n),
      (|g x k| + η) ^ (p - 2) ≤ η ^ (p - 2) := fun x =>
    Real.rpow_le_rpow_of_nonpos hη (by linarith only [abs_nonneg (g x k)]) hp2n.le
  have hgcm : AEMeasurable (fun x => g x k) (volume.restrict (tsupport ζ)) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous.measurable).comp_aemeasurable
      hgK.aemeasurable
  have hbm : AEMeasurable (fun x => (|g x k| + η) ^ (p - 2))
      (volume.restrict (tsupport ζ)) :=
    (((continuous_abs.measurable.comp_aemeasurable hgcm).add_const η).pow_const _)
  have hDpim : AEMeasurable (fun x => Dpi η (g x k))
      (volume.restrict (tsupport ζ)) :=
    ((hDpicont η hη).measurable).comp_aemeasurable hgcm
  have hDη0 : (0:ℝ) ≤ η ^ (p - 2) := Real.rpow_nonneg hη.le _
  -- (D4): the weight comparison `w^{p/2-1} ≤ 2^{2-p}(|g^k|+η)^{p-2}`,
  -- which is where `η² < ε` is used
  have hD4 : ∀ x : EuclideanSpace ℝ (Fin n),
      W x ≤ (2:ℝ) ^ (2 - p) * (|g x k| + η) ^ (p - 2) := by
    intro x
    have hw0 : (0:ℝ) < ε + ‖g x‖ ^ 2 := hwp x
    have hsq : Real.sqrt (ε + ‖g x‖ ^ 2) ^ 2 = ε + ‖g x‖ ^ 2 :=
      Real.sq_sqrt hw0.le
    have hs0 : 0 < Real.sqrt (ε + ‖g x‖ ^ 2) := Real.sqrt_pos.2 hw0
    have hη2 : η ≤ Real.sqrt (ε + ‖g x‖ ^ 2) := by
      nlinarith only [hsq, hs0, hη, hηε, sq_nonneg ‖g x‖]
    have hgk : |g x k| ≤ Real.sqrt (ε + ‖g x‖ ^ 2) := by
      have h1 : (g x k) ^ 2 ≤ ‖g x‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        exact Finset.single_le_sum (f := fun m => (g x m) ^ 2)
          (fun m _ => sq_nonneg _) (Finset.mem_univ k)
      nlinarith only [hsq, hs0, h1, hε, abs_nonneg (g x k), sq_abs (g x k)]
    have hble : |g x k| + η ≤ 2 * Real.sqrt (ε + ‖g x‖ ^ 2) := by
      linarith only [hη2, hgk]
    have h2s : (0:ℝ) < 2 * Real.sqrt (ε + ‖g x‖ ^ 2) := by linarith only [hs0]
    have hstep : (2 * Real.sqrt (ε + ‖g x‖ ^ 2)) ^ (p - 2)
        ≤ (|g x k| + η) ^ (p - 2) :=
      Real.rpow_le_rpow_of_nonpos (hbpos x) hble hp2n.le
    have hexpand : (2 * Real.sqrt (ε + ‖g x‖ ^ 2)) ^ (p - 2)
        = (2:ℝ) ^ (p - 2) * (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) := by
      rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _),
        Real.sqrt_eq_rpow, ← Real.rpow_mul hw0.le]
      congr 2
      ring
    have h2p : (0:ℝ) < (2:ℝ) ^ (2 - p) := Real.rpow_pos_of_pos (by norm_num) _
    have hmulinv : (2:ℝ) ^ (2 - p) * (2:ℝ) ^ (p - 2) = 1 := by
      rw [← Real.rpow_add (by norm_num)]
      norm_num
    rw [hWeq x]
    nlinarith only [hstep, hexpand, h2p, hmulinv,
      Real.rpow_nonneg hw0.le (p / 2 - 1)]
  -- the sign-free core
  have key : ∀ (T : Set (EuclideanSpace ℝ (Fin n))) (sg : ℝ)
      (v : EuclideanSpace ℝ (Fin n) → ℝ)
      (Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      (sg = 1 ∨ sg = -1) → MeasurableSet T → T ⊆ Metric.ball x₀ R →
      (∀ x, 0 ≤ v x) →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
        (x ∈ T → Z x = (sg * Dpi η (g x k)) • Dg k x)
          ∧ (x ∉ T → Z x = 0 ∧ v x = 0)) →
      MemW1pLocOn n 2 (Metric.ball x₀ R) v Z →
      (∫ x in T, W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
        ≤ (2 * (n:ℝ) * r * (2:ℝ) ^ (1 - p / 2) / (p - 1)) ^ 2
          * ∫ x in Metric.ball x₀ R, v x ^ 2
            * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 :=
    RegularisedSignedPowerCaccioppoliCore n p r η Dpi x₀ R ε γ₀ γ₁ A u g Dg k ζ W
      M Lζ LDζ LW hn hp hr hDpilow hDpibd hη hε hγ₀ hγ₁ hγ01 hR hγ₁p hQ hC1 hsol
      hDg hζsm hζcs hζΩ hWpos hMeq hQ1b hQ2b hKcpt hKmeas hζ0 hDζ0 hextend hWm hMm
      hDgcm hζm hDζm haemul haesum hMint hLζ0 hLζ hLDζ0 hLDζ hLW0 hLW hsumbd habs2
      hDgns hDgb hpull2 hcsn hbpos hbbd hbm hDpim hDη0 hD4
  -- the identity `‖V_η‖² = (p²/4)(|g^k|+η)^{p-2}‖Dg^k‖²` of (D.2)
  have hVsqeq : ∀ x : EuclideanSpace ℝ (Fin n),
      (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
          * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2
        = p ^ 2 / 4
          * (W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2) := by
    intro x
    have hc0 : (0:ℝ) ≤ p / 2 * (|g x k| + η) ^ (p / 2 - 1) :=
      mul_nonneg (by linarith only [hp0])
        (Real.rpow_nonneg (hbpos x).le _)
    have e : ((|g x k| + η) ^ (p / 2 - 1)) ^ 2 = (|g x k| + η) ^ (p - 2) := by
      rw [← Real.rpow_natCast ((|g x k| + η) ^ (p / 2 - 1)) 2,
        ← Real.rpow_mul (hbpos x).le]
      congr 1
      push_cast
      ring
    rw [norm_smul, Real.norm_eq_abs, mul_pow, abs_of_nonneg hc0, hWeq x]
    calc (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
          * ((p / 2 * (|g x k| + η) ^ (p / 2 - 1)) ^ 2 * ‖Dg k x‖ ^ 2) * ζ x ^ 2
        = p ^ 2 / 4 * ((ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ((|g x k| + η) ^ (p / 2 - 1)) ^ 2 * ‖Dg k x‖ ^ 2 * ζ x ^ 2) := by
          ring
      _ = p ^ 2 / 4 * ((ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2) := by rw [e]
  -- integrability of the weighted integrand on `B_R`
  have hDgnm2 : AEMeasurable (fun x => ‖Dg k x‖ ^ 2)
      (volume.restrict (tsupport ζ)) :=
    (((hDg k).2 (tsupport ζ) hKcpt hζΩ).2.1.aemeasurable.norm).pow_const 2
  have hXint2 : IntegrableOn
      (fun x => W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
      (tsupport ζ) volume := by
    refine Integrable.mono' (hMint.const_mul (LW * (η ^ (p - 2)) * Lζ))
      (AEMeasurable.aestronglyMeasurable
        (haemul _ _ (haemul _ _ (haemul _ _ hWm hbm) hDgnm2)
          (hζm.pow_const 2))) ?_
    filter_upwards [hLW] with x hWx
    have hW0 : (0:ℝ) ≤ W x := (hWpos x).le
    have hbx : (0:ℝ) ≤ (|g x k| + η) ^ (p - 2) :=
      Real.rpow_nonneg (hbpos x).le _
    rw [Real.norm_eq_abs]
    calc |W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2|
        = W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2 :=
          abs_of_nonneg (by positivity)
      _ ≤ LW * (η ^ (p - 2)) * ‖Dg k x‖ ^ 2 * Lζ := by
          refine mul_le_mul (mul_le_mul (mul_le_mul hWx (hbbd x) hbx
            (le_trans hW0 hWx)) le_rfl (sq_nonneg _) (by positivity))
            (hLζ x) (sq_nonneg _) (by positivity)
      _ = LW * (η ^ (p - 2)) * Lζ * ‖Dg k x‖ ^ 2 := by ring
  have hXΩ2 : IntegrableOn
      (fun x => W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
      (Metric.ball x₀ R) volume := by
    refine hextend _ (fun x hx => by rw [hζ0 x hx]; ring) hXint2
  -- the constant bookkeeping of (D4)
  have hconst : p ^ 2 / 4
      * (2 * (n:ℝ) * r * (2:ℝ) ^ (1 - p / 2) / (p - 1)) ^ 2 = C₂ := by
    rw [hC₂def, hC₁def]
    field_simp
    ring
  have hp240 : (0:ℝ) ≤ p ^ 2 / 4 := by positivity
  -- the level sets, taken on the continuous representative
  have hgae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∈ Metric.ball x₀ R → g x = g' x :=
    (ae_restrict_iff' hΩ.measurableSet).1 hg'ae
  have hpcont : ContinuousOn (fun y => pie η (g' y k)) (Metric.ball x₀ R) :=
    (hpieC1 η hη).continuous.comp_continuousOn
      ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp_continuousOn hg'cont)
  have hTpOpen : IsOpen (Metric.ball x₀ R ∩ {y | ℓ < pie η (g' y k)}) :=
    hpcont.isOpen_inter_preimage hΩ (isOpen_Ioi (a := ℓ))
  have hTmOpen : IsOpen (Metric.ball x₀ R ∩ {y | pie η (g' y k) < ℓ}) :=
    hpcont.isOpen_inter_preimage hΩ (isOpen_Iio (a := ℓ))
  have hTpres : volume.restrict (Metric.ball x₀ R ∩ {y | ℓ < pie η (g y k)})
      = volume.restrict (Metric.ball x₀ R ∩ {y | ℓ < pie η (g' y k)}) := by
    refine Measure.restrict_congr_set (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [hgae] with x hx
    constructor
    · rintro ⟨hxΩ, hxl⟩
      exact ⟨hxΩ, by show ℓ < pie η (g' x k); rw [← hx hxΩ]; exact hxl⟩
    · rintro ⟨hxΩ, hxl⟩
      exact ⟨hxΩ, by show ℓ < pie η (g x k); rw [hx hxΩ]; exact hxl⟩
  have hTmres : volume.restrict (Metric.ball x₀ R ∩ {y | pie η (g y k) < ℓ})
      = volume.restrict (Metric.ball x₀ R ∩ {y | pie η (g' y k) < ℓ}) := by
    refine Measure.restrict_congr_set (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [hgae] with x hx
    constructor
    · rintro ⟨hxΩ, hxl⟩
      exact ⟨hxΩ, by show pie η (g' x k) < ℓ; rw [← hx hxΩ]; exact hxl⟩
    · rintro ⟨hxΩ, hxl⟩
      exact ⟨hxΩ, by show pie η (g x k) < ℓ; rw [hx hxΩ]; exact hxl⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ((hXΩ2.const_mul (p ^ 2 / 4)).congr
      (Filter.Eventually.of_forall fun x => (hVsqeq x).symm))
  · rw [hTpres]
    have e1 : (∫ x in Metric.ball x₀ R ∩ {y | ℓ < pie η (g' y k)},
          (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
        = p ^ 2 / 4 * ∫ x in Metric.ball x₀ R ∩ {y | ℓ < pie η (g' y k)},
          W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2 := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => hVsqeq x)
    rw [e1, ← hconst, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hp240
    refine key _ 1 _ _ (Or.inl rfl) hTpOpen.measurableSet Set.inter_subset_left
      (fun x => le_max_right _ _) ?_ hplusloc
    filter_upwards [hg'ae, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
    have hgk : pie η (g x k) = pie η (g' x k) := by rw [hx]
    constructor
    · rintro ⟨-, hxl⟩
      have hlt : ℓ < pie η (g x k) := by rw [hgk]; exact hxl
      rw [if_pos hlt, one_mul]
    · intro hxT
      have hnl : ¬ (ℓ < pie η (g' x k)) := fun hc => hxT ⟨hxΩ, hc⟩
      have hle : pie η (g x k) ≤ ℓ := by rw [hgk]; exact not_lt.1 hnl
      exact ⟨if_neg (not_lt.2 hle), max_eq_right (by linarith only [hle])⟩
  · rw [hTmres]
    have e1 : (∫ x in Metric.ball x₀ R ∩ {y | pie η (g' y k) < ℓ},
          (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
            * ‖(p / 2 * (|g x k| + η) ^ (p / 2 - 1)) • Dg k x‖ ^ 2 * ζ x ^ 2)
        = p ^ 2 / 4 * ∫ x in Metric.ball x₀ R ∩ {y | pie η (g' y k) < ℓ},
          W x * (|g x k| + η) ^ (p - 2) * ‖Dg k x‖ ^ 2 * ζ x ^ 2 := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => hVsqeq x)
    rw [e1, ← hconst, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hp240
    refine key _ (-1) _ _ (Or.inr rfl) hTmOpen.measurableSet
      Set.inter_subset_left (fun x => le_max_right _ _) ?_ hminusloc
    filter_upwards [hg'ae, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
    have hgk : pie η (g x k) = pie η (g' x k) := by rw [hx]
    constructor
    · rintro ⟨-, hxl⟩
      have hlt : pie η (g x k) < ℓ := by rw [hgk]; exact hxl
      rw [if_pos hlt, neg_one_mul, neg_smul]
    · intro hxT
      have hnl : ¬ (pie η (g' x k) < ℓ) := fun hc => hxT ⟨hxΩ, hc⟩
      have hle : ℓ ≤ pie η (g x k) := by rw [hgk]; exact not_lt.1 hnl
      exact ⟨if_neg (not_lt.2 hle), max_eq_right (by linarith only [hle])⟩
