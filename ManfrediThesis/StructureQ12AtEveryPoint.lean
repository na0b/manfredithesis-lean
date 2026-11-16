import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.EllipticStructureQ6
open MeasureTheory

/-- The two differential structure conditions (Q1) and (Q2), which the paper
states for almost every `x`, hold at *every* point of `Ω` once (Q6) is also
available, and with the same constants `γ₀` and `γ₁`.  The three ingredients are
that `hdiff` and (Q6) are pointwise in `x`, that the almost-everywhere
inequalities integrate along a segment at a point where they hold, and that
(Q6) lets the integrated inequality pass to the limit along a sequence of such
points. -/
theorem StructureQ12AtEveryPoint :
    ∀ (n : ℕ) (p ε γ₀ γ₁ : ℝ), 2 ≤ n → 1 < p → 0 ≤ ε → 0 < γ₀ → 0 < γ₁ →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n))
        (σ : ℝ → ℝ),
        IsOpen Ω →
        EllipticStructureQ12 n p ε γ₀ γ₁ Ω A →
        EllipticStructureQ6 n p Ω A σ →
        (∀ x ∈ Ω, ∀ (z : ℝ) (h ξ : EuclideanSpace ℝ (Fin n)),
            ε + ‖h‖ ^ 2 ≠ 0 →
            γ₀ * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1) * ‖ξ‖ ^ 2
              ≤ ∑ i, (fderiv ℝ (A x z) h ξ) i * ξ i)
          ∧ (∀ x ∈ Ω, ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)) (i j : Fin n),
              ε + ‖h‖ ^ 2 ≠ 0 →
              |(fderiv ℝ (A x z) h (EuclideanSpace.single j (1 : ℝ))) i|
                ≤ γ₁ * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1)) := by
  intro n p ε γ₀ γ₁ hn hp hε hγ₀ hγ₁ Ω A σ hΩ hQ12 hQ6
  have hσnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ σ t := by
    intro t ht
    rw [← hQ6.σ_zero]
    exact hQ6.σ_mono ht
  have hDopen : IsOpen {y : EuclideanSpace ℝ (Fin n) | ε + ‖y‖ ^ 2 ≠ 0} :=
    isOpen_ne.preimage (continuous_const.add (continuous_norm.pow 2))
  have hdiffAt : ∀ x ∈ Ω, ∀ (z : ℝ) (y : EuclideanSpace ℝ (Fin n)),
      ε + ‖y‖ ^ 2 ≠ 0 → DifferentiableAt ℝ (A x z) y := by
    intro x hx z y hy
    exact (((hQ12.hdiff x hx z).differentiableOn (by norm_num)) y hy).differentiableAt
      (hDopen.mem_nhds hy)
  -- Step 1: the good points are dense in `Ω`.
  have hdense : ∀ x₁ ∈ Ω, ∀ r : ℝ, 0 < r →
      ∃ x, dist x x₁ < r ∧ x ∈ Ω ∧
        ((∀ (z : ℝ) (y ξ : EuclideanSpace ℝ (Fin n)), ε + ‖y‖ ^ 2 ≠ 0 →
            γ₀ * (ε + ‖y‖ ^ 2) ^ (p / 2 - 1) * ‖ξ‖ ^ 2
              ≤ ∑ i, (fderiv ℝ (A x z) y ξ) i * ξ i)
          ∧ ∀ (z : ℝ) (y : EuclideanSpace ℝ (Fin n)) (i j : Fin n),
              ε + ‖y‖ ^ 2 ≠ 0 →
              |(fderiv ℝ (A x z) y (EuclideanSpace.single j (1 : ℝ))) i|
                ≤ γ₁ * (ε + ‖y‖ ^ 2) ^ (p / 2 - 1)) := by
    intro x₁ hx₁ r hr
    have hUopen : IsOpen (Metric.ball x₁ r ∩ Ω) := Metric.isOpen_ball.inter hΩ
    have hUpos : 0 < volume (Metric.ball x₁ r ∩ Ω) :=
      hUopen.measure_pos volume ⟨x₁, Metric.mem_ball_self hr, hx₁⟩
    have hne : (volume.restrict (Metric.ball x₁ r ∩ Ω)) ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero]
      exact hUpos.ne'
    have : (ae (volume.restrict (Metric.ball x₁ r ∩ Ω))).NeBot := ae_neBot.2 hne
    have h1 := ae_restrict_of_ae (μ := volume)
      (s := Metric.ball x₁ r ∩ Ω) (hQ12.Q1.and hQ12.Q2)
    have h2 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₁ r ∩ Ω)),
        x ∈ Metric.ball x₁ r ∩ Ω := ae_restrict_mem hUopen.measurableSet
    obtain ⟨x, hxP, hxU⟩ := (h1.and h2).exists
    exact ⟨x, Metric.mem_ball.1 hxU.1, hxU.2, hxP.1 hxU.2, hxP.2 hxU.2⟩
  -- Step 2: admissibility and the weight along a line, in `ε`-`δ` form.
  have hadm : ∀ (y η : EuclideanSpace ℝ (Fin n)), ε + ‖y‖ ^ 2 ≠ 0 →
      ∀ θ : ℝ, 0 < θ → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ s : ℝ, 0 ≤ s → s ≤ t₀ →
        ε + ‖y + s • η‖ ^ 2 ≠ 0 ∧
          |(ε + ‖y + s • η‖ ^ 2) ^ (p / 2 - 1)
              - (ε + ‖y‖ ^ 2) ^ (p / 2 - 1)| ≤ θ := by
    intro y η hy θ hθ
    have hlinecont : Continuous fun s : ℝ => y + s • η :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hw : Continuous fun s : ℝ => ε + ‖y + s • η‖ ^ 2 :=
      continuous_const.add ((hlinecont.norm).pow 2)
    have h1 : ∀ᶠ s in nhds (0 : ℝ), ε + ‖y + s • η‖ ^ 2 ≠ 0 := by
      have := (hlinecont.continuousAt (x := (0 : ℝ))).eventually
        (hDopen.mem_nhds (show y + (0 : ℝ) • η ∈ _ by simpa using hy))
      simpa using this
    have h2 : ∀ᶠ s in nhds (0 : ℝ),
        |(ε + ‖y + s • η‖ ^ 2) ^ (p / 2 - 1)
            - (ε + ‖y‖ ^ 2) ^ (p / 2 - 1)| ≤ θ := by
      have hc : ContinuousAt (fun s : ℝ =>
          (ε + ‖y + s • η‖ ^ 2) ^ (p / 2 - 1)) 0 := by
        refine (hw.continuousAt).rpow_const ?_
        left
        simpa using hy
      rw [Metric.continuousAt_iff] at hc
      obtain ⟨r, hr, hrc⟩ := hc θ hθ
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with s hs
      have hd := hrc (by simpa using hs)
      rw [Real.dist_eq] at hd
      simpa using le_of_lt hd
    obtain ⟨t₀, ht₀, hT⟩ := Metric.eventually_nhds_iff.1 (h1.and h2)
    refine ⟨t₀ / 2, by linarith, fun s hs hst => hT ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hs]
    linarith
  -- THE CORE: a one-sided derivative bound at an arbitrary point of `Ω`.
  have core : ∀ x₁ ∈ Ω, ∀ (z : ℝ) (y η : EuclideanSpace ℝ (Fin n))
      (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (c : ℝ),
      ε + ‖y‖ ^ 2 ≠ 0 →
      (∀ θ : ℝ, 0 < θ → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ s : ℝ, 0 ≤ s → s ≤ t₀ →
        ε + ‖y + s • η‖ ^ 2 ≠ 0 ∧
          ∀ x ∈ Ω,
            (∀ (z' : ℝ) (y' ξ' : EuclideanSpace ℝ (Fin n)), ε + ‖y'‖ ^ 2 ≠ 0 →
              γ₀ * (ε + ‖y'‖ ^ 2) ^ (p / 2 - 1) * ‖ξ'‖ ^ 2
                ≤ ∑ i, (fderiv ℝ (A x z') y' ξ') i * ξ' i) →
            (∀ (z' : ℝ) (y' : EuclideanSpace ℝ (Fin n)) (i j : Fin n),
              ε + ‖y'‖ ^ 2 ≠ 0 →
              |(fderiv ℝ (A x z') y' (EuclideanSpace.single j (1 : ℝ))) i|
                ≤ γ₁ * (ε + ‖y'‖ ^ 2) ^ (p / 2 - 1)) →
            c - θ ≤ L (fderiv ℝ (A x z) (y + s • η) η)) →
      c ≤ L (fderiv ℝ (A x₁ z) y η) := by
    intro x₁ hx₁ z y η L c hy H
    have hline : ∀ (x : EuclideanSpace ℝ (Fin n)) (s₀ : ℝ), x ∈ Ω →
        ε + ‖y + s₀ • η‖ ^ 2 ≠ 0 →
        HasDerivAt (fun s : ℝ => L (A x z (y + s • η)))
          (L (fderiv ℝ (A x z) (y + s₀ • η) η)) s₀ := by
      intro x s₀ hx hs₀
      have hl : HasDerivAt (fun s : ℝ => y + s • η) η s₀ := by
        simpa using ((hasDerivAt_id s₀).smul_const η).const_add y
      exact L.hasFDerivAt.comp_hasDerivAt s₀
        ((hdiffAt x hx z _ hs₀).hasFDerivAt.comp_hasDerivAt s₀ hl)
    refine le_of_forall_pos_le_add fun θ hθ => ?_
    obtain ⟨t₀, ht₀, hT⟩ := H (θ / 2) (by linarith)
    have hslope : ∀ t : ℝ, 0 < t → t ≤ t₀ →
        (c - θ / 2) * t
          ≤ L (A x₁ z (y + t • η)) - L (A x₁ z (y + (0 : ℝ) • η)) := by
      intro t ht htt₀
      refine le_of_forall_pos_le_add fun ρ hρ => ?_
      set K : ℝ := (1 + ‖y + t • η‖ ^ 2) ^ ((p - 1) / 2)
        + (1 + ‖y + (0 : ℝ) • η‖ ^ 2) ^ ((p - 1) / 2) with hKdef
      have hK0 : (0 : ℝ) ≤ K := by
        rw [hKdef]
        exact add_nonneg (Real.rpow_nonneg (by positivity) _)
          (Real.rpow_nonneg (by positivity) _)
      have hcont0 : ContinuousAt σ 0 := hQ6.σ_cont.continuousAt
      rw [Metric.continuousAt_iff] at hcont0
      obtain ⟨r, hr, hrσ⟩ := hcont0 (ρ / (‖L‖ * K + 1)) (by positivity)
      obtain ⟨x, hxd, hxΩ, hxQ1, hxQ2⟩ := hdense x₁ hx₁ r hr
      -- (1) the mean value theorem at the good point `x`
      have hmvt : (c - θ / 2) * t
          ≤ L (A x z (y + t • η)) - L (A x z (y + (0 : ℝ) • η)) := by
        have hcOn : ContinuousOn (fun s : ℝ => L (A x z (y + s • η)))
            (Set.Icc 0 t) := by
          intro s hs
          exact ((hline x s hxΩ (hT s hs.1 (le_trans hs.2 htt₀)).1).continuousAt
            ).continuousWithinAt
        obtain ⟨s, hs, hsEq⟩ := exists_hasDerivAt_eq_slope
          (fun s : ℝ => L (A x z (y + s • η)))
          (fun s : ℝ => L (fderiv ℝ (A x z) (y + s • η) η)) ht hcOn
          (fun s hs => hline x s hxΩ
            (hT s (le_of_lt hs.1) (le_trans (le_of_lt hs.2) htt₀)).1)
        have hge := (hT s (le_of_lt hs.1) (le_trans (le_of_lt hs.2) htt₀)).2
          x hxΩ hxQ1 hxQ2
        rw [hsEq, sub_zero] at hge
        calc (c - θ / 2) * t ≤ ((L (A x z (y + t • η))
                - L (A x z (y + (0 : ℝ) • η))) / t) * t :=
              mul_le_mul_of_nonneg_right hge (le_of_lt ht)
          _ = L (A x z (y + t • η)) - L (A x z (y + (0 : ℝ) • η)) := by
              field_simp
      -- (2) the (Q6) transport from `x` to `x₁`
      have htrans : ∀ v : EuclideanSpace ℝ (Fin n),
          |L (A x z v) - L (A x₁ z v)|
            ≤ ‖L‖ * (σ (dist x x₁) * (1 + ‖v‖ ^ 2) ^ ((p - 1) / 2)) := by
        intro v
        rw [← ContinuousLinearMap.map_sub, ← Real.norm_eq_abs]
        refine le_trans (L.le_opNorm _) ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg L)
        simpa using hQ6.Q6 x hxΩ x₁ hx₁ z z v
      have hσsmall : ‖L‖ * (σ (dist x x₁) * K) ≤ ρ := by
        have h1 : σ (dist x x₁) ≤ ρ / (‖L‖ * K + 1) := by
          have hd := hrσ (show dist (dist x x₁) 0 < r by
            rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]; exact hxd)
          rw [Real.dist_eq, hQ6.σ_zero, sub_zero] at hd
          exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hd)
        have h2 : (0 : ℝ) ≤ σ (dist x x₁) := hσnn _ dist_nonneg
        have hLK : (0 : ℝ) ≤ ‖L‖ * K := mul_nonneg (norm_nonneg L) hK0
        have hid : (‖L‖ * K + 1) * (ρ / (‖L‖ * K + 1)) = ρ := by
          field_simp
        have h3 : ‖L‖ * K * σ (dist x x₁) ≤ ‖L‖ * K * (ρ / (‖L‖ * K + 1)) :=
          mul_le_mul_of_nonneg_left h1 hLK
        have hdiv : (0 : ℝ) ≤ ρ / (‖L‖ * K + 1) := by positivity
        calc ‖L‖ * (σ (dist x x₁) * K) = ‖L‖ * K * σ (dist x x₁) := by ring
          _ ≤ ‖L‖ * K * (ρ / (‖L‖ * K + 1)) := h3
          _ ≤ ρ := by nlinarith [hid, hdiv]
      have e1 := abs_le.1 (htrans (y + t • η))
      have e2 := abs_le.1 (htrans (y + (0 : ℝ) • η))
      have hsplit : ‖L‖ * (σ (dist x x₁) * (1 + ‖y + t • η‖ ^ 2) ^ ((p - 1) / 2))
            + ‖L‖ * (σ (dist x x₁)
              * (1 + ‖y + (0 : ℝ) • η‖ ^ 2) ^ ((p - 1) / 2))
          = ‖L‖ * (σ (dist x x₁) * K) := by rw [hKdef]; ring
      linarith [e1.1, e1.2, e2.1, e2.2, hmvt, hσsmall, hsplit]
    -- (3) let `t ↓ 0`
    have hd0 : HasDerivAt (fun s : ℝ => L (A x₁ z (y + s • η)))
        (L (fderiv ℝ (A x₁ z) y η)) 0 := by
      have hraw := hline x₁ 0 hx₁
        (show ε + ‖y + (0 : ℝ) • η‖ ^ 2 ≠ 0 by simpa using hy)
      simpa using hraw
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        c - θ / 2 ≤ t⁻¹ • (L (A x₁ z (y + (0 + t) • η))
          - L (A x₁ z (y + (0 : ℝ) • η))) := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) ht₀] with t htb htIoi
      have ht : 0 < t := htIoi
      have htt₀ : t ≤ t₀ := by
        have := Metric.mem_ball.1 htb
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_of_lt ht)] at this
        linarith
      rw [zero_add, smul_eq_mul, inv_mul_eq_div, le_div_iff₀ ht]
      exact hslope t ht htt₀
    linarith [ge_of_tendsto hd0.tendsto_slope_zero_right hev]
  -- The coordinate functionals, and the two conclusions.
  set P : Fin n → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    fun i => (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) with hPdef
  have hPapp : ∀ (i : Fin n) (v : EuclideanSpace ℝ (Fin n)), P i v = v i :=
    fun i v => rfl
  refine ⟨?_, ?_⟩
  · -- (Q1) at every point of `Ω`
    intro x₁ hx₁ z h ξ hh
    set L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := ∑ i : Fin n, ξ i • P i with hLdef
    have hLapp : ∀ v : EuclideanSpace ℝ (Fin n), L v = ∑ i, v i * ξ i := by
      intro v
      rw [hLdef]
      simp only [FunLike.coe_sum, Finset.sum_apply,
        FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hPapp]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [← hLapp]
    refine core x₁ hx₁ z h ξ L _ hh fun θ hθ => ?_
    obtain ⟨t₀, ht₀, hT⟩ :=
      hadm h ξ hh (θ / (γ₀ * ‖ξ‖ ^ 2 + 1)) (by positivity)
    refine ⟨t₀, ht₀, fun s hs hst => ⟨(hT s hs hst).1, fun x hxΩ hxQ1 hxQ2 => ?_⟩⟩
    rw [hLapp]
    refine le_trans ?_ (hxQ1 z (h + s • ξ) ξ (hT s hs hst).1)
    have hb := abs_le.1 (hT s hs hst).2
    have hQ : (0 : ℝ) ≤ γ₀ * ‖ξ‖ ^ 2 := by positivity
    have hdiv : (0 : ℝ) < θ / (γ₀ * ‖ξ‖ ^ 2 + 1) := by positivity
    have hid : (γ₀ * ‖ξ‖ ^ 2 + 1) * (θ / (γ₀ * ‖ξ‖ ^ 2 + 1)) = θ := by field_simp
    have step1 : γ₀ * ‖ξ‖ ^ 2 * ((ε + ‖h‖ ^ 2) ^ (p / 2 - 1)
          - (ε + ‖h + s • ξ‖ ^ 2) ^ (p / 2 - 1))
        ≤ γ₀ * ‖ξ‖ ^ 2 * (θ / (γ₀ * ‖ξ‖ ^ 2 + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith [hb.1]) hQ
    nlinarith [step1, hid, hdiv.le]
  · -- (Q2) at every point of `Ω`
    intro x₁ hx₁ z h i j hh
    have hH : ∀ L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
        (∀ (v : EuclideanSpace ℝ (Fin n)), L v = v i ∨ L v = -(v i)) →
        ∀ θ : ℝ, 0 < θ → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ s : ℝ, 0 ≤ s → s ≤ t₀ →
          ε + ‖h + s • EuclideanSpace.single j (1 : ℝ)‖ ^ 2 ≠ 0 ∧
            ∀ x ∈ Ω,
              (∀ (z' : ℝ) (y' ξ' : EuclideanSpace ℝ (Fin n)), ε + ‖y'‖ ^ 2 ≠ 0 →
                γ₀ * (ε + ‖y'‖ ^ 2) ^ (p / 2 - 1) * ‖ξ'‖ ^ 2
                  ≤ ∑ k, (fderiv ℝ (A x z') y' ξ') k * ξ' k) →
              (∀ (z' : ℝ) (y' : EuclideanSpace ℝ (Fin n)) (k l : Fin n),
                ε + ‖y'‖ ^ 2 ≠ 0 →
                |(fderiv ℝ (A x z') y' (EuclideanSpace.single l (1 : ℝ))) k|
                  ≤ γ₁ * (ε + ‖y'‖ ^ 2) ^ (p / 2 - 1)) →
              -(γ₁ * (ε + ‖h‖ ^ 2) ^ (p / 2 - 1)) - θ
                ≤ L (fderiv ℝ (A x z) (h + s • EuclideanSpace.single j (1 : ℝ))
                    (EuclideanSpace.single j (1 : ℝ))) := by
      intro L hLv θ hθ
      obtain ⟨t₀, ht₀, hT⟩ := hadm h (EuclideanSpace.single j (1 : ℝ)) hh
        (θ / (γ₁ + 1)) (by positivity)
      refine ⟨t₀, ht₀, fun s hs hst => ⟨(hT s hs hst).1, fun x hxΩ hxQ1 hxQ2 => ?_⟩⟩
      have hgood := abs_le.1 (hxQ2 z (h + s • EuclideanSpace.single j (1 : ℝ)) i j
        (hT s hs hst).1)
      have hb := abs_le.1 (hT s hs hst).2
      have hdiv : (0 : ℝ) < θ / (γ₁ + 1) := by positivity
      have hid : (γ₁ + 1) * (θ / (γ₁ + 1)) = θ := by field_simp
      have step1 : γ₁ * ((ε + ‖h + s • EuclideanSpace.single j (1 : ℝ)‖ ^ 2)
            ^ (p / 2 - 1) - (ε + ‖h‖ ^ 2) ^ (p / 2 - 1))
          ≤ γ₁ * (θ / (γ₁ + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith [hb.2]) (le_of_lt hγ₁)
      rcases hLv (fderiv ℝ (A x z) (h + s • EuclideanSpace.single j (1 : ℝ))
          (EuclideanSpace.single j (1 : ℝ))) with hv | hv
      · rw [hv]; nlinarith [hgood.1, step1, hid, hdiv.le]
      · rw [hv]; nlinarith [hgood.2, step1, hid, hdiv.le]
    have hup := core x₁ hx₁ z h (EuclideanSpace.single j (1 : ℝ)) (P i) _ hh
      (hH (P i) (fun v => Or.inl (hPapp i v)))
    have hdn := core x₁ hx₁ z h (EuclideanSpace.single j (1 : ℝ)) (-(P i)) _ hh
      (hH (-(P i)) (fun v => Or.inr (by
        rw [neg_apply, hPapp])))
    rw [hPapp] at hup
    rw [neg_apply, hPapp] at hdn
    exact abs_le.2 ⟨by linarith, by linarith⟩
