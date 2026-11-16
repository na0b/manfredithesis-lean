import ManfrediThesis.Preamble
import ManfrediThesis.WeakGradientLinear
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.WeakGradientPositivePart
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.StructureGrowthBound
import ManfrediThesis.StructureMonotonicityBound
open MeasureTheory

/-- The comparison principle on a ball for `div A(∇u) = 0`. -/
theorem BallComparisonPrinciple :
    ∀ (n : ℕ) (p ε γ₀ γ₁ : ℝ), 2 ≤ n → 1 < p → 0 ≤ ε → 0 < γ₀ → γ₀ ≤ γ₁ →
      CitedSobolevPoincareBall n →
      ∀ (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
        (u v U V : EuclideanSpace ℝ (Fin n) → ℝ)
        (gu gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < R →
        EllipticStructureQ12 n p ε γ₀ γ₁ Set.univ (fun _ _ h => A h) →
        IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h) (fun _ _ _ => 0) u gu →
        IsWeakSolutionOn n p (Metric.ball x₀ R) (fun _ _ h => A h) (fun _ _ _ => 0) v gv →
        MemW1pOn n p (Metric.ball x₀ R) u gu →
        MemW1pOn n p (Metric.ball x₀ R) v gv →
        ContinuousOn U (Metric.closedBall x₀ R) →
        (∀ x ∈ Metric.ball x₀ R, U x = u x) →
        ContinuousOn V (Metric.closedBall x₀ R) →
        (∀ x ∈ Metric.ball x₀ R, V x = v x) →
        (∀ x ∈ Metric.sphere x₀ R, U x ≤ V x) →
        ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), u x ≤ v x := by
  intro n p ε γ₀ γ₁ hn hp hε hγ₀ hγ hSP A x₀ R u v U V gu gv hR hQ hu hv hWu hWv
    hUc hUu hVc hVv hUV
  -- Ambient facts about the ball, and the nondegeneracy of the ambient space.
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hp1 : (1:ℝ) ≤ p := hp.le
  have hγ₁ : 0 < γ₁ := lt_of_lt_of_le hγ₀ hγ
  have hball_meas : MeasurableSet (Metric.ball x₀ R) := measurableSet_ball
  have hball_lt : volume (Metric.ball x₀ R) < ⊤ := measure_ball_lt_top
  have hball_pos : 0 < volume (Metric.ball x₀ R) :=
    Metric.isOpen_ball.measure_pos volume ⟨x₀, Metric.mem_ball_self hR⟩
  have hfin : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hball_lt⟩
  have hvol0 : (volume : Measure (EuclideanSpace ℝ (Fin n))) ≠ 0 := by
    intro hcon
    rw [hcon] at hball_pos
    simp at hball_pos
  have hnebot : (MeasureTheory.ae (volume : Measure (EuclideanSpace ℝ (Fin n)))).NeBot :=
    MeasureTheory.ae_neBot.mpr hvol0
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hntriv : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, hnpos⟩ (1 : ℝ), ?_⟩⟩
    intro hcon
    have h := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w ⟨0, hnpos⟩) hcon
    simp at h
  have hnR : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnm1 : (0:ℝ) < (n : ℝ) - 1 := by linarith
  have hexp : (0:ℝ) < (n : ℝ) / ((n : ℝ) - 1) := div_pos (by linarith) hnm1
  -- Step 1: strict monotonicity of `A`, from (Q1) integrated along a segment.
  obtain ⟨Cm, hCm0, hCm⟩ := StructureMonotonicityBound n p (γ₁ / γ₀) hn hp (div_pos hγ₁ hγ₀)
  have hmono : ∀ a b : EuclideanSpace ℝ (Fin n),
      Cm * γ₀ * (ε + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2
        ≤ ∑ i, (A a i - A b i) * (a i - b i) := by
    have hae := hCm ε γ₀ γ₁ Set.univ (fun _ _ h => A h) hε hγ₀
      (le_of_eq (by rw [div_mul_cancel₀ _ hγ₀.ne'])) hQ
    obtain ⟨x, hx⟩ := hae.exists
    intro a b
    exact hx (Set.mem_univ x) 0 a b
  -- (2): the monotonicity is strict in the sense that equality forces `a = b`.
  have hinj : ∀ a b : EuclideanSpace ℝ (Fin n),
      (∑ i, (A a i - A b i) * (a i - b i)) = 0 → a = b := by
    intro a b h0
    have h1 := hmono a b
    rw [h0] at h1
    have hwt : (0:ℝ) ≤ (ε + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1) :=
      Real.rpow_nonneg (by positivity) _
    have hsq : (0:ℝ) ≤ ‖a - b‖ ^ 2 := sq_nonneg _
    have hprod : (ε + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1) * ‖a - b‖ ^ 2 = 0 := by
      refine le_antisymm ?_ (mul_nonneg hwt hsq)
      by_contra hcon
      rw [not_le] at hcon
      linarith [mul_pos (mul_pos hCm0 hγ₀) hcon]
    rcases mul_eq_zero.mp hprod with hz | hz
    · have hz2 := (Real.rpow_eq_zero_iff_of_nonneg (by positivity)).mp hz
      have ha2 : ‖a‖ ^ 2 = 0 := by
        have := hz2.1
        linarith [sq_nonneg ‖a‖, sq_nonneg ‖b‖]
      have hb2 : ‖b‖ ^ 2 = 0 := by
        have := hz2.1
        linarith [sq_nonneg ‖a‖, sq_nonneg ‖b‖]
      have ha : a = 0 := norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp ha2)
      have hb : b = 0 := norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp hb2)
      rw [ha, hb]
    · have hab : ‖a - b‖ = 0 := (pow_eq_zero_iff (by norm_num)).mp hz
      exact norm_sub_eq_zero_iff.mp hab
  -- `w = u - v` is in `W^{1,p}(B_R)` with weak gradient `g_u - g_v`.
  have hw : MemW1pOn n p (Metric.ball x₀ R) (fun x => u x - v x)
      (fun x => gu x - gv x) := by
    have h := (WeakGradientLinear n p hn1 hp1 (Metric.ball x₀ R) u v gu gv 1 (-1) 0
      Metric.isOpen_ball).2.1 hWu hWv
    have e1 : (fun x => (1:ℝ) * u x + (-1:ℝ) * v x) = fun x => u x - v x := by
      funext x; ring
    have e2 : (fun x => (1:ℝ) • gu x + (-1:ℝ) • gv x) = fun x => gu x - gv x := by
      funext x
      simp [sub_eq_add_neg]
    rw [e1, e2] at h
    exact h
  -- Membership in `W^{1,p}(B_R)` only sees the values on `B_R`.
  have htrans : ∀ (f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      Set.EqOn f₁ f₂ (Metric.ball x₀ R) →
      MemW1pOn n p (Metric.ball x₀ R) f₁ g → MemW1pOn n p (Metric.ball x₀ R) f₂ g := by
    intro f₁ f₂ g heq h
    refine ⟨?_, ?_, h.2.2⟩
    · intro φ hφ1 hφ2 hφ3 i
      have e : (∫ x in Metric.ball x₀ R,
            f₂ x * fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ)))
          = ∫ x in Metric.ball x₀ R,
            f₁ x * fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ)) :=
        setIntegral_congr_fun hball_meas (fun x hx => by rw [heq hx])
      rw [e]
      exact h.1 φ hφ1 hφ2 hφ3 i
    · have hae : f₁ =ᵐ[volume.restrict (Metric.ball x₀ R)] f₂ :=
        (ae_restrict_iff' hball_meas).mpr
          (Filter.Eventually.of_forall (fun x hx => heq hx))
      exact (memLp_congr_ae hae).mp h.2.1
  -- The main estimate, for each threshold `η > 0` (Steps 2-4).
  have hmain : ∀ η : ℝ, 0 < η →
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), u x - v x ≤ η := by
    intro η hη
    -- Step 2: the test function `φ_η` and its weak gradient.
    obtain ⟨gη, hgη⟩ : ∃ g, g = (fun x => if η < u x - v x then gu x - gv x else 0) :=
      ⟨_, rfl⟩
    obtain ⟨Ψ, hΨ⟩ : ∃ f, f = Set.indicator (Metric.ball x₀ R)
        (fun x => max (u x - v x - η) 0) := ⟨_, rfl⟩
    have hΨin : ∀ x ∈ Metric.ball x₀ R, Ψ x = max (u x - v x - η) 0 := by
      intro x hx
      simp only [hΨ]
      exact Set.indicator_of_mem hx _
    have hΨout : ∀ x, x ∉ Metric.ball x₀ R → Ψ x = 0 := by
      intro x hx
      simp only [hΨ]
      exact Set.indicator_of_notMem hx _
    have hΨ0 : ∀ x, 0 ≤ Ψ x := by
      intro x
      by_cases hx : x ∈ Metric.ball x₀ R
      · rw [hΨin x hx]
        exact le_max_right _ _
      · rw [hΨout x hx]
    have hppos := WeakGradientPositivePart n p η hn1 hp1 (Metric.ball x₀ R)
      (fun x => u x - v x) (fun x => gu x - gv x) Metric.isOpen_ball hball_lt.ne hw
    have hΨmem : MemW1pOn n p (Metric.ball x₀ R) Ψ gη := by
      simp only [hgη]
      exact htrans _ _ _ (fun x hx => (hΨin x hx).symm) hppos
    -- Support: `φ_η` is supported in the compact set `K_η ⊆ B_R`.
    obtain ⟨K, hK⟩ : ∃ S, S = Metric.closedBall x₀ R ∩ (fun x => U x - V x) ⁻¹' Set.Ici η :=
      ⟨_, rfl⟩
    have hKclosed : IsClosed K := by
      rw [hK]
      exact (hUc.sub hVc).preimage_isClosed_of_isClosed Metric.isClosed_closedBall
        isClosed_Ici
    have hKsub : K ⊆ Metric.ball x₀ R := by
      intro x hx
      rw [hK] at hx
      have hx1 : dist x x₀ ≤ R := Metric.mem_closedBall.mp hx.1
      have hx2 : η ≤ U x - V x := hx.2
      rcases lt_or_eq_of_le hx1 with hlt | heq
      · exact Metric.mem_ball.mpr hlt
      · have := hUV x (Metric.mem_sphere.mpr heq)
        linarith
    have hKcpt : IsCompact K :=
      (isCompact_closedBall x₀ R).of_isClosed_subset hKclosed
        (by rw [hK]; exact Set.inter_subset_left)
    have hsupp : {x | Ψ x ≠ 0} ⊆ K := by
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      by_cases hb : x ∈ Metric.ball x₀ R
      · rw [hK]
        refine ⟨Metric.ball_subset_closedBall hb, ?_⟩
        rw [hΨin x hb] at hx
        have hpos : 0 < u x - v x - η := by
          rcases lt_or_ge 0 (u x - v x - η) with h | h
          · exact h
          · exact absurd (max_eq_right h) hx
        simp only [Set.mem_preimage, Set.mem_Ici, hUu x hb, hVv x hb]
        linarith
      · exact absurd (hΨout x hb) hx
    have htsub : tsupport Ψ ⊆ K := hKclosed.closure_subset_iff.mpr hsupp
    have hΨcs : HasCompactSupport Ψ := hKcpt.of_isClosed_subset isClosed_closure htsub
    have hΨsub : tsupport Ψ ⊆ Metric.ball x₀ R := htsub.trans hKsub
    -- Step 3: test both equations against `φ_η` and subtract.
    have ht1 := hu.2 Ψ gη hΨmem hΨcs hΨsub
    have ht2 := hv.2 Ψ gη hΨmem hΨcs hΨsub
    simp only [zero_mul, add_zero] at ht1 ht2
    obtain ⟨F, hF⟩ : ∃ f, f = (fun x => if η < u x - v x then
        (∑ i, (A (gu x) i - A (gv x) i) * (gu x i - gv x i)) else 0) := ⟨_, rfl⟩
    have hFeq : ∀ x, (∑ i, A (gu x) i * gη x i) - (∑ i, A (gv x) i * gη x i) = F x := by
      intro x
      simp only [hF, hgη]
      by_cases hx : η < u x - v x
      · simp only [if_pos hx]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [PiLp.sub_apply]
        ring
      · simp only [if_neg hx]
        simp
    have hFint : IntegrableOn F (Metric.ball x₀ R) volume :=
      (ht1.1.sub ht2.1).congr_fun (fun x _ => hFeq x) hball_meas
    have hFnn : ∀ x, 0 ≤ F x := by
      intro x
      simp only [hF]
      by_cases hx : η < u x - v x
      · simp only [if_pos hx]
        have h1 := hmono (gu x) (gv x)
        have h2 : (0:ℝ) ≤ Cm * γ₀ * (ε + ‖gu x‖ ^ 2 + ‖gv x‖ ^ 2) ^ (p / 2 - 1)
            * ‖gu x - gv x‖ ^ 2 :=
          mul_nonneg (mul_nonneg (mul_nonneg hCm0.le hγ₀.le)
            (Real.rpow_nonneg (by positivity) _)) (sq_nonneg _)
        linarith
      · simp only [if_neg hx]
        exact le_refl 0
    have hFzero : (∫ x in Metric.ball x₀ R, F x) = 0 := by
      rw [← setIntegral_congr_fun hball_meas (fun x _ => hFeq x),
        integral_sub ht1.1 ht2.1, ht1.2, ht2.2, sub_zero]
    have hF0 : (0 : EuclideanSpace ℝ (Fin n) → ℝ)
        ≤ᵐ[volume.restrict (Metric.ball x₀ R)] F := Filter.Eventually.of_forall hFnn
    have hFae : F =ᵐ[volume.restrict (Metric.ball x₀ R)] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hF0 hFint).mp hFzero
    -- (7): the weak gradient of `φ_η` vanishes almost everywhere on `B_R`.
    have hgη0 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), gη x = 0 := by
      filter_upwards [hFae] with x hx
      simp only [hgη]
      by_cases hc : η < u x - v x
      · simp only [if_pos hc]
        have h0 : (∑ i, (A (gu x) i - A (gv x) i) * (gu x i - gv x i)) = 0 := by
          simp only [hF, if_pos hc, Pi.zero_apply] at hx
          exact hx
        rw [hinj (gu x) (gv x) h0, sub_self]
      · simp only [if_neg hc]
    -- Step 4: `φ_η` is a.e. constant on `B_R`, by Sobolev-Poincaré.
    have hΨ1 : MemW1pOn n 1 (Metric.ball x₀ R) Ψ gη := by
      refine ⟨hΨmem.1, ?_, ?_⟩
      · exact hΨmem.2.1.mono_exponent (ENNReal.ofReal_le_ofReal hp1)
      · exact hΨmem.2.2.mono_exponent (ENNReal.ofReal_le_ofReal hp1)
    obtain ⟨C6, hC60, hC6⟩ := hSP
    have hRHS : (∫ x in Metric.ball x₀ R, ‖gη x‖) = 0 := by
      have h0 : (fun x => ‖gη x‖) =ᵐ[volume.restrict (Metric.ball x₀ R)] 0 := by
        filter_upwards [hgη0] with x hx
        simp [hx]
      rw [integral_congr_ae h0]
      simp
    obtain ⟨c, hc⟩ : ∃ t : ℝ, t = (volume (Metric.ball x₀ R)).toReal⁻¹
        * ∫ y in Metric.ball x₀ R, Ψ y := ⟨_, rfl⟩
    have hSPapp := hC6 x₀ R hR Ψ gη hΨ1
    rw [hRHS, mul_zero, ← hc] at hSPapp
    have hXnn : 0 ≤ ∫ x in Metric.ball x₀ R, |Ψ x - c| ^ ((n:ℝ) / ((n:ℝ) - 1)) :=
      setIntegral_nonneg hball_meas (fun x _ => Real.rpow_nonneg (abs_nonneg _) _)
    have hX0 : (∫ x in Metric.ball x₀ R, |Ψ x - c| ^ ((n:ℝ) / ((n:ℝ) - 1))) = 0 := by
      by_contra hne
      have hXpos : 0 < ∫ x in Metric.ball x₀ R, |Ψ x - c| ^ ((n:ℝ) / ((n:ℝ) - 1)) :=
        lt_of_le_of_ne hXnn (Ne.symm hne)
      have := Real.rpow_pos_of_pos hXpos (((n:ℝ) - 1) / (n:ℝ))
      linarith
    -- `φ_η` is bounded, because `U - V` is continuous on the closed ball.
    obtain ⟨Cb, hCb⟩ := (isCompact_closedBall x₀ R).exists_bound_of_continuousOn (hUc.sub hVc)
    have hCb0 : 0 ≤ Cb := le_trans (norm_nonneg _) (hCb x₀ (Metric.mem_closedBall_self hR.le))
    have hΨbd : ∀ x, |Ψ x| ≤ Cb := by
      intro x
      by_cases hb : x ∈ Metric.ball x₀ R
      · have h1 : |U x - V x| ≤ Cb := by
          have h := hCb x (Metric.ball_subset_closedBall hb)
          rwa [Real.norm_eq_abs] at h
        have h2 : u x - v x = U x - V x := by rw [hUu x hb, hVv x hb]
        have h3 := abs_le.mp h1
        rw [hΨin x hb, abs_le]
        refine ⟨by linarith [le_max_right (u x - v x - η) 0], ?_⟩
        rcases max_cases (u x - v x - η) 0 with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he]; linarith [h3.2]
        · rw [he]; exact hCb0
      · rw [hΨout x hb]
        simpa using hCb0
    have hmemtop : MemLp (fun x => Ψ x - c) ⊤ (volume.restrict (Metric.ball x₀ R)) := by
      refine memLp_top_of_bound
        (hΨmem.2.1.aestronglyMeasurable.sub aestronglyMeasurable_const) (Cb + |c|)
        (Filter.Eventually.of_forall (fun x => ?_))
      have h3 : |Ψ x - c| ≤ |Ψ x| + |c| := by
        have h := abs_add_le (Ψ x) (-c)
        simpa [sub_eq_add_neg, abs_neg] using h
      rw [Real.norm_eq_abs]
      linarith [hΨbd x]
    have hintX : Integrable (fun x => |Ψ x - c| ^ ((n:ℝ) / ((n:ℝ) - 1)))
        (volume.restrict (Metric.ball x₀ R)) := by
      have hmeme : MemLp (fun x => Ψ x - c) (ENNReal.ofReal ((n:ℝ) / ((n:ℝ) - 1)))
          (volume.restrict (Metric.ball x₀ R)) := hmemtop.mono_exponent le_top
      have h2 := hmeme.integrable_norm_rpow
        (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hexp) (by simp)
      rw [ENNReal.toReal_ofReal hexp.le] at h2
      simpa only [Real.norm_eq_abs] using h2
    have hΨc : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), Ψ x = c := by
      have hnn : (0 : EuclideanSpace ℝ (Fin n) → ℝ)
          ≤ᵐ[volume.restrict (Metric.ball x₀ R)]
            (fun x => |Ψ x - c| ^ ((n:ℝ) / ((n:ℝ) - 1))) :=
        Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (abs_nonneg _) _)
      filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hintX).mp hX0] with x hx
      have h2 : |Ψ x - c| ^ ((n:ℝ) / ((n:ℝ) - 1)) = 0 := hx
      have h3 : |Ψ x - c| = 0 := by
        by_contra hne
        have h4 := Real.rpow_pos_of_pos
          (lt_of_le_of_ne (abs_nonneg (Ψ x - c)) (Ne.symm hne)) ((n:ℝ) / ((n:ℝ) - 1))
        rw [h2] at h4
        exact absurd h4 (lt_irrefl 0)
      have h5 := abs_eq_zero.mp h3
      linarith
    -- The constant is `0`, because `φ_η` vanishes near the sphere.
    obtain ⟨Φ, hΦ⟩ : ∃ f, f = (fun x => max (U x - V x - η) 0) := ⟨_, rfl⟩
    have hΦcont : ContinuousOn Φ (Metric.ball x₀ R) := by
      rw [hΦ]
      exact (((hUc.sub hVc).sub continuousOn_const).sup continuousOn_const).mono
        Metric.ball_subset_closedBall
    have hΨΦ : ∀ x ∈ Metric.ball x₀ R, Ψ x = Φ x := by
      intro x hx
      simp only [hΦ]
      rw [hΨin x hx, hUu x hx, hVv x hx]
    have hΦc : ∀ x ∈ Metric.ball x₀ R, Φ x = c := by
      intro y hy
      by_contra hne
      have hopen : IsOpen (Metric.ball x₀ R ∩ Φ ⁻¹' {z : ℝ | z ≠ c}) :=
        hΦcont.isOpen_inter_preimage Metric.isOpen_ball isOpen_ne
      have hposm : 0 < volume (Metric.ball x₀ R ∩ Φ ⁻¹' {z : ℝ | z ≠ c}) :=
        hopen.measure_pos volume ⟨y, hy, hne⟩
      have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          x ∈ Metric.ball x₀ R → Φ x = c := by
        refine (ae_restrict_iff' hball_meas).mp ?_
        filter_upwards [hΨc, ae_restrict_mem hball_meas] with x h1 h2
        rw [← hΨΦ x h2]
        exact h1
      have hnull : volume (Metric.ball x₀ R ∩ Φ ⁻¹' {z : ℝ | z ≠ c}) = 0 := by
        refine measure_mono_null ?_ (ae_iff.mp hae)
        intro x hx
        simp only [Set.mem_ofPred_eq]
        intro hc2
        exact hx.2 (hc2 hx.1)
      rw [hnull] at hposm
      exact absurd hposm (lt_irrefl 0)
    have hc0 : c = 0 := by
      by_contra hcne
      have hsubK : Metric.ball x₀ R ⊆ K := by
        intro x hx
        refine hsupp ?_
        simp only [Set.mem_ofPred_eq]
        rw [hΨΦ x hx, hΦc x hx]
        exact hcne
      have hcl : Metric.closedBall x₀ R ⊆ Metric.ball x₀ R := by
        have h1 := hKclosed.closure_subset_iff.mpr hsubK
        rw [closure_ball x₀ hR.ne'] at h1
        exact h1.trans hKsub
      obtain ⟨xs, hxs⟩ := (NormedSpace.sphere_nonempty (x := x₀) (r := R)).mpr hR.le
      have h2 := hcl (Metric.sphere_subset_closedBall hxs)
      rw [Metric.mem_ball] at h2
      rw [Metric.mem_sphere] at hxs
      linarith
    -- (8): `u - v ≤ η` almost everywhere on `B_R`.
    filter_upwards [hΨc, ae_restrict_mem hball_meas] with x hx hmem
    rw [hΨin x hmem, hc0] at hx
    have h3 := le_max_left (u x - v x - η) 0
    rw [hx] at h3
    linarith
  -- Step 5: let `η ↓ 0`.
  have hall : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      ∀ j : ℕ, u x - v x ≤ 1 / ((j:ℝ) + 1) := by
    rw [ae_all_iff]
    intro j
    exact hmain (1 / ((j:ℝ) + 1)) (by positivity)
  filter_upwards [hall] with x hx
  have hlim : u x - v x ≤ 0 :=
    ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat hx
  linarith
