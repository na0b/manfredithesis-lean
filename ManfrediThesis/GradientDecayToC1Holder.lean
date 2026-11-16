import ManfrediThesis.Preamble
import ManfrediThesis.MeanReplacementLpGeneral
import ManfrediThesis.IsBoundedLipschitzDomain
import ManfrediThesis.CampanatoBoundOn
import ManfrediThesis.MorreyBoundOn
import ManfrediThesis.MemHolderOn
import ManfrediThesis.MemC1HolderOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.CitedCampanatoEmbedding
import ManfrediThesis.WeakGradientRestrict
import ManfrediThesis.WeakGradientContinuousRep
open MeasureTheory

/-- The passage from the gradient's Campanato decay on small balls to the two
conclusions of Theorems 4 and 6: the componentwise Campanato bound for `∇u` on
`Ω'` at the exponent `n + lam₀`, and the `C^{1+lam₀/p}` representative of `u`.
The decay is the only thing the argument sees, so one node serves the
variational and the general setting alike; the constant is bound before the
data, as the dependency lists of Theorems 4 and 6 require. -/
theorem GradientDecayToC1Holder :
    ∀ (n : ℕ) (p lam₀ c₂₀ ρ₀ W : ℝ),
      2 ≤ n → 1 < p → 0 < lam₀ → lam₀ < p → 0 < c₂₀ → 0 < ρ₀ → ρ₀ ≤ 1 →
      0 ≤ W →
      ∃ N : ℝ, 0 ≤ N ∧
        ∀ (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          IsOpen Ω → IsOpen Ω' → closure Ω' ⊆ Ω →
          IsBoundedLipschitzDomain n Ω' →
          CitedCampanatoEmbedding n p Ω' →
          MemW1pOn n p Ω u g →
          (∫ x in Ω, ‖g x‖ ^ p) ≤ W ^ p →
          (∀ x₀ ∈ Ω', ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → Metric.ball x₀ ρ ⊆ Ω) →
          (∀ x₀ ∈ Ω', ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
            (∫ x in Metric.ball x₀ ρ,
                ‖g x - (volume (Metric.ball x₀ ρ)).toReal⁻¹
                  • ∫ y in Metric.ball x₀ ρ, g y‖ ^ p)
              ≤ c₂₀ * ρ ^ ((n : ℝ) + lam₀)) →
          (∀ i : Fin n,
              CampanatoBoundOn n p ((n : ℝ) + lam₀) Ω' (fun x => g x i) N)
            ∧ ∃ (w : EuclideanSpace ℝ (Fin n) → ℝ)
                (gw : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
                (∀ᵐ x ∂(volume.restrict Ω'), u x = w x) ∧
                  (∀ᵐ x ∂(volume.restrict Ω'), g x = gw x) ∧
                  MemC1HolderOn n (lam₀ / p) Ω' (closure Ω') w gw := by
  intro n p lam₀ c₂₀ ρ₀ W hn hp hlam0 hlamp hc20 hρ0 hρ1 hW
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnl : (0:ℝ) < (n:ℝ) + lam₀ := by linarith
  have hp1E : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hp.le
  have htoR : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  -- Step 1: the constant
  set K : ℝ := max c₂₀ (W ^ p * ρ₀ ^ (-((n:ℝ) + lam₀))) with hKdef
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le hc20 (le_max_left _ _)
  have hKp0 : (0:ℝ) < K ^ (1/p) := Real.rpow_pos_of_pos hK0 _
  refine ⟨2 * K ^ (1/p), by positivity, ?_⟩
  have hNp : (2 * K ^ (1/p)) ^ p = 2 ^ p * K := by
    rw [Real.mul_rpow (by norm_num) hKp0.le, ← Real.rpow_mul hK0.le,
      one_div_mul_cancel hp0.ne', Real.rpow_one]
  have h2p0 : (0:ℝ) < 2 ^ p := Real.rpow_pos_of_pos (by norm_num) _
  have h1a : 2 ^ p * c₂₀ ≤ (2 * K ^ (1/p)) ^ p := by
    rw [hNp]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) h2p0.le
  have h1b : 2 ^ p * (W ^ p * ρ₀ ^ (-((n:ℝ) + lam₀))) ≤ (2 * K ^ (1/p)) ^ p := by
    rw [hNp]; exact mul_le_mul_of_nonneg_left (le_max_right _ _) h2p0.le
  have hρinv : (1:ℝ) ≤ ρ₀ ^ (-((n:ℝ) + lam₀)) := by
    rw [show (1:ℝ) = ρ₀ ^ (0:ℝ) from (Real.rpow_zero ρ₀).symm]
    exact Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 (by linarith)
  have hWK : W ^ p ≤ K := by
    refine le_trans ?_ (le_max_right _ _)
    nlinarith [Real.rpow_nonneg hW p, hρinv]
  have hWN : W ≤ 2 * K ^ (1/p) := by
    have h1 : (W ^ p) ^ (1/p) ≤ K ^ (1/p) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hW _) hWK (by positivity)
    rw [← Real.rpow_mul hW, mul_one_div_cancel hp0.ne', Real.rpow_one] at h1
    nlinarith [hKp0]
  -- the mean-replacement inequality (M), for real-valued f
  have hM : ∀ (S : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (c : ℝ), 0 < volume S → volume S ≠ ⊤ →
      MemLp f (ENNReal.ofReal p) (volume.restrict S) →
      (∫ x in S, ‖f x - (volume S).toReal⁻¹ • ∫ y in S, f y‖ ^ p)
        ≤ 2 ^ p * ∫ x in S, ‖f x - c‖ ^ p :=
    fun S f c h1 h2 h3 => MeanReplacementLpGeneral n p S f c hp h1 h2 h3
  intro Ω Ω' u g hΩ hΩ' hclΩ' hLip hC5 hW1p hWbd hball hdecay
  have hΩ'Ω : Ω' ⊆ Ω := subset_trans subset_closure hclΩ'
  -- Step 2: the components of the gradient lie in L^p
  have hproj : ∀ i : Fin n, Continuous (fun v : EuclideanSpace ℝ (Fin n) => v i) :=
    fun i => (EuclideanSpace.proj i).continuous
  have hcoord : ∀ (v : EuclideanSpace ℝ (Fin n)) (i : Fin n), |v i| ≤ ‖v‖ := by
    intro v i
    have h1 : (v i) ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (f := fun m => (v m) ^ 2)
        (fun m _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith [abs_nonneg (v i), norm_nonneg v, sq_abs (v i)]
  have hofR0 : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero]
    linarith
  have hofRtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hgΩ : MemLp g (ENNReal.ofReal p) (volume.restrict Ω) := hW1p.2.2
  have hgsub : ∀ S : Set (EuclideanSpace ℝ (Fin n)), S ⊆ Ω →
      MemLp g (ENNReal.ofReal p) (volume.restrict S) :=
    fun S hS => hgΩ.mono_measure (Measure.restrict_mono hS le_rfl)
  have hcomp : ∀ (S : Set (EuclideanSpace ℝ (Fin n))), S ⊆ Ω → ∀ i : Fin n,
      MemLp (fun x => g x i) (ENNReal.ofReal p) (volume.restrict S) := by
    intro S hS i
    refine (hgsub S hS).mono ((hproj i).comp_aestronglyMeasurable (hgsub S hS).1) ?_
    filter_upwards with y
    simpa [Real.norm_eq_abs] using hcoord (g y) i
  have hgnorm : IntegrableOn (fun y => ‖g y‖ ^ p) Ω := by
    have h := hgΩ.integrable_norm_rpow hofR0 hofRtop
    rwa [htoR] at h
  -- Step 4: part (i)
  have hpi : ∀ i : Fin n, CampanatoBoundOn n p ((n : ℝ) + lam₀) Ω'
      (fun x => g x i) (2 * K ^ (1/p)) := by
    intro i
    refine ⟨hcomp Ω' hΩ'Ω i, ?_⟩
    intro x hx ρ hρ hdiam
    have hSmeas : MeasurableSet (Ω' ∩ Metric.ball x ρ) :=
      hΩ'.measurableSet.inter measurableSet_ball
    have hSsubΩ' : Ω' ∩ Metric.ball x ρ ⊆ Ω' := Set.inter_subset_left
    have hSsubB : Ω' ∩ Metric.ball x ρ ⊆ Metric.ball x ρ := Set.inter_subset_right
    have hSsubΩ : Ω' ∩ Metric.ball x ρ ⊆ Ω := hSsubΩ'.trans hΩ'Ω
    have hSfin : volume (Ω' ∩ Metric.ball x ρ) ≠ ⊤ :=
      ((measure_mono hSsubB).trans_lt measure_ball_lt_top).ne
    have hρl : (0:ℝ) ≤ ρ ^ ((n:ℝ) + lam₀) := Real.rpow_nonneg hρ.le _
    have hBfinm : IsFiniteMeasure (volume.restrict (Metric.ball x ρ)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have hSfinm : IsFiniteMeasure (volume.restrict (Ω' ∩ Metric.ball x ρ)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hSfin⟩
    rcases eq_or_ne (volume (Ω' ∩ Metric.ball x ρ)) 0 with hS0z | hS0ne
    · rw [setIntegral_measure_zero _ hS0z]
      have : (0:ℝ) ≤ (2 * K ^ (1/p)) ^ p := Real.rpow_nonneg (by positivity) _
      exact mul_nonneg this hρl
    · have hS0 : 0 < volume (Ω' ∩ Metric.ball x ρ) := zero_lt_iff.mpr hS0ne
      have hfS : MemLp (fun y => g y i) (ENNReal.ofReal p)
          (volume.restrict (Ω' ∩ Metric.ball x ρ)) := hcomp _ hSsubΩ i
      by_cases hcase : ρ ≤ ρ₀
      · -- the small-radius regime: the decay hypothesis
        have hBsubΩ : Metric.ball x ρ ⊆ Ω := hball x hx ρ hρ hcase
        set m : EuclideanSpace ℝ (Fin n) :=
          (volume (Metric.ball x ρ)).toReal⁻¹ • ∫ y in Metric.ball x ρ, g y with hmdef
        have hMS := hM (Ω' ∩ Metric.ball x ρ) (fun y => g y i) (m i) hS0 hSfin hfS
        simp only [Real.norm_eq_abs, smul_eq_mul] at hMS
        refine le_trans hMS ?_
        have hgB : MemLp (fun y => g y - m) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x ρ)) := (hgsub _ hBsubΩ).sub (memLp_const m)
        have hBint : IntegrableOn (fun y => ‖g y - m‖ ^ p) (Metric.ball x ρ) := by
          have h := hgB.integrable_norm_rpow hofR0 hofRtop
          rwa [htoR] at h
        have hSint : IntegrableOn (fun y => ‖g y - m‖ ^ p) (Ω' ∩ Metric.ball x ρ) :=
          hBint.mono_set hSsubB
        have hdom : ∀ y, |g y i - m i| ^ p ≤ ‖g y - m‖ ^ p := by
          intro y
          refine Real.rpow_le_rpow (abs_nonneg _) ?_ hp0.le
          simpa using hcoord (g y - m) i
        have hci : MemLp (fun y => g y i - m i) (ENNReal.ofReal p)
            (volume.restrict (Ω' ∩ Metric.ball x ρ)) :=
          (hcomp _ hSsubΩ i).sub (memLp_const (m i))
        have hSintc : IntegrableOn (fun y => |g y i - m i| ^ p) (Ω' ∩ Metric.ball x ρ) := by
          have h := hci.integrable_norm_rpow hofR0 hofRtop
          rw [htoR] at h
          simp only [Real.norm_eq_abs] at h
          exact h
        have hstep1 : (∫ y in Ω' ∩ Metric.ball x ρ, |g y i - m i| ^ p)
            ≤ ∫ y in Ω' ∩ Metric.ball x ρ, ‖g y - m‖ ^ p :=
          integral_mono_ae hSintc hSint (Filter.Eventually.of_forall hdom)
        have hstep2 : (∫ y in Ω' ∩ Metric.ball x ρ, ‖g y - m‖ ^ p)
            ≤ ∫ y in Metric.ball x ρ, ‖g y - m‖ ^ p := by
          refine setIntegral_mono_set hBint ?_ (Filter.Eventually.of_forall hSsubB)
          filter_upwards with y using Real.rpow_nonneg (norm_nonneg _) _
        have hstep3 := hdecay x hx ρ hρ hcase
        have hchain : (∫ y in Ω' ∩ Metric.ball x ρ, |g y i - m i| ^ p)
            ≤ c₂₀ * ρ ^ ((n:ℝ) + lam₀) := by
          rw [hmdef] at hstep1 hstep2 ⊢
          linarith [hstep1, hstep2, hstep3]
        calc 2 ^ p * ∫ y in Ω' ∩ Metric.ball x ρ, |g y i - m i| ^ p
            ≤ 2 ^ p * (c₂₀ * ρ ^ ((n:ℝ) + lam₀)) :=
              mul_le_mul_of_nonneg_left hchain h2p0.le
          _ = (2 ^ p * c₂₀) * ρ ^ ((n:ℝ) + lam₀) := by ring
          _ ≤ (2 * K ^ (1/p)) ^ p * ρ ^ ((n:ℝ) + lam₀) :=
              mul_le_mul_of_nonneg_right h1a hρl
      · -- the large-radius regime: the W^{1,p} bound
        rw [not_le] at hcase
        have hMS := hM (Ω' ∩ Metric.ball x ρ) (fun y => g y i) 0 hS0 hSfin hfS
        simp only [Real.norm_eq_abs, smul_eq_mul, sub_zero] at hMS
        refine le_trans hMS ?_
        have hSintc : IntegrableOn (fun y => |g y i| ^ p) (Ω' ∩ Metric.ball x ρ) := by
          have h := (hcomp _ hSsubΩ i).integrable_norm_rpow hofR0 hofRtop
          rw [htoR] at h
          simp only [Real.norm_eq_abs] at h
          exact h
        have hSintn : IntegrableOn (fun y => ‖g y‖ ^ p) (Ω' ∩ Metric.ball x ρ) :=
          hgnorm.mono_set hSsubΩ
        have hstep1 : (∫ y in Ω' ∩ Metric.ball x ρ, |g y i| ^ p)
            ≤ ∫ y in Ω' ∩ Metric.ball x ρ, ‖g y‖ ^ p := by
          refine integral_mono_ae hSintc hSintn ?_
          filter_upwards with y
          exact Real.rpow_le_rpow (abs_nonneg _) (hcoord (g y) i) hp0.le
        have hstep2 : (∫ y in Ω' ∩ Metric.ball x ρ, ‖g y‖ ^ p) ≤ ∫ y in Ω, ‖g y‖ ^ p := by
          refine setIntegral_mono_set hgnorm ?_ (Filter.Eventually.of_forall hSsubΩ)
          filter_upwards with y using Real.rpow_nonneg (norm_nonneg _) _
        have hWp : (∫ y in Ω' ∩ Metric.ball x ρ, |g y i| ^ p) ≤ W ^ p := by
          linarith [hstep1, hstep2, hWbd]
        have hratio : W ^ p ≤ W ^ p * ρ₀ ^ (-((n:ℝ) + lam₀)) * ρ ^ ((n:ℝ) + lam₀) := by
          have hone : (1:ℝ) ≤ ρ₀ ^ (-((n:ℝ) + lam₀)) * ρ ^ ((n:ℝ) + lam₀) := by
            have h1 : ρ₀ ^ ((n:ℝ) + lam₀) ≤ ρ ^ ((n:ℝ) + lam₀) :=
              Real.rpow_le_rpow hρ0.le hcase.le hnl.le
            have h2 : ρ₀ ^ (-((n:ℝ) + lam₀)) * ρ₀ ^ ((n:ℝ) + lam₀) = 1 := by
              rw [← Real.rpow_add hρ0]; simp
            have h3 : (0:ℝ) < ρ₀ ^ (-((n:ℝ) + lam₀)) := Real.rpow_pos_of_pos hρ0 _
            nlinarith [h1, h2, h3]
          nlinarith [Real.rpow_nonneg hW p, hone]
        calc 2 ^ p * ∫ y in Ω' ∩ Metric.ball x ρ, |g y i| ^ p
            ≤ 2 ^ p * (W ^ p * ρ₀ ^ (-((n:ℝ) + lam₀)) * ρ ^ ((n:ℝ) + lam₀)) :=
              mul_le_mul_of_nonneg_left (le_trans hWp hratio) h2p0.le
          _ = (2 ^ p * (W ^ p * ρ₀ ^ (-((n:ℝ) + lam₀)))) * ρ ^ ((n:ℝ) + lam₀) := by ring
          _ ≤ (2 * K ^ (1/p)) ^ p * ρ ^ ((n:ℝ) + lam₀) :=
              mul_le_mul_of_nonneg_right h1b hρl
  refine ⟨hpi, ?_⟩
  -- Step 5: the (C5) step
  have hWNp : W ^ p ≤ (2 * K ^ (1/p)) ^ p :=
    Real.rpow_le_rpow hW hWN hp0.le
  have hmorrey : ∀ i : Fin n, MorreyBoundOn n p 0 Ω' (fun x => g x i) (2 * K ^ (1/p)) := by
    intro i
    refine ⟨hcomp Ω' hΩ'Ω i, ?_⟩
    intro x hx ρ hρ hdiam
    have hSsubΩ' : Ω' ∩ Metric.ball x ρ ⊆ Ω' := Set.inter_subset_left
    have hSsubΩ : Ω' ∩ Metric.ball x ρ ⊆ Ω := hSsubΩ'.trans hΩ'Ω
    have hSintc : IntegrableOn (fun y => |g y i| ^ p) (Ω' ∩ Metric.ball x ρ) := by
      have h := (hcomp _ hSsubΩ i).integrable_norm_rpow hofR0 hofRtop
      rw [htoR] at h
      simp only [Real.norm_eq_abs] at h
      exact h
    have hSintn : IntegrableOn (fun y => ‖g y‖ ^ p) (Ω' ∩ Metric.ball x ρ) :=
      hgnorm.mono_set hSsubΩ
    have hstep1 : (∫ y in Ω' ∩ Metric.ball x ρ, |g y i| ^ p)
        ≤ ∫ y in Ω' ∩ Metric.ball x ρ, ‖g y‖ ^ p := by
      refine integral_mono_ae hSintc hSintn ?_
      filter_upwards with y
      exact Real.rpow_le_rpow (abs_nonneg _) (hcoord (g y) i) hp0.le
    have hstep2 : (∫ y in Ω' ∩ Metric.ball x ρ, ‖g y‖ ^ p) ≤ ∫ y in Ω, ‖g y‖ ^ p := by
      refine setIntegral_mono_set hgnorm ?_ (Filter.Eventually.of_forall hSsubΩ)
      filter_upwards with y using Real.rpow_nonneg (norm_nonneg _) _
    rw [Real.rpow_zero, mul_one]
    linarith [hstep1, hstep2, hWbd, hWNp]
  have hlamn : (n:ℝ) < (n:ℝ) + lam₀ := by linarith
  have hlamnp : (n:ℝ) + lam₀ < (n:ℝ) + p := by linarith
  obtain ⟨Nh, hNh0, hNh⟩ :=
    hC5 hLip ((n:ℝ) + lam₀) hlamn hlamnp (2 * K ^ (1/p)) (by positivity)
  have hβ : ((n:ℝ) + lam₀ - (n:ℝ))/p = lam₀/p := by ring_nf
  have hw : ∀ i : Fin n, ∃ wi : EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ᵐ y ∂(volume.restrict Ω'), g y i = wi y) ∧
        MemHolderOn n (lam₀/p) (closure Ω') wi ∧
        (∀ a ∈ closure Ω', ∀ b ∈ closure Ω',
          |wi a - wi b| ≤ Nh * dist a b ^ (lam₀/p)) := by
    intro i
    obtain ⟨wi, h1, h2, h3⟩ := hNh (fun y => g y i) (hpi i) (hmorrey i)
    rw [hβ] at h2 h3
    exact ⟨wi, h1, h2, h3⟩
  choose wf hwae hwhol hwbd using hw
  -- the vector field assembled from the components
  set gw : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun y => WithLp.toLp 2 (fun i => wf i y) with hgwdef
  have hgwapp : ∀ (y : EuclideanSpace ℝ (Fin n)) (i : Fin n), gw y i = wf i y := by
    intro y i; rfl
  have hgae : ∀ᵐ y ∂(volume.restrict Ω'), g y = gw y := by
    have hall : ∀ᵐ y ∂(volume.restrict Ω'), ∀ i : Fin n, g y i = wf i y :=
      (ae_all_iff).2 hwae
    filter_upwards [hall] with y hy
    refine PiLp.ext ?_
    intro i
    rw [hgwapp y i]
    exact hy i
  have hgwcont : ContinuousOn gw (closure Ω') := by
    have hpi' : ContinuousOn (fun y => (fun i => wf i y)) (closure Ω') :=
      continuousOn_pi.2 (fun i => (hwhol i).1)
    have h := ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin n => ℝ)).symm.continuous).comp_continuousOn hpi'
    simpa [hgwdef, Function.comp_def] using h
  -- the √n Hölder bound for the assembled field
  have hsq : ∀ a ∈ closure Ω', ∀ b ∈ closure Ω',
      ‖gw a - gw b‖ ≤ Real.sqrt (n:ℝ) * Nh * dist a b ^ (lam₀/p) := by
    intro a ha b hb
    have hB0 : (0:ℝ) ≤ Nh * dist a b ^ (lam₀/p) :=
      mul_nonneg hNh0 (Real.rpow_nonneg dist_nonneg _)
    have hcc : ∀ i : Fin n,
        ((gw a - gw b) i) ^ 2 ≤ (Nh * dist a b ^ (lam₀/p)) ^ 2 := by
      intro i
      have h1 : |gw a i - gw b i| ≤ Nh * dist a b ^ (lam₀/p) := by
        rw [hgwapp a i, hgwapp b i]; exact hwbd i a ha b hb
      have h2 : ((gw a - gw b) i) = gw a i - gw b i := rfl
      rw [h2]
      nlinarith [abs_nonneg (gw a i - gw b i), sq_abs (gw a i - gw b i), h1, hB0]
    have h3 : ‖gw a - gw b‖ ^ 2 ≤ (n:ℝ) * (Nh * dist a b ^ (lam₀/p)) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc ∑ i, ((gw a - gw b) i) ^ 2
          ≤ ∑ _i : Fin n, (Nh * dist a b ^ (lam₀/p)) ^ 2 :=
            Finset.sum_le_sum (fun i _ => hcc i)
        _ = (n:ℝ) * (Nh * dist a b ^ (lam₀/p)) ^ 2 := by
            simp [Finset.sum_const]
    have h4 : ‖gw a - gw b‖ ≤ Real.sqrt ((n:ℝ) * (Nh * dist a b ^ (lam₀/p)) ^ 2) := by
      rw [show ‖gw a - gw b‖ = Real.sqrt (‖gw a - gw b‖ ^ 2) from
        (Real.sqrt_sq (norm_nonneg _)).symm]
      exact Real.sqrt_le_sqrt h3
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hB0] at h4
    calc ‖gw a - gw b‖ ≤ Real.sqrt (n:ℝ) * (Nh * dist a b ^ (lam₀/p)) := h4
      _ = Real.sqrt (n:ℝ) * Nh * dist a b ^ (lam₀/p) := by ring
  -- Step 6: the differentiable representative
  have hp1R : (1:ℝ) ≤ p := hp.le
  have hres1 := (WeakGradientRestrict n p hn1 hp1R Ω Ω' u g hΩ hΩ' hΩ'Ω).1 hW1p
  have hres2 :=
    (WeakGradientRestrict n p hn1 hp1R Ω' Ω' u g hΩ' hΩ' (subset_refl Ω')).2.2.1 hres1
  obtain ⟨w, hwu, hwd⟩ :=
    WeakGradientContinuousRep n p hn1 hp1R Ω' u g gw hΩ' hres2
      (hgwcont.mono subset_closure) hgae
  exact ⟨w, gw, hwu, hgae, hwd, hgwcont,
    Real.sqrt (n:ℝ) * Nh, by positivity, hsq⟩
