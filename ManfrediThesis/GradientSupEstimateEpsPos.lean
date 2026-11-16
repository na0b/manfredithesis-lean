import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.CaccioppoliPowerWeight
import ManfrediThesis.MoserLocalBoundedness
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.WeakGradientVectorComp
import ManfrediThesis.WeakGradientRestrict
open MeasureTheory

/-- Claim A of Theorem 1: the sup bound for `(ε + |∇u|²)^{p/2}` on `B_{ρ/2}` by
its mean on `B_ρ` in the nondegenerate case `ε > 0`, with a constant depending
only on `n`, `p` and the ratio bound `r`. -/
theorem GradientSupEstimateEpsPos :
    ∀ (n : ℕ) (p r : ℝ), 2 ≤ n → 1 < p → 0 < r →
      CitedSobolevPoincareBall n →
      (∀ (ε' γ₀' γ₁' : ℝ) (Ω' : Set (EuclideanSpace ℝ (Fin n)))
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → IsOpen Ω' → CitedRegularityEpsPos n p ε' γ₀' γ₁' Ω' A') →
      ∃ C : ℝ, 0 < C ∧
        ∀ (ε γ₀ γ₁ : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
          (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (y : EuclideanSpace ℝ (Fin n)) (ρ : ℝ),
          0 < ε → 0 < γ₀ → 0 < γ₁ → γ₁ ≤ r * γ₀ → IsOpen Ω → 0 < ρ →
          EllipticStructureQ12 n p ε γ₀ γ₁ Ω (fun _ _ h => A h) →
          IsWeakSolutionOn n p Ω (fun _ _ h => A h) (fun _ _ _ => 0) u g →
          Metric.closedBall y ρ ⊆ Ω →
          ∀ᵐ x ∂(volume.restrict (Metric.ball y (ρ / 2))),
            (ε + ‖g x‖ ^ 2) ^ (p / 2)
              ≤ C / ρ ^ (n : ℝ) * ∫ z in Metric.ball y ρ, (ε + ‖g z‖ ^ 2) ^ (p / 2) := by
  intro n p r hn hp hr hSP hC1
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hp0 : (0:ℝ) < p := by linarith
  -- Step 0: the constants, chosen before all the data
  obtain ⟨c, hc0, hCacc⟩ := CaccioppoliPowerWeight n p r hn hp hr
  obtain ⟨C₀, hC₀0, hMoser⟩ := MoserLocalBoundedness n c hn hc0 hSP
  refine ⟨C₀ ^ 2, by positivity, ?_⟩
  intro ε γ₀ γ₁ Ω A u g y ρ hε hγ₀ hγ₁ hγ₁r hΩ hρ hQ hsol hball
  have hballsub : Metric.ball y ρ ⊆ Ω :=
    subset_trans Metric.ball_subset_closedBall hball
  -- A1: what the cited regularity result supplies
  have hC1inst : CitedRegularityEpsPos n p ε γ₀ γ₁ Ω A := hC1 ε γ₀ γ₁ Ω A hγ₀ hγ₁ hΩ
  obtain ⟨-, ĝ, hĝcont, hĝae, Dĝ, hDĝ⟩ := hC1inst hε hQ u g hsol
  -- A2: the weight `w = ε + |ĝ|²` is positive everywhere and continuous on `Ω`
  have hw0 : ∀ x : EuclideanSpace ℝ (Fin n), (0:ℝ) < ε + ‖ĝ x‖ ^ 2 := fun x => by
    nlinarith [sq_nonneg ‖ĝ x‖]
  have hwcont : ContinuousOn (fun x => ε + ‖ĝ x‖ ^ 2) Ω :=
    continuousOn_const.add (hĝcont.norm.pow 2)
  have hvcont : ContinuousOn (fun x => (ε + ‖ĝ x‖ ^ 2) ^ (p / 4)) Ω :=
    hwcont.rpow_const fun x _ => Or.inl (ne_of_gt (hw0 x))
  have hnorm2 : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ^ 2 = ∑ k, (v k) ^ 2 := by
    intro v
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt
      (Finset.sum_nonneg fun k _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun k _ => by rw [Real.norm_eq_abs, sq_abs]
  have hnormsq : ∀ x : EuclideanSpace ℝ (Fin n), ‖ĝ x‖ ^ 2 = ∑ k, (ĝ x k) ^ 2 :=
    fun x => hnorm2 (ĝ x)
  have hcoord : ∀ (v : EuclideanSpace ℝ (Fin n)) (i : Fin n), |v i| ≤ ‖v‖ := by
    intro v i
    have h1 : (v i) ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [hnorm2 v]
      exact Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ i)
    nlinarith [abs_nonneg (v i), sq_abs (v i), h1, norm_nonneg v]
  have hsumapply : ∀ (i : Fin n) (F : Fin n → EuclideanSpace ℝ (Fin n)),
      (∑ k, F k) i = ∑ k, F k i := by
    intro i F
    exact map_sum (EuclideanSpace.proj (𝕜 := ℝ) i) F Finset.univ
  -- the family of fields, indexed by `θ` throughout (the `.tex`'s `G_θ`)
  obtain ⟨gvF, hgvFdef⟩ : ∃ gvF : ℝ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n), gvF = fun θ x =>
        ∑ k, (fderiv ℝ (fun z : Fin n → ℝ => (ε + ∑ j, (z j) ^ 2) ^ (p * θ / 4))
          (fun i => ĝ x i) (Pi.single k (1:ℝ))) • Dĝ k x := ⟨_, rfl⟩
  -- the derivative of the outer function, computed once
  have hFderiv : ∀ (θ : ℝ) (yv : Fin n → ℝ) (k : Fin n),
      fderiv ℝ (fun z : Fin n → ℝ => (ε + ∑ j, (z j) ^ 2) ^ (p * θ / 4)) yv
          (Pi.single k (1:ℝ))
        = (p * θ / 4) * (ε + ∑ j, (yv j) ^ 2) ^ (p * θ / 4 - 1) * (2 * yv k) := by
    intro θ yv k
    have hS : HasFDerivAt (fun z : Fin n → ℝ => ε + ∑ j, (z j) ^ 2)
        (∑ j, (2 * yv j) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) yv := by
      have h1 : ∀ j : Fin n, HasFDerivAt (fun z : Fin n → ℝ => (z j) ^ 2)
          ((2 * yv j) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) yv := by
        intro j
        have h2 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ)
          j).hasFDerivAt (x := yv)
        have h3 := h2.pow 2
        simpa using h3
      have h5 : HasFDerivAt (fun z : Fin n → ℝ => ∑ j, (z j) ^ 2)
          (∑ j, (2 * yv j) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) yv := by
        have hfun : (fun z : Fin n → ℝ => ∑ j, (z j) ^ 2)
            = ∑ j : Fin n, fun z : Fin n → ℝ => (z j) ^ 2 := by
          funext z
          simp [Finset.sum_apply]
        rw [hfun]
        exact HasFDerivAt.sum (fun j (_ : j ∈ Finset.univ) => h1 j)
      exact h5.const_add ε
    have hpos : (0:ℝ) < ε + ∑ j, (yv j) ^ 2 := by
      have h5 : (0:ℝ) ≤ ∑ j, (yv j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      linarith
    have hd : HasDerivAt (fun s : ℝ => s ^ (p * θ / 4))
        ((p * θ / 4) * (ε + ∑ j, (yv j) ^ 2) ^ (p * θ / 4 - 1))
        (ε + ∑ j, (yv j) ^ 2) :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hpos))
    have hcomp0 : HasFDerivAt ((fun s : ℝ => s ^ (p * θ / 4)) ∘
        (fun z : Fin n → ℝ => ε + ∑ j, (z j) ^ 2))
        (((p * θ / 4) * (ε + ∑ j, (yv j) ^ 2) ^ (p * θ / 4 - 1)) •
          (∑ j, (2 * yv j) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))) yv :=
      hd.comp_hasFDerivAt yv hS
    have hcomp : HasFDerivAt
        (fun z : Fin n → ℝ => (ε + ∑ j, (z j) ^ 2) ^ (p * θ / 4))
        (((p * θ / 4) * (ε + ∑ j, (yv j) ^ 2) ^ (p * θ / 4 - 1)) •
          (∑ j, (2 * yv j) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))) yv :=
      hcomp0
    rw [hcomp.fderiv]
    simp [Pi.single_apply]
  have hW1congr : ∀ (S : Set (EuclideanSpace ℝ (Fin n)))
      (f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ)
      (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      MeasurableSet S → (∀ᵐ x ∂(volume.restrict S), f₁ x = f₂ x) →
      MemW1pLocOn n 2 S f₁ G → MemW1pLocOn n 2 S f₂ G := by
    intro S f₁ f₂ G hS hae h
    refine ⟨?_, ?_⟩
    · intro φ hφ hcs hts i
      have heq : (∫ x in S, f₂ x * fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ)))
          = ∫ x in S, f₁ x * fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ)) := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with x hx
        show f₂ x * fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ))
          = f₁ x * fderiv ℝ φ x (EuclideanSpace.single i (1:ℝ))
        rw [hx]
      rw [heq]
      exact h.1 φ hφ hcs hts i
    · intro K hK hKS
      refine ⟨?_, (h.2 K hK hKS).2⟩
      refine MemLp.ae_eq ?_ (h.2 K hK hKS).1
      exact hae.filter_mono (ae_mono (Measure.restrict_mono hKS le_rfl))
  have hfderiv0 : ∀ (ζ : EuclideanSpace ℝ (Fin n) → ℝ)
      (x : EuclideanSpace ℝ (Fin n)), x ∉ tsupport ζ → fderiv ℝ ζ x = 0 := by
    intro ζ x hx
    have hopen : IsOpen (tsupport ζ)ᶜ := (isClosed_tsupport ζ).isOpen_compl
    have hev : ζ =ᶠ[nhds x] fun _ => (0:ℝ) := by
      filter_upwards [hopen.mem_nhds hx] with z hz
      exact image_eq_zero_of_notMem_tsupport hz
    rw [hev.fderiv_eq]
    simp
  have hrestrict : ∀ F : EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ x, x ∉ Metric.ball y ρ → F x = 0) →
      (∫ x in Ω, F x) = ∫ x in Metric.ball y ρ, F x := by
    intro F hF
    rw [← integral_indicator hΩ.measurableSet,
      ← integral_indicator measurableSet_ball]
    congr 1
    funext z
    by_cases hz : z ∈ Metric.ball y ρ
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hballsub hz)]
    · rw [Set.indicator_of_notMem hz]
      by_cases hz2 : z ∈ Ω
      · rw [Set.indicator_of_mem hz2, hF z hz]
      · rw [Set.indicator_of_notMem hz2]
  have hgDĝ : ∀ i : Fin n, MemW1pLocOn n 2 Ω (fun x => g x i) (Dĝ i) := by
    intro i
    refine hW1congr Ω (fun x => ĝ x i) (fun x => g x i) (Dĝ i)
      hΩ.measurableSet ?_ (hDĝ i)
    filter_upwards [hĝae] with x hx
    show ĝ x i = g x i
    rw [hx]
  -- A3: `v^θ = w^{pθ/4}` is a local `W^{1,2}` function on the ball
  have hA3 : ∀ θ : ℝ, 1 < θ →
      MemW1pLocOn n 2 (Metric.ball y ρ)
        (fun x => (ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 4)) (gvF θ) := by
    intro θ hθ
    have hbound : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω →
        ∃ L : ℝ, ∀ x ∈ K, ∀ j, |ĝ x j| ≤ L := by
      intro K hK hKΩ
      obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn (hĝcont.mono hKΩ)
      exact ⟨L, fun x hx j => le_trans (hcoord (ĝ x) j) (hL x hx)⟩
    have hFC1 : ContDiff ℝ 1
        (fun z : Fin n → ℝ => (ε + ∑ j, (z j) ^ 2) ^ (p * θ / 4)) := by
      have hinner : ContDiff ℝ 1 (fun z : Fin n → ℝ => ε + ∑ j, (z j) ^ 2) := by
        fun_prop
      refine hinner.rpow_const_of_ne fun z => ?_
      have hz : (0:ℝ) ≤ ∑ j, (z j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      exact ne_of_gt (by linarith)
    have hvc := WeakGradientVectorComp n n 2 hn1 (by norm_num) Ω
      (fun k x => ĝ x k) Dĝ
      (fun z : Fin n → ℝ => (ε + ∑ j, (z j) ^ 2) ^ (p * θ / 4)) hΩ hDĝ hbound hFC1
    have hvc2 : MemW1pLocOn n 2 Ω
        (fun x => (ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 4)) (gvF θ) := by
      have heq : (fun x : EuclideanSpace ℝ (Fin n) =>
            (ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 4))
          = fun x => (ε + ∑ j, (ĝ x j) ^ 2) ^ (p * θ / 4) := by
        funext x
        rw [hnormsq x]
      rw [heq, hgvFdef]
      exact hvc
    exact (WeakGradientRestrict n 2 hn1 (by norm_num) Ω (Metric.ball y ρ) _ _
      hΩ Metric.isOpen_ball hballsub).2.1 hvc2
  -- the squared norm of the field, in the shape `CaccioppoliPowerWeight` produces
  have hgvnorm : ∀ (θ : ℝ) (x : EuclideanSpace ℝ (Fin n)),
      ‖gvF θ x‖ ^ 2
        = (p * θ / 4) ^ 2 * (ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 2 - 2)
          * ∑ i, (2 * ∑ k, ĝ x k * Dĝ k x i) ^ 2 := by
    intro θ x
    have hgx : gvF θ x = ((p * θ / 4) * (ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 4 - 1))
        • (∑ k, (2 * ĝ x k) • Dĝ k x) := by
      simp only [hgvFdef, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hFderiv θ (fun i => ĝ x i) k, smul_smul, hnormsq x]
    have hV : ‖∑ k, (2 * ĝ x k) • Dĝ k x‖ ^ 2
        = ∑ i, (2 * ∑ k, ĝ x k * Dĝ k x i) ^ 2 := by
      rw [hnorm2]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsumapply i (fun k => (2 * ĝ x k) • Dĝ k x)]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      show (2 * ĝ x k) * Dĝ k x i = 2 * (ĝ x k * Dĝ k x i)
      ring
    have hpow : ((ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 4 - 1)) ^ 2
        = (ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 2 - 2) := by
      rw [← Real.rpow_natCast ((ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 4 - 1)) 2,
        ← Real.rpow_mul (hw0 x).le]
      congr 1
      push_cast
      ring
    rw [hgx, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hV, mul_pow, hpow]
  -- A4: the Caccioppoli inequality in the shape Moser's lemma consumes
  have hA4 : ∀ θ : ℝ, 1 < θ → ∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball y ρ →
      (∫ x in Metric.ball y ρ, ‖gvF θ x‖ ^ 2 * ζ x ^ 2)
        ≤ c * ∫ x in Metric.ball y ρ,
            ((ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 4)) ^ 2
              * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 := by
    intro θ hθ ζ hζ1 hζ2 hζ3
    have ht : (0:ℝ) < p * (θ - 1) := mul_pos hp0 (by linarith)
    have htsΩ : tsupport ζ ⊆ Ω := subset_trans hζ3 hballsub
    have hcac := hCacc ε γ₀ γ₁ (p * (θ - 1)) Ω A u g Dĝ ζ hε hγ₀ hγ₁r ht hΩ hQ
      hC1inst hsol hgDĝ hζ1 hζ2 htsΩ
    rw [show (p + p * (θ - 1)) / 4 = p * θ / 4 by ring,
      show (p + p * (θ - 1)) / 2 = p * θ / 2 by ring] at hcac
    -- the two integrands rewritten with the representative
    have hL : (∫ x in Ω, (p * θ / 4) ^ 2 * (ε + ‖g x‖ ^ 2) ^ (p * θ / 2 - 2)
          * (∑ i, (2 * ∑ k, g x k * Dĝ k x i) ^ 2) * ζ x ^ 2)
        = ∫ x in Ω, ‖gvF θ x‖ ^ 2 * ζ x ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hĝae] with x hx
      show (p * θ / 4) ^ 2 * (ε + ‖g x‖ ^ 2) ^ (p * θ / 2 - 2)
          * (∑ i, (2 * ∑ k, g x k * Dĝ k x i) ^ 2) * ζ x ^ 2
        = ‖gvF θ x‖ ^ 2 * ζ x ^ 2
      rw [hx, hgvnorm θ x]
    have hR : (∫ x in Ω, (ε + ‖g x‖ ^ 2) ^ (p * θ / 2)
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
        = ∫ x in Ω, ((ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 4)) ^ 2
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hĝae] with x hx
      show (ε + ‖g x‖ ^ 2) ^ (p * θ / 2)
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2
        = ((ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 4)) ^ 2
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2
      rw [hx]
      congr 1
      rw [← Real.rpow_natCast ((ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 4)) 2,
        ← Real.rpow_mul (hw0 x).le]
      congr 1
      push_cast
      ring
    rw [hL, hR] at hcac
    -- restrict both integrals from `Ω` to the ball
    have hLres : (∫ x in Ω, ‖gvF θ x‖ ^ 2 * ζ x ^ 2)
        = ∫ x in Metric.ball y ρ, ‖gvF θ x‖ ^ 2 * ζ x ^ 2 := by
      refine hrestrict _ fun x hx => ?_
      have hx' : x ∉ tsupport ζ := fun hc => hx (hζ3 hc)
      rw [image_eq_zero_of_notMem_tsupport hx']
      ring
    have hRres : (∫ x in Ω, ((ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 4)) ^ 2
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
        = ∫ x in Metric.ball y ρ, ((ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 4)) ^ 2
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 := by
      refine hrestrict _ fun x hx => ?_
      have hx' : x ∉ tsupport ζ := fun hc => hx (hζ3 hc)
      rw [hfderiv0 ζ x hx']
      simp
    rw [hLres, hRres] at hcac
    exact hcac
  -- A5: the truncation `ṽ = 1_{B_ρ(y)} v`
  obtain ⟨vt, hvtdef⟩ : ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
    f = (Metric.ball y ρ).indicator (fun x => (ε + ‖ĝ x‖ ^ 2) ^ (p / 4)) := ⟨_, rfl⟩
  have hvton : ∀ x ∈ Metric.ball y ρ, vt x = (ε + ‖ĝ x‖ ^ 2) ^ (p / 4) := by
    intro x hx
    rw [hvtdef]
    exact Set.indicator_of_mem hx _
  have hvtoff : ∀ x, x ∉ Metric.ball y ρ → vt x = 0 := by
    intro x hx
    rw [hvtdef]
    exact Set.indicator_of_notMem hx _
  have hvt0 : ∀ x, 0 ≤ vt x := by
    intro x
    by_cases hx : x ∈ Metric.ball y ρ
    · rw [hvton x hx]
      exact Real.rpow_nonneg (hw0 x).le _
    · rw [hvtoff x hx]
  have hvtpow : ∀ (θ : ℝ) (x : EuclideanSpace ℝ (Fin n)), x ∈ Metric.ball y ρ →
      vt x ^ θ = (ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 4) := by
    intro θ x hx
    rw [hvton x hx, ← Real.rpow_mul (hw0 x).le]
    congr 1
    ring
  -- A5(2): measurability
  have hvtmeas : Measurable vt := by
    refine measurable_of_Ioi fun a => ?_
    rcases lt_or_ge a 0 with ha | ha
    · have hset : vt ⁻¹' Set.Ioi a = Set.univ := by
        ext z
        simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
        exact lt_of_lt_of_le ha (hvt0 z)
      rw [hset]
      exact MeasurableSet.univ
    · have hset : vt ⁻¹' Set.Ioi a
          = Metric.ball y ρ ∩ (fun x => (ε + ‖ĝ x‖ ^ 2) ^ (p / 4)) ⁻¹' Set.Ioi a := by
        ext z
        constructor
        · intro hz
          have hz' : a < vt z := hz
          have hzb : z ∈ Metric.ball y ρ := by
            by_contra hc
            rw [hvtoff z hc] at hz'
            linarith
          refine ⟨hzb, ?_⟩
          show a < (ε + ‖ĝ z‖ ^ 2) ^ (p / 4)
          rw [← hvton z hzb]
          exact hz'
        · intro hz
          show a < vt z
          rw [hvton z hz.1]
          exact hz.2
      rw [hset]
      exact ((hvcont.mono hballsub).isOpen_inter_preimage Metric.isOpen_ball
        isOpen_Ioi).measurableSet
  -- A5(3): `ṽ²` is integrable on the ball
  have hfinm : IsFiniteMeasure (volume.restrict (Metric.ball y ρ)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  obtain ⟨M, hM⟩ := (isCompact_closedBall y ρ).exists_bound_of_continuousOn
    ((hvcont.mono hball).pow 2)
  have hvt2int : IntegrableOn (fun z => vt z ^ 2) (Metric.ball y ρ) volume := by
    refine Integrable.mono' (integrable_const M)
      (hvtmeas.pow_const 2).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_ball).2
      (Filter.Eventually.of_forall fun z hz => ?_)
    rw [hvton z hz]
    exact hM z (Metric.ball_subset_closedBall hz)
  -- A5(5): the powers, on the ball
  have hvtW : ∀ θ : ℝ, 1 < θ →
      MemW1pLocOn n 2 (Metric.ball y ρ) (fun x => vt x ^ θ) (gvF θ) := by
    intro θ hθ
    refine hW1congr (Metric.ball y ρ) (fun x => (ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 4))
      (fun x => vt x ^ θ) (gvF θ) measurableSet_ball ?_ (hA3 θ hθ)
    refine (ae_restrict_iff' measurableSet_ball).2
      (Filter.Eventually.of_forall fun x hx => ?_)
    rw [hvtpow θ x hx]
  -- A5(6): the Caccioppoli family, on the ball
  have hvtC : ∀ θ : ℝ, 1 < θ → ∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball y ρ →
      (∫ x in Metric.ball y ρ, ‖gvF θ x‖ ^ 2 * ζ x ^ 2)
        ≤ c * ∫ x in Metric.ball y ρ, (vt x ^ θ) ^ 2
            * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 := by
    intro θ hθ ζ hζ1 hζ2 hζ3
    have heq : (∫ x in Metric.ball y ρ, (vt x ^ θ) ^ 2
          * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2)
        = ∫ x in Metric.ball y ρ, ((ε + ‖ĝ x‖ ^ 2) ^ (p * θ / 4)) ^ 2
            * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1:ℝ))) ^ 2 := by
      refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
      rw [hvtpow θ x hx]
    rw [heq]
    exact hA4 θ hθ ζ hζ1 hζ2 hζ3
  -- A6: Moser's lemma
  have hA6 := hMoser y ρ vt gvF hρ hvtmeas hvt0 hvt2int hvtW hvtC
  -- A7: squaring, and the single passage back to the given field
  have hsub2 : Metric.ball y (ρ / 2) ⊆ Metric.ball y ρ :=
    Metric.ball_subset_ball (by linarith)
  have hĝae2 : ∀ᵐ x ∂(volume.restrict (Metric.ball y (ρ / 2))), g x = ĝ x :=
    ae_restrict_of_ae_restrict_of_subset
      (subset_trans hsub2 hballsub) hĝae
  have hIeq : (∫ z in Metric.ball y ρ, vt z ^ 2)
      = ∫ z in Metric.ball y ρ, (ε + ‖g z‖ ^ 2) ^ (p / 2) := by
    refine integral_congr_ae ?_
    have hae2 : ∀ᵐ z ∂(volume.restrict (Metric.ball y ρ)),
        z ∈ Metric.ball y ρ ∧ g z = ĝ z := by
      refine (ae_restrict_mem measurableSet_ball).and ?_
      exact ae_restrict_of_ae_restrict_of_subset hballsub hĝae
    filter_upwards [hae2] with z hz
    show vt z ^ 2 = (ε + ‖g z‖ ^ 2) ^ (p / 2)
    rw [hvton z hz.1, hz.2, ← Real.rpow_natCast ((ε + ‖ĝ z‖ ^ 2) ^ (p / 4)) 2,
      ← Real.rpow_mul (hw0 z).le]
    congr 1
    push_cast
    ring
  have hInn : (0:ℝ) ≤ ρ ^ (-(n : ℝ)) * ∫ z in Metric.ball y ρ, vt z ^ 2 := by
    refine mul_nonneg (Real.rpow_nonneg hρ.le _) ?_
    exact integral_nonneg fun z => sq_nonneg _
  have hρn : (0:ℝ) < ρ ^ (n : ℝ) := Real.rpow_pos_of_pos hρ _
  filter_upwards [hA6, hĝae2, ae_restrict_mem measurableSet_ball] with x hx hxg hxmem
  have hxb : x ∈ Metric.ball y ρ := hsub2 hxmem
  have hvx : vt x = (ε + ‖g x‖ ^ 2) ^ (p / 4) := by
    rw [hvton x hxb, hxg]
  have hsq : (ε + ‖g x‖ ^ 2) ^ (p / 2) = (vt x) ^ 2 := by
    rw [hvx, ← Real.rpow_natCast ((ε + ‖g x‖ ^ 2) ^ (p / 4)) 2,
      ← Real.rpow_mul (by nlinarith [sq_nonneg ‖g x‖] : (0:ℝ) ≤ ε + ‖g x‖ ^ 2)]
    congr 1
    push_cast
    ring
  rw [hsq]
  have hstep : (vt x) ^ 2
      ≤ (C₀ * (ρ ^ (-(n : ℝ)) * ∫ z in Metric.ball y ρ, vt z ^ 2) ^ (1/2 : ℝ)) ^ 2 := by
    refine pow_le_pow_left₀ (hvt0 x) hx 2
  refine le_trans hstep (le_of_eq ?_)
  rw [mul_pow, ← Real.rpow_natCast ((ρ ^ (-(n : ℝ))
      * ∫ z in Metric.ball y ρ, vt z ^ 2) ^ (1/2 : ℝ)) 2,
    ← Real.rpow_mul hInn]
  rw [show (1/2 : ℝ) * ((2:ℕ) : ℝ) = 1 by push_cast; ring, Real.rpow_one,
    hIeq, Real.rpow_neg hρ.le]
  field_simp
