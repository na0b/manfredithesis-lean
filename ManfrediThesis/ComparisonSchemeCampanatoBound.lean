import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MorreyBoundOn
import ManfrediThesis.CampanatoBoundOn
import ManfrediThesis.MorreyGradientToCampanato
import ManfrediThesis.MorreyBoundFromBundle
import ManfrediThesis.MeanReplacementLp
import ManfrediThesis.CitedSobolevPoincareBall
import ManfrediThesis.WeakGradientRestrict
set_option maxHeartbeats 1600000
open MeasureTheory

/-- The Campanato half of the abstract comparison scheme: under the scheme's
hypotheses, for every exponent `t` in `(0, n)` there is a constant `N`,
depending on the data but not on `ε`, `Ω`, `u` or `g`, bounding the Campanato
quantity of `u` on the inner domain `Ω'` at the exponent
`n + (1 - t/p)·q`, where `q = n/(n-1)`.

Conventions, restated here because a helper inherits none of its parent's.
`Ω' ⊂⊂ Ω'' ⊂⊂ Ω` are the three open sets of the scheme, separated at distance
`d`; `M` bounds `|u|` almost everywhere on `Ω`, `W` bounds the `L^p` energy of
`(u, g)` on `Ω`, `c₀` is the decay constant of (4.11) for the comparison maps
and `σ₂` their remainder modulus, with `σ₂` continuous, monotone, vanishing at
`0` and nonnegative; `R₁` is the radius up to which the comparison hypothesis is
available.  All powers of positive reals are real powers, and the weight
`(ε + ‖g_v‖²)^{p/2}` is written exactly as the comparison hypothesis prints it.
`q = n/(n-1)` throughout, and `CampanatoBoundOn`/`MorreyBoundOn` are the
tablet's own predicates.  The exponent `t` is quantified inside the conclusion
precisely because the consumer needs the bound at two different exponents, and
`N` is allowed to depend on `t`.

The proof is the Campanato half of the scheme's argument, run at the given `t`.
The Morrey bound for `‖g‖` at that exponent comes from
\noderef{MorreyBoundFromBundle}; the Poincaré-type step converts it into a
bound for the mean oscillation of `u` on balls, through the scalar
mean-replacement inequality and \noderef{MeanReplacementLp}; and the two
regimes of radii --- small radii, where the comparison hypothesis applies, and
large radii, where the global energy bound `W` and the measure bound `M`
suffice --- are combined by taking the maximum of the two constants, which is
why the resulting `N` is a maximum and is nonnegative by construction. -/
theorem ComparisonSchemeCampanatoBound :
    ∀ (n : ℕ) (p c₀ W M d R₁ : ℝ) (σ₂ : ℝ → ℝ),
      2 ≤ n → 1 < p → 0 < c₀ → 0 ≤ W → 0 ≤ M → 0 < d →
      0 < R₁ → Continuous σ₂ → Monotone σ₂ → σ₂ 0 = 0 → (∀ t : ℝ, 0 ≤ σ₂ t) →
      CitedSobolevPoincareBall n →
      ∀ t : ℝ, 0 < t → t < (n:ℝ) →
      ∃ N : ℝ, 0 ≤ N ∧
      ∀ (ε : ℝ) (Ω Ω'' Ω' : Set (EuclideanSpace ℝ (Fin n)))
      (u : EuclideanSpace ℝ (Fin n) → ℝ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      0 ≤ ε → ε ≤ 1 → IsOpen Ω → IsOpen Ω'' → IsOpen Ω' → Ω'.Nonempty →
      Bornology.IsBounded Ω'' → closure Ω' ⊆ Ω'' → closure Ω'' ⊆ Ω →
      (∀ x ∈ Ω', ∀ y, y ∉ Ω'' → d ≤ dist x y) →
      (∀ x ∈ Ω'', ∀ y, y ∉ Ω → d ≤ dist x y) →
      MemW1pOn n p Ω u g →
      (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
      ((∫ x in Ω, |u x| ^ p) + ∫ x in Ω, ‖g x‖ ^ p) ≤ W ^ p →
      (∀ x₀ ∈ Ω'', ∀ R : ℝ, 0 < R → R ≤ R₁ → Metric.closedBall x₀ R ⊆ Ω →
      ∃ (v : EuclideanSpace ℝ (Fin n) → ℝ)
      (gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      MemW1pOn n p (Metric.ball x₀ R) v gv ∧
      (∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      (∫ x in Metric.ball x₀ ρ, (ε + ‖gv x‖ ^ 2) ^ (p / 2))
      ≤ c₀ * (ρ / R) ^ (n : ℝ)
      * ∫ x in Metric.ball x₀ R, (ε + ‖gv x‖ ^ 2) ^ (p / 2)) ∧
      (∫ x in Metric.ball x₀ R, ‖g x - gv x‖ ^ p)
      ≤ σ₂ R * ∫ x in Metric.ball x₀ R, (1 + ‖g x‖ ^ 2) ^ (p / 2)) →
      CampanatoBoundOn n ((n : ℝ) / ((n : ℝ) - 1))
      ((n : ℝ) + (1 - t / p) * ((n : ℝ) / ((n : ℝ) - 1))) Ω' u N := by
  intro n p c₀ W M d R₁ σ₂ hn hp hc₀ hW hM hd hR₁ hσc hσm hσ0 hσnn hSP
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  set q : ℝ := (n:ℝ) / ((n:ℝ) - 1) with hqdef
  have hq1 : (1:ℝ) < q := by
    rw [hqdef, lt_div_iff₀ (by linarith)]; linarith
  have hq0 : (0:ℝ) < q := lt_trans one_pos hq1
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hnpos⟩ (1:ℝ) with hedef
  have he : ‖e‖ = 1 := by rw [hedef]; simp
  -- the scalar form of the mean-replacement inequality
  have hMscal : ∀ (s : Set (EuclideanSpace ℝ (Fin n)))
      (h : EuclideanSpace ℝ (Fin n) → ℝ) (c : ℝ),
      MeasurableSet s → 0 < volume s → volume s ≠ ⊤ →
      MemLp h (ENNReal.ofReal q) (volume.restrict s) →
      (∫ x in s, |h x - (volume s).toReal⁻¹ * ∫ y in s, h y| ^ q)
        ≤ 2 ^ q * ∫ x in s, |h x - c| ^ q := by
    intro s h c hsm hs0 hsfin hmem
    have hmem' : MemLp (fun x => h x • e) (ENNReal.ofReal q) (volume.restrict s) := by
      refine hmem.mono (hmem.1.smul_const e) (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_smul, he, mul_one]
    have hmr := MeanReplacementLp n q s (fun x => h x • e) (c • e) hq1 hsm hs0 hsfin hmem'
    rw [integral_smul_const] at hmr
    have hL : ∀ x : EuclideanSpace ℝ (Fin n),
        ‖h x • e - (volume s).toReal⁻¹ • ((∫ y in s, h y) • e)‖
          = |h x - (volume s).toReal⁻¹ * ∫ y in s, h y| := by
      intro x
      rw [smul_smul, ← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs]
    have hR : ∀ x : EuclideanSpace ℝ (Fin n), ‖h x • e - c • e‖ = |h x - c| := by
      intro x
      rw [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs]
    simp only [hL, hR] at hmr
    exact hmr
  intro t ht0 htn
  obtain ⟨N₁t, hN₁t0, hmorreyt⟩ :=
    MorreyBoundFromBundle n p t c₀ W d R₁ σ₂ hn hp ht0 htn hc₀ hW hd hR₁ hσc hσm hσ0 hσnn
  have hntriv : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, e, ?_⟩⟩
    intro hcon
    have h := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w ⟨0, hnpos⟩) hcon
    rw [hedef] at h
    simp at h
  set ωn : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal with hωdef
  have hω : 0 < ωn := by
    rw [hωdef]
    refine ENNReal.toReal_pos (ne_of_gt ?_) measure_ball_lt_top.ne
    exact Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self one_pos⟩
  have hballvol : ∀ (y : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 ≤ r →
      (volume (Metric.ball y r)).toReal = ωn * r ^ ((n:ℝ)) := by
    intro y r hr
    rw [Measure.addHaar_ball volume y hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hr _),
      show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n by simp, ← hωdef,
      ← Real.rpow_natCast r n]
    ring
  -- the Campanato exponent and its positivity
  set θ : ℝ := (n:ℝ) + (1 - t/p) * q with hθdef
  have hn1ne : (n:ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hnq : (n:ℝ) + q = (n:ℝ) * q := by
    rw [hqdef]
    field_simp
    ring
  have hθeq : θ = (n:ℝ) + q - t * q / p := by
    rw [hθdef]
    field_simp
    ring
  have hθ0 : 0 < θ := by
    have h1 : t * q / p < (n:ℝ) * q / p :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_right htn hq0) hp0
    have h2 : (n:ℝ) * q / p < (n:ℝ) * q :=
      div_lt_self (mul_pos (by linarith) hq0) hp
    rw [hθeq]
    linarith
  -- the constant handed to Lemma 4.2
  set Nflat : ℝ := max N₁t (M * ωn ^ (1/q) * (d/4) ^ ((n:ℝ)/q)) with hNflatdef
  have hNflat0 : 0 ≤ Nflat := le_trans hN₁t0 (le_max_left _ _)
  obtain ⟨N', hN'0, hMGC⟩ :=
    MorreyGradientToCampanato n p t Nflat (d/8) hn hp ht0 htn.le hNflat0 (by linarith) hSP
  -- the large-radius constant, valid in both exponent regimes
  set K1 : ℝ := M ^ (max (q - p) 0) * W ^ (min p q) * (d/8) ^ (-θ) with hK1def
  set K2 : ℝ := W ^ q * ωn ^ (max (1 - q/p) 0)
    * (d/8) ^ ((n:ℝ) * (max (1 - q/p) 0) - θ) with hK2def
  have hd8 : (0:ℝ) < d/8 := by linarith
  have hK10 : 0 ≤ K1 := by
    rw [hK1def]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hM _) (Real.rpow_nonneg hW _))
      (Real.rpow_nonneg hd8.le _)
  set KL : ℝ := max K1 K2 with hKLdef
  set Nbig : ℝ := max (2 * N') ((2 ^ q * KL) ^ (1/q)) with hNbigdef
  have hNbig0 : 0 ≤ Nbig := le_trans (by linarith) (le_max_left _ _)
  refine ⟨Nbig, hNbig0, ?_⟩
  intro ε Ω Ω'' Ω' u g hε0 hε1 hΩ hΩ'' hΩ' hΩ'ne hbdd hclΩ' hclΩ'' hsep1 hsep2
    hu hMb hWb hbundle
  have hsubP : Ω' ⊆ Ω'' := subset_trans subset_closure hclΩ'
  have hΩ''ΩP : Ω'' ⊆ Ω := subset_trans subset_closure hclΩ''
  have hΩ'Ω : Ω' ⊆ Ω := subset_trans hsubP hΩ''ΩP
  have hpne0 : (ENNReal.ofReal p) ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have hpnet : (ENNReal.ofReal p) ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  have htoRp : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hcq : Continuous fun z : ℝ => z ^ q :=
    continuous_iff_continuousAt.mpr fun z => Real.continuousAt_rpow_const z q (Or.inr hq0.le)
  -- |u|^p is integrable on Ω with integral at most W^p
  have hupΩ : IntegrableOn (fun y => |u y| ^ p) Ω volume := by
    have h := (hu.2.1).integrable_norm_rpow hpne0 hpnet
    rw [htoRp] at h
    exact MeasureTheory.IntegrableOn.congr_fun h
      (fun y _ => by rw [Real.norm_eq_abs]) hΩ.measurableSet
  have hupW : (∫ y in Ω, |u y| ^ p) ≤ W ^ p := by
    have h0 : (0:ℝ) ≤ ∫ y in Ω, ‖g y‖ ^ p :=
      integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) _
    linarith
  -- Ω' is of finite measure
  obtain ⟨rB, _hrB, hBall⟩ := (hbdd.subset hsubP).subset_closedBall_lt 0 0
  have hΩ'fin : volume Ω' ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hBall)
  have hfinΩ' : IsFiniteMeasure (volume.restrict Ω') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hΩ'fin⟩
  have humΩ' : AEStronglyMeasurable u (volume.restrict Ω') :=
    (hu.2.1).aestronglyMeasurable.mono_measure (Measure.restrict_mono hΩ'Ω le_rfl)
  have hMbΩ' : ∀ᵐ y ∂(volume.restrict Ω'), ‖u y‖ ≤ M := by
    have h0 := hMb.filter_mono (ae_mono (Measure.restrict_mono hΩ'Ω le_rfl))
    filter_upwards [h0] with y hy
    rwa [Real.norm_eq_abs]
  refine ⟨MemLp.of_bound humΩ' M hMbΩ', ?_⟩
  intro x₁ hx₁ ρ hρ hρd
  set S : Set (EuclideanSpace ℝ (Fin n)) := Ω' ∩ Metric.ball x₁ ρ with hSdef
  have hSmeas : MeasurableSet S := hΩ'.measurableSet.inter measurableSet_ball
  have hSopen : IsOpen S := hΩ'.inter Metric.isOpen_ball
  have hS0 : 0 < volume S :=
    hSopen.measure_pos volume ⟨x₁, hx₁, Metric.mem_ball_self hρ⟩
  have hSΩ' : S ⊆ Ω' := Set.inter_subset_left
  have hSball : S ⊆ Metric.ball x₁ ρ := Set.inter_subset_right
  have hSΩ : S ⊆ Ω := subset_trans hSΩ' hΩ'Ω
  have hSfin : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top hΩ'fin (measure_mono hSΩ')
  have hfinS : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hSfin⟩
  have humS : AEStronglyMeasurable u (volume.restrict S) :=
    (hu.2.1).aestronglyMeasurable.mono_measure (Measure.restrict_mono hSΩ le_rfl)
  have hMbS : ∀ᵐ y ∂(volume.restrict S), |u y| ≤ M := by
    have h0 := hMb.filter_mono (ae_mono (Measure.restrict_mono hSΩ le_rfl))
    exact h0
  have hMemS : MemLp u (ENNReal.ofReal q) (volume.restrict S) :=
    MemLp.of_bound humS M (by filter_upwards [hMbS] with y hy; rwa [Real.norm_eq_abs])
  have humqS : AEStronglyMeasurable (fun y => |u y| ^ q) (volume.restrict S) := by
    have h2 := hcq.comp_aestronglyMeasurable humS.norm
    simpa [Real.norm_eq_abs] using h2
  have hρθ : (0:ℝ) ≤ ρ ^ θ := Real.rpow_nonneg hρ.le _
  have hNbigq : 2 ^ q * KL ≤ Nbig ^ q := by
    have h1 : ((2:ℝ) ^ q * KL) ^ (1/q) ≤ Nbig := le_max_right _ _
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) h1 hq0.le
    rwa [← Real.rpow_mul (by positivity : (0:ℝ) ≤ 2 ^ q * KL), one_div,
      inv_mul_cancel₀ (ne_of_gt hq0), Real.rpow_one] at h2
  rcases le_or_gt ρ (d/8) with hcase | hcase
  · -- small radii: Lemma 4.2 on the pair of balls B_{d/8}(x1) ⊂ B_{d/4}(x1)
    have hd4 : (0:ℝ) < d/4 := by linarith
    have hNflatge : N₁t ≤ Nflat := by rw [hNflatdef]; exact le_max_left _ _
    have hcb4 : Metric.closedBall x₁ (d/4) ⊆ Ω'' := by
      intro y hy
      by_contra hcon
      have h1 := hsep1 x₁ hx₁ y hcon
      rw [Metric.mem_closedBall, dist_comm] at hy
      linarith
    have hb4Ω'' : Metric.ball x₁ (d/4) ⊆ Ω'' :=
      subset_trans Metric.ball_subset_closedBall hcb4
    have hb4Ω : Metric.ball x₁ (d/4) ⊆ Ω := subset_trans hb4Ω'' hΩ''ΩP
    have hclos4 : closure (Metric.ball x₁ (d/4)) ⊆ Ω :=
      subset_trans Metric.closure_ball_subset_closedBall (subset_trans hcb4 hΩ''ΩP)
    have hclos8 : closure (Metric.ball x₁ (d/8)) ⊆ Metric.ball x₁ (d/4) :=
      subset_trans Metric.closure_ball_subset_closedBall
        (Metric.closedBall_subset_ball (by linarith))
    have hsep8 : ∀ x ∈ Metric.ball x₁ (d/8), ∀ y, y ∉ Metric.ball x₁ (d/4) →
        d/8 ≤ dist x y := by
      intro x hx y hy
      rw [Metric.mem_ball] at hx
      rw [Metric.mem_ball, not_lt] at hy
      have h1 := dist_triangle y x x₁
      rw [dist_comm]
      linarith
    have hloc : MemW1pLocOn n p Ω u g :=
      (WeakGradientRestrict n p hn1 hp.le Ω Ω u g hΩ hΩ (subset_refl Ω)).2.2.1 hu
    have hgpΩ2 : IntegrableOn (fun y => ‖g y‖ ^ p) Ω volume := by
      have h := (hu.2.2).integrable_norm_rpow hpne0 hpnet
      rw [htoRp] at h
      exact h
    have hdiamΩ'' : (0:ℝ) < d → Metric.diam (Metric.ball x₁ d) ≤ Metric.diam Ω'' := by
      intro _
      refine Metric.diam_mono ?_ hbdd
      intro y hy
      by_contra hcon
      have h1 := hsep1 x₁ hx₁ y hcon
      rw [Metric.mem_ball, dist_comm] at hy
      linarith
    -- Morrey datum for the gradient on the ball of radius d/4
    have hmor9 : MorreyBoundOn n p ((n:ℝ) - t) (Metric.ball x₁ (d/4))
        (fun x => ‖g x‖) Nflat := by
      obtain ⟨hmL, hmB⟩ :=
        hmorreyt ε Ω Ω'' u g hε0 hε1 hΩ hΩ'' hbdd hclΩ'' hsep2 hu hWb hbundle
      refine ⟨MeasureTheory.MemLp.mono_measure
        (Measure.restrict_mono hb4Ω'' le_rfl) hmL, ?_⟩
      intro x hx r hr hrd
      have hdiam4 : Metric.diam (Metric.ball x₁ (d/4)) = 2 * (d/4) :=
        Metric.diam_ball_eq x₁ (by linarith)
      have hdb : Metric.diam (Metric.ball x₁ d) = 2 * d := Metric.diam_ball_eq x₁ hd.le
      have hrΩ'' : r < Metric.diam Ω'' := by
        have h2 := hdiamΩ'' hd
        rw [hdb] at h2
        rw [hdiam4] at hrd
        linarith
      have h3 := hmB x (hb4Ω'' hx) r hr hrΩ''
      simp only [abs_norm] at h3 ⊢
      have hsub1 : Ω'' ∩ Metric.ball x r ⊆ Ω := fun y hy => hΩ''ΩP hy.1
      have hsub2 : Metric.ball x₁ (d/4) ∩ Metric.ball x r ⊆ Ω'' ∩ Metric.ball x r :=
        fun y hy => ⟨hb4Ω'' hy.1, hy.2⟩
      refine le_trans (setIntegral_mono_set
        (hgpΩ2.mono_set hsub1)
        (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (norm_nonneg _) _)
        (Filter.Eventually.of_forall hsub2)) ?_
      refine le_trans h3 (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hN₁t0 hNflatge hp0.le) (Real.rpow_nonneg hr.le _))
    -- the lambda = 0 Morrey datum for u on the ball of radius d/4: this is
    -- the only place the uniform bound M is used.
    have hmor10 : MorreyBoundOn n q 0 (Metric.ball x₁ (d/4)) u Nflat := by
      have hfin4 : IsFiniteMeasure (volume.restrict (Metric.ball x₁ (d/4))) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
      have hum4 : AEStronglyMeasurable u (volume.restrict (Metric.ball x₁ (d/4))) :=
        (hu.2.1).aestronglyMeasurable.mono_measure (Measure.restrict_mono hb4Ω le_rfl)
      have hMb4 : ∀ᵐ y ∂(volume.restrict (Metric.ball x₁ (d/4))), |u y| ≤ M :=
        hMb.filter_mono (ae_mono (Measure.restrict_mono hb4Ω le_rfl))
      have humq4 : AEStronglyMeasurable (fun y => |u y| ^ q)
          (volume.restrict (Metric.ball x₁ (d/4))) := by
        have h2 := hcq.comp_aestronglyMeasurable hum4.norm
        simpa [Real.norm_eq_abs] using h2
      have hint4 : IntegrableOn (fun y => |u y| ^ q) (Metric.ball x₁ (d/4)) volume := by
        refine Integrable.mono' (integrable_const (M ^ q)) humq4 ?_
        filter_upwards [hMb4] with y hy
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact Real.rpow_le_rpow (abs_nonneg _) hy hq0.le
      have hNq : M ^ q * (ωn * (d/4) ^ ((n:ℝ)))
          = (M * ωn ^ (1/q) * (d/4) ^ ((n:ℝ)/q)) ^ q := by
        rw [Real.mul_rpow (mul_nonneg hM (Real.rpow_nonneg hω.le _))
            (Real.rpow_nonneg hd4.le _),
          Real.mul_rpow hM (Real.rpow_nonneg hω.le _),
          ← Real.rpow_mul hω.le, ← Real.rpow_mul hd4.le,
          one_div, inv_mul_cancel₀ (ne_of_gt hq0), Real.rpow_one,
          div_mul_cancel₀ _ (ne_of_gt hq0)]
        ring
      refine ⟨MemLp.of_bound hum4 M
        (by filter_upwards [hMb4] with y hy; rwa [Real.norm_eq_abs]), ?_⟩
      intro x hx r hr hrd
      rw [Real.rpow_zero, mul_one]
      have hle : (∫ y in Metric.ball x₁ (d/4) ∩ Metric.ball x r, |u y| ^ q)
          ≤ ∫ y in Metric.ball x₁ (d/4), |u y| ^ q :=
        setIntegral_mono_set hint4
          (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (abs_nonneg _) _)
          (Filter.Eventually.of_forall fun y hy => hy.1)
      have hle2 : (∫ y in Metric.ball x₁ (d/4), |u y| ^ q)
          ≤ (volume (Metric.ball x₁ (d/4))).toReal * M ^ q := by
        have h5 : (∫ y in Metric.ball x₁ (d/4), |u y| ^ q)
            ≤ ∫ _y in Metric.ball x₁ (d/4), M ^ q := by
          refine integral_mono_ae hint4 (integrable_const _) ?_
          filter_upwards [hMb4] with y hy
          exact Real.rpow_le_rpow (abs_nonneg _) hy hq0.le
        rwa [setIntegral_const, smul_eq_mul] at h5
      have hle3 : (volume (Metric.ball x₁ (d/4))).toReal * M ^ q ≤ Nflat ^ q := by
        rw [hballvol x₁ (d/4) hd4.le, mul_comm (ωn * (d/4) ^ ((n:ℝ))) (M ^ q), hNq]
        refine Real.rpow_le_rpow (by positivity) ?_ hq0.le
        rw [hNflatdef]
        exact le_max_right _ _
      linarith
    -- Lemma 4.2 on the ball pair
    have hC := hMGC Ω (Metric.ball x₁ (d/4)) (Metric.ball x₁ (d/8)) u g hΩ
      Metric.isOpen_ball Metric.isOpen_ball Metric.isBounded_ball hclos4 hclos8
      hsep8 hloc hmor9 hmor10
    have hθc : (n:ℝ) + q * (1 - t/p) = θ := by rw [hθdef]; ring
    rw [hθc] at hC
    have hdiam8 : Metric.diam (Metric.ball x₁ (d/8)) = 2 * (d/8) :=
      Metric.diam_ball_eq x₁ (by linarith)
    have hρlt : ρ < Metric.diam (Metric.ball x₁ (d/8)) := by
      rw [hdiam8]; linarith
    have hC2 := hC.2 x₁ (Metric.mem_ball_self hd8) ρ hρ hρlt
    have hinter : Metric.ball x₁ (d/8) ∩ Metric.ball x₁ ρ = Metric.ball x₁ ρ :=
      Set.inter_eq_self_of_subset_right (Metric.ball_subset_ball hcase)
    rw [hinter] at hC2
    set B : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball x₁ ρ with hBdef
    set c : ℝ := (volume B).toReal⁻¹ * ∫ w in B, u w with hcdef
    have hBΩ : B ⊆ Ω := by
      rw [hBdef]
      exact subset_trans (Metric.ball_subset_ball (by linarith)) hb4Ω
    have hfinB : IsFiniteMeasure (volume.restrict B) :=
      ⟨by rw [Measure.restrict_apply_univ, hBdef]; exact measure_ball_lt_top⟩
    have humB : AEStronglyMeasurable u (volume.restrict B) :=
      (hu.2.1).aestronglyMeasurable.mono_measure (Measure.restrict_mono hBΩ le_rfl)
    have hMbB : ∀ᵐ y ∂(volume.restrict B), |u y| ≤ M :=
      hMb.filter_mono (ae_mono (Measure.restrict_mono hBΩ le_rfl))
    have hmeasB : AEStronglyMeasurable (fun y => |u y - c| ^ q) (volume.restrict B) := by
      have h2 := hcq.comp_aestronglyMeasurable
        (humB.sub (aestronglyMeasurable_const (b := c))).norm
      simpa [Real.norm_eq_abs, Pi.sub_apply] using h2
    have hintB : IntegrableOn (fun y => |u y - c| ^ q) B volume := by
      refine Integrable.mono' (integrable_const ((M + |c|) ^ q)) hmeasB ?_
      filter_upwards [hMbB] with y hy
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      refine Real.rpow_le_rpow (abs_nonneg _) ?_ hq0.le
      have h6 : |u y - c| ≤ |u y| + |c| := by
        calc |u y - c| ≤ |u y| + |(-c)| := by
              rw [sub_eq_add_neg]; exact abs_add_le _ _
          _ = |u y| + |c| := by rw [abs_neg]
      linarith
    have hNbigl : 2 * N' ≤ Nbig := by rw [hNbigdef]; exact le_max_left _ _
    calc (∫ y in S, |u y - (volume S).toReal⁻¹ * ∫ w in S, u w| ^ q)
        ≤ 2 ^ q * ∫ y in S, |u y - c| ^ q := hMscal S u c hSmeas hS0 hSfin hMemS
      _ ≤ 2 ^ q * ∫ y in B, |u y - c| ^ q := by
          refine mul_le_mul_of_nonneg_left (setIntegral_mono_set hintB
            (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (abs_nonneg _) _)
            (Filter.Eventually.of_forall fun y hy => hSball hy))
            (Real.rpow_nonneg (by norm_num) _)
      _ ≤ 2 ^ q * (N' ^ q * ρ ^ θ) :=
          mul_le_mul_of_nonneg_left hC2 (Real.rpow_nonneg (by norm_num) _)
      _ = (2 * N') ^ q * ρ ^ θ := by
          rw [Real.mul_rpow (by norm_num) hN'0]; ring
      _ ≤ Nbig ^ q * ρ ^ θ :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (by positivity) hNbigl hq0.le) hρθ
  · -- large radii
    have hmr := hMscal S u 0 hSmeas hS0 hSfin hMemS
    simp only [sub_zero] at hmr
    have hρd8 : (d/8) ^ θ ≤ ρ ^ θ := Real.rpow_le_rpow hd8.le hcase.le hθ0.le
    have hbd : (∫ y in S, |u y| ^ q) ≤ KL * ρ ^ θ := by
      rcases le_or_gt p q with hpq | hpq
      · -- q ≥ p : compare pointwise with |u|^p
        have hpt : ∀ᵐ y ∂(volume.restrict S), |u y| ^ q ≤ M ^ (q - p) * |u y| ^ p := by
          filter_upwards [hMbS] with y hy
          rcases eq_or_lt_of_le (abs_nonneg (u y)) with h0 | h0
          · rw [← h0, Real.zero_rpow (ne_of_gt hq0), Real.zero_rpow (ne_of_gt hp0)]
            simp
          · conv_lhs => rw [show q = p + (q - p) from by ring]
            rw [Real.rpow_add h0, mul_comm (M ^ (q - p)) (|u y| ^ p)]
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (abs_nonneg _) hy (by linarith))
              (Real.rpow_nonneg (abs_nonneg _) _)
        have hintp : IntegrableOn (fun y => |u y| ^ p) S volume := hupΩ.mono_set hSΩ
        have h1 := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (abs_nonneg _) _)
          (hintp.const_mul (M ^ (q - p))) hpt
        rw [integral_const_mul] at h1
        have h2 : (∫ y in S, |u y| ^ p) ≤ W ^ p :=
          le_trans (setIntegral_mono_set hupΩ
            (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (abs_nonneg _) _)
            (Filter.Eventually.of_forall fun y hy => hSΩ hy)) hupW
        have h3 : M ^ (q - p) * (∫ y in S, |u y| ^ p) ≤ M ^ (q - p) * W ^ p :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hM _)
        have hK1eq : M ^ (q - p) * W ^ p = K1 * (d/8) ^ θ := by
          rw [hK1def, max_eq_left (by linarith : (0:ℝ) ≤ q - p),
            min_eq_left hpq, mul_assoc, ← Real.rpow_add hd8]
          simp
        have h4 : K1 * (d/8) ^ θ ≤ KL * ρ ^ θ := by
          refine le_trans (mul_le_mul_of_nonneg_left hρd8 hK10) ?_
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hρθ
        linarith [h1, h3, hK1eq ▸ h4]
      · -- q < p : Hoelder on the finite-measure set S
        have hPQ : (1:ℝ) < p / q := by rw [lt_div_iff₀ hq0]; linarith
        set Q : ℝ := (p/q) / ((p/q) - 1) with hQdef
        have hconj : Real.HolderConjugate (p/q) Q := by
          refine Real.holderConjugate_iff.2 ⟨hPQ, ?_⟩
          rw [hQdef, inv_div, inv_div]
          field_simp
          ring
        have hQinv : 1 / Q = 1 - q / p := by
          rw [hQdef]
          field_simp
        have hf_mem : MemLp (fun y => |u y| ^ q) (ENNReal.ofReal (p/q))
            (volume.restrict S) := by
          refine MemLp.of_bound humqS (M ^ q) ?_
          filter_upwards [hMbS] with y hy
          rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
          exact Real.rpow_le_rpow (abs_nonneg _) hy hq0.le
        have hhol := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict S) hconj
          (f := fun y => |u y| ^ q) (g := fun _ => (1:ℝ))
          (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (abs_nonneg _) _)
          (Filter.Eventually.of_forall fun _ => zero_le_one)
          hf_mem (memLp_const 1)
        simp only [mul_one, Real.one_rpow, integral_const, smul_eq_mul] at hhol
        rw [Measure.real_def, Measure.restrict_apply_univ, hQinv] at hhol
        have hpow : ∀ y : EuclideanSpace ℝ (Fin n), (|u y| ^ q) ^ (p/q) = |u y| ^ p := by
          intro y
          rw [← Real.rpow_mul (abs_nonneg _)]
          congr 1
          field_simp
        simp only [hpow] at hhol
        rw [one_div_div] at hhol
        -- bound the two factors
        have hup : (∫ y in S, |u y| ^ p) ≤ W ^ p :=
          le_trans (setIntegral_mono_set hupΩ
            (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (abs_nonneg _) _)
            (Filter.Eventually.of_forall fun y hy => hSΩ hy)) hupW
        have hup0 : (0:ℝ) ≤ ∫ y in S, |u y| ^ p :=
          integral_nonneg fun y => Real.rpow_nonneg (abs_nonneg _) _
        have hqp0 : (0:ℝ) ≤ q / p := le_of_lt (div_pos hq0 hp0)
        have h1mqp : (0:ℝ) < 1 - q / p := by
          have : q / p < 1 := by rw [div_lt_one hp0]; exact hpq
          linarith
        have hA : (∫ y in S, |u y| ^ p) ^ (q/p) ≤ W ^ q := by
          refine le_trans (Real.rpow_le_rpow hup0 hup hqp0) ?_
          rw [← Real.rpow_mul hW]
          rw [show p * (q/p) = q from by field_simp]
        have hSvol : (volume S).toReal ≤ ωn * ρ ^ ((n:ℝ)) := by
          rw [← hballvol x₁ ρ hρ.le]
          exact ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono hSball)
        have hSvol0 : (0:ℝ) ≤ (volume S).toReal := ENNReal.toReal_nonneg
        have hB : (volume S).toReal ^ (1 - q/p)
            ≤ ωn ^ (1 - q/p) * ρ ^ ((n:ℝ) * (1 - q/p)) := by
          refine le_trans (Real.rpow_le_rpow hSvol0 hSvol h1mqp.le) ?_
          rw [Real.mul_rpow hω.le (Real.rpow_nonneg hρ.le _), ← Real.rpow_mul hρ.le]
        have hexp0 : (n:ℝ) * (1 - q/p) - θ ≤ 0 := by
          have he : (n:ℝ) * (1 - q/p) - θ = q * ((t - (n:ℝ))/p - 1) := by
            rw [hθeq]; field_simp; ring
          have h2 : (t - (n:ℝ))/p - 1 < 0 := by
            have : (t - (n:ℝ))/p < 0 := div_neg_of_neg_of_pos (by linarith) hp0
            linarith
          rw [he]
          exact le_of_lt (mul_neg_of_pos_of_neg hq0 h2)
        have hmono : ρ ^ ((n:ℝ) * (1 - q/p) - θ) ≤ (d/8) ^ ((n:ℝ) * (1 - q/p) - θ) :=
          Real.rpow_le_rpow_of_nonpos hd8 hcase.le hexp0
        have hsplitρ : ρ ^ ((n:ℝ) * (1 - q/p))
            = ρ ^ ((n:ℝ) * (1 - q/p) - θ) * ρ ^ θ := by
          rw [← Real.rpow_add (by linarith : (0:ℝ) < ρ)]
          congr 1
          ring
        calc (∫ y in S, |u y| ^ q)
            ≤ (∫ y in S, |u y| ^ p) ^ (q/p) * (volume S).toReal ^ (1 - q/p) := hhol
          _ ≤ W ^ q * (ωn ^ (1 - q/p) * ρ ^ ((n:ℝ) * (1 - q/p))) :=
              mul_le_mul hA hB (Real.rpow_nonneg hSvol0 _) (Real.rpow_nonneg hW _)
          _ = W ^ q * ωn ^ (1 - q/p) * (ρ ^ ((n:ℝ) * (1 - q/p) - θ) * ρ ^ θ) := by
              rw [hsplitρ]; ring
          _ ≤ W ^ q * ωn ^ (1 - q/p) * ((d/8) ^ ((n:ℝ) * (1 - q/p) - θ) * ρ ^ θ) := by
              refine mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hmono hρθ) ?_
              exact mul_nonneg (Real.rpow_nonneg hW _) (Real.rpow_nonneg hω.le _)
          _ = K2 * ρ ^ θ := by
              rw [hK2def, max_eq_left h1mqp.le]; ring
          _ ≤ KL * ρ ^ θ := mul_le_mul_of_nonneg_right (le_max_right _ _) hρθ
    calc (∫ y in S, |u y - (volume S).toReal⁻¹ * ∫ w in S, u w| ^ q)
        ≤ 2 ^ q * ∫ y in S, |u y| ^ q := hmr
      _ ≤ 2 ^ q * (KL * ρ ^ θ) :=
          mul_le_mul_of_nonneg_left hbd (Real.rpow_nonneg (by norm_num) _)
      _ = (2 ^ q * KL) * ρ ^ θ := by ring
      _ ≤ Nbig ^ q * ρ ^ θ := mul_le_mul_of_nonneg_right hNbigq hρθ
