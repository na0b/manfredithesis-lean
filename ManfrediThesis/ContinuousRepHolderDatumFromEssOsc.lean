import ManfrediThesis.Preamble
import ManfrediThesis.EssOscOn
open MeasureTheory

/-- From an essential-oscillation decay bound on one ball to the pointwise
Hölder datum of a continuous representative.

Let `u` be essentially bounded by `M` on an open-set-sized region `Ω`
containing `closedBall x₀ (d/2)`, let `0 < R ≤ d/2`, and let `U` be continuous
on `closedBall x₀ R` with `U = u` at every point of `ball x₀ R`.  Suppose the
essential oscillation of `u` on `ball x₀ R` obeys the scaled decay bound
`4^α · max (osc(u, B_{d/2}) , dst · d/2) · (R/(d/2))^α`.  Then
`|U x - U x₀| ≤ 4^α · max (2M, dst · d/2) · (2/d)^α · R^α` for every
`x ∈ closedBall x₀ R`.

Two elementary facts are packaged here.  First, `|u| ≤ M` almost everywhere
forces `osc(u, B_{d/2}) ≤ 2M`, which turns the decay bound's inner maximum
into the `ε`-free, data-free constant `max (2M, dst · d/2)`, and
`(R/(d/2))^α = R^α (2/d)^α` splits off the radius.  Second, a function
continuous on `closedBall x₀ R` that agrees pointwise with `u` on `ball x₀ R`
is trapped pointwise between the essential infimum and the essential supremum
of `u` over `ball x₀ R`, on the whole *closed* ball; two points of that
interval differ by at most the essential oscillation.

The hypothesis is exactly the conclusion of the cited Hölder oscillation
estimate (C4) applied at outer radius `d/2` and inner radius `R`, so no
structure predicate -- neither (F1) on an integrand nor (Q1)-(Q5) on a field --
appears here.  That is what lets both the §4 branch
(`MinimumHolderDatumOnBall`, via part (a) of (C4)) and the §5 branch
(`SolutionHolderDatumOnBall`, via part (b)) cite this one lemma with their own
instance of the oscillation bound.  Mathematically it is the paper's step at
thesis l. 1130-1136: "It follows from the Hölder continuity property of `u`
that there exists `R₀` and `C₁` ... such that `|u(x₀) - u(x)| ≤ C₁ R^α`",
which §4 and §5 invoke in the same way. -/
theorem ContinuousRepHolderDatumFromEssOsc :
    ∀ (n : ℕ) (α dst M d : ℝ), 0 < d →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (u U : EuclideanSpace ℝ (Fin n) → ℝ)
        (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ),
        0 < R → R ≤ d/2 →
        Metric.closedBall x₀ (d/2) ⊆ Ω →
        (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
        ContinuousOn U (Metric.closedBall x₀ R) →
        (∀ x ∈ Metric.ball x₀ R, U x = u x) →
        EssOscOn n (Metric.ball x₀ R) u
          ≤ (4:ℝ) ^ α * max (EssOscOn n (Metric.ball x₀ (d/2)) u) (dst * (d/2))
              * (R / (d/2)) ^ α →
        ∀ x ∈ Metric.closedBall x₀ R,
          |U x - U x₀|
            ≤ (4:ℝ) ^ α * max (2 * M) (dst * (d/2)) * (2/d) ^ α * R ^ α := by
  intro n α dst M d hd Ω u U x₀ R hR hRd2 hcb hMu hUc hUu hC4R
  have h4α : (0:ℝ) < (4:ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
  -- the essential-supremum bookkeeping
  have hNeBot : ∀ {s : Set (EuclideanSpace ℝ (Fin n))}, volume s ≠ 0 →
      (ae (volume.restrict s)).NeBot := by
    intro s hs
    refine ⟨fun hb => ?_⟩
    rw [ae_eq_bot] at hb
    exact hs (by simpa using congrArg (fun m => m s) hb)
  have hcobdd_le : ∀ {μ : Measure (EuclideanSpace ℝ (Fin n))}
      {v : EuclideanSpace ℝ (Fin n) → ℝ} {m : ℝ}, (ae μ).NeBot →
      (∀ᵐ x ∂μ, m ≤ v x) → Filter.IsCoboundedUnder (· ≤ ·) (ae μ) v := by
    intro μ v m hb hlo
    have := hb
    refine ⟨m, fun c hc => ?_⟩
    rw [Filter.eventually_map] at hc
    obtain ⟨x, hax, hxm⟩ := (hc.and hlo).exists
    linarith
  have hcobdd_ge : ∀ {μ : Measure (EuclideanSpace ℝ (Fin n))}
      {v : EuclideanSpace ℝ (Fin n) → ℝ} {Mb : ℝ}, (ae μ).NeBot →
      (∀ᵐ x ∂μ, v x ≤ Mb) → Filter.IsCoboundedUnder (· ≥ ·) (ae μ) v := by
    intro μ v Mb hb hhi
    have := hb
    refine ⟨Mb, fun c hc => ?_⟩
    rw [Filter.eventually_map] at hc
    obtain ⟨x, hax, hxM⟩ := (hc.and hhi).exists
    linarith
  have hsubhi : ∀ s : Set (EuclideanSpace ℝ (Fin n)), s ⊆ Ω →
      ∀ᵐ z ∂(volume.restrict s), u z ≤ M := by
    intro s hs
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hMu] with z hz
      using (abs_le.1 hz).2
  have hsublo : ∀ s : Set (EuclideanSpace ℝ (Fin n)), s ⊆ Ω →
      ∀ᵐ z ∂(volume.restrict s), -M ≤ u z := by
    intro s hs
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hMu] with z hz
      using (abs_le.1 hz).1
  -- the oscillation over the big ball is at most `2M`
  have hbigΩ : Metric.ball x₀ (d/2) ⊆ Ω :=
    Metric.ball_subset_closedBall.trans hcb
  have hosc2M : EssOscOn n (Metric.ball x₀ (d/2)) u ≤ 2 * M := by
    have hb : (ae (volume.restrict (Metric.ball x₀ (d/2)))).NeBot :=
      hNeBot (Metric.measure_ball_pos volume x₀ (by linarith)).ne'
    have hhi := hsubhi _ hbigΩ
    have hlo := hsublo _ hbigΩ
    have h1 : essSup u (volume.restrict (Metric.ball x₀ (d/2))) ≤ M :=
      essSup_le_of_ae_le M hhi (hcobdd_le hb hlo)
    have h2 : -M ≤ essInf u (volume.restrict (Metric.ball x₀ (d/2))) :=
      le_essInf_of_ae_le (-M) hlo (hcobdd_ge hb hhi)
    show essSup u (volume.restrict (Metric.ball x₀ (d/2)))
      - essInf u (volume.restrict (Metric.ball x₀ (d/2))) ≤ 2 * M
    linarith
  -- the cited oscillation estimate, scaled
  have hratio : R / (d/2) = R * (2/d) := by field_simp
  have hsplit : (R / (d/2)) ^ α = R ^ α * (2/d) ^ α := by
    rw [hratio, Real.mul_rpow hR.le (by positivity)]
  have hstep : EssOscOn n (Metric.ball x₀ R) u
      ≤ (4:ℝ) ^ α * max (2 * M) (dst * (d/2)) * (2/d) ^ α * R ^ α := by
    refine le_trans hC4R ?_
    have hmx : max (EssOscOn n (Metric.ball x₀ (d/2)) u) (dst * (d/2))
        ≤ max (2 * M) (dst * (d/2)) :=
      max_le_max hosc2M le_rfl
    have hpow : (0:ℝ) ≤ (R / (d/2)) ^ α := Real.rpow_nonneg (by positivity) _
    calc (4:ℝ) ^ α * max (EssOscOn n (Metric.ball x₀ (d/2)) u) (dst * (d/2))
            * (R / (d/2)) ^ α
        ≤ (4:ℝ) ^ α * max (2 * M) (dst * (d/2)) * (R / (d/2)) ^ α := by
          refine mul_le_mul_of_nonneg_right ?_ hpow
          exact mul_le_mul_of_nonneg_left hmx h4α.le
      _ = (4:ℝ) ^ α * max (2 * M) (dst * (d/2)) * (2/d) ^ α * R ^ α := by
          rw [hsplit]; ring
  -- the pointwise bounds on `U`
  have hballΩ : Metric.ball x₀ R ⊆ Ω :=
    (Metric.ball_subset_ball hRd2).trans hbigΩ
  have hbR : (ae (volume.restrict (Metric.ball x₀ R))).NeBot :=
    hNeBot (Metric.measure_ball_pos volume x₀ hR).ne'
  have hhiR := hsubhi _ hballΩ
  have hloR := hsublo _ hballΩ
  have haeS : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ R)),
      u z ≤ essSup u (volume.restrict (Metric.ball x₀ R)) :=
    ae_le_essSup ⟨M, by rw [Filter.eventually_map]; exact hhiR⟩
  have haeI : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ R)),
      essInf u (volume.restrict (Metric.ball x₀ R)) ≤ u z :=
    ae_essInf_le ⟨-M, by rw [Filter.eventually_map]; exact hloR⟩
  have haeUS : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      z ∈ Metric.ball x₀ R → U z ≤ essSup u (volume.restrict (Metric.ball x₀ R)) := by
    refine (ae_restrict_iff' measurableSet_ball).1 ?_
    filter_upwards [haeS, ae_restrict_mem measurableSet_ball] with z h1 h2
    rw [hUu z h2]
    exact h1
  have haeUI : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      z ∈ Metric.ball x₀ R → essInf u (volume.restrict (Metric.ball x₀ R)) ≤ U z := by
    refine (ae_restrict_iff' measurableSet_ball).1 ?_
    filter_upwards [haeI, ae_restrict_mem measurableSet_ball] with z h1 h2
    rw [hUu z h2]
    exact h1
  have hUcb : ContinuousOn U (Metric.ball x₀ R) :=
    hUc.mono Metric.ball_subset_closedBall
  have hptU : ∀ x ∈ Metric.ball x₀ R,
      essInf u (volume.restrict (Metric.ball x₀ R)) ≤ U x
        ∧ U x ≤ essSup u (volume.restrict (Metric.ball x₀ R)) := by
    intro x hx
    constructor
    · by_contra hc
      rw [not_le] at hc
      have hopen : IsOpen (Metric.ball x₀ R ∩ U ⁻¹'
          (Set.Iio (essInf u (volume.restrict (Metric.ball x₀ R))))) :=
        hUcb.isOpen_inter_preimage Metric.isOpen_ball isOpen_Iio
      have hpos := hopen.measure_pos volume ⟨x, hx, hc⟩
      rw [ae_iff] at haeUI
      refine absurd (measure_mono_null (fun z hz => ?_) haeUI) hpos.ne'
      intro hcon
      exact absurd (hcon hz.1) (not_le.2 hz.2)
    · by_contra hc
      rw [not_le] at hc
      have hopen : IsOpen (Metric.ball x₀ R ∩ U ⁻¹'
          (Set.Ioi (essSup u (volume.restrict (Metric.ball x₀ R))))) :=
        hUcb.isOpen_inter_preimage Metric.isOpen_ball isOpen_Ioi
      have hpos := hopen.measure_pos volume ⟨x, hx, hc⟩
      rw [ae_iff] at haeUS
      refine absurd (measure_mono_null (fun z hz => ?_) haeUS) hpos.ne'
      intro hcon
      exact absurd (hcon hz.1) (not_le.2 hz.2)
  have hptUc : ∀ x ∈ Metric.closedBall x₀ R,
      essInf u (volume.restrict (Metric.ball x₀ R)) ≤ U x
        ∧ U x ≤ essSup u (volume.restrict (Metric.ball x₀ R)) := by
    have hcl : IsClosed (Metric.closedBall x₀ R ∩ U ⁻¹'
        (Set.Icc (essInf u (volume.restrict (Metric.ball x₀ R)))
          (essSup u (volume.restrict (Metric.ball x₀ R))))) :=
      hUc.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_Icc
    have hsub : Metric.ball x₀ R ⊆ Metric.closedBall x₀ R ∩ U ⁻¹'
        (Set.Icc (essInf u (volume.restrict (Metric.ball x₀ R)))
          (essSup u (volume.restrict (Metric.ball x₀ R)))) := by
      intro x hx
      exact ⟨Metric.ball_subset_closedBall hx, (hptU x hx).1, (hptU x hx).2⟩
    have hclos : Metric.closedBall x₀ R ⊆ Metric.closedBall x₀ R ∩ U ⁻¹'
        (Set.Icc (essInf u (volume.restrict (Metric.ball x₀ R)))
          (essSup u (volume.restrict (Metric.ball x₀ R)))) := by
      have h1 : closure (Metric.ball x₀ R) = Metric.closedBall x₀ R :=
        closure_ball x₀ (ne_of_gt hR)
      intro y hy
      rw [← h1] at hy
      exact ((closure_mono hsub).trans hcl.closure_subset) hy
    intro x hx
    exact ⟨(hclos hx).2.1, (hclos hx).2.2⟩
  intro x hx
  have h1 := hptUc x hx
  have h2 := hptUc x₀ (Metric.mem_closedBall_self hR.le)
  have hES : EssOscOn n (Metric.ball x₀ R) u
      = essSup u (volume.restrict (Metric.ball x₀ R))
        - essInf u (volume.restrict (Metric.ball x₀ R)) := rfl
  rw [hES] at hstep
  rw [abs_le]
  exact ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩
