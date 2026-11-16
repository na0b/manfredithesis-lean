import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pZeroOn
import ManfrediThesis.IsLocalMinimumOn
import ManfrediThesis.VariationalStructureF123
import ManfrediThesis.SmoothCompactSupportMemW1p
open MeasureTheory

/-- The variational twin of `WeakSolutionZeroTest`: the minimality inequality of
`IsLocalMinimumOn` extends from its compactly supported test class to a
`W^{1,p}_0(B)` perturbation, on an open `B ⊆ Ω` of finite measure.  This is the
step the thesis performs silently when it compares the local minimum `u` with
the comparison map `v` on `B_R`, whose difference lies in `W^{1,p}_0(B_R)` and
so has no compact support. -/
theorem LocalMinimumZeroTest :
    ∀ (n : ℕ) (p ε lam Lam a ν₀ ν₁ : ℝ), 1 ≤ n → 1 < p → 0 ≤ ε → ε ≤ 1 →
      0 < lam → lam ≤ Lam →
      ∀ (Ω B : Set (EuclideanSpace ℝ (Fin n)))
        (fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
        (σ : ℝ → ℝ)
        (u v : EuclideanSpace ℝ (Fin n) → ℝ)
        (g gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        IsOpen Ω → IsOpen B → B ⊆ Ω → volume B ≠ ⊤ →
        VariationalStructureF123 n p ε lam Lam a ν₀ ν₁ Ω fdens σ →
        MemLp u (ENNReal.ofReal p) (volume.restrict B) →
        MemLp g (ENNReal.ofReal p) (volume.restrict B) →
        IsLocalMinimumOn n p Ω fdens u g →
        MemW1pZeroOn n p B (fun x => v x - u x) (fun x => gv x - g x) →
        (∫ x in B, fdens x (u x) (g x)) ≤ ∫ x in B, fdens x (v x) (gv x) := by
  intro n p ε lam Lam a ν₀ ν₁ hn hp hε hε1 hlam hlamLam Ω B fdens σ u v g gv
    hΩ hB hBΩ hBfin hF hu hg hmin hzero
  have hp0 : (0:ℝ) < p := by linarith
  have hLam0 : (0:ℝ) ≤ Lam := le_trans hlam.le hlamLam
  have hBmeas : MeasurableSet B := hB.measurableSet
  have hfin : IsFiniteMeasure (volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hBfin⟩
  -- Carathéodory: the integrand composed with measurable data is measurable
  have hCara : ∀ (w : EuclideanSpace ℝ (Fin n) → ℝ)
      (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      AEStronglyMeasurable w (volume.restrict B) →
      AEStronglyMeasurable h (volume.restrict B) →
      AEStronglyMeasurable (fun x => fdens x (w x) (h x)) (volume.restrict B) := by
    have hU : Measurable (Function.uncurry
        (fun (q : ℝ × EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) =>
          fdens x q.1 q.2)) :=
      measurable_uncurry_of_continuous_of_measurable
        (fun x => hF.cont_zh x) (fun q => hF.meas_x q.1 q.2)
    intro w h hw hh
    obtain ⟨w', hw'm, hw'e⟩ := hw
    obtain ⟨h', hh'm, hh'e⟩ := hh
    refine ⟨fun x => fdens x (w' x) (h' x), ?_, ?_⟩
    · exact Measurable.stronglyMeasurable
        (hU.comp ((hw'm.measurable.prodMk hh'm.measurable).prodMk measurable_id))
    · filter_upwards [hw'e, hh'e] with x h1 h2
      rw [h1, h2]
  -- the weight `(ε + s²)^{p/2}` is bounded by `(1+s)^p` and is monotone in `s ≥ 0`
  have hwtle : ∀ s : ℝ, 0 ≤ s → (ε + s ^ 2) ^ (p / 2) ≤ (1 + s) ^ p := by
    intro s hs
    have h1 : ε + s ^ 2 ≤ (1 + s) ^ 2 := by nlinarith
    have h2 : (ε + s ^ 2) ^ (p / 2) ≤ ((1 + s) ^ 2) ^ (p / 2) :=
      Real.rpow_le_rpow (by positivity) h1 (by positivity)
    have h3 : (((1 + s) ^ 2 : ℝ)) ^ (p / 2) = (1 + s) ^ p := by
      rw [show ((1 + s) ^ 2 : ℝ) = (1 + s) ^ (2:ℝ) by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]]
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      ring
    rwa [h3] at h2
  have hwtmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → (ε + s ^ 2) ^ (p / 2) ≤ (ε + t ^ 2) ^ (p / 2) := by
    intro s t hs hst
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    nlinarith
  -- the F1 majorant is integrable on `B` for any nonnegative `L^p` weight
  have hmaj : ∀ W : EuclideanSpace ℝ (Fin n) → ℝ,
      MemLp W (ENNReal.ofReal p) (volume.restrict B) →
      IntegrableOn (fun x => Lam * (ε + W x ^ 2) ^ (p / 2) + a) B volume := by
    intro W hW
    have hone : MemLp (fun x => (1:ℝ) + ‖W x‖) (ENNReal.ofReal p) (volume.restrict B) :=
      (memLp_const (1:ℝ)).add hW.norm
    have hpow := hone.norm_rpow_div (ENNReal.ofReal p)
    rw [ENNReal.toReal_ofReal hp0.le,
      ENNReal.div_self (ne_of_gt (ENNReal.ofReal_pos.2 hp0)) ENNReal.ofReal_ne_top] at hpow
    have hint1 : Integrable (fun x => ((1:ℝ) + ‖W x‖) ^ p) (volume.restrict B) := by
      have h := memLp_one_iff_integrable.1 hpow
      refine h.congr ?_
      filter_upwards with x
      rw [Real.norm_of_nonneg (by positivity)]
    have hmeasw : AEStronglyMeasurable (fun x => (ε + W x ^ 2) ^ (p / 2))
        (volume.restrict B) := by
      have hc : Continuous fun z : ℝ => (ε + z ^ 2) ^ (p / 2) := by
        have h1 : Continuous fun z : ℝ => ε + z ^ 2 := by fun_prop
        refine h1.rpow_const fun z => Or.inr (by positivity)
      exact hc.comp_aestronglyMeasurable hW.aestronglyMeasurable
    have hint2 : Integrable (fun x => (ε + W x ^ 2) ^ (p / 2)) (volume.restrict B) := by
      refine hint1.mono' hmeasw ?_
      filter_upwards with x
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      have hsq : W x ^ 2 = ‖W x‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
      rw [hsq]
      exact hwtle ‖W x‖ (norm_nonneg _)
    exact (hint2.const_mul Lam).add (integrable_const a)
  -- hence the functional's integrand is integrable on `B`
  have hintB : ∀ (w : EuclideanSpace ℝ (Fin n) → ℝ)
      (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      AEStronglyMeasurable w (volume.restrict B) →
      MemLp h (ENNReal.ofReal p) (volume.restrict B) →
      IntegrableOn (fun x => fdens x (w x) (h x)) B volume := by
    intro w h hw hh
    refine Integrable.mono' (hmaj (fun x => ‖h x‖) hh.norm) (hCara w h hw hh.1) ?_
    filter_upwards [ae_restrict_mem hBmeas] with x hx
    have h1 := hF.F1 x (hBΩ hx) (w x) (h x)
    rw [Real.norm_eq_abs, abs_le]
    have hw1 : 0 ≤ lam * (ε + ‖h x‖ ^ 2) ^ (p / 2) := by positivity
    have hw2 : 0 ≤ Lam * (ε + ‖h x‖ ^ 2) ^ (p / 2) := by positivity
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  -- the Euclidean norm as a coordinate sum
  have hnorm : ∀ w : EuclideanSpace ℝ (Fin n),
      (∑ i, |w i| ^ 2) ^ (p / 2) = ‖w‖ ^ p := by
    intro w
    have hS : (0:ℝ) ≤ ∑ i, |w i| ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hw : ‖w‖ = (∑ i, |w i| ^ 2) ^ ((1:ℝ) / 2) := by
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_rpow]
      congr 1
    rw [hw, ← Real.rpow_mul hS, show (1:ℝ) / 2 * p = p / 2 by ring]
  -- the approximating sequence
  obtain ⟨hdiffW, φ, hφsm, hφ1, hφ2⟩ := hzero
  obtain ⟨-, htest⟩ := hmin
  set G : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun k x => WithLp.toLp 2 fun i =>
      fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ)) with hGdef
  set Wseq : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k x => u x + φ k x with hWdef
  set Hseq : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun k x => g x + G k x with hHdef
  have hsupΩ : ∀ k, tsupport (φ k) ⊆ Ω := fun k => (hφsm k).2.2.trans hBΩ
  have hadm : ∀ k, MemW1pOn n p Ω (φ k) (G k) := fun k =>
    SmoothCompactSupportMemW1p n p hn hp.le Ω (φ k) hΩ (hφsm k).1 (hφsm k).2.1 (hsupΩ k)
  have hGLp : ∀ k, MemLp (G k) (ENNReal.ofReal p) (volume.restrict B) := fun k =>
    MeasureTheory.MemLp.mono_measure (Measure.restrict_mono hBΩ le_rfl) (hadm k).2.2
  have hφLp : ∀ k, MemLp (φ k) (ENNReal.ofReal p) (volume.restrict B) := fun k =>
    MeasureTheory.MemLp.mono_measure (Measure.restrict_mono hBΩ le_rfl) (hadm k).2.1
  have hWLp : ∀ k, MemLp (Wseq k) (ENNReal.ofReal p) (volume.restrict B) :=
    fun k => hu.add (hφLp k)
  have hHLp : ∀ k, MemLp (Hseq k) (ENNReal.ofReal p) (volume.restrict B) :=
    fun k => hg.add (hGLp k)
  have hvLp : MemLp v (ENNReal.ofReal p) (volume.restrict B) := by
    have h := hu.add hdiffW.2.1
    have he : (u + fun x => v x - u x) = v := by funext x; simp
    rwa [he] at h
  have hgvLp : MemLp gv (ENNReal.ofReal p) (volume.restrict B) := by
    have h := hg.add hdiffW.2.2
    have he : (g + fun x => gv x - g x) = gv := by funext x; simp
    rwa [he] at h
  -- (5.2): the minimality instance, extended from `tsupport φ k` to `B`
  have h52 : ∀ k : ℕ, (∫ x in B, fdens x (u x) (g x))
      ≤ ∫ x in B, fdens x (Wseq k x) (Hseq k x) := by
    intro k
    obtain ⟨-, -, hle⟩ := htest (φ k) (G k) (hadm k) (hφsm k).2.1 (hsupΩ k)
    have hTmeas : MeasurableSet (tsupport (φ k)) :=
      (isClosed_tsupport (φ k)).measurableSet
    have hTB : tsupport (φ k) ⊆ B := (hφsm k).2.2
    have hoff : ∀ x ∉ tsupport (φ k), φ k x = 0 ∧ G k x = 0 := by
      intro x hx
      refine ⟨image_eq_zero_of_notMem_tsupport hx, ?_⟩
      have hev : φ k =ᶠ[nhds x] (fun _ => (0:ℝ)) := by
        filter_upwards [(isOpen_compl_iff.2 (isClosed_tsupport (φ k))).mem_nhds hx] with y hy
        exact image_eq_zero_of_notMem_tsupport hy
      have hd0 : fderiv ℝ (φ k) x = 0 := by rw [hev.fderiv_eq]; simp
      show (WithLp.toLp 2 fun i =>
        fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ))) = 0
      rw [hd0]
      ext i
      simp
    have hJ1 : IntegrableOn (fun x => fdens x (u x) (g x)) B volume :=
      hintB u g hu.aestronglyMeasurable hg
    have hJ2 : IntegrableOn (fun x => fdens x (Wseq k x) (Hseq k x)) B volume :=
      hintB (Wseq k) (Hseq k) (hWLp k).aestronglyMeasurable (hHLp k)
    have hsplit : ∀ F : EuclideanSpace ℝ (Fin n) → ℝ, IntegrableOn F B volume →
        (∫ x in B, F x) = (∫ x in tsupport (φ k), F x) + ∫ x in B \ tsupport (φ k), F x := by
      intro F hFi
      have h := integral_add_compl (μ := volume.restrict B) hTmeas hFi
      rw [Measure.restrict_restrict hTmeas, Set.inter_eq_self_of_subset_left hTB,
        Measure.restrict_restrict hTmeas.compl,
        show (tsupport (φ k))ᶜ ∩ B = B \ tsupport (φ k) by
          rw [Set.inter_comm]; rfl] at h
      exact h.symm
    have heq : (∫ x in B \ tsupport (φ k), fdens x (u x) (g x))
        = ∫ x in B \ tsupport (φ k), fdens x (Wseq k x) (Hseq k x) := by
      refine setIntegral_congr_fun (hBmeas.diff hTmeas) ?_
      intro x hx
      have h0 := hoff x hx.2
      show fdens x (u x) (g x) = fdens x (u x + φ k x) (g x + G k x)
      rw [h0.1, h0.2, add_zero, add_zero]
    rw [hsplit _ hJ1, hsplit _ hJ2, heq]
    have hle' : (∫ x in tsupport (φ k), fdens x (u x) (g x))
        ≤ ∫ x in tsupport (φ k), fdens x (Wseq k x) (Hseq k x) := hle
    linarith [hle']
  -- the two `L^p` convergences, in the form needed below
  have hpne0 : (ENNReal.ofReal p) ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have hpnet : (ENNReal.ofReal p) ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  have htoRp : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hD1 : ∀ k, MemLp (fun x => v x - Wseq k x) (ENNReal.ofReal p)
      (volume.restrict B) := fun k => hvLp.sub (hWLp k)
  have hD2 : ∀ k, MemLp (fun x => gv x - Hseq k x) (ENNReal.ofReal p)
      (volume.restrict B) := fun k => hgvLp.sub (hHLp k)
  have hi1 : ∀ k, Integrable (fun x => |v x - Wseq k x| ^ p) (volume.restrict B) := by
    intro k
    have h := (hD1 k).integrable_norm_rpow hpne0 hpnet
    rw [htoRp] at h
    refine h.congr ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
  have hi2 : ∀ k, Integrable (fun x => ‖gv x - Hseq k x‖ ^ p) (volume.restrict B) := by
    intro k
    have h := (hD2 k).integrable_norm_rpow hpne0 hpnet
    rwa [htoRp] at h
  have hconv1 : Filter.Tendsto (fun k => ∫ x in B, |v x - Wseq k x| ^ p)
      Filter.atTop (nhds 0) := by
    refine hφ1.congr fun k => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show |v x - u x - φ k x| ^ p = |v x - (u x + φ k x)| ^ p
    congr 2
    ring
  have hconv2 : Filter.Tendsto (fun k => ∫ x in B, ‖gv x - Hseq k x‖ ^ p)
      Filter.atTop (nhds 0) := by
    refine hφ2.congr fun k => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (∑ i, |(gv x - g x) i
        - fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ))| ^ 2) ^ (p / 2)
      = ‖gv x - (g x + G k x)‖ ^ p
    rw [← hnorm (gv x - (g x + G k x))]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    show (gv x - g x) i - fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ))
      = (gv x - (g x + G k x)) i
    show gv x i - g x i - fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ))
      = gv x i - (g x i + fderiv ℝ (φ k) x (EuclideanSpace.single i (1:ℝ)))
    ring
  -- a subsequence along which both errors are summable
  have he0 : Filter.Tendsto
      (fun k => (∫ x in B, |v x - Wseq k x| ^ p) + ∫ x in B, ‖gv x - Hseq k x‖ ^ p)
      Filter.atTop (nhds 0) := by
    have h := hconv1.add hconv2
    rwa [add_zero] at h
  have hNex : ∀ k : ℕ, ∃ m : ℕ,
      (∫ x in B, |v x - Wseq m x| ^ p) + ∫ x in B, ‖gv x - Hseq m x‖ ^ p
        ≤ (1/2:ℝ) ^ k := by
    intro k
    have hpos : (0:ℝ) < (1/2:ℝ) ^ k := by positivity
    exact ((he0.eventually (gt_mem_nhds hpos)).exists).imp fun m hm => hm.le
  choose N hN using hNex
  have hnn1 : ∀ k, (0:ℝ) ≤ ∫ x in B, |v x - Wseq k x| ^ p :=
    fun k => integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
  have hnn2 : ∀ k, (0:ℝ) ≤ ∫ x in B, ‖gv x - Hseq k x‖ ^ p :=
    fun k => integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  -- the ℝ≥0∞ series
  set c : ℕ → EuclideanSpace ℝ (Fin n) → ENNReal := fun k x =>
    ENNReal.ofReal (|v x - Wseq (N k) x| ^ p)
      + ENNReal.ofReal (‖gv x - Hseq (N k) x‖ ^ p) with hcdef
  have hcm1 : ∀ k, AEMeasurable
      (fun x => ENNReal.ofReal (|v x - Wseq (N k) x| ^ p)) (volume.restrict B) :=
    fun k => ((hi1 (N k)).aestronglyMeasurable.aemeasurable).ennreal_ofReal
  have hcm2 : ∀ k, AEMeasurable
      (fun x => ENNReal.ofReal (‖gv x - Hseq (N k) x‖ ^ p)) (volume.restrict B) :=
    fun k => ((hi2 (N k)).aestronglyMeasurable.aemeasurable).ennreal_ofReal
  have hcmeas : ∀ k, AEMeasurable (c k) (volume.restrict B) :=
    fun k => (hcm1 k).add (hcm2 k)
  have hclint : ∀ k, (∫⁻ x in B, c k x) ≤ ENNReal.ofReal ((1/2:ℝ) ^ k) := by
    intro k
    have hsum : (∫⁻ x in B, c k x)
        = (∫⁻ x in B, ENNReal.ofReal (|v x - Wseq (N k) x| ^ p))
          + ∫⁻ x in B, ENNReal.ofReal (‖gv x - Hseq (N k) x‖ ^ p) :=
      lintegral_add_left' (hcm1 k) _
    have ha : (∫⁻ x in B, ENNReal.ofReal (|v x - Wseq (N k) x| ^ p))
        = ENNReal.ofReal (∫ x in B, |v x - Wseq (N k) x| ^ p) :=
      (ofReal_integral_eq_lintegral_ofReal (hi1 (N k))
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _)).symm
    have hb : (∫⁻ x in B, ENNReal.ofReal (‖gv x - Hseq (N k) x‖ ^ p))
        = ENNReal.ofReal (∫ x in B, ‖gv x - Hseq (N k) x‖ ^ p) :=
      (ofReal_integral_eq_lintegral_ofReal (hi2 (N k))
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)).symm
    rw [hsum, ha, hb, ← ENNReal.ofReal_add (hnn1 (N k)) (hnn2 (N k))]
    exact ENNReal.ofReal_le_ofReal (hN k)
  set T : EuclideanSpace ℝ (Fin n) → ENNReal := fun x => ∑' k, c k x with hTdef
  have hTm : AEMeasurable T (volume.restrict B) := AEMeasurable.tsum hcmeas
  have hTlint : (∫⁻ x in B, T x) ≠ ⊤ := by
    rw [hTdef, lintegral_tsum hcmeas]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hclint)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  have hTfin : ∀ᵐ x ∂(volume.restrict B), T x ≠ ⊤ := by
    filter_upwards [ae_lt_top' hTm hTlint] with x hx
    exact hx.ne
  -- from a vanishing `ofReal (rᵖ)` to a vanishing `r`
  have hrootlim : ∀ r : ℕ → ℝ, (∀ k, 0 ≤ r k) →
      Filter.Tendsto (fun k => ENNReal.ofReal (r k ^ p)) Filter.atTop (nhds 0) →
      Filter.Tendsto r Filter.atTop (nhds 0) := by
    intro r hr0 hrt
    have h1 : Filter.Tendsto (fun k => (ENNReal.ofReal (r k ^ p)).toReal)
        Filter.atTop (nhds 0) := by
      have hc := (ENNReal.tendsto_toReal (by simp : (0:ENNReal) ≠ ⊤)).comp hrt
      simpa [Function.comp_def] using hc
    have h2 : Filter.Tendsto (fun k => r k ^ p) Filter.atTop (nhds 0) := by
      refine h1.congr fun k => ?_
      exact ENNReal.toReal_ofReal (Real.rpow_nonneg (hr0 k) _)
    have hcts : Filter.Tendsto (fun t : ℝ => t ^ (1/p)) (nhds 0) (nhds 0) := by
      have h := (Real.continuousAt_rpow_const (0:ℝ) (1/p) (Or.inr (by positivity))).tendsto
      rwa [Real.zero_rpow (by positivity)] at h
    refine (hcts.comp h2).congr fun k => ?_
    show ((r k ^ p) ^ (1/p) : ℝ) = r k
    rw [← Real.rpow_mul (hr0 k), mul_one_div, div_self (ne_of_gt hp0), Real.rpow_one]
  -- the dominating function
  set Wt : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ‖gv x‖ + (T x).toReal ^ (1/p)
    with hWtdef
  have hWtLp : MemLp Wt (ENNReal.ofReal p) (volume.restrict B) := by
    have hTint : Integrable (fun x => (T x).toReal) (volume.restrict B) :=
      integrable_toReal_of_lintegral_ne_top hTm hTlint
    have h1 : MemLp (fun x => (T x).toReal) 1 (volume.restrict B) :=
      memLp_one_iff_integrable.2 hTint
    have h2 := h1.norm_rpow_div (ENNReal.ofReal (1/p))
    rw [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 1/p)] at h2
    have hexp : (1 : ENNReal) / ENNReal.ofReal (1/p) = ENNReal.ofReal p := by
      rw [one_div p, ENNReal.ofReal_inv_of_pos hp0, one_div, inv_inv]
    rw [hexp] at h2
    have he : (fun x => ‖(T x).toReal‖ ^ (1/p))
        = fun x => (T x).toReal ^ (1/p) := by
      funext x
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    rw [he] at h2
    exact hgvLp.norm.add h2
  have hWtnn : ∀ x, 0 ≤ Wt x := fun x =>
    add_nonneg (norm_nonneg _) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  -- domination
  have hdom : ∀ k : ℕ, ∀ᵐ x ∂(volume.restrict B), ‖Hseq (N k) x‖ ≤ Wt x := by
    intro k
    filter_upwards [hTfin] with x hx
    have hle : ENNReal.ofReal (‖gv x - Hseq (N k) x‖ ^ p) ≤ T x := by
      refine le_trans ?_ (ENNReal.le_tsum k)
      exact le_add_self
    have hle' : ‖gv x - Hseq (N k) x‖ ^ p ≤ (T x).toReal := by
      have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hx).2 hle
      rwa [ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] at h
    have hroot : ‖gv x - Hseq (N k) x‖ ≤ (T x).toReal ^ (1/p) := by
      have h := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hle'
        (by positivity : (0:ℝ) ≤ 1/p)
      rwa [← Real.rpow_mul (norm_nonneg _), mul_one_div, div_self (ne_of_gt hp0),
        Real.rpow_one] at h
    have htri : ‖Hseq (N k) x‖ ≤ ‖gv x‖ + ‖gv x - Hseq (N k) x‖ := by
      have h := norm_sub_le (gv x) (gv x - Hseq (N k) x)
      simpa using h
    exact le_trans htri (by linarith [hroot])
  -- pointwise convergence of the integrand
  have hptlim : ∀ᵐ x ∂(volume.restrict B),
      Filter.Tendsto (fun k => fdens x (Wseq (N k) x) (Hseq (N k) x)) Filter.atTop
        (nhds (fdens x (v x) (gv x))) := by
    filter_upwards [hTfin] with x hx
    have hc0 : Filter.Tendsto (fun k => c k x) Filter.atTop (nhds 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx
    have ha0 : Filter.Tendsto
        (fun k => ENNReal.ofReal (|v x - Wseq (N k) x| ^ p)) Filter.atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc0
        (fun _ => zero_le) (fun k => le_self_add)
    have hb0 : Filter.Tendsto
        (fun k => ENNReal.ofReal (‖gv x - Hseq (N k) x‖ ^ p)) Filter.atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc0
        (fun _ => zero_le) (fun k => le_add_self)
    have h1 : Filter.Tendsto (fun k => |v x - Wseq (N k) x|) Filter.atTop (nhds 0) :=
      hrootlim _ (fun k => abs_nonneg _) ha0
    have h2 : Filter.Tendsto (fun k => ‖gv x - Hseq (N k) x‖) Filter.atTop (nhds 0) :=
      hrootlim _ (fun k => norm_nonneg _) hb0
    have hw : Filter.Tendsto (fun k => Wseq (N k) x) Filter.atTop (nhds (v x)) := by
      have h3 : Filter.Tendsto (fun k => v x - Wseq (N k) x) Filter.atTop (nhds 0) :=
        tendsto_zero_iff_norm_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using h1)
      have h4 := (tendsto_const_nhds (x := v x) (f := (Filter.atTop : Filter ℕ))).sub h3
      simpa using h4
    have hh : Filter.Tendsto (fun k => Hseq (N k) x) Filter.atTop (nhds (gv x)) := by
      have h3 : Filter.Tendsto (fun k => gv x - Hseq (N k) x) Filter.atTop (nhds 0) :=
        tendsto_zero_iff_norm_tendsto_zero.2 h2
      have h4 := (tendsto_const_nhds (x := gv x) (f := (Filter.atTop : Filter ℕ))).sub h3
      simpa using h4
    exact ((hF.cont_zh x).tendsto (v x, gv x)).comp (hw.prodMk_nhds hh)
  -- dominated convergence
  have hlim : Filter.Tendsto
      (fun k => ∫ x in B, fdens x (Wseq (N k) x) (Hseq (N k) x))
      Filter.atTop (nhds (∫ x in B, fdens x (v x) (gv x))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => Lam * (ε + Wt x ^ 2) ^ (p / 2) + a)
      (fun k => hCara _ _ (hWLp (N k)).aestronglyMeasurable (hHLp (N k)).aestronglyMeasurable)
      (hmaj Wt hWtLp) ?_ hptlim
    intro k
    filter_upwards [ae_restrict_mem hBmeas, hdom k] with x hx hdx
    have h1 := hF.F1 x (hBΩ hx) (Wseq (N k) x) (Hseq (N k) x)
    have hmono : (ε + ‖Hseq (N k) x‖ ^ 2) ^ (p / 2) ≤ (ε + Wt x ^ 2) ^ (p / 2) :=
      hwtmono _ _ (norm_nonneg _) hdx
    have hw1 : 0 ≤ lam * (ε + ‖Hseq (N k) x‖ ^ 2) ^ (p / 2) := by positivity
    have hw2 : 0 ≤ Lam * (ε + ‖Hseq (N k) x‖ ^ 2) ^ (p / 2) := by positivity
    have hw3 : Lam * (ε + ‖Hseq (N k) x‖ ^ 2) ^ (p / 2)
        ≤ Lam * (ε + Wt x ^ 2) ^ (p / 2) := mul_le_mul_of_nonneg_left hmono hLam0
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun k => h52 (N k))
