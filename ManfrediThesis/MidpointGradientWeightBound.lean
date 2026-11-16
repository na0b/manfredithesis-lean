import ManfrediThesis.Preamble
import ManfrediThesis.SegmentWeightIntegrable
open MeasureTheory
set_option maxHeartbeats 1600000

/-- The elementary inequality stated after (4.4): the `t`-average of the weight
along the segment from `b` to `a` dominates the weight at the endpoints. -/
theorem MidpointGradientWeightBound :
    ∀ p : ℝ, 1 < p →
      ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ) (ε : ℝ) (a b : EuclideanSpace ℝ (Fin n)), 1 ≤ n → 0 ≤ ε →
          C * (ε + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2 - 1)
            ≤ ∫ t in (0 : ℝ)..1,
                (1 - t) * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1) := by
  intro p hp
  -- the integrand is interval-integrable, by the closed node beneath this one
  have hint : ∀ (n : ℕ) (ε : ℝ) (a b : EuclideanSpace ℝ (Fin n)), 0 ≤ ε →
      IntervalIntegrable
        (fun t : ℝ => (1 - t) * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ (p / 2 - 1))
        volume 0 1 := by
    intro n ε a b hε
    have hw := SegmentWeightIntegrable n p hp ε a b hε
    exact hw.continuousOn_mul (by fun_prop)
  have hid : (∫ t in (0:ℝ)..1, (1 - t)) = 1/2 := by
    norm_num [intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
  have hhalf : ∀ c : ℝ, (∫ t in (0 : ℝ)..1, (1 - t) * c) = c / 2 := by
    intro c
    rw [intervalIntegral.integral_mul_const, hid]
    ring
  -- a subset of the line whose points are pairwise within `d` has measure at most `d`
  have measure_le_of_pairwise_dist_le : ∀ {Z : Set ℝ} {d : ℝ},
      Bornology.IsBounded Z → (∀ x ∈ Z, ∀ y ∈ Z, |x - y| ≤ d) →
      volume Z ≤ ENNReal.ofReal d := by
    intro Z d hbdd h
    rcases Z.eq_empty_or_nonempty with rfl | hne
    · simp
    have hbb : BddBelow Z := hbdd.bddBelow
    have hba : BddAbove Z := hbdd.bddAbove
    have hup : ∀ x ∈ Z, x ≤ sInf Z + d := by
      intro x hx
      have hall : ∀ y ∈ Z, x - d ≤ y := by
        intro y hy
        have h1 : x - y ≤ d := (abs_le.1 (h x hx y hy)).2
        linarith
      have := le_csInf hne hall
      linarith
    have hsup : sSup Z ≤ sInf Z + d := csSup_le hne hup
    have hsub : Z ⊆ Set.Icc (sInf Z) (sSup Z) := fun x hx =>
      ⟨csInf_le hbb hx, le_csSup hba hx⟩
    calc volume Z ≤ volume (Set.Icc (sInf Z) (sSup Z)) := measure_mono hsub
      _ = ENNReal.ofReal (sSup Z - sInf Z) := Real.volume_Icc
      _ ≤ ENNReal.ofReal d := by apply ENNReal.ofReal_le_ofReal; linarith
  -- a constant lower bound on a subset gives a lower bound for the interval integral
  have interval_lower : ∀ {f : ℝ → ℝ} {E : Set ℝ} {c : ℝ},
      (∀ t ∈ Set.Ioc (0:ℝ) 1, 0 ≤ f t) → IntegrableOn f (Set.Ioc (0:ℝ) 1) volume →
      MeasurableSet E → E ⊆ Set.Ioc (0:ℝ) 1 → (∀ t ∈ E, c ≤ f t) →
      c * volume.real E ≤ ∫ t in (0:ℝ)..1, f t := by
    intro f E c hf0 hfi hEm hEsub hc
    have hEfin : volume E ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) (measure_mono (hEsub.trans Set.Ioc_subset_Icc_self))
    have hEi : IntegrableOn f E volume := hfi.mono_set hEsub
    have h1 : c * volume.real E ≤ ∫ t in E, f t :=
      setIntegral_ge_of_const_le_real (μ := volume) (s := E) hEm hEfin hc hEi
    have h2 : ∫ t in E, f t ≤ ∫ t in Set.Ioc (0:ℝ) 1, f t := by
      refine setIntegral_mono_set hfi ?_ (LE.le.eventuallyLE hEsub)
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0:ℝ)) (b := 1))]
        with t ht using hf0 t ht
    have h3 : ∫ t in (0:ℝ)..1, f t = ∫ t in Set.Ioc (0:ℝ) 1, f t :=
      intervalIntegral.integral_of_le (by norm_num)
    rw [h3]; linarith
  rcases le_or_gt 2 p with hp2 | hp2
  · -- p ≥ 2: the exponent is nonnegative, so we need the base bounded BELOW on a
    -- set of substantial measure
    refine ⟨(1/16) * (128:ℝ) ^ (1 - p/2), by positivity, ?_⟩
    intro n ε a b hn hε
    set s : ℝ := p/2 - 1 with hs
    have hs0 : (0:ℝ) ≤ s := by rw [hs]; linarith
    set T : ℝ := ε + ‖a‖ ^ 2 + ‖b‖ ^ 2 with hT
    have hT0 : 0 ≤ T := by rw [hT]; positivity
    have hTs0 : (0:ℝ) ≤ T ^ s := Real.rpow_nonneg hT0 s
    have h128 : (128:ℝ) ^ (1 - p/2) = (128:ℝ) ^ (-s) := by rw [hs]; ring_nf
    have hCle : (1/16) * (128:ℝ) ^ (1 - p/2) ≤ 1/2 := by
      rw [h128, Real.rpow_neg (by norm_num)]
      have : (1:ℝ) ≤ (128:ℝ) ^ s := Real.one_le_rpow (by norm_num) hs0
      have hpos : (0:ℝ) < (128:ℝ) ^ s := by positivity
      rw [mul_comm]
      rw [inv_mul_le_iff₀ hpos] at *
      nlinarith [this]
    set M : ℝ := max ‖a‖ ‖b‖ with hM
    have hM0 : 0 ≤ M := le_trans (norm_nonneg a) (le_max_left _ _)
    set L : ℝ := ‖a - b‖ with hL
    have hL0 : 0 ≤ L := norm_nonneg _
    -- the integrand is nonnegative and integrable on `Set.Ioc 0 1`
    have hnn : ∀ t ∈ Set.Ioc (0:ℝ) 1,
        0 ≤ (1 - t) * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ s := by
      intro t ht
      have h1 : (0:ℝ) ≤ 1 - t := by linarith [ht.2]
      have h2 : (0:ℝ) ≤ (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ s :=
        Real.rpow_nonneg (by positivity) s
      positivity
    have hion : IntegrableOn
        (fun t : ℝ => (1 - t) * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ s)
        (Set.Ioc (0:ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 (hint n ε a b hε)
    -- THE KEY STEP: a constant lower bound on a subset of substantial measure
    have key : ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Ioc (0:ℝ) 1 →
        (1/4 : ℝ) ≤ volume.real E → (∀ t ∈ E, M/8 ≤ ‖t • a + (1 - t) • b‖) →
        (∀ t ∈ E, t ≤ 3/4) →
        (1/16) * (128:ℝ) ^ (1 - p/2) * T ^ s
          ≤ ∫ t in (0:ℝ)..1, (1 - t) * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ s := by
      intro E hEm hEsub hEvol hElow hEup
      have hc0 : (0:ℝ) ≤ (1/4) * (T/128) ^ s :=
        by positivity
      have hptw : ∀ t ∈ E, (1/4) * (T/128) ^ s
          ≤ (1 - t) * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ s := by
        intro t hE
        have hbase : T/128 ≤ ε + ‖t • a + (1 - t) • b‖ ^ 2 := by
          have h1 : M/8 ≤ ‖t • a + (1 - t) • b‖ := hElow t hE
          have h2 : M^2/64 ≤ ‖t • a + (1 - t) • b‖ ^ 2 := by
            nlinarith [hM0, norm_nonneg (t • a + (1 - t) • b), h1]
          have h3 : ‖a‖ ^ 2 ≤ M ^ 2 := by
            nlinarith [norm_nonneg a, le_max_left ‖a‖ ‖b‖, hM0]
          have h4 : ‖b‖ ^ 2 ≤ M ^ 2 := by
            nlinarith [norm_nonneg b, le_max_right ‖a‖ ‖b‖, hM0]
          rw [hT]
          nlinarith [hε, h2, h3, h4]
        have hrp : (T/128) ^ s ≤ (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ s :=
          Real.rpow_le_rpow (by positivity) hbase hs0
        have hfac : (1:ℝ)/4 ≤ 1 - t := by linarith [hEup t hE]
        calc (1/4) * (T/128) ^ s ≤ (1 - t) * (T/128) ^ s :=
              mul_le_mul_of_nonneg_right hfac (Real.rpow_nonneg (by positivity) s)
          _ ≤ (1 - t) * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ s :=
              mul_le_mul_of_nonneg_left hrp (by linarith [hEup t hE])
      have hlow := interval_lower hnn hion hEm hEsub hptw
      have hstep : (1/4) * (T/128) ^ s * (1/4)
          ≤ (1/4) * (T/128) ^ s * volume.real E :=
        mul_le_mul_of_nonneg_left hEvol hc0
      refine le_trans (le_of_eq ?_) (le_trans hstep hlow)
      rw [Real.div_rpow hT0 (by norm_num), h128, Real.rpow_neg (by norm_num)]
      field_simp
      ring
    -- three cases
    rcases eq_or_lt_of_le hM0 with hMz | hMpos
    · -- `M = 0`: both `a` and `b` vanish and the integrand is `(1-t) T^s`
      have ha : a = 0 := by
        have : ‖a‖ = 0 := le_antisymm (by rw [hMz] at *; exact le_max_left ‖a‖ ‖b‖ |>.trans_eq hMz.symm) (norm_nonneg a)
        simpa using this
      have hb : b = 0 := by
        have : ‖b‖ = 0 := le_antisymm (by rw [hMz] at *; exact le_max_right ‖a‖ ‖b‖ |>.trans_eq hMz.symm) (norm_nonneg b)
        simpa using this
      have hTe : T = ε := by rw [hT, ha, hb]; simp
      have hrhs : (∫ t in (0:ℝ)..1,
          (1 - t) * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ s) = T ^ s / 2 := by
        have : ∀ t : ℝ, (1 - t) * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ s
            = (1 - t) * T ^ s := by
          intro t; rw [ha, hb, hTe]; simp
        rw [intervalIntegral.integral_congr (g := fun t => (1 - t) * T ^ s)
          (fun t _ => this t), hhalf]
      rw [hrhs]
      nlinarith [hCle, hTs0]
    · -- `M > 0`
      rcases lt_or_ge L (M/2) with hLlt | hLge
      · -- Subcase 2a: the whole segment stays far from the origin
        refine key (Set.Ioc (0:ℝ) (3/4)) measurableSet_Ioc
          (fun t ht => ⟨ht.1, by linarith [ht.2]⟩) ?_ ?_ (fun t ht => ht.2)
        · rw [Measure.real, Real.volume_Ioc]
          rw [ENNReal.toReal_ofReal (by norm_num)]; norm_num
        · intro t ht
          have ht0 : 0 ≤ t := le_of_lt ht.1
          have ht1 : t ≤ 1 := by linarith [ht.2]
          have e1 : t • a + (1 - t) • b = a - (1 - t) • (a - b) := by module
          have h1 : ‖a‖ - (1 - t) * L ≤ ‖t • a + (1 - t) • b‖ := by
            have := norm_sub_norm_le a ((1 - t) • (a - b))
            rw [← e1] at this
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)] at this
            linarith [this]
          have e2 : t • a + (1 - t) • b = b - (-t) • (a - b) := by module
          have h2 : ‖b‖ - t * L ≤ ‖t • a + (1 - t) • b‖ := by
            have hh := norm_sub_norm_le b ((-t) • (a - b))
            rw [← e2] at hh
            rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ht0] at hh
            linarith [hh]
          have hmax : M - L ≤ ‖t • a + (1 - t) • b‖ := by
            rcases le_total ‖b‖ ‖a‖ with hc | hc
            · have : M = ‖a‖ := by rw [hM]; exact max_eq_left hc
              rw [this]; nlinarith [h1, hL0, ht1, ht0]
            · have : M = ‖b‖ := by rw [hM]; exact max_eq_right hc
              rw [this]; nlinarith [h2, hL0, ht1, ht0]
          nlinarith [hmax, hLlt, hMpos]
      · -- Subcase 2b: remove the bad set, which has measure at most 1/2
        set Z : Set ℝ := {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ ‖t • a + (1 - t) • b‖ ≤ M/8}
          with hZ
        have hZm : MeasurableSet Z := by
          have hcont : Continuous fun t : ℝ => ‖t • a + (1 - t) • b‖ := by fun_prop
          have : Z = Set.Icc (0:ℝ) 1 ∩ {t : ℝ | ‖t • a + (1 - t) • b‖ ≤ M/8} := by
            rw [hZ]; ext t; simp [Set.mem_inter_iff]
          rw [this]
          exact measurableSet_Icc.inter (measurableSet_le hcont.measurable measurable_const)
        have hZbdd : Bornology.IsBounded Z := by
          refine (Metric.isBounded_Icc (0:ℝ) 1).subset ?_
          intro t ht; rw [hZ] at ht; exact ht.1
        have hZhalf : volume Z ≤ ENNReal.ofReal (1/2) := by
          refine measure_le_of_pairwise_dist_le hZbdd ?_
          intro t ht t' ht'
          rw [hZ] at ht ht'
          have hd : ‖t • a + (1 - t) • b - (t' • a + (1 - t') • b)‖ = |t - t'| * L := by
            have e : t • a + (1 - t) • b - (t' • a + (1 - t') • b) = (t - t') • (a - b) := by
              module
            rw [e, norm_smul, Real.norm_eq_abs, hL]
          have h4 : |t - t'| * L ≤ M/4 := by
            have := norm_sub_le (t • a + (1 - t) • b) (t' • a + (1 - t') • b)
            rw [hd] at this
            linarith [ht.2, ht'.2, this]
          have hLpos : 0 < L := by linarith
          rw [← le_div_iff₀ hLpos] at h4
          refine h4.trans ?_
          rw [div_le_iff₀ hLpos]; linarith
        have hEvolE : ENNReal.ofReal (1/4) ≤ volume (Set.Ioc (0:ℝ) (3/4) \ Z) := by
          have hIoc : volume (Set.Ioc (0:ℝ) (3/4)) = ENNReal.ofReal (3/4) := by
            rw [Real.volume_Ioc]; norm_num
          have h1 : ENNReal.ofReal (3/4) - ENNReal.ofReal (1/2)
              ≤ volume (Set.Ioc (0:ℝ) (3/4)) - volume Z := by
            rw [hIoc]; exact tsub_le_tsub_left hZhalf _
          have h2 : volume (Set.Ioc (0:ℝ) (3/4)) - volume Z
              ≤ volume (Set.Ioc (0:ℝ) (3/4) \ Z) := le_measure_sdiff
          refine le_trans (le_of_eq ?_) (h1.trans h2)
          rw [← ENNReal.ofReal_sub _ (by norm_num)]; norm_num
        refine key (Set.Ioc (0:ℝ) (3/4) \ Z) (measurableSet_Ioc.diff hZm)
          (fun t ht => ⟨ht.1.1, by linarith [ht.1.2]⟩) ?_ ?_ (fun t ht => ht.1.2)
        · have hfin : volume (Set.Ioc (0:ℝ) (3/4) \ Z) ≠ ⊤ :=
            ne_top_of_le_ne_top (by simp) (measure_mono Set.sdiff_subset)
          rw [Measure.real]
          exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 hEvolE
        · intro t ht
          by_contra hcon
          push Not at hcon
          exact ht.2 (by rw [hZ]; exact ⟨⟨le_of_lt ht.1.1, by linarith [ht.1.2]⟩, le_of_lt hcon⟩)
  · -- 1 < p < 2: the weight is bounded below because the base is bounded above
    refine ⟨(2:ℝ) ^ (p/2 - 2), by positivity, ?_⟩
    intro n ε a b hn hε
    set s : ℝ := p/2 - 1 with hs
    have hsneg : s < 0 := by rw [hs]; linarith
    set T : ℝ := ε + ‖a‖ ^ 2 + ‖b‖ ^ 2 with hT
    have hT0 : 0 ≤ T := by rw [hT]; positivity
    rcases eq_or_lt_of_le hT0 with hTz | hTpos
    · -- T = 0 forces ε = 0 and a = b = 0, and both sides vanish
      have hε0 : ε = 0 := by
        have h1 : (0:ℝ) ≤ ‖a‖ ^ 2 := by positivity
        have h2 : (0:ℝ) ≤ ‖b‖ ^ 2 := by positivity
        rw [hT] at hTz; linarith
      have ha : a = 0 := by
        have : ‖a‖ ^ 2 = 0 := by
          have h2 : (0:ℝ) ≤ ‖b‖ ^ 2 := by positivity
          rw [hT] at hTz; nlinarith [sq_nonneg ‖a‖]
        simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      have hb : b = 0 := by
        have : ‖b‖ ^ 2 = 0 := by
          have h1 : (0:ℝ) ≤ ‖a‖ ^ 2 := by positivity
          rw [hT] at hTz; nlinarith [sq_nonneg ‖b‖]
        simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      have hsne : s ≠ 0 := ne_of_lt hsneg
      have hrhs : (∫ t in (0:ℝ)..1,
          (1 - t) * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ s) = 0 := by
        have hzero : ∀ t : ℝ,
            (1 - t) * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ s = 0 := by
          intro t; simp [ha, hb, hε0, Real.zero_rpow hsne]
        simp [hzero]
      rw [hrhs, ← hTz, Real.zero_rpow hsne, mul_zero]
    · -- T > 0
      have hbase : ∀ t ∈ Set.Icc (0:ℝ) 1, ε + ‖t • a + (1 - t) • b‖ ^ 2 ≤ 2 * T := by
        intro t ht
        have ht0 : 0 ≤ t := ht.1
        have ht1 : t ≤ 1 := ht.2
        have h1 : ‖t • a + (1 - t) • b‖ ≤ ‖a‖ + ‖b‖ := by
          calc ‖t • a + (1 - t) • b‖ ≤ ‖t • a‖ + ‖(1 - t) • b‖ := norm_add_le _ _
            _ = t * ‖a‖ + (1 - t) * ‖b‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_nonneg ht0, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)]
            _ ≤ ‖a‖ + ‖b‖ := by nlinarith [norm_nonneg a, norm_nonneg b]
        have h2 : ‖t • a + (1 - t) • b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
          nlinarith [norm_nonneg (t • a + (1 - t) • b), h1, norm_nonneg a, norm_nonneg b]
        rw [hT]
        nlinarith [sq_nonneg (‖a‖ - ‖b‖), hε]
      -- the base vanishes for at most one `t`
      have hbad : {t : ℝ | ε + ‖t • a + (1 - t) • b‖ ^ 2 = 0}.Subsingleton := by
        intro t ht t' ht'
        simp only [Set.mem_ofPred_eq] at ht ht'
        have hz : ∀ r : ℝ, ε + ‖r • a + (1 - r) • b‖ ^ 2 = 0 →
            r • a + (1 - r) • b = 0 := by
          intro r hr
          have h1 : (0:ℝ) ≤ ‖r • a + (1 - r) • b‖ ^ 2 := by positivity
          have : ‖r • a + (1 - r) • b‖ ^ 2 = 0 := by linarith
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
          simpa using this
        have e1 := hz t ht
        have e2 := hz t' ht'
        have hdiff : (t - t') • (a - b) = 0 := by
          have : (t - t') • (a - b)
              = (t • a + (1 - t) • b) - (t' • a + (1 - t') • b) := by module
          rw [this, e1, e2, sub_zero]
        rcases eq_or_ne a b with hab | hab
        · -- then the segment is constantly `b`, and `T > 0` forces `b ≠ 0`
          exfalso
          have hb0 : b = 0 := by
            have : (t:ℝ) • a + (1 - t) • b = b := by rw [hab]; module
            rw [this] at e1; exact e1
          have ha0 : a = 0 := by rw [hab]; exact hb0
          have hε0 : ε = 0 := by
            have h1 : (0:ℝ) ≤ ‖t • a + (1 - t) • b‖ ^ 2 := by positivity
            linarith [ht, h1]
          rw [hT, ha0, hb0, hε0] at hTpos
          simp at hTpos
        · have hne : a - b ≠ 0 := sub_ne_zero_of_ne hab
          rcases smul_eq_zero.1 hdiff with h | h
          · linarith [sub_eq_zero.1 (by exact_mod_cast h : t - t' = 0)]
          · exact absurd h hne
      have hnull : volume {t : ℝ | ε + ‖t • a + (1 - t) • b‖ ^ 2 = 0} = 0 :=
        Set.Subsingleton.measure_zero hbad volume
      have hcmp : ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
          (1 - t) * (2 * T) ^ s
            ≤ (1 - t) * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ s := by
        have hco : ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
            ε + ‖t • a + (1 - t) • b‖ ^ 2 ≠ 0 := by
          have : ∀ᵐ t ∂(volume : Measure ℝ),
              ε + ‖t • a + (1 - t) • b‖ ^ 2 ≠ 0 := by
            rw [MeasureTheory.ae_iff]; simpa using hnull
          exact ae_restrict_of_ae this
        filter_upwards [hco,
          self_mem_ae_restrict (measurableSet_Icc (a := (0:ℝ)) (b := 1))] with t hne ht
        have hpos : 0 < ε + ‖t • a + (1 - t) • b‖ ^ 2 := by
          have h1 : (0:ℝ) ≤ ‖t • a + (1 - t) • b‖ ^ 2 := by positivity
          rcases lt_or_eq_of_le (by linarith : (0:ℝ) ≤ ε + ‖t • a + (1 - t) • b‖ ^ 2) with h | h
          · exact h
          · exact absurd h.symm hne
        have hrp : (2 * T) ^ s ≤ (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ s :=
          Real.rpow_le_rpow_of_nonpos hpos (hbase t ht) (le_of_lt hsneg)
        exact mul_le_mul_of_nonneg_left hrp (by linarith [ht.2])
      have hcint : IntervalIntegrable (fun t : ℝ => (1 - t) * (2 * T) ^ s) volume 0 1 :=
        (by fun_prop : Continuous fun t : ℝ => (1 - t) * (2 * T) ^ s).intervalIntegrable 0 1
      have h1 : (∫ t in (0:ℝ)..1, (1 - t) * (2 * T) ^ s)
          ≤ ∫ t in (0:ℝ)..1, (1 - t) * (ε + ‖t • a + (1 - t) • b‖ ^ 2) ^ s :=
        intervalIntegral.integral_mono_ae_restrict (by norm_num) hcint
          (hint n ε a b hε) hcmp
      rw [hhalf] at h1
      refine le_trans (le_of_eq ?_) h1
      rw [Real.mul_rpow (by norm_num) hT0, hs]
      have h2 : (2:ℝ) ^ (p/2 - 1) = (2:ℝ) ^ (p/2 - 2) * 2 := by
        have h3 := Real.rpow_add (by norm_num : (0:ℝ) < 2) (p/2 - 2) 1
        rw [Real.rpow_one, show p/2 - 2 + 1 = p/2 - 1 by ring] at h3
        linarith [h3]
      rw [h2]
      ring
