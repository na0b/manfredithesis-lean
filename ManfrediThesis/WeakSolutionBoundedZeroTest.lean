import ManfrediThesis.Preamble
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pZeroOn
import ManfrediThesis.SmoothCompactSupportMemW1p
import ManfrediThesis.WeakGradientPositivePart
import ManfrediThesis.WeakGradientLinear
import ManfrediThesis.WeakGradientZeroExtend
open MeasureTheory

/-- Testing the weak form of `div A(x,u,∇u) = B(x,u,∇u)` against an
**essentially bounded** `W^{1,p}_0` pair supported in a ball inside the domain.
This is the paper's own step at l. 1464-1469: `w` is "used as a test function in
the weak versions of (1.1), equation (1.2)".

Two hypotheses carry the right-hand side, and both are forced by `B` being only
`L¹`.  The test function must be essentially bounded, because the `B`-pairing is
an `L^∞`-`L¹` pairing and no bound on `∫ B φ_k` follows from `φ_k → φ` in `L^p`
alone; and `B(·,u,∇u)` must be integrable on the ball.  The truncation of the
approximating sequence that the proof performs is spent exactly there.

This is **not** `WeakSolutionZeroTest`.  That node is the `B = 0` case on a
single open set and asks nothing of the test function beyond
`MemW1pZeroOn`; it is the statement that suffices when the pairing is
`L^{p'}`-`L^p` throughout.  The present node carries a general `B`, adds the two
hypotheses just named, and separates the set `Ω` carrying the equation from the
ball `B_r(x₀)` carrying the test pair, which is what lets a `W^{1,p}_0(B_r)`
function test an equation posed on a larger `Ω`.  Neither statement implies the
other: setting `B = 0` and `Ω = B_r(x₀)` here still demands an essential bound
on `φ`, which `WeakSolutionZeroTest` does not require. -/
theorem WeakSolutionBoundedZeroTest :
    ∀ (n : ℕ) (p : ℝ), 1 ≤ n → 1 < p →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n))) (x₀ : EuclideanSpace ℝ (Fin n))
        (r : ℝ)
        (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n))
        (B : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (φ : EuclideanSpace ℝ (Fin n) → ℝ)
        (gφ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (T : ℝ),
        IsOpen Ω → 0 < r → Metric.ball x₀ r ⊆ Ω →
        IsWeakSolutionOn n p Ω A B u g →
        MemLp (fun x => A x (u x) (g x)) (ENNReal.ofReal (p / (p - 1)))
          (volume.restrict (Metric.ball x₀ r)) →
        IntegrableOn (fun x => B x (u x) (g x)) (Metric.ball x₀ r) volume →
        MemW1pZeroOn n p (Metric.ball x₀ r) φ gφ →
        0 ≤ T →
        (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ r)), |φ x| ≤ T) →
        (∫ x in Metric.ball x₀ r,
            ((∑ i, (A x (u x) (g x)) i * gφ x i) + B x (u x) (g x) * φ x)) = 0 := by
  intro n p hn hp Ω x₀ r A B u g φ gφ T hΩ hr hBsub hsol hALp hBint hzero hT0 hφT
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp
  have hp1 : (1:ℝ) ≤ p := hp.le
  have hbms : MeasurableSet (Metric.ball x₀ r) := measurableSet_ball
  have hbfin : volume (Metric.ball x₀ r) ≠ ⊤ := measure_ball_lt_top.ne
  have hbopen : IsOpen (Metric.ball x₀ r) := Metric.isOpen_ball
  obtain ⟨hφW, φk, hφkprop, hL1, hL2⟩ := hzero
  set T' := T + 1 with hT'def
  have hT'0 : (0:ℝ) < T' := by rw [hT'def]; linarith
  set Dφ : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun k x => WithLp.toLp 2 fun i =>
      fderiv ℝ (φk k) x (EuclideanSpace.single i (1 : ℝ)) with hDφdef
  -- Step 1: each `φk` lies in `W^{1,p}` of the ball
  have hφkW : ∀ k, MemW1pOn n p (Metric.ball x₀ r) (φk k) (Dφ k) := by
    intro k
    obtain ⟨hsm, hcs, hts⟩ := hφkprop k
    exact SmoothCompactSupportMemW1p n p hn hp1 (Metric.ball x₀ r) (φk k)
      hbopen hsm hcs hts
  -- Step 2: the symmetric truncation of any `W^{1,p}` pair on the ball
  have htrunc : ∀ (c : ℝ), 0 < c → ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      MemW1pOn n p (Metric.ball x₀ r) f G →
      MemW1pOn n p (Metric.ball x₀ r) (fun x => max (-c) (min (f x) c))
        (fun x => if -c < f x then (if f x < c then G x else 0) else 0) := by
    intro c hc f G hf
    have hΩ : IsOpen (Metric.ball x₀ r) := hbopen
    have hvol : volume (Metric.ball x₀ r) ≠ ⊤ := hbfin
    set Ω := Metric.ball x₀ r with hΩdef
    have hlin := WeakGradientLinear n p hn hp1 Ω
    have hconst : MemW1pOn n p Ω (fun _ => c) (fun _ => (0 : EuclideanSpace ℝ (Fin n))) :=
      (hlin f f G G 0 0 c hΩ).2.2.2 hvol
    have hconst' : MemW1pOn n p Ω (fun _ => -c) (fun _ => (0 : EuclideanSpace ℝ (Fin n))) :=
      (hlin f f G G 0 0 (-c) hΩ).2.2.2 hvol
    -- Step A: the negated pair
    have hA : MemW1pOn n p Ω (fun x => -f x) (fun x => -G x) := by
      have h := (hlin f f G G (-1) 0 0 hΩ).2.1 hf hf
      have e1 : (fun x => (-1 : ℝ) * f x + (0:ℝ) * f x) = (fun x => -f x) := by
        funext x; ring
      have e2 : (fun x => (-1 : ℝ) • G x + (0:ℝ) • G x) = (fun x => -G x) := by
        funext x; simp
      rwa [e1, e2] at h
    -- Step B: max (c - f) 0
    have hB : MemW1pOn n p Ω (fun x => max (c - f x) 0)
        (fun x => if f x < c then -G x else 0) := by
      have h := WeakGradientPositivePart n p (-c) hn hp1 Ω (fun x => -f x)
        (fun x => -G x) hΩ hvol hA
      have e1 : (fun x => max (-f x - -c) 0) = (fun x => max (c - f x) 0) := by
        funext x; congr 1; ring
      have e2 : (fun x => if -c < -f x then -G x else 0)
          = (fun x => if f x < c then -G x else 0) := by
        funext x
        by_cases h' : f x < c
        · rw [if_pos (by linarith), if_pos h']
        · rw [not_lt] at h'
          rw [if_neg (by rw [not_lt]; linarith), if_neg (by rw [not_lt]; exact h')]
      rwa [e1, e2] at h
    -- Step C: min f c
    have hC : MemW1pOn n p Ω (fun x => min (f x) c)
        (fun x => if f x < c then G x else 0) := by
      have h := (hlin (fun x => max (c - f x) 0) (fun _ => c)
        (fun x => if f x < c then -G x else 0) (fun _ => 0) (-1) 1 0 hΩ).2.1 hB hconst
      have e1 : (fun x => (-1 : ℝ) * max (c - f x) 0 + (1:ℝ) * c)
          = (fun x => min (f x) c) := by
        funext x
        rcases le_total (f x) c with h' | h'
        · rw [max_eq_left (by linarith), min_eq_left h']; ring
        · rw [max_eq_right (by linarith), min_eq_right h']; ring
      have e2 : (fun x => (-1 : ℝ) • (if f x < c then -G x else 0)
            + (1:ℝ) • (0 : EuclideanSpace ℝ (Fin n)))
          = (fun x => if f x < c then G x else 0) := by
        funext x
        by_cases h' : f x < c
        · rw [if_pos h', if_pos h']; simp
        · rw [if_neg h', if_neg h']; simp
      rwa [e1, e2] at h
    -- Step D: max (min f c + c) 0
    have hD : MemW1pOn n p Ω (fun x => max (min (f x) c + c) 0)
        (fun x => if -c < f x then (if f x < c then G x else 0) else 0) := by
      have h := WeakGradientPositivePart n p (-c) hn hp1 Ω (fun x => min (f x) c)
        (fun x => if f x < c then G x else 0) hΩ hvol hC
      have e1 : (fun x => max (min (f x) c - -c) 0)
          = (fun x => max (min (f x) c + c) 0) := by
        funext x; congr 1; ring
      have hiff : ∀ x, (-c < min (f x) c) ↔ (-c < f x) := by
        intro x
        rw [lt_min_iff]
        exact ⟨fun h' => h'.1, fun h' => ⟨h', by linarith⟩⟩
      have e2 : (fun x => if -c < min (f x) c then (if f x < c then G x else 0) else 0)
          = (fun x => if -c < f x then (if f x < c then G x else 0) else 0) := by
        funext x
        by_cases h' : -c < f x
        · rw [if_pos ((hiff x).mpr h'), if_pos h']
        · rw [if_neg (fun hh => h' ((hiff x).mp hh)), if_neg h']
      rwa [e1, e2] at h
    -- Step E: add the constant -c
    have h := (hlin (fun x => max (min (f x) c + c) 0) (fun _ => -c)
      (fun x => if -c < f x then (if f x < c then G x else 0) else 0) (fun _ => 0)
      1 1 0 hΩ).2.1 hD hconst'
    have e1 : (fun x => (1:ℝ) * max (min (f x) c + c) 0 + (1:ℝ) * -c)
        = (fun x => max (-c) (min (f x) c)) := by
      funext x
      rcases le_total (-c) (min (f x) c) with h' | h'
      · rw [max_eq_left (show (0:ℝ) ≤ min (f x) c + c by linarith),
          max_eq_right h']
        ring
      · rw [max_eq_right (show min (f x) c + c ≤ (0:ℝ) by linarith),
          max_eq_left h']
        ring
    have e2 : (fun x => (1:ℝ) • (if -c < f x then (if f x < c then G x else 0) else 0)
          + (1:ℝ) • (0 : EuclideanSpace ℝ (Fin n)))
        = (fun x => if -c < f x then (if f x < c then G x else 0) else 0) := by
      funext x; simp
    rwa [e1, e2] at h
  -- the truncated sequence and its weak gradient
  set ψ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun k x => max (-T') (min (φk k x) T') with hψdef
  set Gk : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun k x => if -T' < φk k x then (if φk k x < T' then Dφ k x else 0) else 0
    with hGkdef
  have hψW : ∀ k, MemW1pOn n p (Metric.ball x₀ r) (ψ k) (Gk k) :=
    fun k => htrunc T' hT'0 (φk k) (Dφ k) (hφkW k)
  have hψbd : ∀ k x, |ψ k x| ≤ T' := by
    intro k x
    rw [hψdef]
    simp only
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hψsupp : ∀ k, tsupport (ψ k) ⊆ tsupport (φk k) := by
    intro k
    refine closure_mono fun x hx => ?_
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro hz
    apply hx
    rw [hψdef]
    simp only
    rw [hz, min_eq_left hT'0.le, max_eq_right (by linarith)]
  have hψcs : ∀ k, HasCompactSupport (ψ k) := by
    intro k
    obtain ⟨hsm, hcs, hts⟩ := hφkprop k
    exact hcs.of_isClosed_subset isClosed_closure (hψsupp k)
  have hψts : ∀ k, tsupport (ψ k) ⊆ Metric.ball x₀ r := by
    intro k
    obtain ⟨hsm, hcs, hts⟩ := hφkprop k
    exact (hψsupp k).trans hts
  -- Step 3: the test identity for each `k`
  have hident : ∀ k, (∫ x in Metric.ball x₀ r,
      ((∑ i, (A x (u x) (g x)) i * Gk k x i) + B x (u x) (g x) * ψ k x)) = 0 := by
    intro k
    have hext := WeakGradientZeroExtend n p hn hp1 Ω x₀ r (ψ k) (Gk k) hΩ hBsub
      (hψW k) (hψcs k) (hψts k)
    have htsΩ : tsupport (ψ k) ⊆ Ω := (hψts k).trans hBsub
    obtain ⟨hint, hzero⟩ := hsol.2 (ψ k) ((Metric.ball x₀ r).indicator (Gk k))
      hext (hψcs k) htsΩ
    have hFvan : ∀ x ∉ Metric.ball x₀ r,
        ((∑ i, (A x (u x) (g x)) i * ((Metric.ball x₀ r).indicator (Gk k)) x i)
          + B x (u x) (g x) * ψ k x) = 0 := by
      intro x hx
      rw [Set.indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport (fun h => hx (hψts k h))]
      simp
    have e1 : (∫ x in Ω,
          ((∑ i, (A x (u x) (g x)) i * ((Metric.ball x₀ r).indicator (Gk k)) x i)
            + B x (u x) (g x) * ψ k x))
        = ∫ x, ((∑ i, (A x (u x) (g x)) i
              * ((Metric.ball x₀ r).indicator (Gk k)) x i)
            + B x (u x) (g x) * ψ k x) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hFvan x (fun h => hx (hBsub h)))
    have e2 : (∫ x in Metric.ball x₀ r,
          ((∑ i, (A x (u x) (g x)) i * ((Metric.ball x₀ r).indicator (Gk k)) x i)
            + B x (u x) (g x) * ψ k x))
        = ∫ x, ((∑ i, (A x (u x) (g x)) i
              * ((Metric.ball x₀ r).indicator (Gk k)) x i)
            + B x (u x) (g x) * ψ k x) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hFvan
    have e3 : (∫ x in Metric.ball x₀ r,
          ((∑ i, (A x (u x) (g x)) i * ((Metric.ball x₀ r).indicator (Gk k)) x i)
            + B x (u x) (g x) * ψ k x))
        = ∫ x in Metric.ball x₀ r,
          ((∑ i, (A x (u x) (g x)) i * Gk k x i) + B x (u x) (g x) * ψ k x) := by
      refine setIntegral_congr_fun hbms fun x hx => ?_
      rw [Set.indicator_of_mem hx]
    rw [← e3, e2, ← e1]
    exact hzero
  -- Step 4: the Lebesgue dictionary, and the a.e. convergent subsequence
  have hpne : ENNReal.ofReal p ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hp0
  have hdictR : ∀ (S : Set (EuclideanSpace ℝ (Fin n)))
      (v : EuclideanSpace ℝ (Fin n) → ℝ),
      MemLp v (ENNReal.ofReal p) (volume.restrict S) →
      (eLpNorm v (ENNReal.ofReal p) (volume.restrict S)).toReal
        = (∫ x in S, |v x| ^ p) ^ (1 / p) := by
    intro S v hv
    rw [hv.eLpNorm_eq_integral_rpow_norm hpne ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hp0.le]
    simp only [Real.norm_eq_abs, one_div]
  have hrpow0 : Filter.Tendsto (fun a : ℝ => a ^ (1 / p)) (nhds 0) (nhds 0) := by
    have h3 := (Real.continuousAt_rpow_const (0 : ℝ) (1 / p)
      (Or.inr (by positivity : (0:ℝ) ≤ 1 / p))).tendsto
    rwa [Real.zero_rpow (by positivity)] at h3
  have hdiffmem : ∀ k, MemLp (fun x => φk k x - φ x) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ r)) :=
    fun k => (hφkW k).2.1.sub hφW.2.1
  have hL1e : Filter.Tendsto
      (fun k => eLpNorm (fun x => φk k x - φ x) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ r))) Filter.atTop (nhds 0) := by
    have hr : ∀ k, eLpNorm (fun x => φk k x - φ x) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ r))
        = ENNReal.ofReal ((∫ x in Metric.ball x₀ r, |φ x - φk k x| ^ p) ^ (1 / p)) := by
      intro k
      rw [← ENNReal.ofReal_toReal (hdiffmem k).eLpNorm_lt_top.ne,
        hdictR _ _ (hdiffmem k)]
      congr 2
      refine setIntegral_congr_fun hbms fun x _ => ?_
      rw [abs_sub_comm]
    simp only [hr]
    have h4 : ENNReal.ofReal (0 : ℝ) = 0 := by simp
    rw [← h4]
    exact (ENNReal.continuous_ofReal.tendsto _).comp (hrpow0.comp hL1)
  obtain ⟨ns, hnsmono, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top
    hpne ENNReal.ofReal_ne_top (fun k => (hφkW k).2.1.1) hφW.2.1.1
    hL1e).exists_seq_tendsto_ae
  -- the Euclidean norm identity, which turns `hL2` into an `L^p` statement
  have hnormp : ∀ v : EuclideanSpace ℝ (Fin n),
      (∑ i, |v i| ^ 2) ^ (p / 2) = ‖v‖ ^ p := by
    intro v
    have hsum : (∑ i, ‖v i‖ ^ 2) = ∑ i, |v i| ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs]
    have h2 : (0:ℝ) ≤ ∑ i, |v i| ^ 2 := by positivity
    have h1 : ‖v‖ = (∑ i, |v i| ^ 2) ^ ((1:ℝ)/2) := by
      rw [EuclideanSpace.norm_eq, hsum, Real.sqrt_eq_rpow]
    rw [h1, ← Real.rpow_mul h2]
    congr 1
    ring
  have hgφLp : MemLp gφ (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ r)) := hφW.2.2
  have hgφp : Integrable (fun x => ‖gφ x‖ ^ p)
      (volume.restrict (Metric.ball x₀ r)) := by
    simpa [ENNReal.toReal_ofReal hp0.le] using hgφLp.integrable_norm_rpow hpne (by simp)
  have hL2' : Filter.Tendsto
      (fun k => ∫ x in Metric.ball x₀ r, ‖Dφ k x - gφ x‖ ^ p)
      Filter.atTop (nhds 0) := by
    refine hL2.congr fun k => ?_
    refine setIntegral_congr_fun hbms fun x _ => ?_
    rw [← hnormp (Dφ k x - gφ x)]
    refine congrArg (fun t : ℝ => t ^ (p/2)) (Finset.sum_congr rfl fun i _ => ?_)
    rw [show (Dφ k x - gφ x) i = Dφ k x i - gφ x i from by simp, abs_sub_comm]
  -- the excess term, written as an indicator so that its Lebesgue data is free
  set S : ℕ → Set (EuclideanSpace ℝ (Fin n)) :=
    fun k => {x | ¬(-T' < φk k x ∧ φk k x < T')} with hSdef
  have hSms : ∀ k, MeasurableSet (S k) := by
    intro k
    obtain ⟨hsm, hcs, hts⟩ := hφkprop k
    have h1 : IsOpen {x | -T' < φk k x} := isOpen_lt continuous_const hsm.continuous
    have h2 : IsOpen {x | φk k x < T'} := isOpen_lt hsm.continuous continuous_const
    rw [hSdef]
    exact ((h1.inter h2).measurableSet).compl
  set E : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun k => (S k).indicator (fun x => ‖gφ x‖ ^ p) with hEdef
  have hEnn : ∀ k x, 0 ≤ E k x := by
    intro k x
    rw [hEdef]
    exact Set.indicator_nonneg (fun y _ => Real.rpow_nonneg (norm_nonneg _) _) x
  have hEle : ∀ k x, E k x ≤ ‖gφ x‖ ^ p := by
    intro k x
    rw [hEdef]
    exact Set.indicator_le_self' (fun y _ => Real.rpow_nonneg (norm_nonneg _) _) x
  have hEmeas : ∀ k, AEStronglyMeasurable (E k)
      (volume.restrict (Metric.ball x₀ r)) := by
    intro k
    rw [hEdef]
    exact hgφp.aestronglyMeasurable.indicator (hSms k)
  have hEint : ∀ k, Integrable (E k) (volume.restrict (Metric.ball x₀ r)) := by
    intro k
    refine hgφp.mono' (hEmeas k) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hEnn k x)]
    exact hEle k x
  have hGkval : ∀ k x, (-T' < φk k x ∧ φk k x < T') → Gk k x = Dφ k x := by
    intro k x h
    rw [hGkdef]; simp only
    rw [if_pos h.1, if_pos h.2]
  have hGkzero : ∀ k x, ¬(-T' < φk k x ∧ φk k x < T') → Gk k x = 0 := by
    intro k x h
    rw [hGkdef]; simp only
    by_cases h1 : -T' < φk k x
    · rw [if_pos h1, if_neg (fun h2 => h ⟨h1, h2⟩)]
    · rw [if_neg h1]
  have hGpow : ∀ k x, ‖Gk k x - gφ x‖ ^ p
      ≤ (2:ℝ) ^ p * (‖Dφ k x - gφ x‖ ^ p + E k x) := by
    intro k x
    have hD0 : (0:ℝ) ≤ ‖Dφ k x - gφ x‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
    by_cases h : -T' < φk k x ∧ φk k x < T'
    · have hbd : ‖Gk k x - gφ x‖ ^ p ≤ ‖Dφ k x - gφ x‖ ^ p := by
        rw [hGkval k x h]
      have h1le : (1:ℝ) ≤ (2:ℝ) ^ p := Real.one_le_rpow (by norm_num) hp0.le
      nlinarith [hbd, hEnn k x, h1le, hD0]
    · have hEx : E k x = ‖gφ x‖ ^ p := by
        rw [hEdef]
        exact Set.indicator_of_mem (by rw [hSdef]; exact h) _
      have hbd : ‖Gk k x - gφ x‖ ^ p = ‖gφ x‖ ^ p := by
        rw [hGkzero k x h, zero_sub, norm_neg]
      have h2 : (0:ℝ) < (2:ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
      have h1le : (1:ℝ) ≤ (2:ℝ) ^ p :=
        Real.one_le_rpow (by norm_num) hp0.le
      rw [hbd, hEx]
      nlinarith [hD0, h1le, Real.rpow_nonneg (norm_nonneg (gφ x)) p]
  have hEtend : Filter.Tendsto (fun j => ∫ x in Metric.ball x₀ r, E (ns j) x)
      Filter.atTop (nhds 0) := by
    have hlim : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ r)),
        Filter.Tendsto (fun j => E (ns j) x) Filter.atTop (nhds ((0:ℝ))) := by
      filter_upwards [hae, hφT] with x hx hbdx
      have heq : ∀ᶠ j in Filter.atTop, E (ns j) x = 0 := by
        obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hx 1 one_pos
        filter_upwards [Filter.eventually_ge_atTop N] with j hj
        have hj' : |φk (ns j) x - φ x| < 1 := by
          simpa [Real.dist_eq] using hN j hj
        have h2 : -T' < φk (ns j) x ∧ φk (ns j) x < T' := by
          rw [abs_lt] at hj'
          rw [abs_le] at hbdx
          rw [hT'def]
          exact ⟨by linarith [hbdx.1, hj'.1], by linarith [hbdx.2, hj'.2]⟩
        rw [hEdef]
        refine Set.indicator_of_notMem ?_ _
        rw [hSdef]
        exact fun hcon => hcon h2
      exact Filter.Tendsto.congr' (heq.mono fun j hj => hj.symm)
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0:ℝ)) Filter.atTop (nhds 0))
    have h := tendsto_integral_of_dominated_convergence (fun x => ‖gφ x‖ ^ p)
      (fun j => hEmeas (ns j)) hgφp
      (fun j => Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hEnn (ns j) x)]
        exact hEle (ns j) x)
      hlim
    simpa using h
  -- the `L^p` convergence of the truncated gradients
  have hGdiffLp : ∀ k, MemLp (fun x => Gk k x - gφ x) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ r)) := fun k => (hψW k).2.2.sub hgφLp
  have hpowint : ∀ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      MemLp H (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ r)) →
      Integrable (fun x => ‖H x‖ ^ p) (volume.restrict (Metric.ball x₀ r)) := by
    intro H hH
    simpa [ENNReal.toReal_ofReal hp0.le] using hH.integrable_norm_rpow hpne (by simp)
  have hGconv : Filter.Tendsto
      (fun j => ∫ x in Metric.ball x₀ r, ‖Gk (ns j) x - gφ x‖ ^ p)
      Filter.atTop (nhds 0) := by
    have hlow : ∀ j, (0:ℝ) ≤ ∫ x in Metric.ball x₀ r, ‖Gk (ns j) x - gφ x‖ ^ p :=
      fun j => setIntegral_nonneg hbms fun x _ => Real.rpow_nonneg (norm_nonneg _) _
    have hup : ∀ j, (∫ x in Metric.ball x₀ r, ‖Gk (ns j) x - gφ x‖ ^ p)
        ≤ (2:ℝ) ^ p * ((∫ x in Metric.ball x₀ r, ‖Dφ (ns j) x - gφ x‖ ^ p)
          + ∫ x in Metric.ball x₀ r, E (ns j) x) := by
      intro j
      have hD : Integrable (fun x => ‖Dφ (ns j) x - gφ x‖ ^ p)
          (volume.restrict (Metric.ball x₀ r)) :=
        hpowint (fun x => Dφ (ns j) x - gφ x) ((hφkW (ns j)).2.2.sub hgφLp)
      have e : (2:ℝ) ^ p * ((∫ x in Metric.ball x₀ r, ‖Dφ (ns j) x - gφ x‖ ^ p)
            + ∫ x in Metric.ball x₀ r, E (ns j) x)
          = ∫ x in Metric.ball x₀ r,
              (2:ℝ) ^ p * (‖Dφ (ns j) x - gφ x‖ ^ p + E (ns j) x) := by
        rw [integral_const_mul, integral_add hD (hEint (ns j))]
      rw [e]
      exact integral_mono (hpowint _ (hGdiffLp (ns j)))
        ((hD.add (hEint (ns j))).const_mul _) fun x => hGpow (ns j) x
    have h1 := hL2'.comp hnsmono.tendsto_atTop
    have hmaj : Filter.Tendsto
        (fun j => (2:ℝ) ^ p * ((∫ x in Metric.ball x₀ r, ‖Dφ (ns j) x - gφ x‖ ^ p)
          + ∫ x in Metric.ball x₀ r, E (ns j) x)) Filter.atTop (nhds 0) := by
      have h2 := (h1.add hEtend).const_mul ((2:ℝ) ^ p)
      simpa using h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmaj hlow hup
  -- the Hölder pairing
  have hIP : ∀ a b : EuclideanSpace ℝ (Fin n),
      (∑ i, a i * b i) = (innerSL ℝ b) a := by
    intro a b
    show (∑ i, a i * b i) = inner ℝ b a
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hCS : ∀ a b : EuclideanSpace ℝ (Fin n), |∑ i, a i * b i| ≤ ‖a‖ * ‖b‖ := by
    intro a b
    rw [hIP a b, mul_comm ‖a‖ ‖b‖]
    exact abs_real_inner_le_norm b a
  have hconj : Real.HolderConjugate p (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have hconj' : Real.HolderConjugate (p / (p - 1)) p := hconj.symm
  have hHT : ENNReal.HolderTriple (ENNReal.ofReal (p / (p - 1)))
      (ENNReal.ofReal p) 1 :=
    ⟨by rw [inv_one]; exact hconj'.inv_add_inv_ennreal⟩
  have hpairint : ∀ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      MemLp H (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ r)) →
      IntegrableOn (fun x => ∑ i, (A x (u x) (g x)) i * H x i)
        (Metric.ball x₀ r) volume := by
    intro H hH
    have hprod : Integrable (fun x => ‖A x (u x) (g x)‖ * ‖H x‖)
        (volume.restrict (Metric.ball x₀ r)) := hALp.norm.integrable_mul hH.norm
    have hmeas : AEStronglyMeasurable (fun x => ∑ i, (A x (u x) (g x)) i * H x i)
        (volume.restrict (Metric.ball x₀ r)) := by
      have hinner : AEStronglyMeasurable
          (fun x => (inner ℝ (H x) (A x (u x) (g x)) : ℝ))
          (volume.restrict (Metric.ball x₀ r)) :=
        (continuous_inner (𝕜 := ℝ)
          (E := EuclideanSpace ℝ (Fin n))).comp_aestronglyMeasurable
          (hH.aestronglyMeasurable.prodMk hALp.aestronglyMeasurable)
      exact hinner.congr (Filter.Eventually.of_forall fun x =>
        (hIP (A x (u x) (g x)) (H x)).symm)
    refine hprod.mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hCS _ _
  have hholder : ∀ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      MemLp H (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ r)) →
      |∫ x in Metric.ball x₀ r, ∑ i, (A x (u x) (g x)) i * H x i|
        ≤ (∫ x in Metric.ball x₀ r, ‖A x (u x) (g x)‖ ^ (p / (p - 1))) ^ ((p - 1) / p)
          * (∫ x in Metric.ball x₀ r, ‖H x‖ ^ p) ^ (1 / p) := by
    intro H hH
    have hprod : Integrable (fun x => ‖A x (u x) (g x)‖ * ‖H x‖)
        (volume.restrict (Metric.ball x₀ r)) := hALp.norm.integrable_mul hH.norm
    have h1 : |∫ x in Metric.ball x₀ r, ∑ i, (A x (u x) (g x)) i * H x i|
        ≤ ∫ x in Metric.ball x₀ r, ‖A x (u x) (g x)‖ * ‖H x‖ := by
      refine le_trans abs_integral_le_integral_abs ?_
      exact integral_mono (hpairint H hH).abs hprod fun x => hCS _ _
    refine le_trans h1 ?_
    have h2 := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume.restrict (Metric.ball x₀ r)) hconj'
      (Filter.Eventually.of_forall fun x => norm_nonneg (A x (u x) (g x)))
      (Filter.Eventually.of_forall fun x => norm_nonneg (H x)) hALp.norm hH.norm
    rwa [show 1 / (p / (p - 1)) = (p - 1) / p by field_simp] at h2
  -- the `A`-pairing passes to the limit
  have hAconv : Filter.Tendsto
      (fun j => ∫ x in Metric.ball x₀ r,
        ∑ i, (A x (u x) (g x)) i * Gk (ns j) x i)
      Filter.atTop (nhds (∫ x in Metric.ball x₀ r,
        ∑ i, (A x (u x) (g x)) i * gφ x i)) := by
    rw [← tendsto_sub_nhds_zero_iff]
    have hdiffeq : ∀ j, (∫ x in Metric.ball x₀ r,
          ∑ i, (A x (u x) (g x)) i * Gk (ns j) x i)
        - (∫ x in Metric.ball x₀ r, ∑ i, (A x (u x) (g x)) i * gφ x i)
        = ∫ x in Metric.ball x₀ r,
            ∑ i, (A x (u x) (g x)) i * (Gk (ns j) x - gφ x) i := by
      intro j
      rw [← integral_sub (hpairint _ (hψW (ns j)).2.2) (hpairint _ hgφLp)]
      refine setIntegral_congr_fun hbms fun x _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (Gk (ns j) x - gφ x) i = Gk (ns j) x i - gφ x i from by simp]
      ring
    simp only [hdiffeq]
    have hC0 : (0:ℝ) ≤ (∫ x in Metric.ball x₀ r,
        ‖A x (u x) (g x)‖ ^ (p / (p - 1))) ^ ((p - 1) / p) :=
      Real.rpow_nonneg (setIntegral_nonneg hbms fun x _ =>
        Real.rpow_nonneg (norm_nonneg _) _) _
    have hmaj : Filter.Tendsto
        (fun j => (∫ x in Metric.ball x₀ r,
            ‖A x (u x) (g x)‖ ^ (p / (p - 1))) ^ ((p - 1) / p)
          * (∫ x in Metric.ball x₀ r, ‖Gk (ns j) x - gφ x‖ ^ p) ^ (1 / p))
        Filter.atTop (nhds 0) := by
      have h := (hrpow0.comp hGconv).const_mul ((∫ x in Metric.ball x₀ r,
        ‖A x (u x) (g x)‖ ^ (p / (p - 1))) ^ ((p - 1) / p))
      simpa [Function.comp_def] using h
    refine squeeze_zero_norm' (Filter.Eventually.of_forall fun j => ?_) hmaj
    rw [Real.norm_eq_abs]
    exact hholder _ (hGdiffLp (ns j))
  -- the `B`-pairing passes to the limit
  have hψcont : ∀ k, Continuous (ψ k) := by
    intro k
    obtain ⟨hsm, hcs, hts⟩ := hφkprop k
    rw [hψdef]
    exact continuous_const.max ((hsm.continuous).min continuous_const)
  have hBψint : ∀ k, IntegrableOn (fun x => B x (u x) (g x) * ψ k x)
      (Metric.ball x₀ r) volume := by
    intro k
    refine (hBint.abs.const_mul T').mono'
      (hBint.aestronglyMeasurable.mul (hψcont k).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hψbd k x) (abs_nonneg _)
  have hBφint : IntegrableOn (fun x => B x (u x) (g x) * φ x)
      (Metric.ball x₀ r) volume := by
    refine (hBint.abs.const_mul T').mono'
      (hBint.aestronglyMeasurable.mul hφW.2.1.aestronglyMeasurable) ?_
    filter_upwards [hφT] with x hx
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [hT'def]; linarith
  have hBconv : Filter.Tendsto
      (fun j => ∫ x in Metric.ball x₀ r, B x (u x) (g x) * ψ (ns j) x)
      Filter.atTop (nhds (∫ x in Metric.ball x₀ r, B x (u x) (g x) * φ x)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => T' * |B x (u x) (g x)|)
      (fun j => hBint.aestronglyMeasurable.mul (hψcont (ns j)).aestronglyMeasurable)
      (hBint.abs.const_mul T')
      (fun j => Filter.Eventually.of_forall fun x => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hψbd (ns j) x) (abs_nonneg _)
    · filter_upwards [hae, hφT] with x hx hbdx
      have hτ : Filter.Tendsto (fun j => ψ (ns j) x) Filter.atTop (nhds (φ x)) := by
        have hcont : Filter.Tendsto (fun t : ℝ => max (-T') (min t T'))
            (nhds (φ x)) (nhds (max (-T') (min (φ x) T'))) :=
          (continuous_const.max (continuous_id.min continuous_const)).tendsto _
        have hval : max (-T') (min (φ x) T') = φ x := by
          rw [abs_le] at hbdx
          rw [min_eq_left (by rw [hT'def]; linarith [hbdx.2]),
            max_eq_right (by rw [hT'def]; linarith [hbdx.1])]
        rw [← hval]
        exact hcont.comp hx
      exact (hτ.const_mul _)
  -- assembly
  have hsplitk : ∀ j, (∫ x in Metric.ball x₀ r,
        ((∑ i, (A x (u x) (g x)) i * Gk (ns j) x i) + B x (u x) (g x) * ψ (ns j) x))
      = (∫ x in Metric.ball x₀ r, ∑ i, (A x (u x) (g x)) i * Gk (ns j) x i)
        + ∫ x in Metric.ball x₀ r, B x (u x) (g x) * ψ (ns j) x :=
    fun j => integral_add (hpairint _ (hψW (ns j)).2.2) (hBψint (ns j))
  have htargetsplit : (∫ x in Metric.ball x₀ r,
        ((∑ i, (A x (u x) (g x)) i * gφ x i) + B x (u x) (g x) * φ x))
      = (∫ x in Metric.ball x₀ r, ∑ i, (A x (u x) (g x)) i * gφ x i)
        + ∫ x in Metric.ball x₀ r, B x (u x) (g x) * φ x :=
    integral_add (hpairint _ hgφLp) hBφint
  rw [htargetsplit]
  have hzeroseq : ∀ j, (∫ x in Metric.ball x₀ r,
        ∑ i, (A x (u x) (g x)) i * Gk (ns j) x i)
      + (∫ x in Metric.ball x₀ r, B x (u x) (g x) * ψ (ns j) x) = 0 := by
    intro j
    rw [← hsplitk j]
    exact hident (ns j)
  have h0 : Filter.Tendsto (fun _ : ℕ => (0:ℝ)) Filter.atTop
      (nhds ((∫ x in Metric.ball x₀ r, ∑ i, (A x (u x) (g x)) i * gφ x i)
        + ∫ x in Metric.ball x₀ r, B x (u x) (g x) * φ x)) :=
    (hAconv.add hBconv).congr hzeroseq
  exact tendsto_nhds_unique h0 tendsto_const_nhds
