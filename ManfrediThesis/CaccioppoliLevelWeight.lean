import ManfrediThesis.Preamble
import ManfrediThesis.EllipticStructureQ12
import ManfrediThesis.CitedRegularityEpsPos
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.DifferentiatedEquationWeak
import ManfrediThesis.WeakGradientPositivePart
import ManfrediThesis.WeakGradientSmoothMul
import ManfrediThesis.WeakGradientRestrict
import ManfrediThesis.WeakGradientLinear
import ManfrediThesis.WeightedCaccioppoliSignedCore
open MeasureTheory

/-- Inequality (3.4): a Caccioppoli inequality at the levels of `D_k u`, in both
the `+` and the `-` case, with a constant depending only on `n`, `p` and the
bound `r` for the structure ratio `γ₁/γ₀`. -/
theorem CaccioppoliLevelWeight :
    ∀ (n : ℕ) (p r : ℝ), 2 ≤ n → 1 < p → 0 < r →
      ∃ c : ℝ, 0 < c ∧
        ∀ (ε γ₀ γ₁ : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
          (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (Dg : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (ζ : EuclideanSpace ℝ (Fin n) → ℝ) (k : Fin n) (l : ℝ),
          0 < ε → 0 < γ₀ → γ₁ ≤ r * γ₀ → IsOpen Ω →
          EllipticStructureQ12 n p ε γ₀ γ₁ Ω (fun _ _ h => A h) →
          CitedRegularityEpsPos n p ε γ₀ γ₁ Ω A →
          IsWeakSolutionOn n p Ω (fun _ _ h => A h) (fun _ _ _ => 0) u g →
          (∀ i : Fin n, MemW1pLocOn n 2 Ω (fun x => g x i) (Dg i)) →
          ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
          (∫ x in Ω ∩ {y | l < g y k},
                (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
              ≤ c * ∫ x in Ω, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
                  * max (g x k - l) 0 ^ 2
                  * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2
            ∧ (∫ x in Ω ∩ {y | g y k < l},
                (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) * ‖Dg k x‖ ^ 2 * ζ x ^ 2)
              ≤ c * ∫ x in Ω, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1)
                  * max (l - g x k) 0 ^ 2
                  * ∑ i, (fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 := by
  intro n p r hn hp hr
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  refine ⟨4 * (n : ℝ) ^ 2 * r ^ 2, by positivity, ?_⟩
  intro ε γ₀ γ₁ Ω A u g Dg ζ k l hε hγ₀ hγ₁r hΩ hQ hC1 hsol hDg hζsm hζcs hζΩ
  -- the weight `w` and its power `W`
  obtain ⟨w, hwdef⟩ : ∃ w : EuclideanSpace ℝ (Fin n) → ℝ,
      w = fun x => ε + ‖g x‖ ^ 2 := ⟨_, rfl⟩
  have hweq : ∀ x, w x = ε + ‖g x‖ ^ 2 := fun x => by rw [hwdef]
  obtain ⟨W, hWdef⟩ : ∃ W : EuclideanSpace ℝ (Fin n) → ℝ,
      W = fun x => w x ^ (p / 2 - 1) := ⟨_, rfl⟩
  have hWeq : ∀ x, W x = w x ^ (p / 2 - 1) := fun x => by rw [hWdef]
  have hWval : ∀ x, (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) = W x := fun x => by
    rw [hWeq x, hweq x]
  simp only [hWval]
  -- Step 0: the degenerate case `Ω = ∅`
  rcases Set.eq_empty_or_nonempty Ω with hΩe | hΩne
  · rw [hΩe]
    constructor <;> simp
  -- Step 1: `γ₀ ≤ γ₁`
  have hγ : γ₀ ≤ γ₁ := by
    obtain ⟨i0⟩ : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
    obtain ⟨e, hedef⟩ : ∃ e : EuclideanSpace ℝ (Fin n),
        e = EuclideanSpace.single i0 (1 : ℝ) := ⟨_, rfl⟩
    have hen : ‖e‖ = 1 := by rw [hedef]; simp
    have hen2 : ‖e‖ ^ 2 = 1 := by rw [hen]; norm_num
    have hguard : ε + ‖e‖ ^ 2 ≠ 0 := by rw [hen2]; positivity
    have hneb : Filter.NeBot (ae (volume.restrict Ω)) := by
      refine ae_neBot.2 ?_
      simp only [ne_eq, Measure.restrict_eq_zero]
      exact (hΩ.measure_pos volume hΩne).ne'
    obtain ⟨x, ⟨hx1, hx2⟩, hxΩ⟩ :=
      ((ae_restrict_of_ae (hQ.Q1.and hQ.Q2)).and
        (ae_restrict_mem hΩ.measurableSet)).exists
    have hQ1 := hx1 hxΩ 0 e e hguard
    have hQ2 := hx2 hxΩ 0 e i0 i0 hguard
    have hsum : (∑ i, (fderiv ℝ (fun h => A h) e e) i * e i)
        = (fderiv ℝ (fun h => A h) e e) i0 := by
      rw [hedef]
      simp
    rw [hsum, hen2, mul_one] at hQ1
    rw [← hedef, hen2] at hQ2
    have hpow : (0 : ℝ) < (ε + 1) ^ (p / 2 - 1) :=
      Real.rpow_pos_of_pos (by linarith) _
    have hle : (fderiv ℝ (fun h => A h) e e) i0 ≤ γ₁ * (ε + 1) ^ (p / 2 - 1) :=
      le_trans (le_abs_self _) hQ2
    exact le_of_mul_le_mul_right (by linarith) hpow
  -- Step 2: the continuous representative supplied by (C1)
  obtain ⟨-, g', hg'cont, hg'ae, -⟩ := hC1 hε hQ u g hsol
  -- a transfer of integrals from an intermediate open set to `Ω`
  have htrans : ∀ (V B : Set (EuclideanSpace ℝ (Fin n)))
      (F : EuclideanSpace ℝ (Fin n) → ℝ),
      MeasurableSet V → V ⊆ Ω → B ⊆ V → (∀ x, x ∉ B → F x = 0) →
      (∫ x in V, F x) = ∫ x in Ω, F x := by
    intro V B F hVm hVΩ hBV hF
    rw [← integral_indicator hVm, ← integral_indicator hΩ.measurableSet]
    congr 1
    funext x
    by_cases hxV : x ∈ V
    · rw [Set.indicator_of_mem hxV, Set.indicator_of_mem (hVΩ hxV)]
    · rw [Set.indicator_of_notMem hxV]
      by_cases hxΩ : x ∈ Ω
      · rw [Set.indicator_of_mem hxΩ, hF x (fun hc => hxV (hBV hc))]
      · rw [Set.indicator_of_notMem hxΩ]
  have hloccongr : ∀ (f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ)
      (G₁ G₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      (∀ x, f₁ x = f₂ x) → (∀ x, G₁ x = G₂ x) →
      MemW1pLocOn n 2 Ω f₁ G₁ → MemW1pLocOn n 2 Ω f₂ G₂ := by
    intro f₁ f₂ G₁ G₂ hf hG h
    rw [← funext hf, ← funext hG]
    exact h
  -- Steps 3a-3d: the positive part of a `W^{1,2}_loc` function, on all of `Ω`
  have hposloc : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (cc : ℝ),
      MemW1pLocOn n 2 Ω f G →
      MemW1pLocOn n 2 Ω (fun x => max (f x - cc) 0)
        (fun x => if cc < f x then G x else 0) := by
    intro f G cc hf
    have hV : ∀ L : Set (EuclideanSpace ℝ (Fin n)), IsCompact L → L ⊆ Ω →
        ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ L ⊆ V ∧ V ⊆ Ω ∧
          MemW1pOn n 2 V (fun x => max (f x - cc) 0)
            (fun x => if cc < f x then G x else 0) := by
      intro L hL hLΩ
      obtain ⟨C, hCcpt, hLC, hCΩ⟩ := exists_compact_between hL hΩ hLΩ
      have hVΩ : interior C ⊆ Ω := subset_trans interior_subset hCΩ
      have hclsub : closure (interior C) ⊆ C :=
        closure_minimal interior_subset hCcpt.isClosed
      have hclcpt : IsCompact (closure (interior C)) :=
        hCcpt.of_isClosed_subset isClosed_closure hclsub
      have hvol : volume (interior C) ≠ ⊤ :=
        ne_top_of_le_ne_top hCcpt.measure_lt_top.ne (measure_mono interior_subset)
      have h6 : MemW1pOn n 2 (interior C) f G :=
        (WeakGradientRestrict n 2 (by omega) (by norm_num) Ω (interior C) f G
          hΩ isOpen_interior hVΩ).2.2.2 hf hclcpt (subset_trans hclsub hCΩ)
      exact ⟨interior C, isOpen_interior, hLC, hVΩ,
        WeakGradientPositivePart n 2 cc (by omega) (by norm_num) (interior C) f G
          isOpen_interior hvol h6⟩
    refine ⟨?_, ?_⟩
    · intro θ hθsm hθcs hθΩ i
      obtain ⟨V, hVop, hLV, hVΩ, hmem⟩ := hV (tsupport θ) hθcs hθΩ
      have hid := hmem.1 θ hθsm hθcs hLV i
      have e1 : (∫ x in V, max (f x - cc) 0
            * fderiv ℝ θ x (EuclideanSpace.single i (1 : ℝ)))
          = ∫ x in Ω, max (f x - cc) 0
            * fderiv ℝ θ x (EuclideanSpace.single i (1 : ℝ)) := by
        refine htrans V (tsupport θ) _ hVop.measurableSet hVΩ hLV (fun x hx => ?_)
        rw [fderiv_of_notMem_tsupport ℝ hx]
        simp
      have e2 : (∫ x in V, (if cc < f x then G x else 0) i * θ x)
          = ∫ x in Ω, (if cc < f x then G x else 0) i * θ x := by
        refine htrans V (tsupport θ) _ hVop.measurableSet hVΩ hLV (fun x hx => ?_)
        rw [image_eq_zero_of_notMem_tsupport hx]
        ring
      rw [← e1, ← e2]
      exact hid
    · intro K hK hKΩ
      obtain ⟨V, hVop, hKV, hVΩ, hmem⟩ := hV K hK hKΩ
      exact ⟨hmem.2.1.mono_measure (Measure.restrict_mono hKV le_rfl),
        hmem.2.2.mono_measure (Measure.restrict_mono hKV le_rfl)⟩
  -- the two test pairs of Steps 3 and 4
  have hplus : MemW1pLocOn n 2 Ω (fun x => max (g x k - l) 0)
      (fun x => if l < g x k then Dg k x else 0) :=
    hposloc (fun x => g x k) (Dg k) l (hDg k)
  have hneg0 : MemW1pLocOn n 2 Ω (fun x => -(g x k)) (fun x => -(Dg k x)) := by
    have hsrc := (WeakGradientLinear n 2 (by omega) (by norm_num) Ω
      (fun x => g x k) (fun x => g x k) (Dg k) (Dg k) (-1) 0 0 hΩ).1 (hDg k) (hDg k)
    refine hloccongr _ _ _ _ (fun x => by ring) (fun x => ?_) hsrc
    show (-1 : ℝ) • Dg k x + (0 : ℝ) • Dg k x = -(Dg k x)
    rw [neg_smul, one_smul, zero_smul, add_zero]
  have hminus : MemW1pLocOn n 2 Ω (fun x => max (l - g x k) 0)
      (fun x => if g x k < l then -(Dg k x) else 0) := by
    refine hloccongr _ _ _ _ (fun x => by ring_nf) (fun x => ?_)
      (hposloc (fun x => -(g x k)) (fun x => -(Dg k x)) (-l) hneg0)
    by_cases hx : g x k < l
    · rw [if_pos (by linarith : (-l : ℝ) < -(g x k)), if_pos hx]
    · rw [if_neg (not_lt.2 (by have h := not_lt.1 hx; linarith)), if_neg hx]
  -- the sign-free core of Steps 3-9.  This is `WeightedCaccioppoliSignedCore`,
  -- whose docstring records the route (the test pair `(v ζ², ζ² Z + v ∇(ζ²))`,
  -- `DifferentiatedEquationWeak` against it, `Q1` on the left and `Q2` with two
  -- index Cauchy-Schwarz steps on the right, then one Cauchy-Schwarz in the
  -- integral and `γ₁ ≤ r γ₀`).
  have hWdef' : W = fun x => (ε + ‖g x‖ ^ 2) ^ (p / 2 - 1) :=
    funext fun x => (hWval x).symm
  have key := WeightedCaccioppoliSignedCore n p r hn hp hr ε γ₀ γ₁ Ω A u g Dg ζ k
    hε hγ₀ hγ₁r hγ hΩ hΩne hQ hC1 hsol hDg hζsm hζcs hζΩ W hWdef'
  -- the two level sets, taken on the continuous representative
  have hcontk : ContinuousOn (fun y => g' y k) Ω :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp_continuousOn hg'cont
  have hgae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∈ Ω → g x = g' x := (ae_restrict_iff' hΩ.measurableSet).1 hg'ae
  have hTpOpen : IsOpen (Ω ∩ {y | l < g' y k}) := by
    have h := hcontk.isOpen_inter_preimage hΩ (isOpen_Ioi (a := l))
    exact h
  have hTmOpen : IsOpen (Ω ∩ {y | g' y k < l}) := by
    have h := hcontk.isOpen_inter_preimage hΩ (isOpen_Iio (a := l))
    exact h
  have hTpres : volume.restrict (Ω ∩ {y | l < g y k})
      = volume.restrict (Ω ∩ {y | l < g' y k}) := by
    refine Measure.restrict_congr_set (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [hgae] with x hx
    constructor
    · rintro ⟨hxΩ, hxl⟩
      refine ⟨hxΩ, ?_⟩
      show l < g' x k
      rw [← hx hxΩ]
      exact hxl
    · rintro ⟨hxΩ, hxl⟩
      refine ⟨hxΩ, ?_⟩
      show l < g x k
      rw [hx hxΩ]
      exact hxl
  have hTmres : volume.restrict (Ω ∩ {y | g y k < l})
      = volume.restrict (Ω ∩ {y | g' y k < l}) := by
    refine Measure.restrict_congr_set (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [hgae] with x hx
    constructor
    · rintro ⟨hxΩ, hxl⟩
      refine ⟨hxΩ, ?_⟩
      show g' x k < l
      rw [← hx hxΩ]
      exact hxl
    · rintro ⟨hxΩ, hxl⟩
      refine ⟨hxΩ, ?_⟩
      show g x k < l
      rw [hx hxΩ]
      exact hxl
  constructor
  · rw [hTpres]
    refine key (Ω ∩ {y | l < g' y k}) 1 _ _ (Or.inl rfl) hTpOpen.measurableSet
      Set.inter_subset_left (fun x => le_max_right _ _) ?_ hplus
    filter_upwards [hg'ae, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
    have hgk : g x k = g' x k := by rw [hx]
    constructor
    · rintro ⟨-, hxl⟩
      have hlt : l < g x k := by rw [hgk]; exact hxl
      rw [if_pos hlt, one_smul]
    · intro hxT
      have hnl : ¬ (l < g' x k) := fun hc => hxT ⟨hxΩ, hc⟩
      have hle : g x k ≤ l := by
        rw [hgk]
        exact not_lt.1 hnl
      exact ⟨if_neg (not_lt.2 hle), max_eq_right (by linarith)⟩
  · rw [hTmres]
    refine key (Ω ∩ {y | g' y k < l}) (-1) _ _ (Or.inr rfl) hTmOpen.measurableSet
      Set.inter_subset_left (fun x => le_max_right _ _) ?_ hminus
    filter_upwards [hg'ae, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
    have hgk : g x k = g' x k := by rw [hx]
    constructor
    · rintro ⟨-, hxl⟩
      have hlt : g x k < l := by rw [hgk]; exact hxl
      rw [if_pos hlt, neg_smul, one_smul]
    · intro hxT
      have hnl : ¬ (g' x k < l) := fun hc => hxT ⟨hxΩ, hc⟩
      have hle : l ≤ g x k := by
        rw [hgk]
        exact not_lt.1 hnl
      exact ⟨if_neg (not_lt.2 hle), max_eq_right (by linarith)⟩
