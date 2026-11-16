import ManfrediThesis.Preamble
import ManfrediThesis.EssOscOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemHolderOn
import ManfrediThesis.OscillationDecayToHolder
import ManfrediThesis.AEModificationInvariance
open MeasureTheory

/-- The inner domain of §4 and the continuous representative on it: for a
bounded `W^{1,p}` function obeying the De Giorgi oscillation decay on every ball
whose closure lies in `Ω`, the `d/2`-neighbourhood `Ω₁` of `Ω'` is compactly
contained in `Ω` with a `d/2` margin, and `u` has a representative that is
continuous on `Ω₁`, Hölder continuous of exponent `α` on every ball of radius
`d/16` centred in `Ω₁`, and carries the same weak gradient `g`. -/
theorem InnerDomainRepresentative :
    ∀ (n : ℕ) (p α d₀ M d : ℝ), 1 ≤ n → 1 ≤ p → 0 < α → α ≤ 1 → 0 < d₀ →
      0 ≤ M → 0 < d →
      ∀ (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        IsOpen Ω → Ω'.Nonempty → Bornology.IsBounded Ω' →
        (∀ x ∈ Ω', ∀ y, y ∉ Ω → d ≤ dist x y) →
        MemW1pOn n p Ω u g →
        (∀ᵐ x ∂(volume.restrict Ω), |u x| ≤ M) →
        (∀ (y : EuclideanSpace ℝ (Fin n)) (R₃ ρ : ℝ),
          Metric.closedBall y R₃ ⊆ Ω → 0 < ρ → ρ ≤ R₃ →
          EssOscOn n (Metric.ball y ρ) u
            ≤ (4 : ℝ) ^ α * max (EssOscOn n (Metric.ball y R₃) u) (d₀ * R₃)
              * (ρ / R₃) ^ α) →
        ∃ (Ω₁ : Set (EuclideanSpace ℝ (Fin n)))
          (U : EuclideanSpace ℝ (Fin n) → ℝ),
          IsOpen Ω₁ ∧ Bornology.IsBounded Ω₁ ∧ closure Ω' ⊆ Ω₁ ∧
            closure Ω₁ ⊆ Ω ∧
            (∀ x ∈ Ω', ∀ y, y ∉ Ω₁ → d / 2 ≤ dist x y) ∧
            (∀ x ∈ Ω₁, ∀ y, y ∉ Ω → d / 2 ≤ dist x y) ∧
            (∀ x ∈ Ω₁, Metric.closedBall x (d / 2) ⊆ Ω) ∧
            (∀ᵐ x ∂(volume.restrict Ω), U x = u x) ∧
            MemW1pOn n p Ω U g ∧
            ContinuousOn U Ω₁ ∧
            (∀ x ∈ Ω₁, MemHolderOn n α (Metric.closedBall x (d / 16)) U) := by
  intro n p α d₀ M d hn1 hp1 hα hα1 hd₀ hM hd Ω Ω' u g hΩ hΩ'ne hΩ'bdd hsep hW hMu hdecay
  classical
  -- Step 1: the two inner domains.
  obtain ⟨Ω₁, hΩ₁⟩ : ∃ S : Set (EuclideanSpace ℝ (Fin n)),
      S = {x : EuclideanSpace ℝ (Fin n) | Metric.infDist x Ω' < d / 2} := ⟨_, rfl⟩
  obtain ⟨Ω₂, hΩ₂⟩ : ∃ S : Set (EuclideanSpace ℝ (Fin n)),
      S = {x : EuclideanSpace ℝ (Fin n) | Metric.infDist x Ω' < 3 * d / 4} := ⟨_, rfl⟩
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin n) => Metric.infDist x Ω' :=
    Metric.continuous_infDist_pt Ω'
  have hΩ₁open : IsOpen Ω₁ := by
    rw [hΩ₁]
    exact isOpen_lt hcont continuous_const
  have hΩ₂open : IsOpen Ω₂ := by
    rw [hΩ₂]
    exact isOpen_lt hcont continuous_const
  have hmem₁ : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ Ω₁ ↔ Metric.infDist x Ω' < d / 2 := by
    intro x; rw [hΩ₁]; exact Iff.rfl
  have hmem₂ : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ Ω₂ ↔ Metric.infDist x Ω' < 3 * d / 4 := by
    intro x; rw [hΩ₂]; exact Iff.rfl
  -- the separation consequence (1)
  have hkey : ∀ c : ℝ, 0 < c → c < d → ∀ x : EuclideanSpace ℝ (Fin n),
      Metric.infDist x Ω' < c → ∀ y, y ∉ Ω → d - c < dist x y := by
    intro c hc0 hcd x hx y hy
    obtain ⟨x', hx', hdx⟩ := (Metric.infDist_lt_iff hΩ'ne).mp hx
    have h1 := hsep x' hx' y hy
    have h2 : dist x' y ≤ dist x' x + dist x y := dist_triangle _ _ _
    rw [dist_comm x' x] at h2
    linarith
  have hΩ₂Ω : Ω₂ ⊆ Ω := by
    intro x hx
    by_contra hxn
    have h1 := hkey (3 * d / 4) (by linarith) (by linarith) x ((hmem₂ x).mp hx) x hxn
    rw [dist_self] at h1
    linarith
  have hΩ₁Ω₂ : Ω₁ ⊆ Ω₂ := by
    intro x hx
    exact (hmem₂ x).mpr (by linarith [(hmem₁ x).mp hx])
  have hball8Ω : ∀ x ∈ Ω₂, Metric.closedBall x (d / 8) ⊆ Ω := by
    intro x hx z hz
    by_contra hzn
    have h1 : Metric.infDist z Ω' ≤ Metric.infDist x Ω' + dist z x :=
      Metric.infDist_le_infDist_add_dist
    have h2 : dist z x ≤ d / 8 := Metric.mem_closedBall.mp hz
    have h3 : Metric.infDist z Ω' < 7 * d / 8 := by
      have := (hmem₂ x).mp hx
      linarith
    have h4 := hkey (7 * d / 8) (by linarith) (by linarith) z h3 z hzn
    rw [dist_self] at h4
    linarith
  have hsepΩ₁ : ∀ x ∈ Ω₁, ∀ y, y ∉ Ω → d / 2 ≤ dist x y := by
    intro x hx y hy
    have := hkey (d / 2) (by linarith) (by linarith) x ((hmem₁ x).mp hx) y hy
    linarith
  have hball2Ω : ∀ x ∈ Ω₁, Metric.closedBall x (d / 2) ⊆ Ω := by
    intro x hx z hz
    by_contra hzn
    have h1 := hkey (d / 2) (by linarith) (by linarith) x ((hmem₁ x).mp hx) z hzn
    have h2 : dist x z ≤ d / 2 := by
      rw [dist_comm]
      exact Metric.mem_closedBall.mp hz
    linarith
  have hball8Ω₂ : ∀ x ∈ Ω₁, Metric.closedBall x (d / 8) ⊆ Ω₂ := by
    intro x hx z hz
    refine (hmem₂ z).mpr ?_
    have h1 : Metric.infDist z Ω' ≤ Metric.infDist x Ω' + dist z x :=
      Metric.infDist_le_infDist_add_dist
    have h2 : dist z x ≤ d / 8 := Metric.mem_closedBall.mp hz
    have h3 := (hmem₁ x).mp hx
    linarith
  have hclΩ' : closure Ω' ⊆ Ω₁ := by
    intro x hx
    refine (hmem₁ x).mpr ?_
    have h1 : Metric.infDist x Ω' = 0 := by
      rw [← Metric.mem_closure_iff_infDist_zero hΩ'ne]
      exact hx
    linarith
  have hclΩ₁ : closure Ω₁ ⊆ Ω := by
    intro x hx
    refine hΩ₂Ω ((hmem₂ x).mpr ?_)
    have hsub : closure Ω₁ ⊆ {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y Ω' ≤ d / 2} := by
      refine closure_minimal ?_ (isClosed_le hcont continuous_const)
      intro y hy
      exact le_of_lt ((hmem₁ y).mp hy)
    have h1 : Metric.infDist x Ω' ≤ d / 2 := hsub hx
    linarith
  have hΩ₁bdd : Bornology.IsBounded Ω₁ := by
    obtain ⟨x', hx'⟩ := id hΩ'ne
    obtain ⟨r, hr⟩ := hΩ'bdd.subset_closedBall x'
    refine (Metric.isBounded_closedBall (x := x') (r := r + d)).subset ?_
    intro x hx
    obtain ⟨y, hy, hdy⟩ := (Metric.infDist_lt_iff hΩ'ne).mp ((hmem₁ x).mp hx)
    have h1 : dist y x' ≤ r := Metric.mem_closedBall.mp (hr hy)
    have h2 : dist x x' ≤ dist x y + dist y x' := dist_triangle _ _ _
    exact Metric.mem_closedBall.mpr (by linarith)
  have hsep1 : ∀ x ∈ Ω', ∀ y, y ∉ Ω₁ → d / 2 ≤ dist x y := by
    intro x hx y hy
    have h0 : ¬ (Metric.infDist y Ω' < d / 2) := fun hc => hy ((hmem₁ y).mpr hc)
    have h1 : Metric.infDist y Ω' ≤ dist y x := Metric.infDist_le_dist_of_mem hx
    rw [dist_comm]
    rw [not_lt] at h0
    linarith
  -- Step 2: the oscillation bound and the continuous representative.
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
    refine ⟨m, fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨x, hax, hxm⟩ := (ha.and hlo).exists
    linarith
  have hcobdd_ge : ∀ {μ : Measure (EuclideanSpace ℝ (Fin n))}
      {v : EuclideanSpace ℝ (Fin n) → ℝ} {Mb : ℝ}, (ae μ).NeBot →
      (∀ᵐ x ∂μ, v x ≤ Mb) → Filter.IsCoboundedUnder (· ≥ ·) (ae μ) v := by
    intro μ v Mb hb hhi
    have := hb
    refine ⟨Mb, fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨x, hax, hxM⟩ := (ha.and hhi).exists
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
  have hosc2M : ∀ (y : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
      Metric.ball y ρ ⊆ Ω → EssOscOn n (Metric.ball y ρ) u ≤ 2 * M := by
    intro y ρ hρ hsub
    have hb : (ae (volume.restrict (Metric.ball y ρ))).NeBot :=
      hNeBot (Metric.measure_ball_pos volume y hρ).ne'
    have hhi := hsubhi _ hsub
    have hlo := hsublo _ hsub
    have h1 : essSup u (volume.restrict (Metric.ball y ρ)) ≤ M :=
      essSup_le_of_ae_le M hhi (hcobdd_le hb hlo)
    have h2 : -M ≤ essInf u (volume.restrict (Metric.ball y ρ)) :=
      le_essInf_of_ae_le (-M) hlo (hcobdd_ge hb hhi)
    rw [EssOscOn]
    linarith
  obtain ⟨s, hs⟩ : ∃ t : ℝ, t = d / 8 := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; linarith
  obtain ⟨K, hK⟩ : ∃ t : ℝ, t = (4:ℝ) ^ α * max (2 * M) (d₀ * s) + 2 * M := ⟨_, rfl⟩
  have h4α : (0:ℝ) < (4:ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 : (0:ℝ) ≤ max (2 * M) (d₀ * s) := le_trans (by linarith) (le_max_left _ _)
    nlinarith
  have hK2M : 2 * M ≤ K := by
    rw [hK]
    have h1 : (0:ℝ) ≤ max (2 * M) (d₀ * s) := le_trans (by linarith) (le_max_left _ _)
    nlinarith
  -- the decay (3) at the fixed scale `s`, on `Ω₂`
  have hdecay3 : ∀ (y : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
      Metric.closedBall y ρ ⊆ Ω₂ → EssOscOn n (Metric.ball y ρ) u ≤ K * (ρ / s) ^ α := by
    intro y ρ hρ hsub
    have hyΩ₂ : y ∈ Ω₂ := hsub (Metric.mem_closedBall_self hρ.le)
    have hsΩ : Metric.closedBall y s ⊆ Ω := by
      rw [hs]
      exact hball8Ω y hyΩ₂
    rcases le_or_gt ρ s with hcase | hcase
    · have h1 := hdecay y s ρ hsΩ hρ hcase
      have h2 : EssOscOn n (Metric.ball y s) u ≤ 2 * M :=
        hosc2M y s hs0 (Metric.ball_subset_closedBall.trans hsΩ)
      have h3 : max (EssOscOn n (Metric.ball y s) u) (d₀ * s) ≤ max (2 * M) (d₀ * s) :=
        max_le_max h2 (le_refl _)
      have h4 : (0:ℝ) ≤ (ρ / s) ^ α := Real.rpow_nonneg (by positivity) _
      have h5 : (4:ℝ) ^ α * max (EssOscOn n (Metric.ball y s) u) (d₀ * s)
          ≤ (4:ℝ) ^ α * max (2 * M) (d₀ * s) := by
        exact mul_le_mul_of_nonneg_left h3 h4α.le
      have h6 : (4:ℝ) ^ α * max (2 * M) (d₀ * s) ≤ K := by
        rw [hK]; linarith
      calc EssOscOn n (Metric.ball y ρ) u
          ≤ (4:ℝ) ^ α * max (EssOscOn n (Metric.ball y s) u) (d₀ * s) * (ρ / s) ^ α := h1
        _ ≤ K * (ρ / s) ^ α := by
            refine mul_le_mul_of_nonneg_right ?_ h4
            linarith
    · have h1 : EssOscOn n (Metric.ball y ρ) u ≤ 2 * M :=
        hosc2M y ρ hρ (Metric.ball_subset_closedBall.trans (hsub.trans hΩ₂Ω))
      have h2 : (1:ℝ) ≤ (ρ / s) ^ α := by
        refine Real.one_le_rpow ?_ hα.le
        rw [le_div_iff₀ hs0]
        linarith
      nlinarith
  have hMu₂ : ∀ᵐ x ∂(volume.restrict Ω₂), |u x| ≤ M :=
    ae_restrict_of_ae_restrict_of_subset hΩ₂Ω hMu
  obtain ⟨C₂, hC₂0, hOD⟩ := OscillationDecayToHolder n α K M hn1 hα hα1 hK0 hM
  have hrep : ∀ x₁ ∈ Ω₁, ∃ V : EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ᵐ x ∂(volume.restrict Ω₂), V x = u x) ∧ ContinuousOn V Ω₂ ∧
        (∀ x ∈ Metric.closedBall x₁ (s / 2), ∀ y ∈ Metric.closedBall x₁ (s / 2),
          |V x - V y| ≤ C₂ * K * (dist x y / s) ^ α) := by
    intro x₁ hx₁
    have hsub : Metric.closedBall x₁ s ⊆ Ω₂ := by
      rw [hs]
      exact hball8Ω₂ x₁ hx₁
    obtain ⟨V, h1, h2, _, h4⟩ := hOD Ω₂ u x₁ s hΩ₂open hs0 hsub hMu₂ hdecay3
    exact ⟨V, h1, h2, h4⟩
  -- two continuous representatives agree pointwise on the open set `Ω₂`
  have hglue : ∀ V W : EuclideanSpace ℝ (Fin n) → ℝ,
      ContinuousOn V Ω₂ → ContinuousOn W Ω₂ →
      (∀ᵐ x ∂(volume.restrict Ω₂), V x = W x) → ∀ x ∈ Ω₂, V x = W x := by
    intro V W hV hW hae y hy
    by_contra hne
    have hopen : IsOpen (Ω₂ ∩ (fun x => V x - W x) ⁻¹' {z : ℝ | z ≠ 0}) :=
      (hV.sub hW).isOpen_inter_preimage hΩ₂open isOpen_ne
    have hposm : 0 < volume (Ω₂ ∩ (fun x => V x - W x) ⁻¹' {z : ℝ | z ≠ 0}) :=
      hopen.measure_pos volume ⟨y, hy, sub_ne_zero.mpr hne⟩
    have hnull : volume (Ω₂ ∩ (fun x => V x - W x) ⁻¹' {z : ℝ | z ≠ 0}) = 0 := by
      refine measure_mono_null ?_
        (ae_iff.mp ((ae_restrict_iff' hΩ₂open.measurableSet).mp hae))
      intro x hx
      simp only [Set.mem_ofPred_eq]
      intro hc
      exact hx.2 (sub_eq_zero.mpr (hc hx.1))
    rw [hnull] at hposm
    exact absurd hposm (lt_irrefl 0)
  -- the common representative
  obtain ⟨x₁₀, hx₁₀⟩ : ∃ x : EuclideanSpace ℝ (Fin n), x ∈ Ω₁ := by
    obtain ⟨x, hx⟩ := id hΩ'ne
    exact ⟨x, hclΩ' (subset_closure hx)⟩
  obtain ⟨U₀, hU₀ae, hU₀cont, hU₀hol⟩ := hrep x₁₀ hx₁₀
  have hU₀hol' : ∀ x₁ ∈ Ω₁, ∀ x ∈ Metric.closedBall x₁ (s / 2),
      ∀ y ∈ Metric.closedBall x₁ (s / 2),
      |U₀ x - U₀ y| ≤ C₂ * K * (dist x y / s) ^ α := by
    intro x₁ hx₁ x hx y hy
    obtain ⟨V, hVae, hVcont, hVhol⟩ := hrep x₁ hx₁
    have hsub : Metric.closedBall x₁ (s / 2) ⊆ Ω₂ := by
      have h1 : Metric.closedBall x₁ (s / 2) ⊆ Metric.closedBall x₁ (d / 8) :=
        Metric.closedBall_subset_closedBall (by rw [hs]; linarith)
      exact h1.trans (hball8Ω₂ x₁ hx₁)
    have heq : ∀ z ∈ Ω₂, V z = U₀ z := by
      refine hglue V U₀ hVcont hU₀cont ?_
      filter_upwards [hVae, hU₀ae] with z h1 h2
      rw [h1, h2]
    rw [← heq x (hsub hx), ← heq y (hsub hy)]
    exact hVhol x hx y hy
  -- Step 3: the modification and the transport of the Sobolev datum.
  obtain ⟨U, hU⟩ : ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
      f = fun x => if x ∈ Ω₂ then U₀ x else u x := ⟨_, rfl⟩
  have hUin : ∀ x ∈ Ω₂, U x = U₀ x := by
    intro x hx
    simp only [hU, if_pos hx]
  have hUae : ∀ᵐ x ∂(volume.restrict Ω), U x = u x := by
    have h1 : ∀ᵐ x ∂(volume.restrict Ω₂), U x = u x := by
      filter_upwards [hU₀ae, ae_restrict_mem hΩ₂open.measurableSet] with x h1 h2
      rw [hUin x h2, h1]
    rw [ae_restrict_iff' hΩ.measurableSet]
    rw [ae_restrict_iff' hΩ₂open.measurableSet] at h1
    filter_upwards [h1] with x hx1 _
    by_cases hx2 : x ∈ Ω₂
    · exact hx1 hx2
    · simp only [hU, if_neg hx2]
  have hUW : MemW1pOn n p Ω U g := by
    refine (AEModificationInvariance n p hn1 hp1 Ω u U g hΩ ?_).2.1 hW
    filter_upwards [hUae] with x hx
    exact hx.symm
  have hUcont : ContinuousOn U Ω₁ := by
    refine (hU₀cont.mono hΩ₁Ω₂).congr (fun x hx => ?_)
    exact hUin x (hΩ₁Ω₂ hx)
  have hUhol : ∀ x ∈ Ω₁, MemHolderOn n α (Metric.closedBall x (d / 16)) U := by
    intro x hx
    have hball : Metric.closedBall x (d / 16) ⊆ Metric.closedBall x (s / 2) := by
      rw [hs]
      exact Metric.closedBall_subset_closedBall (by linarith)
    have hsub : Metric.closedBall x (s / 2) ⊆ Ω₂ := by
      have h1 : Metric.closedBall x (s / 2) ⊆ Metric.closedBall x (d / 8) :=
        Metric.closedBall_subset_closedBall (by rw [hs]; linarith)
      exact h1.trans (hball8Ω₂ x hx)
    refine ⟨?_, C₂ * K * s ^ (-α), by positivity, ?_⟩
    · refine (hU₀cont.mono (subset_trans hball hsub)).congr (fun y hy => ?_)
      exact hUin y (hsub (hball hy))
    · intro y hy z hz
      rw [hUin y (hsub (hball hy)), hUin z (hsub (hball hz))]
      have h1 := hU₀hol' x hx y (hball hy) z (hball hz)
      have h2 : (dist y z / s) ^ α = s ^ (-α) * dist y z ^ α := by
        rw [Real.div_rpow dist_nonneg hs0.le, Real.rpow_neg hs0.le]
        field_simp
      rw [h2] at h1
      calc |U₀ y - U₀ z| ≤ C₂ * K * (s ^ (-α) * dist y z ^ α) := h1
        _ = C₂ * K * s ^ (-α) * dist y z ^ α := by ring
  exact ⟨Ω₁, U, hΩ₁open, hΩ₁bdd, hclΩ', hclΩ₁, hsep1, hsepΩ₁, hball2Ω, hUae, hUW,
    hUcont, hUhol⟩
