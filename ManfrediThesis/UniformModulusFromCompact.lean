import ManfrediThesis.Preamble
open MeasureTheory

/-- The modulus of continuity of §5's distortion matrix, smoothed into a
function that (F3) can be stated with: from entries continuous on a compact set
one builds a single `σ` that is nonnegative, continuous, nondecreasing, bounded
and vanishes at `0`, dominates the oscillation of every entry, and inherits a
Hölder rate from a Hölder bound on the entries.  The smoothing is needed because
the raw modulus is only monotone, while (F3) asks for a continuous `σ`. -/
theorem UniformModulusFromCompact :
    ∀ (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n)))
      (τ' : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ),
      IsCompact A →
      (∀ j k : Fin n, ContinuousOn (fun x => τ' x j k) A) →
      ∃ σ : ℝ → ℝ,
        (∀ t : ℝ, 0 ≤ σ t) ∧ Continuous σ ∧ Monotone σ ∧ σ 0 = 0 ∧
          (∃ C : ℝ, ∀ t : ℝ, σ t ≤ C) ∧
          (∀ x ∈ A, ∀ y ∈ A, ∀ j k : Fin n,
            |τ' x j k - τ' y j k| ≤ σ (dist x y)) ∧
          ∀ δ C : ℝ, 0 < δ → δ ≤ 1 → 0 ≤ C →
            (∀ x ∈ A, ∀ y ∈ A, ∀ j k : Fin n,
              |τ' x j k - τ' y j k| ≤ C * dist x y ^ δ) →
            ∀ t : ℝ, 0 ≤ t → σ t ≤ 2 * C * t ^ δ := by
  intro n A τ' hA hcont
  -- The entries, bundled as one map into a finite product with the sup norm.
  have hcontPi : ContinuousOn
      (fun x => (fun jk : Fin n × Fin n => τ' x jk.1 jk.2)) A :=
    continuousOn_pi.2 fun jk => hcont jk.1 jk.2
  obtain ⟨M₀, hM₀⟩ := hA.exists_bound_of_continuousOn hcontPi
  set M : ℝ := max M₀ 0 with hMdef
  have hM0 : (0 : ℝ) ≤ M := le_max_right _ _
  have hentry : ∀ x ∈ A, ∀ j k : Fin n, |τ' x j k| ≤ M := by
    intro x hx j k
    refine le_trans (le_trans ?_ (hM₀ x hx)) (le_max_left _ _)
    simpa using norm_le_pi_norm (fun jk : Fin n × Fin n => τ' x jk.1 jk.2) (j, k)
  have hdiff : ∀ x ∈ A, ∀ y ∈ A, ∀ j k : Fin n,
      |τ' x j k - τ' y j k| ≤ 2 * M := by
    intro x hx y hy j k
    have h1 := hentry x hx j k
    have h2 := hentry y hy j k
    calc |τ' x j k - τ' y j k| ≤ |τ' x j k| + |τ' y j k| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  -- Uniform continuity of the entries on the compact set `A`.
  have huc : ∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 < θ ∧ ∀ x ∈ A, ∀ y ∈ A, ∀ j k : Fin n,
      dist x y < θ → |τ' x j k - τ' y j k| ≤ ε := by
    intro ε hε
    have hU := hA.uniformContinuousOn_of_continuous hcontPi
    rw [Metric.uniformContinuousOn_iff] at hU
    obtain ⟨θ, hθ0, hθ⟩ := hU ε hε
    refine ⟨θ, hθ0, fun x hx y hy j k hxy => ?_⟩
    refine le_trans ?_ (le_of_lt (hθ x hx y hy hxy))
    simpa [Real.dist_eq] using
      dist_le_pi_dist (fun jk : Fin n × Fin n => τ' x jk.1 jk.2)
        (fun jk : Fin n × Fin n => τ' y jk.1 jk.2) (j, k)
  -- The scale-invariant ramp: `1` below `t`, `0` above `2t`, linear between.
  set W : ℝ → ℝ → ℝ :=
    fun t d => if 0 < t then min 1 (max 0 (2 - d / t)) else 0 with hWdef
  have hW0 : ∀ t d : ℝ, 0 ≤ W t d := by
    intro t d
    simp only [hWdef]
    split_ifs
    · exact le_min zero_le_one (le_max_left 0 _)
    · exact le_rfl
  have hW1 : ∀ t d : ℝ, W t d ≤ 1 := by
    intro t d
    simp only [hWdef]
    split_ifs
    · exact min_le_left _ _
    · exact zero_le_one
  have hWzero : ∀ t d : ℝ, 2 * t ≤ d → W t d = 0 := by
    intro t d hd
    simp only [hWdef]
    split_ifs with ht
    · have h2 : (2 : ℝ) ≤ d / t := by rw [le_div_iff₀ ht]; linarith
      rw [max_eq_left (by linarith : (2 : ℝ) - d / t ≤ 0), min_eq_right zero_le_one]
    · rfl
  have hWone : ∀ t d : ℝ, 0 < t → d ≤ t → W t d = 1 := by
    intro t d ht hdt
    simp only [hWdef, if_pos ht]
    have h1 : d / t ≤ 1 := by rw [div_le_one ht]; exact hdt
    rw [max_eq_right (by linarith : (0 : ℝ) ≤ 2 - d / t),
      min_eq_left (by linarith : (1 : ℝ) ≤ 2 - d / t)]
  have hWmono : ∀ d : ℝ, 0 ≤ d → ∀ t t' : ℝ, t ≤ t' → W t d ≤ W t' d := by
    intro d hd t t' htt'
    simp only [hWdef]
    split_ifs with h1 h2 h2
    · have hdd : d / t' ≤ d / t := by gcongr
      exact min_le_min le_rfl (max_le_max le_rfl (by linarith))
    · exact absurd (lt_of_lt_of_le h1 htt') h2
    · exact le_min zero_le_one (le_max_left 0 _)
    · exact le_rfl
  have hWlip : ∀ a t t' d : ℝ, 0 < a → a ≤ t → t ≤ t' → 0 ≤ d →
      W t' d - W t d ≤ 2 / a * (t' - t) := by
    intro a t t' d ha hat htt' hd
    have ht : 0 < t := lt_of_lt_of_le ha hat
    have ht' : 0 < t' := lt_of_lt_of_le ht htt'
    have h2 : (0 : ℝ) ≤ t' - t := by linarith
    rcases le_or_gt (2 * t') d with hcase | hcase
    · rw [hWzero t' d hcase, hWzero t d (by linarith)]
      have : (0 : ℝ) ≤ 2 / a * (t' - t) := by positivity
      linarith
    · simp only [hWdef, if_pos ht, if_pos ht']
      have hdd : d / t' ≤ d / t := by gcongr
      have hclamp : min 1 (max 0 (2 - d / t')) - min 1 (max 0 (2 - d / t))
          ≤ (2 - d / t') - (2 - d / t) := by
        simp only [min_def, max_def]
        split_ifs <;> linarith
      have hkey : (2 - d / t') - (2 - d / t) = d * (t' - t) / (t * t') := by
        field_simp
        ring
      have hb : d * (t' - t) / (t * t') ≤ 2 / a * (t' - t) := by
        rw [div_le_iff₀ (by positivity)]
        have e1 : d * (t' - t) ≤ 2 * t' * (t' - t) :=
          mul_le_mul_of_nonneg_right (le_of_lt hcase) h2
        have hta : (1 : ℝ) ≤ t / a := (one_le_div ha).mpr hat
        have hnn : (0 : ℝ) ≤ 2 * t' * (t' - t) :=
          mul_nonneg (by linarith) h2
        have e2 : 2 * t' * (t' - t) ≤ 2 / a * (t' - t) * (t * t') := by
          calc 2 * t' * (t' - t) ≤ 2 * t' * (t' - t) * (t / a) :=
                le_mul_of_one_le_right hnn hta
            _ = 2 / a * (t' - t) * (t * t') := by field_simp
        linarith
      linarith [hclamp, hkey, hb]
  -- The modulus: the pairwise oscillation, weighted by the ramp.
  set S : ℝ → Set ℝ := fun t =>
    insert (0 : ℝ) {r : ℝ | ∃ x ∈ A, ∃ y ∈ A, ∃ j k : Fin n,
      r = |τ' x j k - τ' y j k| * W t (dist x y)} with hSdef
  set σ : ℝ → ℝ := fun t => sSup (S t) with hσdef
  have hbdd : ∀ t : ℝ, BddAbove (S t) := by
    intro t
    refine ⟨2 * M, fun r hr => ?_⟩
    rcases hr with rfl | ⟨x, hx, y, hy, j, k, rfl⟩
    · linarith
    · calc |τ' x j k - τ' y j k| * W t (dist x y)
          ≤ |τ' x j k - τ' y j k| * 1 :=
            mul_le_mul_of_nonneg_left (hW1 _ _) (abs_nonneg _)
        _ = |τ' x j k - τ' y j k| := mul_one _
        _ ≤ 2 * M := hdiff x hx y hy j k
  have hσ0 : ∀ t : ℝ, 0 ≤ σ t := fun t =>
    le_csSup (hbdd t) (Set.mem_insert _ _)
  have hterm : ∀ (t : ℝ), ∀ x ∈ A, ∀ y ∈ A, ∀ j k : Fin n,
      |τ' x j k - τ' y j k| * W t (dist x y) ≤ σ t := by
    intro t x hx y hy j k
    exact le_csSup (hbdd t)
      (Set.mem_insert_of_mem _ ⟨x, hx, y, hy, j, k, rfl⟩)
  have hσle : ∀ t a : ℝ, 0 ≤ a →
      (∀ x ∈ A, ∀ y ∈ A, ∀ j k : Fin n,
        |τ' x j k - τ' y j k| * W t (dist x y) ≤ a) → σ t ≤ a := by
    intro t a ha h
    refine Real.sSup_le (fun r hr => ?_) ha
    rcases hr with rfl | ⟨x, hx, y, hy, j, k, rfl⟩
    · exact ha
    · exact h x hx y hy j k
  have hσnonpos : ∀ t : ℝ, t ≤ 0 → σ t = 0 := by
    intro t ht
    refine le_antisymm (hσle t 0 le_rfl fun x hx y hy j k => ?_) (hσ0 t)
    rw [hWzero t (dist x y) (by linarith [dist_nonneg (x := x) (y := y)]), mul_zero]
  have hmono : Monotone σ := by
    intro t t' htt'
    refine hσle t (σ t') (hσ0 t') fun x hx y hy j k => ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (hWmono (dist x y) dist_nonneg t t' htt') (abs_nonneg _)) ?_
    exact hterm t' x hx y hy j k
  have hlip : ∀ a t t' : ℝ, 0 < a → a ≤ t → t ≤ t' →
      σ t' ≤ σ t + 2 * M * (2 / a) * (t' - t) := by
    intro a t t' ha hat htt'
    have h2 : (0 : ℝ) ≤ t' - t := by linarith
    have hrest : (0 : ℝ) ≤ 2 * M * (2 / a) * (t' - t) := by positivity
    refine hσle t' _ (by linarith [hσ0 t]) fun x hx y hy j k => ?_
    have hw := hWlip a t t' (dist x y) ha hat htt' dist_nonneg
    have hab := hdiff x hx y hy j k
    have hterm' := hterm t x hx y hy j k
    have hsplit : |τ' x j k - τ' y j k| * W t' (dist x y)
        = |τ' x j k - τ' y j k| * W t (dist x y)
          + |τ' x j k - τ' y j k| * (W t' (dist x y) - W t (dist x y)) := by
      ring
    rw [hsplit]
    have hle2 : |τ' x j k - τ' y j k| * (W t' (dist x y) - W t (dist x y))
        ≤ 2 * M * (2 / a * (t' - t)) := by
      refine mul_le_mul hab hw ?_ (by linarith)
      linarith [hWmono (dist x y) dist_nonneg t t' htt']
    nlinarith [hterm', hle2]
  -- Smallness near the origin, from uniform continuity.
  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 < θ ∧ ∀ t : ℝ, t < θ → σ t ≤ ε := by
    intro ε hε
    obtain ⟨θ₀, hθ₀, hθ⟩ := huc ε hε
    refine ⟨θ₀ / 2, by linarith, fun t ht => ?_⟩
    refine hσle t ε (le_of_lt hε) fun x hx y hy j k => ?_
    rcases eq_or_ne (W t (dist x y)) 0 with hw | hw
    · rw [hw, mul_zero]; exact le_of_lt hε
    · have hlt : dist x y < 2 * t := by
        by_contra hcon
        exact hw (hWzero t (dist x y) (not_lt.mp hcon))
      calc |τ' x j k - τ' y j k| * W t (dist x y)
          ≤ |τ' x j k - τ' y j k| * 1 :=
            mul_le_mul_of_nonneg_left (hW1 _ _) (abs_nonneg _)
        _ = |τ' x j k - τ' y j k| := mul_one _
        _ ≤ ε := hθ x hx y hy j k (by linarith)
  have hcontσ : Continuous σ := by
    rw [Metric.continuous_iff]
    intro b ε hε
    rcases le_or_gt b 0 with hb | hb
    · obtain ⟨θ, hθ0, hθ⟩ := hsmall (ε / 2) (by linarith)
      refine ⟨min θ 1, lt_min hθ0 one_pos, fun a ha => ?_⟩
      rw [Real.dist_eq] at ha
      have ha' : a < θ := by
        have h1 := (abs_lt.mp ha).2
        have h2 : min θ 1 ≤ θ := min_le_left _ _
        linarith
      rw [Real.dist_eq, hσnonpos b hb, sub_zero, abs_of_nonneg (hσ0 a)]
      linarith [hθ a ha']
    · set L : ℝ := 2 * M * (2 / (b / 2)) with hLdef
      have hL0 : (0 : ℝ) ≤ L := by rw [hLdef]; positivity
      refine ⟨min (b / 2) (ε / (L + 1)),
        lt_min (by linarith) (by positivity), fun a ha => ?_⟩
      rw [Real.dist_eq] at ha
      have h1 : |a - b| < b / 2 := lt_of_lt_of_le ha (min_le_left _ _)
      have h2 : |a - b| < ε / (L + 1) := lt_of_lt_of_le ha (min_le_right _ _)
      have h3 : |a - b| * (L + 1) < ε := by
        rw [lt_div_iff₀ (by linarith)] at h2
        exact h2
      have h4 : L * |a - b| < ε := by
        nlinarith [abs_nonneg (a - b)]
      have ha2 : b / 2 ≤ a := by
        have := (abs_lt.mp h1).1
        linarith
      rw [Real.dist_eq]
      rcases le_total a b with hle | hle
      · have hup := hlip (b / 2) a b (by linarith) ha2 hle
        rw [← hLdef] at hup
        have hlow := hmono hle
        rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ b - σ a)]
        have : |a - b| = b - a := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)]
        nlinarith [hup, h4]
      · have hup := hlip (b / 2) b a (by linarith) (by linarith) hle
        rw [← hLdef] at hup
        have hlow := hmono hle
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ a - σ b)]
        have : |a - b| = a - b := abs_of_nonneg (by linarith)
        nlinarith [hup, h4]
  refine ⟨σ, hσ0, hcontσ, hmono, hσnonpos 0 le_rfl, ⟨2 * M, fun t => ?_⟩, ?_, ?_⟩
  · exact hσle t (2 * M) (by linarith) fun x hx y hy j k =>
      le_trans (mul_le_mul_of_nonneg_left (hW1 _ _) (abs_nonneg _))
        (by rw [mul_one]; exact hdiff x hx y hy j k)
  · -- the modulus dominates the oscillation
    intro x hx y hy j k
    rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist x y) with h0 | h0
    · have hxy : x = y := by
        rw [← dist_eq_zero]; exact h0.symm
      rw [hxy, sub_self, abs_zero]
      exact hσ0 _
    · have := hterm (dist x y) x hx y hy j k
      rwa [hWone (dist x y) (dist x y) h0 le_rfl, mul_one] at this
  · -- the Hölder rate
    intro δ C hδ hδ1 hC0 hhol t ht
    have htd : (0 : ℝ) ≤ t ^ δ := Real.rpow_nonneg ht δ
    refine hσle t _ (by positivity) fun x hx y hy j k => ?_
    rcases eq_or_ne (W t (dist x y)) 0 with hw | hw
    · rw [hw, mul_zero]; positivity
    · have hlt : dist x y < 2 * t := by
        by_contra hcon
        exact hw (hWzero t (dist x y) (not_lt.mp hcon))
      have h1 : |τ' x j k - τ' y j k| ≤ C * (2 * t) ^ δ :=
        le_trans (hhol x hx y hy j k)
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow dist_nonneg (le_of_lt hlt) (le_of_lt hδ)) hC0)
      have h2 : C * (2 * t) ^ δ ≤ 2 * C * t ^ δ := by
        rw [Real.mul_rpow (by norm_num) ht]
        have h3 : (2 : ℝ) ^ δ ≤ 2 := by
          calc (2 : ℝ) ^ δ ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
            _ = 2 := Real.rpow_one 2
        have h4 : (0 : ℝ) ≤ C * t ^ δ := mul_nonneg hC0 htd
        calc C * (2 ^ δ * t ^ δ) = C * t ^ δ * 2 ^ δ := by ring
          _ ≤ C * t ^ δ * 2 := mul_le_mul_of_nonneg_left h3 h4
          _ = 2 * C * t ^ δ := by ring
      calc |τ' x j k - τ' y j k| * W t (dist x y)
          ≤ |τ' x j k - τ' y j k| * 1 :=
            mul_le_mul_of_nonneg_left (hW1 _ _) (abs_nonneg _)
        _ = |τ' x j k - τ' y j k| := mul_one _
        _ ≤ 2 * C * t ^ δ := le_trans h1 h2
