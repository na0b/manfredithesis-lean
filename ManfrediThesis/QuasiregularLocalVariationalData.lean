import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.IsQuasiregularOn
import ManfrediThesis.IsDistortionMatrix
import ManfrediThesis.CitedQuasiregularBasics
import ManfrediThesis.VariationalStructureF123
import ManfrediThesis.IsLocalMinimumOn
import ManfrediThesis.WeakGradientRestrict
import ManfrediThesis.InterposedOpenSet
import ManfrediThesis.MatrixFieldAEToEverywhere
import ManfrediThesis.UniformModulusFromCompact
import ManfrediThesis.FrozenQuadraticFormStructure
import ManfrediThesis.QuasiregularFrozenLocalData
open MeasureTheory

/-- The local variational data of Theorem 7: from a quasiregular map whose
distortion matrix has a continuous representative `τ'` obeying the two-sided
bounds of (5.10), the construction of an interposed open set `Ω''` with
`closure Ω' ⊆ Ω'' ⊆ closure Ω'' ⊆ Ω`, of the frozen integrand
`f⁰(x,z,h) = (τ''(x)h,h)^{n/2}`, and of a modulus `σ`, such that
`f⁰` satisfies (F1)-(F3) on `Ω''` with the constants of Theorem 7 and each
component of the map is a bounded `W^{1,n}(Ω'')` local minimum for `f⁰`.  This
is the whole passage from §5's quasiregular data to §4's variational hypotheses,
which the paper leaves to the reader (it gives Theorem 7 no proof), and it is
what the two §4 theorems are then applied to. -/
theorem QuasiregularLocalVariationalData :
    ∀ (n : ℕ) (K lam Lam ν₀ ν₁ : ℝ), 2 ≤ n → 1 ≤ K → 0 < lam → lam ≤ Lam →
      0 < ν₀ → ν₀ ≤ (n : ℝ) / K →
      (n : ℝ) * ((n : ℝ) - 1) * K ^ ((n : ℝ) - 1) ≤ ν₁ →
      ∀ (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
        (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (G : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (τ τ' : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
        (i : Fin n),
        IsOpen Ω → IsOpen Ω' → Ω'.Nonempty → Bornology.IsBounded Ω' →
        closure Ω' ⊆ Ω →
        IsQuasiregularOn n K Ω F G → IsDistortionMatrix n Ω G τ →
        (∀ Ω₀ : Set (EuclideanSpace ℝ (Fin n)), IsOpen Ω₀ → Ω₀ ⊆ Ω →
          CitedQuasiregularBasics n K Ω₀ F G τ) →
        (¬ ∃ c : EuclideanSpace ℝ (Fin n),
          ∀ᵐ x ∂(volume.restrict Ω), F x = c) →
        (∀ᵐ x ∂(volume.restrict Ω), τ x = τ' x) →
        (∀ j k : Fin n, ContinuousOn (fun x => τ' x j k) Ω) →
        (∀ᵐ x ∂(volume.restrict Ω),
          (τ x).IsSymm ∧ (τ x).det = 1 ∧
            (∀ ξ : EuclideanSpace ℝ (Fin n),
              K ^ (-(2 : ℝ) / (n : ℝ)) * ‖ξ‖ ^ 2
                  ≤ ∑ a, ∑ b, τ x a b * ξ a * ξ b ∧
                (∑ a, ∑ b, τ x a b * ξ a * ξ b)
                  ≤ K ^ (2 * ((n : ℝ) - 1) / (n : ℝ)) * ‖ξ‖ ^ 2) ∧
            (∀ h : EuclideanSpace ℝ (Fin n),
              lam * ‖h‖ ^ (n : ℝ)
                  ≤ (∑ a, ∑ b, τ x a b * h a * h b) ^ ((n : ℝ) / 2) ∧
                (∑ a, ∑ b, τ x a b * h a * h b) ^ ((n : ℝ) / 2)
                  ≤ Lam * ‖h‖ ^ (n : ℝ))) →
        ∃ (Ω'' : Set (EuclideanSpace ℝ (Fin n)))
          (fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
          (σ : ℝ → ℝ) (M Wn d : ℝ),
          IsOpen Ω'' ∧ closure Ω' ⊆ Ω'' ∧ closure Ω'' ⊆ Ω ∧
            (∀ x ∈ Ω', ∀ y, y ∉ Ω'' → d ≤ dist x y) ∧
            0 < d ∧ 0 ≤ M ∧ 0 ≤ Wn ∧
            VariationalStructureF123 n (n : ℝ) 0 lam Lam 1 ν₀ ν₁ Ω'' fdens σ ∧
            MemW1pOn n (n : ℝ) Ω'' (fun x => F x i) (G i) ∧
            (∀ᵐ x ∂(volume.restrict Ω''), |F x i| ≤ M) ∧
            ((∫ x in Ω'', |F x i| ^ (n : ℝ))
                + ∫ x in Ω'', ‖G i x‖ ^ (n : ℝ)) ≤ Wn ^ (n : ℝ) ∧
            IsLocalMinimumOn n (n : ℝ) Ω'' fdens (fun x => F x i) (G i) ∧
            ∀ δ C : ℝ, 0 < δ → δ < 1 → 0 ≤ C →
              (∀ x ∈ Ω, ∀ y ∈ Ω, ∀ j k : Fin n,
                |τ' x j k - τ' y j k| ≤ C * dist x y ^ δ) →
              ∃ cσ : ℝ, 0 < cσ ∧ ∀ t : ℝ, 0 ≤ t → σ t ≤ cσ * t ^ δ := by
  classical
  intro n K lam Lam ν₀ ν₁ hn hK hlam hlamLam hν₀ hν₀n hν₁
  -- Context-independent numeric facts, established before the data arrive.
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hKrpow : ∀ e : ℝ, (0 : ℝ) < K ^ e := fun e => Real.rpow_pos_of_pos hK0 e
  set c : ℝ := (n : ℝ) ^ 2 / 2 * K ^ (((n : ℝ) - 1) * ((n : ℝ) - 2) / (n : ℝ))
    with hcdef
  have hcpos : (0 : ℝ) < c := by
    rw [hcdef]
    exact mul_pos (by positivity) (hKrpow _)
  have hc0 : (0 : ℝ) ≤ c := le_of_lt hcpos
  have hpow : ∀ h : EuclideanSpace ℝ (Fin n),
      ((0 : ℝ) + ‖h‖ ^ 2) ^ ((n : ℝ) / 2) = ‖h‖ ^ (n : ℝ) := by
    intro h
    have h1 : (0 : ℝ) + ‖h‖ ^ 2 = ‖h‖ ^ (2 : ℝ) := by
      rw [Real.rpow_two]; ring
    rw [h1, ← Real.rpow_mul (norm_nonneg h),
      show (2 : ℝ) * ((n : ℝ) / 2) = (n : ℝ) by ring]
  have hrpowcont : Continuous fun t : ℝ => t ^ ((n : ℝ) / 2) :=
    continuous_id.rpow_const fun _ => Or.inr (by positivity)
  have hpowle : ∀ h : EuclideanSpace ℝ (Fin n),
      ‖h‖ ^ (n : ℝ) ≤ ((1 : ℝ) + ‖h‖ ^ 2) ^ ((n : ℝ) / 2) := by
    intro h
    rw [← hpow h]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith [sq_nonneg ‖h‖])
      (by positivity)
  -- Now the data.
  intro Ω Ω' F G τ τ' i hΩ hΩ' hΩ'ne hΩ'bdd hclΩ' hqr hdist hbasics hnc hττ'
    hτ'cont hτprops
  -- (3a) the interposed set, together with the separation constant `d` of (3e).
  obtain ⟨Ω'', d, hΩ''open, hΩ''ne, hΩ''bdd, hcl1, hcl2, hcl2cpt, hd0, hsep⟩ :=
    InterposedOpenSet n Ω Ω' hΩ hΩ'ne hΩ'bdd hclΩ'
  have hΩ''sub : Ω'' ⊆ Ω := subset_trans subset_closure hcl2
  -- (3b) the two-sided bounds for the continuous representative at every point.
  have hτ' := MatrixFieldAEToEverywhere n K lam Lam hn hK Ω τ τ' hΩ hττ' hτ'cont
    hτprops
  -- (3c) the integrand, frozen outside `Ω''` so that it is globally measurable.
  set τ'' : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    fun x => if x ∈ Ω'' then τ' x else (1 : Matrix (Fin n) (Fin n) ℝ)
    with hτ''def
  set fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x _ h => (∑ a, ∑ b, τ'' x a b * h a * h b) ^ ((n : ℝ) / 2) with hfdef
  have hτ''eq : ∀ x ∈ Ω'', τ'' x = τ' x := fun x hx => if_pos hx
  have hfeq : ∀ x ∈ Ω'', ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)),
      fdens x z h = (∑ a, ∑ b, τ' x a b * h a * h b) ^ ((n : ℝ) / 2) := by
    intro x hx z h
    simp only [hfdef, hτ''eq x hx]
  -- (3f) the modulus of continuity on the compact set `closure Ω''`.
  obtain ⟨σ₀, hσ₀0, hσ₀cont, hσ₀mono, hσ₀zero, hσ₀bdd, hσ₀osc, hσ₀rate⟩ :=
    UniformModulusFromCompact n (closure Ω'') τ' hcl2cpt
      (fun j k => (hτ'cont j k).mono hcl2)
  set σ : ℝ → ℝ := fun t => c * σ₀ t with hσdef
  -- (3d) and (3e): the local data on `Ω''`.
  obtain ⟨M, Wn, hM0, hWn0, hW1p, hMbd, hWbd, hmin⟩ :=
    QuasiregularFrozenLocalData n K hn hK Ω Ω'' F G τ τ' fdens i hΩ hΩ''open hcl2
      hcl2cpt hqr hdist hbasics hnc hττ' hfeq
  -- The structure facts for the frozen quadratic form at each point of `Ω''`.
  have hstruct := fun x (hx : x ∈ Ω'') =>
    FrozenQuadraticFormStructure n K ν₀ ν₁ hn hK hν₀ hν₀n hν₁ (τ' x)
      (hτ' x (hΩ''sub hx)).1 (hτ' x (hΩ''sub hx)).2.2.1
  refine ⟨Ω'', fdens, σ, M, Wn, d, hΩ''open, hcl1, hcl2, hsep, hd0, hM0, hWn0,
    ?_, hW1p, hMbd, hWbd, hmin, ?_⟩
  · -- (3i) the structure predicate.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- measurability in `x`: the frozen extension is piecewise continuous.
      intro z h
      have hτ''neq : ∀ x, x ∉ Ω'' → τ'' x = (1 : Matrix (Fin n) (Fin n) ℝ) :=
        fun x hx => if_neg hx
      have hpw : (fun x => ∑ a, ∑ b, τ'' x a b * h a * h b)
          = Set.piecewise Ω'' (fun x => ∑ a, ∑ b, τ' x a b * h a * h b)
              (fun _ => ∑ a, ∑ b,
                (1 : Matrix (Fin n) (Fin n) ℝ) a b * h a * h b) := by
        funext x
        by_cases hx : x ∈ Ω''
        · rw [Set.piecewise_eq_of_mem _ _ _ hx, hτ''eq x hx]
        · rw [Set.piecewise_eq_of_notMem _ _ _ hx, hτ''neq x hx]
      have hcts : ContinuousOn (fun x => ∑ a, ∑ b, τ' x a b * h a * h b) Ω'' :=
        continuousOn_finsetSum _ fun a _ =>
          continuousOn_finsetSum _ fun b _ =>
            (((hτ'cont a b).mono hΩ''sub).mul continuousOn_const).mul
              continuousOn_const
      have hq : Measurable fun x => ∑ a, ∑ b, τ'' x a b * h a * h b := by
        rw [hpw]
        exact hcts.measurable_piecewise continuousOn_const
          hΩ''open.measurableSet
      simpa only [hfdef, Function.comp_def] using hrpowcont.measurable.comp hq
    · -- joint continuity in `(z,h)`.
      intro x
      have h1 : Continuous fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
          ∑ a, ∑ b, τ'' x a b * q.2 a * q.2 b :=
        continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
          (continuous_const.mul
              ((EuclideanSpace.proj a).continuous.comp continuous_snd)).mul
            ((EuclideanSpace.proj b).continuous.comp continuous_snd)
      simpa only [hfdef, Function.comp_def] using hrpowcont.comp h1
    · -- (F1), from the two-sided `λ`/`Λ` bounds of (5.10).
      intro x hx z h
      rw [hfeq x hx z h, hpow h]
      obtain ⟨hl, hu⟩ := (hτ' x (hΩ''sub hx)).2.2.2 h
      exact ⟨by linarith, by linarith⟩
    · intro x hx z
      rw [show fdens x z = fun h : EuclideanSpace ℝ (Fin n) =>
          (∑ a, ∑ b, τ' x a b * h a * h b) ^ ((n : ℝ) / 2) from
        funext fun h => hfeq x hx z h]
      exact (hstruct x hx).1
    · intro x hx z
      rw [show fdens x z = fun h : EuclideanSpace ℝ (Fin n) =>
          (∑ a, ∑ b, τ' x a b * h a * h b) ^ ((n : ℝ) / 2) from
        funext fun h => hfeq x hx z h]
      exact (hstruct x hx).2.1
    · -- (F2).
      intro x hx z h ζ hne
      rw [show fdens x z = fun h : EuclideanSpace ℝ (Fin n) =>
          (∑ a, ∑ b, τ' x a b * h a * h b) ^ ((n : ℝ) / 2) from
        funext fun h => hfeq x hx z h]
      exact (hstruct x hx).2.2.1 h ζ hne
    · obtain ⟨C₀, hC₀⟩ := hσ₀bdd
      exact ⟨c * C₀, fun t => mul_le_mul_of_nonneg_left (hC₀ t) hc0⟩
    · exact continuous_const.mul hσ₀cont
    · exact fun a b hab => mul_le_mul_of_nonneg_left (hσ₀mono hab) hc0
    · simp only [hσdef, hσ₀zero, mul_zero]
    · -- (3g) and (F3): the oscillation bound.
      intro x hx x' hx' z z' h
      rw [hfeq x hx z h, hfeq x' hx' z' h]
      have hosc := (hstruct x hx).2.2.2 (τ' x') (σ₀ (dist x x'))
        (fun ξ => ⟨le_trans
            (mul_nonneg (le_of_lt (hKrpow _)) (sq_nonneg ‖ξ‖))
            ((hτ' x' (hΩ''sub hx')).2.2.1 ξ).1,
          ((hτ' x' (hΩ''sub hx')).2.2.1 ξ).2⟩)
        (fun a b => hσ₀osc x (subset_closure hx) x' (subset_closure hx') a b) h
      rw [← hcdef] at hosc
      have h1 : σ₀ (dist x x') ≤ σ₀ (dist x x' + |z - z'|) :=
        hσ₀mono (le_add_of_nonneg_right (abs_nonneg _))
      have h4 : (0 : ℝ) ≤ ‖h‖ ^ (n : ℝ) := Real.rpow_nonneg (norm_nonneg h) (n : ℝ)
      refine le_trans hosc ?_
      calc c * σ₀ (dist x x') * ‖h‖ ^ (n : ℝ)
          ≤ c * σ₀ (dist x x' + |z - z'|) * ‖h‖ ^ (n : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hc0) h4
        _ ≤ c * σ₀ (dist x x' + |z - z'|) * (1 + ‖h‖ ^ 2) ^ ((n : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left (hpowle h)
              (mul_nonneg hc0 (hσ₀0 _))
        _ = (1 + ‖h‖ ^ 2) ^ ((n : ℝ) / 2) * σ (dist x x' + |z - z'|) := by
            simp only [hσdef]; ring
  · -- (3j) the Hölder rate inherited by the modulus.
    intro δ C hδ0 hδ1 hC0 hhol
    have hcC : (0 : ℝ) ≤ 2 * c * C := mul_nonneg (by linarith) hC0
    refine ⟨2 * c * C + c, by linarith, fun t ht => ?_⟩
    have h1 : σ₀ t ≤ 2 * C * t ^ δ :=
      hσ₀rate δ C hδ0 (le_of_lt hδ1) hC0
        (fun x hx y hy j k => hhol x (hcl2 hx) y (hcl2 hy) j k) t ht
    have h2 : (0 : ℝ) ≤ t ^ δ := Real.rpow_nonneg ht δ
    calc σ t = c * σ₀ t := by simp only [hσdef]
      _ ≤ c * (2 * C * t ^ δ) := mul_le_mul_of_nonneg_left h1 hc0
      _ = 2 * c * C * t ^ δ := by ring
      _ ≤ (2 * c * C + c) * t ^ δ :=
          mul_le_mul_of_nonneg_right (by linarith) h2
