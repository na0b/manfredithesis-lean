import ManfrediThesis.Preamble
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.IsQuasiregularOn
import ManfrediThesis.WeakGradientLinear
import ManfrediThesis.AEModificationInvariance
open MeasureTheory

/-- The degenerate branch of Theorem 7: if a quasiregular map agrees almost
everywhere with a constant, then each of its component weak gradients vanishes
almost everywhere.  This is the only place in Theorem 7's proof that uses the
almost-everywhere uniqueness of a weak gradient, and it is what makes the
constant branch of that proof deliver the `C^{1+β}` conclusion as well as the
Hölder one. -/
theorem QuasiregularConstantCase :
    ∀ (n : ℕ) (K : ℝ), 2 ≤ n →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (G : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (c : EuclideanSpace ℝ (Fin n)),
        IsOpen Ω → IsQuasiregularOn n K Ω F G →
        (∀ᵐ x ∂(volume.restrict Ω), F x = c) →
        ∀ i : Fin n, ∀ᵐ x ∂(volume.restrict Ω), G i x = 0 := by
  intro n K hn Ω F G c hΩ hqr hFc i
  have h1n : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
  have h1q : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1n
  -- (1) The component is `W^{1,n}_loc` with weak gradient `G i`.
  have hmem : MemW1pLocOn n (n : ℝ) Ω (fun x => F x i) (G i) := hqr.1 i
  -- (2) The zero field is a weak gradient of the constant.
  have hconst : HasWeakGradientOn n Ω (fun _ => c i) (fun _ => 0) :=
    (WeakGradientLinear n (n : ℝ) h1n h1q Ω (fun _ => 0) (fun _ => 0)
      (fun _ => 0) (fun _ => 0) 0 0 (c i) hΩ).2.2.1.1
  -- (3) So is `G i`, transported across the almost-everywhere equality.
  have hae : ∀ᵐ x ∂(volume.restrict Ω), F x i = (fun _ => c i) x := by
    filter_upwards [hFc] with x hx
    rw [hx]
  have hGi : HasWeakGradientOn n Ω (fun _ => c i) (G i) :=
    (AEModificationInvariance n (n : ℝ) h1n h1q Ω (fun x => F x i)
      (fun _ => c i) (G i) hΩ hae).1 hmem.1
  -- (4) Hence each coordinate of `G i` integrates to zero against every test
  -- function: the two weak-gradient identities for the constant have the same
  -- left-hand side.
  have hzero : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ω → ∀ j : Fin n,
      (∫ x in Ω, G i x j * φ x) = 0 := by
    intro φ hφ hcs hsupp j
    simpa using (hGi φ hφ hcs hsupp j).symm.trans (hconst φ hφ hcs hsupp j)
  -- (5) Each coordinate of `G i` is locally integrable on `Ω`: on a compact
  -- subset the measure is finite, so `L^n` sits inside `L^1`.
  have hli : ∀ j : Fin n,
      MeasureTheory.LocallyIntegrableOn (fun x => G i x j) Ω volume := by
    intro j
    rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro A hAΩ hA
    have : IsFiniteMeasure (volume.restrict A) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hA.measure_lt_top⟩
    have hLp : MemLp (G i) (ENNReal.ofReal (n : ℝ)) (volume.restrict A) :=
      (hmem.2 A hA hAΩ).2
    have h1 : MemLp (G i) 1 (volume.restrict A) :=
      hLp.mono_exponent (by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal h1q)
    exact (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).integrable_comp
      (memLp_one_iff_integrable.mp h1)
  -- (6) The fundamental lemma of the calculus of variations, coordinatewise.
  have hcoord : ∀ j : Fin n, ∀ᵐ x ∂volume, x ∈ Ω → G i x j = 0 := by
    intro j
    refine hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hli j) ?_
    intro g hg hcs hsupp
    have hz : ∀ x ∉ Ω, g x • G i x j = 0 := by
      intro x hx
      have hgx : g x = 0 :=
        image_eq_zero_of_notMem_tsupport fun hmem' => hx (hsupp hmem')
      simp [hgx]
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    simpa only [smul_eq_mul, mul_comm] using hzero g hg hcs hsupp j
  -- (7) Assemble the `n` coordinates.
  rw [MeasureTheory.ae_restrict_iff' hΩ.measurableSet]
  filter_upwards [MeasureTheory.ae_all_iff.2 hcoord] with x hx
  intro hxΩ
  refine PiLp.ext fun j => ?_
  simpa using hx j hxΩ
