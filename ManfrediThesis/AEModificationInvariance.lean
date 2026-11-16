import ManfrediThesis.Preamble
import ManfrediThesis.HasWeakGradientOn
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.IsWeakSolutionOn
import ManfrediThesis.IsLocalMinimumOn
open MeasureTheory

/-- Modifying the function on a set of measure zero changes none of the five
predicates of the development that a function enters only through integrals: the
weak-gradient identity, `W^{1,q}` and `W^{1,q}_loc` membership, being a weak
solution of (1.1), and being a local minimum of `F`.  The weak gradient `g` is
the same in each conclusion as in the corresponding hypothesis. -/
theorem AEModificationInvariance :
    ∀ (n : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ q →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (f f' : EuclideanSpace ℝ (Fin n) → ℝ)
        (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        IsOpen Ω → (∀ᵐ x ∂(volume.restrict Ω), f x = f' x) →
        (HasWeakGradientOn n Ω f g → HasWeakGradientOn n Ω f' g)
          ∧ (MemW1pOn n q Ω f g → MemW1pOn n q Ω f' g)
          ∧ (MemW1pLocOn n q Ω f g → MemW1pLocOn n q Ω f' g)
          ∧ (∀ (A : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) →
                  EuclideanSpace ℝ (Fin n))
               (B : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ),
              IsWeakSolutionOn n q Ω A B f g → IsWeakSolutionOn n q Ω A B f' g)
          ∧ (∀ fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ,
              IsLocalMinimumOn n q Ω fdens f g →
                IsLocalMinimumOn n q Ω fdens f' g) := by
  intro n q _ _ Ω f f' g _ hae
  have hsubae : ∀ S : Set (EuclideanSpace ℝ (Fin n)), S ⊆ Ω →
      ∀ᵐ x ∂(volume.restrict S), f x = f' x :=
    fun S hS => ae_mono (Measure.restrict_mono hS le_rfl) hae
  have hwg : HasWeakGradientOn n Ω f g → HasWeakGradientOn n Ω f' g := by
    intro hw φ hφ hcs hts i
    have h : (fun x => f' x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        =ᵐ[volume.restrict Ω] (fun x => f x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) := by
      filter_upwards [hae] with x hx; rw [hx]
    rw [integral_congr_ae h]
    exact hw φ hφ hcs hts i
  have hLp : ∀ (S : Set (EuclideanSpace ℝ (Fin n))), S ⊆ Ω →
      MemLp f (ENNReal.ofReal q) (volume.restrict S) →
      MemLp f' (ENNReal.ofReal q) (volume.restrict S) :=
    fun S hS hf => hf.ae_eq (hsubae S hS)
  have hloc : MemW1pLocOn n q Ω f g → MemW1pLocOn n q Ω f' g := by
    rintro ⟨hw, hfam⟩
    exact ⟨hwg hw, fun K hK hKsub =>
      ⟨hLp K hKsub (hfam K hK hKsub).1, (hfam K hK hKsub).2⟩⟩
  refine ⟨hwg, ?_, hloc, ?_, ?_⟩
  · rintro ⟨hw, hf, hg⟩
    exact ⟨hwg hw, hLp Ω (subset_refl Ω) hf, hg⟩
  · rintro A B ⟨hw, heq⟩
    refine ⟨hloc hw, fun φ gφ hφ hcs hts => ?_⟩
    have h : (fun x => (∑ i, (A x (f' x) (g x)) i * gφ x i) + B x (f' x) (g x) * φ x)
        =ᵐ[volume.restrict Ω]
        (fun x => (∑ i, (A x (f x) (g x)) i * gφ x i) + B x (f x) (g x) * φ x) := by
      filter_upwards [hae] with x hx; rw [hx]
    obtain ⟨hint, hz⟩ := heq φ gφ hφ hcs hts
    exact ⟨hint.congr h.symm, by rw [integral_congr_ae h]; exact hz⟩
  · rintro fdens ⟨hw, hmin⟩
    refine ⟨hloc hw, fun φ gφ hφ hcs hts => ?_⟩
    have hae' : ∀ᵐ x ∂(volume.restrict (tsupport φ)), f x = f' x := hsubae _ hts
    have h1 : (fun x => fdens x (f' x) (g x))
        =ᵐ[volume.restrict (tsupport φ)] (fun x => fdens x (f x) (g x)) := by
      filter_upwards [hae'] with x hx; rw [hx]
    have h2 : (fun x => fdens x (f' x + φ x) (g x + gφ x))
        =ᵐ[volume.restrict (tsupport φ)] (fun x => fdens x (f x + φ x) (g x + gφ x)) := by
      filter_upwards [hae'] with x hx; rw [hx]
    obtain ⟨hi1, hi2, hle⟩ := hmin φ gφ hφ hcs hts
    exact ⟨hi1.congr h1.symm, hi2.congr h2.symm, by
      rw [integral_congr_ae h1, integral_congr_ae h2]; exact hle⟩
