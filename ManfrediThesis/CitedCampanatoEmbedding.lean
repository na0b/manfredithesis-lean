import ManfrediThesis.Preamble
import ManfrediThesis.IsBoundedLipschitzDomain
import ManfrediThesis.CampanatoBoundOn
import ManfrediThesis.MemHolderOn
import ManfrediThesis.MorreyBoundOn
open MeasureTheory

/-- Cited result (C5): the direction of (4.10) that is used -- Campanato's
theorem on a bounded Lipschitz domain. -/
def CitedCampanatoEmbedding (n : ℕ) (q : ℝ)
    (Ω' : Set (EuclideanSpace ℝ (Fin n))) : Prop :=

  IsBoundedLipschitzDomain n Ω' →
  ∀ lam : ℝ, (n : ℝ) < lam → lam < (n : ℝ) + q →
    ∀ N : ℝ, 0 ≤ N →
      ∃ Nh : ℝ, 0 ≤ Nh ∧
        ∀ u : EuclideanSpace ℝ (Fin n) → ℝ,
          CampanatoBoundOn n q lam Ω' u N → MorreyBoundOn n q 0 Ω' u N →
          ∃ w : EuclideanSpace ℝ (Fin n) → ℝ,
            (∀ᵐ x ∂(volume.restrict Ω'), u x = w x) ∧
              MemHolderOn n ((lam - (n : ℝ)) / q) (closure Ω') w ∧
              (∀ x ∈ closure Ω', ∀ y ∈ closure Ω',
                |w x - w y| ≤ Nh * dist x y ^ ((lam - (n : ℝ)) / q))
