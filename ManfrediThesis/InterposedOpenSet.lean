import ManfrediThesis.Preamble
open MeasureTheory

/-- The interposed set of §4 and §5: between a bounded open `Ω'` whose closure
lies in an open `Ω` there is an open `Ω''` with `closure Ω' ⊆ Ω''`,
`closure Ω'' ⊆ Ω` and `closure Ω''` compact, together with a positive
separation constant `d` between `Ω'` and the complement of `Ω''`.  This is the
geometric step that lets the §4 theorems be applied with `Ω''` in their ambient
slot and the given `Ω'` in their inner slot. -/
theorem InterposedOpenSet :
    ∀ (n : ℕ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen Ω → Ω'.Nonempty → Bornology.IsBounded Ω' → closure Ω' ⊆ Ω →
      ∃ (Ω'' : Set (EuclideanSpace ℝ (Fin n))) (d : ℝ),
        IsOpen Ω'' ∧ Ω''.Nonempty ∧ Bornology.IsBounded Ω'' ∧
          closure Ω' ⊆ Ω'' ∧ closure Ω'' ⊆ Ω ∧ IsCompact (closure Ω'') ∧
          0 < d ∧ ∀ x ∈ Ω', ∀ y, y ∉ Ω'' → d ≤ dist x y := by
  intro n Ω Ω' hΩ hΩ'ne hΩ'bdd hclΩ'
  -- `closure Ω'` is closed and bounded, hence compact.
  have hcpt : IsCompact (closure Ω') := hΩ'bdd.isCompact_closure
  -- A compact subset of an open set admits a thickening still inside it.
  obtain ⟨δ, hδ0, hδsub⟩ := hcpt.exists_thickening_subset_open hΩ hclΩ'
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  have hbdd : Bornology.IsBounded (Metric.thickening (δ / 2) (closure Ω')) :=
    hΩ'bdd.closure.thickening
  refine ⟨Metric.thickening (δ / 2) (closure Ω'), δ / 2, Metric.isOpen_thickening,
    ?_, hbdd, Metric.self_subset_thickening hhalf _, ?_,
    hbdd.isCompact_closure, hhalf, ?_⟩
  · -- nonempty
    obtain ⟨z, hz⟩ := hΩ'ne
    exact ⟨z, Metric.self_subset_thickening hhalf _ (subset_closure hz)⟩
  · -- the closure of the thickening is still inside `Ω`, with room to spare
    refine subset_trans (Metric.closure_thickening_subset_cthickening _ _)
      (subset_trans
        (Metric.cthickening_subset_thickening' hδ0 (by linarith) _) hδsub)
  · -- the separation constant
    intro x hx y hy
    by_contra hcon
    exact hy (Metric.mem_thickening_iff.2
      ⟨x, subset_closure hx, by rw [dist_comm]; exact not_le.mp hcon⟩)
