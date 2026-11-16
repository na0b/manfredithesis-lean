import ManfrediThesis.Preamble
open MeasureTheory

/-- The almost-everywhere to everywhere upgrade for the distortion matrix.  The
properties of `τ` that §5 delivers hold only almost everywhere, while (F1) and
(F2) of §4 are asserted at every point of their domain; a continuous
representative `τ'` of `τ` therefore satisfies them at every point of the open
set, because the exceptional set is relatively open and null. -/
theorem MatrixFieldAEToEverywhere :
    ∀ (n : ℕ) (K lam Lam : ℝ), 2 ≤ n → 1 ≤ K →
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin n)))
        (τ τ' : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ),
        IsOpen Ω →
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
        ∀ x ∈ Ω,
          (τ' x).IsSymm ∧ (τ' x).det = 1 ∧
            (∀ ξ : EuclideanSpace ℝ (Fin n),
              K ^ (-(2 : ℝ) / (n : ℝ)) * ‖ξ‖ ^ 2
                  ≤ ∑ a, ∑ b, τ' x a b * ξ a * ξ b ∧
                (∑ a, ∑ b, τ' x a b * ξ a * ξ b)
                  ≤ K ^ (2 * ((n : ℝ) - 1) / (n : ℝ)) * ‖ξ‖ ^ 2) ∧
            (∀ h : EuclideanSpace ℝ (Fin n),
              lam * ‖h‖ ^ (n : ℝ)
                  ≤ (∑ a, ∑ b, τ' x a b * h a * h b) ^ ((n : ℝ) / 2) ∧
                (∑ a, ∑ b, τ' x a b * h a * h b) ^ ((n : ℝ) / 2)
                  ≤ Lam * ‖h‖ ^ (n : ℝ)) := by
  intro n K lam Lam hn hK Ω τ τ' hΩ hττ' hτ'cont hτprops
  -- The almost-everywhere statement, transported from `τ` to `τ'`.
  have hae : ∀ᵐ x ∂(volume.restrict Ω),
      (τ' x).IsSymm ∧ (τ' x).det = 1 ∧
        (∀ ξ : EuclideanSpace ℝ (Fin n),
          K ^ (-(2 : ℝ) / (n : ℝ)) * ‖ξ‖ ^ 2 ≤ ∑ a, ∑ b, τ' x a b * ξ a * ξ b ∧
            (∑ a, ∑ b, τ' x a b * ξ a * ξ b)
              ≤ K ^ (2 * ((n : ℝ) - 1) / (n : ℝ)) * ‖ξ‖ ^ 2) ∧
        (∀ h : EuclideanSpace ℝ (Fin n),
          lam * ‖h‖ ^ (n : ℝ)
              ≤ (∑ a, ∑ b, τ' x a b * h a * h b) ^ ((n : ℝ) / 2) ∧
            (∑ a, ∑ b, τ' x a b * h a * h b) ^ ((n : ℝ) / 2)
              ≤ Lam * ‖h‖ ^ (n : ℝ)) := by
    filter_upwards [hττ', hτprops] with x h1 h2
    rw [← h1]
    exact h2
  -- The upgrade itself, as one statement about a scalar function and a closed
  -- target set: the exceptional set is relatively open in `Ω`, hence open, and
  -- null, hence empty.  It is applied four times below.
  have key : ∀ (Φ : EuclideanSpace ℝ (Fin n) → ℝ) (S : Set ℝ),
      IsClosed S → ContinuousOn Φ Ω →
      (∀ᵐ x ∂(volume.restrict Ω), Φ x ∈ S) → ∀ x ∈ Ω, Φ x ∈ S := by
    intro Φ S hS hΦ hmem x hx
    by_contra hcon
    have hUopen : IsOpen (Ω ∩ Φ ⁻¹' Sᶜ) :=
      hΦ.isOpen_inter_preimage hΩ hS.isOpen_compl
    have hpos : 0 < volume (Ω ∩ Φ ⁻¹' Sᶜ) :=
      hUopen.measure_pos volume ⟨x, hx, hcon⟩
    have hzero : volume (Ω ∩ Φ ⁻¹' Sᶜ) = 0 := by
      have h1 := MeasureTheory.ae_iff.mp hmem
      rw [Measure.restrict_apply' hΩ.measurableSet] at h1
      rw [Set.inter_comm]
      exact h1
    exact absurd hzero hpos.ne'
  -- The three continuity facts the four applications need.
  have hmat : ContinuousOn τ' Ω :=
    continuousOn_pi.2 fun j => continuousOn_pi.2 fun k => hτ'cont j k
  have hdet : ContinuousOn (fun y => (τ' y).det) Ω :=
    (Continuous.matrix_det continuous_id).comp_continuousOn hmat
  have hform : ∀ h : EuclideanSpace ℝ (Fin n),
      ContinuousOn (fun y => ∑ a, ∑ b, τ' y a b * h a * h b) Ω := fun h =>
    continuousOn_finsetSum _ fun a _ =>
      continuousOn_finsetSum _ fun b _ =>
        ((hτ'cont a b).mul continuousOn_const).mul continuousOn_const
  intro x hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- symmetry
    show (τ' x).transpose = τ' x
    refine Matrix.ext fun j k => ?_
    have h0 := key (fun y => τ' y k j - τ' y j k) {0} isClosed_singleton
      ((hτ'cont k j).sub (hτ'cont j k))
      (by
        filter_upwards [hae] with y hy
        simpa using sub_eq_zero.mpr (hy.1.apply j k)) x hx
    have h1 : τ' x k j - τ' x j k = 0 := h0
    simpa [Matrix.transpose_apply] using sub_eq_zero.mp h1
  · -- the determinant
    have h0 := key (fun y => (τ' y).det) {1} isClosed_singleton hdet
      (by
        filter_upwards [hae] with y hy
        simpa using hy.2.1) x hx
    simpa using h0
  · -- the two-sided bounds on the quadratic form
    intro ξ
    have h0 := key (fun y => ∑ a, ∑ b, τ' y a b * ξ a * ξ b)
      (Set.Icc (K ^ (-(2 : ℝ) / (n : ℝ)) * ‖ξ‖ ^ 2)
        (K ^ (2 * ((n : ℝ) - 1) / (n : ℝ)) * ‖ξ‖ ^ 2))
      isClosed_Icc (hform ξ)
      (by
        filter_upwards [hae] with y hy
        exact ⟨(hy.2.2.1 ξ).1, (hy.2.2.1 ξ).2⟩) x hx
    exact ⟨h0.1, h0.2⟩
  · -- the two-sided `λ`/`Λ` bounds on its `n/2`-th power
    intro h
    have h0 := key (fun y => (∑ a, ∑ b, τ' y a b * h a * h b) ^ ((n : ℝ) / 2))
      (Set.Icc (lam * ‖h‖ ^ (n : ℝ)) (Lam * ‖h‖ ^ (n : ℝ)))
      isClosed_Icc ((hform h).rpow_const fun _ _ => Or.inr (by positivity))
      (by
        filter_upwards [hae] with y hy
        exact ⟨(hy.2.2.2 h).1, (hy.2.2.2 h).2⟩) x hx
    exact ⟨h0.1, h0.2⟩
