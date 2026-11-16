import ManfrediThesis.Preamble
import ManfrediThesis.MemW1pOn
import ManfrediThesis.MemW1pLocOn
import ManfrediThesis.IsQuasiregularOn
import ManfrediThesis.IsDistortionMatrix
import ManfrediThesis.CitedQuasiregularBasics
import ManfrediThesis.IsLocalMinimumOn
import ManfrediThesis.WeakGradientRestrict
open MeasureTheory

/-- The local data extracted from a quasiregular map on the interposed set
`Ω''` of §5: each coordinate lies in `W^{1,n}(Ω'')` rather than merely
`W^{1,n}_loc(Ω)`, is essentially bounded there, has a bound `W` on the sum of
the two `L^n` energies, and is a local minimum of the frozen integrand.  The
last clause transports the local minimality supplied by the cited
quasiregular basics across the almost-everywhere equality `τ = τ'`, which is
legitimate because the two integrands agree almost everywhere on each
`tsupport φ` and the defining integrals are unchanged by a null set. -/
theorem QuasiregularFrozenLocalData :
    ∀ (n : ℕ) (K : ℝ), 2 ≤ n → 1 ≤ K →
      ∀ (Ω Ω'' : Set (EuclideanSpace ℝ (Fin n)))
        (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (G : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (τ τ' : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
        (fdens : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
        (i : Fin n),
        IsOpen Ω → IsOpen Ω'' → closure Ω'' ⊆ Ω → IsCompact (closure Ω'') →
        IsQuasiregularOn n K Ω F G → IsDistortionMatrix n Ω G τ →
        (∀ Ω₀ : Set (EuclideanSpace ℝ (Fin n)), IsOpen Ω₀ → Ω₀ ⊆ Ω →
          CitedQuasiregularBasics n K Ω₀ F G τ) →
        (¬ ∃ c : EuclideanSpace ℝ (Fin n),
          ∀ᵐ x ∂(volume.restrict Ω), F x = c) →
        (∀ᵐ x ∂(volume.restrict Ω), τ x = τ' x) →
        (∀ x ∈ Ω'', ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)),
          fdens x z h = (∑ a, ∑ b, τ' x a b * h a * h b) ^ ((n : ℝ) / 2)) →
        ∃ M Wn : ℝ,
          0 ≤ M ∧ 0 ≤ Wn ∧
            MemW1pOn n (n : ℝ) Ω'' (fun x => F x i) (G i) ∧
            (∀ᵐ x ∂(volume.restrict Ω''), |F x i| ≤ M) ∧
            ((∫ x in Ω'', |F x i| ^ (n : ℝ))
                + ∫ x in Ω'', ‖G i x‖ ^ (n : ℝ)) ≤ Wn ^ (n : ℝ) ∧
            IsLocalMinimumOn n (n : ℝ) Ω'' fdens (fun x => F x i) (G i) := by
  intro n K hn hK Ω Ω'' F G τ τ' fdens i hΩ hΩ'' hcl hcpt hqr hdist hbasics hnc
    hττ' hfd
  have hsub : Ω'' ⊆ Ω := subset_trans subset_closure hcl
  have h1n : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
  have h1q : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1n
  have hnne : (n : ℝ) ≠ 0 := by positivity
  have hpow : ∀ t : ℝ, 0 ≤ t → (t ^ (1 / (n : ℝ))) ^ (n : ℝ) = t := by
    intro t ht
    rw [← Real.rpow_mul ht, one_div_mul_cancel hnne, Real.rpow_one]
  -- The quasiregular data restricts from `Ω` to `Ω''`.
  have hqr'' : IsQuasiregularOn n K Ω'' F G := by
    refine ⟨fun j => (WeakGradientRestrict n (n : ℝ) h1n h1q Ω Ω''
      (fun x => F x j) (G j) hΩ hΩ'' hsub).2.1 (hqr.1 j), ?_⟩
    filter_upwards [hqr.2] with x hx hxΩ''
    exact hx (hsub hxΩ'')
  have hdist'' : IsDistortionMatrix n Ω'' G τ := fun x hx => hdist x (hsub hx)
  -- (C7) at `Ω₀ = Ω''`; its clause (4) is the local minimum for the
  -- `τ`-integrand.
  have hmin_tau : IsLocalMinimumOn n (n : ℝ) Ω''
      (fun x _ h => (∑ a, ∑ b, τ x a b * h a * h b) ^ ((n : ℝ) / 2))
      (fun x => F x i) (G i) :=
    (hbasics Ω'' hΩ'' hsub hqr'' hdist'').2.2.2 i
  -- On `Ω''` the given integrand agrees with the `τ`-integrand almost
  -- everywhere, for every value of the second and third arguments.
  have hττ'' : ∀ᵐ x ∂(volume.restrict Ω''), τ x = τ' x :=
    ae_restrict_of_ae_restrict_of_subset hsub hττ'
  have hkey : ∀ᵐ x ∂(volume.restrict Ω''),
      ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)),
      fdens x z h = (∑ a, ∑ b, τ x a b * h a * h b) ^ ((n : ℝ) / 2) := by
    filter_upwards [hττ'', ae_restrict_mem hΩ''.measurableSet] with x hx hxΩ'' z h
    rw [hfd x hxΩ'' z h, hx]
  -- The local minimum transports to `fdens`.
  have hmin : IsLocalMinimumOn n (n : ℝ) Ω'' fdens (fun x => F x i) (G i) := by
    refine ⟨hmin_tau.1, fun φ gφ hφ hcs hsupp => ?_⟩
    obtain ⟨hint1, hint2, hle⟩ := hmin_tau.2 φ gφ hφ hcs hsupp
    have hts : ∀ᵐ x ∂(volume.restrict (tsupport φ)),
        ∀ (z : ℝ) (h : EuclideanSpace ℝ (Fin n)),
        fdens x z h = (∑ a, ∑ b, τ x a b * h a * h b) ^ ((n : ℝ) / 2) :=
      ae_restrict_of_ae_restrict_of_subset hsupp hkey
    have e1 : (fun x => (∑ a, ∑ b, τ x a b * G i x a * G i x b) ^ ((n : ℝ) / 2))
        =ᵐ[volume.restrict (tsupport φ)]
          fun x => fdens x (F x i) (G i x) := by
      filter_upwards [hts] with x hx
      exact (hx (F x i) (G i x)).symm
    have e2 : (fun x => (∑ a, ∑ b, τ x a b * (G i x + gφ x) a * (G i x + gφ x) b)
            ^ ((n : ℝ) / 2))
        =ᵐ[volume.restrict (tsupport φ)]
          fun x => fdens x (F x i + φ x) (G i x + gφ x) := by
      filter_upwards [hts] with x hx
      exact (hx (F x i + φ x) (G i x + gφ x)).symm
    refine ⟨hint1.congr e1, hint2.congr e2, ?_⟩
    rw [← integral_congr_ae e1, ← integral_congr_ae e2]
    exact hle
  -- `W^{1,n}(Ω'')` membership, by clause (4) of the restriction node.
  have hW1p : MemW1pOn n (n : ℝ) Ω'' (fun x => F x i) (G i) :=
    (WeakGradientRestrict n (n : ℝ) h1n h1q Ω Ω'' (fun x => F x i) (G i)
      hΩ hΩ'' hsub).2.2.2 (hqr.1 i) hcpt hcl
  -- The sup bound, through (C7)'s continuous representative at `Ω₀ = Ω`.
  obtain ⟨Ft, hFtcont, hFtae⟩ := (hbasics Ω hΩ (subset_refl Ω) hqr hdist).1
  have hproj : ContinuousOn (fun x => Ft x i) (closure Ω'') := by
    have := (EuclideanSpace.proj i).continuous.comp_continuousOn
      (hFtcont.mono hcl)
    simpa [Function.comp_def] using this
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hproj
  refine ⟨max C 0, (((∫ x in Ω'', |F x i| ^ (n : ℝ))
      + ∫ x in Ω'', ‖G i x‖ ^ (n : ℝ)) ⊔ 0) ^ (1 / (n : ℝ)),
    le_max_right _ _, Real.rpow_nonneg (le_max_right _ _) _, hW1p, ?_, ?_, hmin⟩
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hFtae,
      ae_restrict_mem hΩ''.measurableSet] with x hx hxΩ''
    rw [hx]
    refine le_trans ?_ (le_max_left C 0)
    simpa [Real.norm_eq_abs] using hC x (subset_closure hxΩ'')
  · rw [hpow _ (le_max_right _ _)]
    exact le_max_left _ _
