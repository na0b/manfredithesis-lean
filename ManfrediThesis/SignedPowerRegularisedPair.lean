import ManfrediThesis.Preamble
set_option maxHeartbeats 800000
open MeasureTheory

/-- The regularised signed power and its primitive, for `1 < p < 2`: there are
`π_η(s) = (|s| + η)^{p-2}s`, its derivative `Dπ_η`, the primitive
`G_η(s) = ∫_0^s \tfrac p2(|t| + η)^{\frac p2-1}dt` and its derivative
`DG_η(s) = \tfrac p2(|s| + η)^{\frac p2-1}`, such that for every `η > 0`:
`Dπ_η ≥ (p-1)(|s| + η)^{p-2}` and `|Dπ_η| ≤ η^{p-2}` pointwise, `Dπ_η` is
continuous, `π_η` is `C¹` with `deriv π_η = Dπ_η`,
`|DG_η| ≤ \tfrac p2η^{\frac p2-1}` pointwise, and `G_η` is `C¹` with
`deriv G_η = DG_η`.

Conventions, restated here because a helper inherits none of its parent's.
Everything here is one-dimensional: no domain, no Sobolev space and no
reference to the equation appear, which is why the only parameters are `p` and
the two sign facts about its exponents.  Every power of a positive real is the
real power, so `(|s| + η)^{p-2}` and `(|s| + η)^{\frac p2-1}` are `rpow` with
NEGATIVE exponents --- `p - 2 < 0` and `p/2 - 1 < 0` are hypotheses, not
consequences --- and this is exactly why the regularisation `η > 0` is needed:
it keeps the base away from `0`, where those powers blow up.  The primitive is
the interval integral from `0`, so `G_η(0) = 0`.

The route.  `Dπ_η` is defined by the product rule applied formally to
`π_η(s) = (|s| + η)^{p-2}s`, namely
`Dπ_η(s) = (|s| + η)^{p-2} + (p-2)(|s| + η)^{p-3}|s|`, and the two bounds come
from `0 ≤ |s| ≤ |s| + η`: the upper one gives
`Dπ_η(s) ≤ (|s| + η)^{p-2}`, so `|Dπ_η| ≤ η^{p-2}` because `p - 2 < 0` makes
the power decreasing and `η ≤ |s| + η`; the lower one gives
`Dπ_η(s) ≥ (1 + (p-2))(|s| + η)^{p-2} = (p-1)(|s| + η)^{p-2} > 0`, using
`(|s| + η)^{p-3}|s| ≤ (|s| + η)^{p-2}` from the same monotonicity.  That
`Dπ_η` is really the derivative is checked by cases on the sign of `s`: away
from `0` the function agrees locally with `(\pm s + η)^{p-2}s`, which is
differentiable by the product and chain rules; at `s = 0` the two one-sided
derivatives agree, both being `η^{p-2}`, because the `|s|` factor contributes
nothing there.  Continuity of `Dπ_η` follows from continuity of
`s ↦ |s| + η > 0` and of the real power on the positive reals, and `π_η` is
therefore `C¹` with `deriv π_η = Dπ_η`.  For the primitive, the integrand
`t ↦ \tfrac p2(|t| + η)^{\frac p2-1}` is continuous and bounded by
`\tfrac p2η^{\frac p2-1}`, so the fundamental theorem of calculus gives
`G_η` differentiable with `deriv G_η = DG_η`, and `C¹` since `DG_η` is
continuous. -/
theorem SignedPowerRegularisedPair :
    ∀ p : ℝ, 1 < p → p / 2 - 1 < 0 → p - 2 < 0 →
      ∃ Dpi pie Gee DG : ℝ → ℝ → ℝ,
        pie = (fun η s => (|s| + η) ^ (p - 2) * s)
        ∧ Gee = (fun η s => ∫ t in (0:ℝ)..s, p / 2 * (|t| + η) ^ (p / 2 - 1))
        ∧ DG = (fun η s => p / 2 * (|s| + η) ^ (p / 2 - 1))
        ∧ (∀ (η : ℝ), 0 < η → ∀ s : ℝ, 0 < |s| + η)
        ∧ (∀ (η : ℝ), 0 < η → ∀ s : ℝ,
            (p - 1) * (|s| + η) ^ (p - 2) ≤ Dpi η s)
        ∧ (∀ (η : ℝ), 0 < η → ∀ s : ℝ, |Dpi η s| ≤ η ^ (p - 2))
        ∧ (∀ (η : ℝ), 0 < η → Continuous (Dpi η))
        ∧ (∀ (η : ℝ), 0 < η → ContDiff ℝ 1 (pie η))
        ∧ (∀ (η : ℝ), 0 < η → deriv (pie η) = Dpi η)
        ∧ (∀ (η : ℝ), 0 < η → ∀ s : ℝ,
            |DG η s| ≤ p / 2 * η ^ (p / 2 - 1))
        ∧ (∀ (η : ℝ), 0 < η → deriv (Gee η) = DG η)
        ∧ (∀ (η : ℝ), 0 < η → ContDiff ℝ 1 (Gee η)) := by
  intro p hp hexpn hp2n
  obtain ⟨Dpi, hDpidef⟩ : ∃ f : ℝ → ℝ → ℝ,
    f = fun η s => (|s| + η) ^ (p - 2) + (p - 2) * (|s| + η) ^ (p - 3) * |s| :=
    ⟨_, rfl⟩
  obtain ⟨pie, hpiedef⟩ : ∃ f : ℝ → ℝ → ℝ,
    f = fun η s => (|s| + η) ^ (p - 2) * s := ⟨_, rfl⟩
  obtain ⟨Gee, hGeedef⟩ : ∃ f : ℝ → ℝ → ℝ,
    f = fun η s => ∫ t in (0:ℝ)..s, p / 2 * (|t| + η) ^ (p / 2 - 1) := ⟨_, rfl⟩
  have hbase : ∀ (η : ℝ), 0 < η → ∀ s : ℝ, 0 < |s| + η := by
    intro η hη s
    have := abs_nonneg s
    linarith only [this, hη]
  -- (D.1)
  have hDpiup : ∀ (η : ℝ), 0 < η → ∀ s : ℝ, Dpi η s ≤ (|s| + η) ^ (p - 2) := by
    intro η hη s
    rw [hDpidef]
    show (|s| + η) ^ (p - 2) + (p - 2) * (|s| + η) ^ (p - 3) * |s|
        ≤ (|s| + η) ^ (p - 2)
    have h1 : (0:ℝ) ≤ (|s| + η) ^ (p - 3) * |s| :=
      mul_nonneg (Real.rpow_nonneg (hbase η hη s).le _) (abs_nonneg s)
    nlinarith only [h1, hp2n]
  have hDpilow : ∀ (η : ℝ), 0 < η → ∀ s : ℝ,
      (p - 1) * (|s| + η) ^ (p - 2) ≤ Dpi η s := by
    intro η hη s
    rw [hDpidef]
    show (p - 1) * (|s| + η) ^ (p - 2)
        ≤ (|s| + η) ^ (p - 2) + (p - 2) * (|s| + η) ^ (p - 3) * |s|
    have hb := hbase η hη s
    have h1 : (|s| + η) ^ (p - 3) * |s| ≤ (|s| + η) ^ (p - 2) := by
      have h2 : (|s| + η) ^ (p - 3) * (|s| + η) = (|s| + η) ^ (p - 2) := by
        rw [← Real.rpow_add_one (ne_of_gt hb) (p - 3),
          show p - 3 + 1 = p - 2 from by ring]
      calc (|s| + η) ^ (p - 3) * |s|
          ≤ (|s| + η) ^ (p - 3) * (|s| + η) :=
            mul_le_mul_of_nonneg_left (by linarith only [hη])
              (Real.rpow_nonneg hb.le _)
        _ = (|s| + η) ^ (p - 2) := h2
    nlinarith only [h1, hp2n]
  have hDpipos : ∀ (η : ℝ), 0 < η → ∀ s : ℝ, 0 < Dpi η s := by
    intro η hη s
    refine lt_of_lt_of_le ?_ (hDpilow η hη s)
    exact mul_pos (by linarith only [hp]) (Real.rpow_pos_of_pos (hbase η hη s) _)
  have hDpibd : ∀ (η : ℝ), 0 < η → ∀ s : ℝ, |Dpi η s| ≤ η ^ (p - 2) := by
    intro η hη s
    rw [abs_of_pos (hDpipos η hη s)]
    refine le_trans (hDpiup η hη s) ?_
    exact Real.rpow_le_rpow_of_nonpos hη (by linarith only [abs_nonneg s]) hp2n.le
  have hDpicont : ∀ (η : ℝ), 0 < η → Continuous (Dpi η) := by
    intro η hη
    rw [hDpidef]
    have hb : Continuous fun s : ℝ => |s| + η := continuous_abs.add continuous_const
    have h1 : Continuous fun s : ℝ => (|s| + η) ^ (p - 2) :=
      hb.rpow_const fun s => Or.inl (ne_of_gt (hbase η hη s))
    have h2 : Continuous fun s : ℝ => (|s| + η) ^ (p - 3) :=
      hb.rpow_const fun s => Or.inl (ne_of_gt (hbase η hη s))
    exact h1.add ((continuous_const.mul h2).mul continuous_abs)
  -- `π_η` is `C¹` with derivative `Dpi η`
  have hpieD : ∀ (η : ℝ), 0 < η → ∀ s : ℝ, HasDerivAt (pie η) (Dpi η s) s := by
    intro η hη s
    have hb := hbase η hη
    rcases lt_trichotomy s 0 with hs | hs | hs
    · have hloc : pie η =ᶠ[nhds s] fun t => (-t + η) ^ (p - 2) * t := by
        filter_upwards [IsOpen.mem_nhds isOpen_Iio hs] with t ht
        rw [hpiedef]
        show (|t| + η) ^ (p - 2) * t = (-t + η) ^ (p - 2) * t
        rw [abs_of_neg ht]
      have hin : HasDerivAt (fun t : ℝ => -t + η) (-1) s :=
        (hasDerivAt_neg s).add_const η
      have hpow : HasDerivAt (fun t : ℝ => (-t + η) ^ (p - 2))
          ((p - 2) * (-s + η) ^ (p - 2 - 1) * (-1)) s :=
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (by
          rw [← abs_of_neg hs]; exact hb s)))).comp s hin
      have hprod := hpow.mul (hasDerivAt_id s)
      have heq : (p - 2) * (-s + η) ^ (p - 2 - 1) * (-1) * s
          + (-s + η) ^ (p - 2) * 1 = Dpi η s := by
        rw [hDpidef]
        show (p - 2) * (-s + η) ^ (p - 2 - 1) * (-1) * s + (-s + η) ^ (p - 2) * 1
            = (|s| + η) ^ (p - 2) + (p - 2) * (|s| + η) ^ (p - 3) * |s|
        rw [abs_of_neg hs, show p - 2 - 1 = p - 3 from by ring]
        ring
      rw [← heq]
      exact hprod.congr_of_eventuallyEq hloc
    · -- `s = 0`
      subst hs
      have hslope : ∀ t : ℝ, t ≠ 0 → slope (pie η) 0 t = (|t| + η) ^ (p - 2) := by
        intro t ht
        rw [slope_def_field, hpiedef]
        show ((|t| + η) ^ (p - 2) * t - (|(0:ℝ)| + η) ^ (p - 2) * 0) / (t - 0)
            = (|t| + η) ^ (p - 2)
        field_simp
        ring
      have hval : Dpi η 0 = (|(0:ℝ)| + η) ^ (p - 2) := by
        rw [hDpidef]
        show (|(0:ℝ)| + η) ^ (p - 2) + (p - 2) * (|(0:ℝ)| + η) ^ (p - 3) * |(0:ℝ)|
            = (|(0:ℝ)| + η) ^ (p - 2)
        simp
      rw [hasDerivAt_iff_tendsto_slope, hval]
      have hc : Continuous fun t : ℝ => (|t| + η) ^ (p - 2) :=
        (continuous_abs.add continuous_const).rpow_const
          fun t => Or.inl (ne_of_gt (hb t))
      refine Filter.Tendsto.congr' ?_ ((hc.tendsto 0).mono_left nhdsWithin_le_nhds)
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hslope t ht).symm
    · have hloc : pie η =ᶠ[nhds s] fun t => (t + η) ^ (p - 2) * t := by
        filter_upwards [IsOpen.mem_nhds isOpen_Ioi hs] with t ht
        rw [hpiedef]
        show (|t| + η) ^ (p - 2) * t = (t + η) ^ (p - 2) * t
        rw [abs_of_pos ht]
      have hin : HasDerivAt (fun t : ℝ => t + η) 1 s := (hasDerivAt_id s).add_const η
      have hpow : HasDerivAt (fun t : ℝ => (t + η) ^ (p - 2))
          ((p - 2) * (s + η) ^ (p - 2 - 1) * 1) s :=
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (by
          rw [← abs_of_pos hs]; exact hb s)))).comp s hin
      have hprod := hpow.mul (hasDerivAt_id s)
      have heq : (p - 2) * (s + η) ^ (p - 2 - 1) * 1 * s + (s + η) ^ (p - 2) * 1
          = Dpi η s := by
        rw [hDpidef]
        show (p - 2) * (s + η) ^ (p - 2 - 1) * 1 * s + (s + η) ^ (p - 2) * 1
            = (|s| + η) ^ (p - 2) + (p - 2) * (|s| + η) ^ (p - 3) * |s|
        rw [abs_of_pos hs, show p - 2 - 1 = p - 3 from by ring]
        ring
      rw [← heq]
      exact hprod.congr_of_eventuallyEq hloc
  have hpieC1 : ∀ (η : ℝ), 0 < η → ContDiff ℝ 1 (pie η) := by
    intro η hη
    refine contDiff_one_iff_deriv.2 ⟨fun s => (hpieD η hη s).differentiableAt, ?_⟩
    have hd : deriv (pie η) = Dpi η := by
      funext s; exact (hpieD η hη s).deriv
    rw [hd]
    exact hDpicont η hη
  have hpiederiv : ∀ (η : ℝ), 0 < η → deriv (pie η) = Dpi η := by
    intro η hη; funext s; exact (hpieD η hη s).deriv
  -- `G_η` is `C¹` with derivative `(p/2)(|s|+η)^{p/2-1}`
  obtain ⟨DG, hDGdef⟩ : ∃ f : ℝ → ℝ → ℝ,
    f = fun η s => p / 2 * (|s| + η) ^ (p / 2 - 1) := ⟨_, rfl⟩
  have hDGcont' : ∀ (η : ℝ), 0 < η →
      Continuous (fun t : ℝ => p / 2 * (|t| + η) ^ (p / 2 - 1)) := by
    intro η hη
    exact continuous_const.mul
      ((continuous_abs.add continuous_const).rpow_const
        fun s => Or.inl (ne_of_gt (hbase η hη s)))
  have hDGcont : ∀ (η : ℝ), 0 < η → Continuous (DG η) := by
    intro η hη
    rw [hDGdef]
    exact hDGcont' η hη
  have hDGbd : ∀ (η : ℝ), 0 < η → ∀ s : ℝ, |DG η s| ≤ p / 2 * η ^ (p / 2 - 1) := by
    intro η hη s
    rw [hDGdef]
    show |p / 2 * (|s| + η) ^ (p / 2 - 1)| ≤ p / 2 * η ^ (p / 2 - 1)
    have h1 : (0:ℝ) < (|s| + η) ^ (p / 2 - 1) :=
      Real.rpow_pos_of_pos (hbase η hη s) _
    rw [abs_of_pos (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Real.rpow_le_rpow_of_nonpos hη (by linarith only [abs_nonneg s]) hexpn.le
  have hGeeD : ∀ (η : ℝ), 0 < η → ∀ s : ℝ, HasDerivAt (Gee η) (DG η s) s := by
    intro η hη s
    simp only [hGeedef, hDGdef]
    exact ((hDGcont' η hη).integral_hasStrictDerivAt 0 s).hasDerivAt
  have hGeederiv : ∀ (η : ℝ), 0 < η → deriv (Gee η) = DG η := by
    intro η hη; funext s; exact (hGeeD η hη s).deriv
  have hGeeC1 : ∀ (η : ℝ), 0 < η → ContDiff ℝ 1 (Gee η) := by
    intro η hη
    refine contDiff_one_iff_deriv.2 ⟨fun s => (hGeeD η hη s).differentiableAt, ?_⟩
    rw [hGeederiv η hη]
    exact hDGcont η hη
  exact ⟨Dpi, pie, Gee, DG, hpiedef, hGeedef, hDGdef, hbase, hDpilow, hDpibd,
    hDpicont, hpieC1, hpiederiv, hDGbd, hGeederiv, hGeeC1⟩
