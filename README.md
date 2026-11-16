# Regularity of the gradient for a class of nonlinear possibly degenerate elliptic equations, in Lean 4

This repository contains a Lean 4 formalization of the numbered lemmas and theorems of the thesis below. It is built on [Mathlib](https://github.com/leanprover-community/mathlib4).

> Juan J. Manfredi,
> *Regularity of the gradient for a class of nonlinear possibly degenerate elliptic equations*,
> Ph.D. thesis, Washington University in St. Louis, 1986. Advisor: Albert Baernstein II.
> ProQuest LLC, Ann Arbor, MI ([ProQuest](http://gateway.proquest.com/openurl?url_ver=Z39.88-2004&rft_val_fmt=info:ofi/fmt:kev:mtx:dissertation&res_dat=xri:pqdiss&rft_dat=xri:pqdiss:8713052), [MR2635642](https://mathscinet.ams.org/mathscinet-getitem?mr=2635642)).

The results of the thesis were published in

> Juan J. Manfredi,
> *Regularity for minima of functionals with p-growth*,
> Journal of Differential Equations **76** (1988), no. 2, 203–212. [doi:10.1016/0022-0396(88)90070-8](https://doi.org/10.1016/0022-0396(88)90070-8)

The thesis studies weak solutions of div A(x, u, ∇u) = B(x, u, ∇u) and local minima of variational integrals ∫ f(x, u, ∇u), with growth of order p > 1 that may degenerate (ε = 0) or be singular (p < 2). It proves:

- local boundedness and Hölder continuity of the gradient for equations with restricted structure (Theorems 1 and 2);
- Morrey and C<sup>1,β</sup> regularity for minima of nondifferentiable functionals (Theorems 3 and 4);
- the same for equations with general structure (Theorems 5 and 6);
- C<sup>η</sup> and C<sup>1,β</sup> regularity of quasiregular mappings whose distortion matrix is continuous, respectively Hölder continuous (Theorem 7).

**Seven results that the thesis quotes from the literature, (C1)–(C7), are not proved.** They are stated precisely and taken as explicit hypotheses; see [Cited results](#cited-results). Everything else is proved, including the passage from ε > 0 to ε = 0 in Theorems 1 and 2, Lemma 4.3 (for which the thesis gives no proof), and the derivation of Theorem 7 from Theorems 3 and 4 (which the thesis leaves to the reader).

The development contains no `sorry` and no axioms. Each of the eighteen results depends only on the three standard axioms of Lean: `propext`, `Classical.choice` and `Quot.sound`.

<!-- TODO: remove once the statements below have been read against the thesis. -->

## Results

| Thesis | Lean declaration |
|---|---|
| Lemma 2.1 | [`DeGiorgiSequenceLemma`](ManfrediThesis/DeGiorgiSequenceLemma.lean) |
| Lemma 2.2 | [`DeGiorgiLevelSetMeasure`](ManfrediThesis/DeGiorgiLevelSetMeasure.lean) |
| Lemma 2.3 | [`LevelTruncationMaximumPrinciple`](ManfrediThesis/LevelTruncationMaximumPrinciple.lean) |
| Lemma 2.4 | [`LevelSetMeasureImprovement`](ManfrediThesis/LevelSetMeasureImprovement.lean) |
| Lemma 2.5 | [`OscillationDecayLemma`](ManfrediThesis/OscillationDecayLemma.lean) |
| Lemma 3.1 | [`DirichletProblemRestricted`](ManfrediThesis/DirichletProblemRestricted.lean) |
| Theorem 1 | [`GradientSupEstimate`](ManfrediThesis/GradientSupEstimate.lean) |
| Theorem 2 | [`GradientOscillationEstimate`](ManfrediThesis/GradientOscillationEstimate.lean) |
| Lemma 3.2 | [`DegenerateAlternative`](ManfrediThesis/DegenerateAlternative.lean) |
| Lemma 4.1 | [`ComparisonGradientEstimateMin`](ManfrediThesis/ComparisonGradientEstimateMin.lean) |
| Lemma 4.2 | [`MorreyGradientToCampanato`](ManfrediThesis/MorreyGradientToCampanato.lean) |
| Lemma 4.3 | [`CampanatoIterationLemma`](ManfrediThesis/CampanatoIterationLemma.lean) |
| Theorem 3 | [`MinimumMorreyRegularity`](ManfrediThesis/MinimumMorreyRegularity.lean) |
| Theorem 4 | [`MinimumGradientHolder`](ManfrediThesis/MinimumGradientHolder.lean) |
| Lemma 5.1 | [`ComparisonGradientEstimateGeneral`](ManfrediThesis/ComparisonGradientEstimateGeneral.lean) |
| Theorem 5 | [`SolutionMorreyRegularity`](ManfrediThesis/SolutionMorreyRegularity.lean) |
| Theorem 6 | [`SolutionGradientHolder`](ManfrediThesis/SolutionGradientHolder.lean) |
| Theorem 7 | [`QuasiregularRegularity`](ManfrediThesis/QuasiregularRegularity.lean) |

## Corrected statements

The formalization follows a LaTeX transcription of the typed thesis. Four statements are formalized with a correction:

- **Lemma 2.1.** The recursion is y<sub>h+1</sub> ≤ c b<sup>h</sup> y<sub>h</sub><sup>1+ε</sup>, as in Ladyzhenskaya–Ural'tseva and as applied in (2.6). With b<sup>h+1</sup>, as printed, the threshold θ is insufficient.
- **Lemma 3.2(a).** The constant 1/16 is replaced by min{1/16, 2<sup>−1−4/p</sup>}. This equals 1/16 for p ≥ 4/3; the step −λ/4<sup>2/p</sup> < −λ/8 on p. 24 needs p > 4/3.
- **Theorems 3 and 5.** τ ∈ (0, n), not [0, n). For τ = 0, part (i) would assert |∇u| ∈ L<sup>p,n</sup> = L<sup>∞</sup>, and the proof needs τ > 0 in Lemma 4.3.
- **Theorem 7.** The distortion matrix satisfies K<sup>−2/n</sup>|ξ|² ≤ (τξ, ξ) ≤ K<sup>2(n−1)/n</sup>|ξ|²; the printed upper bound |ξ|² holds only when τ = I. The exponent β depends only on n, K and δ (the printed "k" is K).

Misprints that do not affect statements were corrected in the transcription. These include the exponent (p−1)/2 in (5.6), the power n/2 in the functional on p. 52, z, z′ ∈ ℝ in (Q6), and h in (F3).

## Definitions and modelling choices

| Thesis | Lean | Meaning |
|---|---|---|
| W<sup>1,p</sup>, W<sup>1,p</sup><sub>loc</sub>, W<sup>1,p</sup><sub>0</sub> | `MemW1pOn`, `MemW1pLocOn`, `MemW1pZeroOn` | with distributional gradient (`HasWeakGradientOn`) |
| weak solution of (1.1) | `IsWeakSolutionOn` | the integrand of (1.2) is integrable and its integral vanishes for all compactly supported W<sup>1,p</sup> test functions |
| local minimum (§4) | `IsLocalMinimumOn` | |
| (Q1)–(Q2), (Q3)–(Q5), (Q6) | `EllipticStructureQ12`, `EllipticStructureQ345`, `EllipticStructureQ6` | |
| (F1), (F1)–(F3) | `VariationalGrowthF1`, `VariationalStructureF123` | |
| Morrey, Campanato spaces | `MorreyBoundOn`, `CampanatoBoundOn` | with Ω(x, ρ) = Ω ∩ B<sub>ρ</sub>(x) |
| C<sup>η</sup>, C<sup>1+β</sup> | `MemHolderOn`, `MemC1HolderOn` | Hölder classes on the closure of Ω′ |
| K-quasiregular, distortion matrix τ | `IsQuasiregularOn`, `IsDistortionMatrix` | |

Points where the Lean statement makes a choice the reader should check:

- **"Depends only on."** When the thesis says that a constant or a norm depends only on certain quantities, the Lean statement chooses it (`∃ C, ...`) after exactly those quantities and before the remaining data. For example, in Theorem 1 the constant is chosen from n, p and a bound r for γ<sub>1</sub>/γ<sub>0</sub>.
- **Representatives.** Sobolev functions are known only up to null sets. Pointwise conclusions are therefore stated almost everywhere (the supremum in Theorem 1 is an essential supremum on B<sub>R/2</sub>). Hölder conclusions assert a representative w, equal to u almost everywhere, with the stated regularity.
- **Measurability.** A and B are Carathéodory: measurable in x and continuous in (z, h).
- **Domains.** In Theorems 3–7, Ω′ is a bounded Lipschitz domain (`IsBoundedLipschitzDomain`) with closure inside Ω, as Campanato's theorem requires.
- **Non-vacuity.** Model witnesses show that the structure hypotheses are satisfiable, including at ε = 0 and 1 < p < 2: `ModelFieldStructureQ12` (A(h) = |h|<sup>p−2</sup>h), `ModelDensityStructureF123` and `ModelQuasiregularIdentity`.

## Theorem 1

```lean
theorem GradientSupEstimate :
    ∀ (n : ℕ) (p r : ℝ), 2 ≤ n → 1 < p → 0 < r →
      CitedSobolevPoincareBall n →
      (∀ (ε' γ₀' γ₁' : ℝ)
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → CitedDirichletW1p n p ε' γ₀' γ₁' A') →
      (∀ (ε' γ₀' γ₁' : ℝ) (Ω' : Set (EuclideanSpace ℝ (Fin n)))
        (A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        0 < γ₀' → 0 < γ₁' → IsOpen Ω' → CitedRegularityEpsPos n p ε' γ₀' γ₁' Ω' A') →
      ∃ C : ℝ, 0 < C ∧
        ∀ (ε γ₀ γ₁ : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
          (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ),
          0 ≤ ε → 0 < γ₀ → γ₁ ≤ r * γ₀ → IsOpen Ω → 0 < R → A 0 = 0 →
          EllipticStructureQ12 n p ε γ₀ γ₁ Ω (fun _ _ h => A h) →
          IsWeakSolutionOn n p Ω (fun _ _ h => A h) (fun _ _ _ => 0) u g →
          Metric.closedBall x₀ R ⊆ Ω →
          ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))),
            (ε + ‖g x‖ ^ 2) ^ (p / 2)
              ≤ C / R ^ (n : ℝ) * ∫ y in Metric.ball x₀ R, (ε + ‖g y‖ ^ 2) ^ (p / 2) := ...
```

The other statements have the same shape: the cited results first, then the constants, then the data. They are longer; see the files linked above.

## Cited results

The cited results are predicates, stated in the file of the same name. Each is an explicit hypothesis of the results that use it. No axiom is introduced.

| Thesis | Lean hypothesis | Content |
|---|---|---|
| (C1) [LU], [DB], [GT] | `CitedRegularityEpsPos` | for ε > 0, a weak solution of (3.1) under (Q1)–(Q2) has W<sup>2,2</sup><sub>loc</sub> regularity and a continuous gradient (up to a representative). The thesis says C²; that is stronger than the literature under (Q1)–(Q2) alone and is not assumed. |
| (C2) monotone operators | `CitedDirichletW1p` | solvability of the Dirichlet problem for (3.1) on a ball with W<sup>1,p</sup> boundary data |
| (C3) [DB, Lemma 5.1], [T, Thm 3] | `CitedDirichletHolder` | existence and regularity in Lemma 3.1; uniqueness and the oscillation bound are proved |
| (C4) [G], [GG2], [LU] | `CitedHolderOscillationMinimum`, `CitedHolderOscillationSolution` | De Giorgi–Ladyzhenskaya–Ural'tseva Hölder estimates for bounded minima (p. 31) and bounded solutions ((5.1)) |
| (C5) Campanato [G, ch. III] | `CitedCampanatoEmbedding` | ℒ<sup>p,λ</sup> ⊂ C<sup>0,(λ−n)/p</sup> on a bounded Lipschitz domain, n < λ < n + p |
| (C6) | `CitedSobolevPoincareBall` | Sobolev–Poincaré inequality on balls with exponent n/(n−1) |
| (C7) [BI], [R], [GLM] | `CitedQuasiregularBasics` | a K-quasiregular map has a continuous representative; J<sub>F</sub> > 0 a.e. unless F is a.e. constant; each component solves (5.11) and minimizes ∫(τ∇v, ∇v)<sup>n/2</sup> |

Each hypothesis was reviewed during the formalization for two things: that it is not stronger than the cited result, and that it is not vacuous. At the first human review gate, an earlier version of (C1) asserted a continuous gradient for the given function rather than for a representative, and the structure conditions did not require measurability in x. A and B are now Carathéodory functions, and the weak-solution identity requires integrability, so that Lean's convention ∫ f = 0 for non-integrable f cannot make it vacuous. These were corrected before the proofs were written.

## What is and is not checked by Lean

The Lean kernel checks that each result follows from Mathlib, the definitions and the stated hypotheses, using only the three standard axioms. Lean does **not** check:

- that the cited results hold: they are taken from the literature, as in the thesis;
- that the definitions and statements say what the thesis says.

The statements were reviewed against the thesis during the formalization; see [How this formalization was produced](#how-this-formalization-was-produced). Readers who rely on the results should still compare them against the thesis themselves, together with the definitions they use. The definitions are listed in Section 1 of the blueprint.

## Blueprint

The directory [`blueprint/`](blueprint) contains a natural-language statement and a detailed proof for every Lean declaration. These are cross-referenced to the thesis and to each other. They are collected in [`blueprint/blueprint.pdf`](blueprint/blueprint.pdf) (395 pages): definitions and lemmas in dependency order, then the eighteen results in the order of the thesis. To rebuild it, run `pdflatex blueprint.tex` three times in that directory.

## Building and checking

Install Lean with [elan](https://github.com/leanprover/elan), then:

```sh
git clone <repository URL> manfredithesis-lean
cd manfredithesis-lean
lake exe cache get        # download prebuilt Mathlib
lake build
lake env lean Axioms.lean # print the axioms used by the eighteen results
```

The project is pinned to Lean `v4.33.0` and to the Mathlib commit recorded in `lakefile.lean`. On every push, continuous integration rebuilds the project and checks the axioms.

## Layout

```
ManfrediThesis.lean      root module, imports the eighteen results
ManfrediThesis/          one file per definition, lemma or theorem (177 files)
Axioms.lean              #print axioms for the eighteen results
blueprint/blueprint.tex  natural-language companion (inputs blueprint/nodes/*.tex)
```

## How this formalization was produced

The formalization was produced with [Trellis](https://github.com/wpegden/trellis), an AI-assisted formalization pipeline. AI agents (Claude, by Anthropic) wrote the Lean proofs and the blueprint under the Trellis protocol. Each node was reviewed automatically on three counts:

- the soundness of its natural-language proof;
- its faithfulness to the thesis;
- the agreement between its Lean statement and its natural-language statement.

Juan J. Manfredi chose the targets, decided which cited results are carried as hypotheses, and approved the statements at the Trellis gates. The Lean kernel checks every proof.

## Citation

Please cite the thesis or the article; see [`CITATION.cff`](CITATION.cff).

## License

Apache License 2.0, the license of Mathlib. See [`LICENSE`](LICENSE).
