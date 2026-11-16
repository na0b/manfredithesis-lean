-- Preamble: shared imports for all tablet nodes.
-- Add specific Mathlib imports here (never `import Mathlib`).
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

-- Background items listed in `Preamble.tex`.  Each import below carries the
-- Mathlib theorem named in the corresponding `proposition` block; nothing here
-- is a project declaration.
-- Hoelder on a set of finite measure, the L^q(E) subset L^1(E) corollary, and
-- the two transport facts: `MeasureTheory.Measure.restrict_mono` with
-- `MeasureTheory.MemLp.mono_measure` for subsets, and
-- `MeasureTheory.memLp_indicator_iff_restrict` (with
-- `MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict`) for zero-extensions:
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
--   `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`,
--   `MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ`,
--   `MeasureTheory.MemLp.mono_exponent`.
-- Vanishing integral of a nonnegative function:
--   `MeasureTheory.integral_eq_zero_iff_of_nonneg_ae`.
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
-- The L^q triangle (Minkowski) inequality, closure under scalar multiples and
-- the constants:
--   `MeasureTheory.eLpNorm_add_le`, `MeasureTheory.MemLp.add`,
--   `MeasureTheory.MemLp.const_mul`, `MeasureTheory.MemLp.const_smul`,
--   `MeasureTheory.memLp_const`.
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
-- Cauchy-Schwarz for a real inner product space:
--   `abs_real_inner_le_norm`, `real_inner_mul_inner_self_le`.
import Mathlib.Analysis.InnerProductSpace.Basic
-- Lebesgue dominated convergence:
--   `MeasureTheory.tendsto_integral_of_dominated_convergence`.
import Mathlib.MeasureTheory.Integral.DominatedConvergence
-- Measurability of superlevel sets and of countable set operations on them:
--   `measurableSet_lt`, `MeasurableSet.diff`, `MeasurableSet.iInter`,
--   `MeasurableSet.iUnion`.
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
-- The fundamental theorem of calculus in interval-integral form:
--   `intervalIntegral.integral_eq_sub_of_hasDerivAt`,
--   `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`.
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
-- Interval integrability of `t ^ r` for `r > -1`:
--   `intervalIntegral.intervalIntegrable_rpow'`.
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
-- Measurability of the derivative of an arbitrary map:
--   `measurable_fderiv`, `measurable_fderiv_apply_const`,
--   `stronglyMeasurable_deriv`.
import Mathlib.Analysis.Calculus.FDeriv.Measurable
-- Domination, monotonicity and the norm inequality for the (interval) integral:
--   `MeasureTheory.Integrable.mono'`, `IntervalIntegrable.mono_fun`,
--   `intervalIntegral.integral_mono_on`, `intervalIntegral.integral_mono_ae`,
--   `intervalIntegral.norm_integral_le_integral_norm`.
import Mathlib.MeasureTheory.Function.L1Space.Integrable
-- Density of the compactly supported continuous functions in `L^q`:
--   `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`.
import Mathlib.MeasureTheory.Function.ContinuousMapDense
-- An almost everywhere convergent subsequence out of `L^q` convergence:
--   `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top`,
--   `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`.
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
-- Tonelli's theorem for a nonnegative measurable function of two variables,
-- and Fubini's theorem for an integrable one:
--   `MeasureTheory.lintegral_lintegral_swap`,
--   `MeasureTheory.integral_integral_swap`.
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
-- Translation invariance of Lebesgue measure and of the `L^q` seminorm, and
-- invariance under a linear automorphism of determinant of absolute value 1:
--   `measurePreserving_add_right`, `MeasureTheory.measure_preimage_add`,
--   `MeasureTheory.eLpNorm_comp_measurePreserving`,
--   `MeasureTheory.Measure.addHaar_preimage_linearMap`,
--   `MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`.
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
-- Smoothness of a convolution with a smooth compactly supported kernel, and
-- its derivative:
--   `HasCompactSupport.contDiff_convolution_right`,
--   `HasCompactSupport.hasFDerivAt_convolution_right`.
import Mathlib.Analysis.Calculus.ContDiff.Convolution
-- The fundamental lemma of the calculus of variations (du Bois-Reymond) on an
-- open set:
--   `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`,
--   `ae_eq_zero_of_integral_contDiff_smul_eq_zero`.
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
-- Symmetry of the second Frechet derivative (Clairaut):
--   `second_derivative_symmetric`, `second_derivative_symmetric_of_eventually`.
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
-- Integration by parts in a direction, for two differentiable functions one of
-- which has compact support:
--   `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`.
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
-- The volume of a ball: translation invariance of the centre and the scaling
-- `|B_r| = r^n |B_1|`:
--   `MeasureTheory.Measure.addHaar_ball_center`,
--   `MeasureTheory.Measure.addHaar_ball`.
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
-- A standard mollifier: a smooth, nonnegative, compactly supported probability
-- density, and its rescalings:
--   `ContDiffBump.contDiff_normed`, `ContDiffBump.nonneg_normed`,
--   `ContDiffBump.integral_normed`, `ContDiffBump.tsupport_normed_eq`,
--   `ContDiffBump.hasCompactSupport_normed`, and, for the positive lower bound
--   on the inner ball and the sup bound, `ContDiffBump.one_of_mem_closedBall`,
--   `ContDiffBump.normed_def`, `ContDiffBump.integral_pos`,
--   `ContDiffBump.normed_le_div_measure_closedBall_rIn`.
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
-- The essential supremum as the limit of normalised `L^q` means:
--   `ae_le_essSup`, `essSup_le_of_ae_le`,
--   `MeasureTheory.pow_mul_meas_ge_le_eLpNorm` (Chebyshev-Markov).
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
