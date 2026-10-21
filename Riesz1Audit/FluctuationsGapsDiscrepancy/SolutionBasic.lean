/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.Tactic

/-!
# Corollary 1 (CLT for interval counts and gaps): the vocabulary of the challenge

The definitions of `Challenge.lean` of the same pair, copied verbatim and without the final
theorem. The solution states and proves the theorem on top of them.
-/

@[expose] public section

namespace Riesz1Audit.FluctuationsGapsDiscrepancy

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Model parameters. -/
@[reducible] def Parameters : Type :=
  {x : ℝ × ℝ // 0 < x.1 ∧ 0 < x.2 ∧ x.2 < 1}

end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- The range for a Riesz exponent. -/
@[reducible] def RieszExponent := {s : ℝ // 0 < s ∧ s < 1}


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- The model exponent with its range proofs. -/
def parametersExponent (P : Parameters) : RieszExponent := ⟨P.val.2, P.property.2.1, P.property.2.2⟩


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Ordered lift domain in a fundamental region. -/
def orderedDomain (N : ℕ+) : Set (Fin (N : ℕ) → ℝ) :=
  {x | StrictMono x ∧ 0 ≤ x ⟨0, N.pos⟩ ∧ x ⟨0, N.pos⟩ < 1 ∧
    ∀ i, x i < x ⟨0, N.pos⟩ + 1}


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Configurations, with unique first lift in [0,1). -/
@[reducible] def Configuration (N : ℕ+) := orderedDomain N


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Canonical analytic representative, twice Mathlib's even Hurwitz function.
The kernel of the paper is its restriction to x ≠ 0.
The Mathlib value at 0 is an analytic continuation with the collision term omitted. -/
def rieszRepresentative (s : RieszExponent) (x : UnitAddCircle) : ℝ :=
  2 * (HurwitzZeta.hurwitzZetaEven x (s.val : ℂ)).re


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Energy, ordered pairs counted twice. -/
def energy (s : RieszExponent) {N : ℕ+} (X : Configuration N) : ℝ :=
  (N : ℝ) ^ (-s.val) *
    ∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.erase i,
      rieszRepresentative s ((X.val i - X.val j : ℝ) : UnitAddCircle)


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Lebesgue measure pulled back to the lift domain. -/
def configurationVolume (N : ℕ+) : Measure (Configuration N) :=
  (volume : Measure (Fin (N : ℕ) → ℝ)).comap Subtype.val


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Unnormalized Gibbs measure. -/
def gibbsWeight (P : Parameters) (N : ℕ+) : Measure (Configuration N) :=
  (configurationVolume N).withDensity (fun X => ENNReal.ofReal (Real.exp (-P.val.1 * energy (parametersExponent P) X)))


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Extended nonnegative partition function. -/
def partitionFunction (P : Parameters) (N : ℕ+) : ℝ≥0∞ := gibbsWeight P N Set.univ


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Gibbs law. Finiteness and positivity are separate analytic obligations,
never taken as hypotheses. -/
def gibbsMeasure (P : Parameters) (N : ℕ+) : Measure (Configuration N) :=
  (partitionFunction P N)⁻¹ • gibbsWeight P N


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Positive scales at most one. -/
@[reducible] def Scale := {ell : ℝ // 0 < ell ∧ ell ≤ 1}


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Fixed positive scales, as in Assumption 1.1. -/
@[reducible] def Scales : Type := ℕ+ → Scale

end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Nℓ_N tends to infinity. -/
def Mesoscopic (ell : Scales) : Prop :=
  Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (ell ⟨n + 1, Nat.succ_pos n⟩).val) atTop atTop


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Centered Gaussian, including variance zero. -/
def normalLaw (v : ℝ≥0) : Measure ℝ := ProbabilityTheory.gaussianReal 0 v


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Weak convergence of probability laws against bounded continuous functions. -/
def ConvergesInLaw (laws : ℕ → Measure ℝ) (limit : Measure ℝ) : Prop :=
  (∀ n, IsProbabilityMeasure (laws n)) ∧ IsProbabilityMeasure limit ∧
    ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun n => ∫ x, f x ∂laws n) atTop (𝓝 (∫ x, f x ∂limit))


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Periodic zeta combination.
At zero the subtraction is identically zero without assigning a collision value. -/
def periodicZeta (s : RieszExponent) (t : UnitAddCircle) : ℝ :=
  2 * ((HurwitzZeta.hurwitzZetaEven t (-s.val : ℂ)).re -
    (HurwitzZeta.hurwitzZetaEven 0 (-s.val : ℂ)).re)


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Count and gap limiting variance. This is the variance in Corollary 1 of the paper. -/
def countVariance (P : Parameters) : ℝ :=
  Real.cos (Real.pi * P.val.2 / 2) / Real.sin (Real.pi * P.val.2 / 2) /
    (2 * P.val.1 * Real.pi * P.val.2)


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Particle count n+1, for sequences starting at zero. -/
def particleNumber (n : ℕ) : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Gibbs normalization is a conclusion, including the nonzero finite partition
function. -/
def ModelWellDefined (P : Parameters) : Prop :=
  ∀ N : ℕ+, 0 < partitionFunction P N ∧ partitionFunction P N < ⊤ ∧
    IsProbabilityMeasure (gibbsMeasure P N)


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Open arc count. -/
def arcCount {N : ℕ+} (center : UnitAddCircle) (a : ℝ) (X : Configuration N) : ℝ :=
  ∑ i : Fin (N : ℕ), if dist (X.val i : UnitAddCircle) center < a then 1 else 0


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Normalized interval discrepancy, as in Corollary 1. -/
def normalizedCount (P : Parameters) (a : ℝ) (_ha : 0 < a) (_ha1 : a < 1 / 2) (ell : Scales) (N : ℕ+)
    (X : Configuration N) : ℝ :=
  (arcCount 0 (a * (ell N).val) X - 2 * a * (N : ℝ) * (ell N).val) /
    Real.sqrt ((N : ℝ) ^ P.val.2 * periodicZeta (parametersExponent P) ((2 * a * (ell N).val : ℝ) : UnitAddCircle))


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- The cyclic lift `x_{j+N} = x_j + 1` of a configuration, for every integer label `j`, computed by
Euclidean division of `j` by `N`. Labels start at zero, so the paper's `x_1` is `cyclicLift X 0`. -/
def cyclicLift {N : ℕ+} (X : Configuration N) (j : ℤ) : ℝ :=
  X.val ⟨(j % (N : ℕ)).toNat, by
    have h := Int.emod_lt_of_pos j (show (0 : ℤ) < (N : ℕ) by exact_mod_cast N.pos)
    exact_mod_cast (Int.toNat_lt (Int.emod_nonneg j (by exact_mod_cast N.ne_zero))).mpr h⟩ +
      (j / (N : ℕ) : ℤ)


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Normalized gap based at paper label 1. This is the gap in Corollary 1 of the paper. -/
def normalizedGap (P : Parameters) (N : ℕ+) (k : ℕ) (_hk : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) (X : Configuration N) : ℝ :=
  ((N : ℝ) * (cyclicLift X k - cyclicLift X 0) - k) /
    Real.sqrt ((N : ℝ) ^ P.val.2 * periodicZeta (parametersExponent P) (((k : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle))


end Riesz1

end

end Riesz1Audit.FluctuationsGapsDiscrepancy

end
