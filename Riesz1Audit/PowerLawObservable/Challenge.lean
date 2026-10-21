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
# Corollary 2 (CLT for power-law observables): the statement

Mathlib-only statement of Corollary 2 of J. Boursier, *Optimal local laws and central limit theorem
for the circular Riesz gas* (arXiv:2112.05881).

Let `β > 0`, `0 < s < 1` and `0 < α < s/2`. Let `ξ` be the periodic function
`ξ(x) = ζ(α, x) + ζ(α, 1-x)` for `0 < x < 1` (`rieszRepresentative`). Then the model is well
defined, `ξ` lies in `L²(T)`, it is integrable with `∫ ξ = 0`, the variance
`v = (2π)^{-1+2α-s} c_α² ζ(1+s-2α) / (β c_s)` is positive (`powerVariance`, with `c_α` and `c_s`
given by `rieszConstant`), the variables `N^{-s/2} Fluct_N[ξ]` are almost everywhere measurable, and
`N^{-s/2} Fluct_N[ξ] → N(0, v)` in law.

## How the objects are specified

`ξ` is `2 Re ζ_even(x, α)`, written with Mathlib's even Hurwitz zeta function. It agrees with the
formula above for `0 < x < 1`, Its value at `0` plays no role, since almost surely no particle is at
`0`. Convergence in law is convergence of the integrals of every bounded continuous function
(`ConvergesInLaw`), along `N = n + 1` (`particleNumber`).

The definitions below are copied without change, in dependency order, from the files
`Riesz1/Frozen/*.lean` of the library, inside the namespace `Riesz1Audit.PowerLawObservable`, so
that `Riesz1.gibbsMeasure` of the library is `Riesz1Audit.PowerLawObservable.Riesz1.gibbsMeasure`
here. The proof of the final theorem is the only `sorry`.
-/

@[expose] public section

namespace Riesz1Audit.PowerLawObservable

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

/-- The model exponent with its range proofs. -/
def parametersExponent (P : Parameters) : RieszExponent := ⟨P.val.2, P.property.2.1, P.property.2.2⟩


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

/-- Linear statistic of a real representative. -/
def linearStatistic {N : ℕ+} (f : UnitAddCircle → ℝ) (X : Configuration N) : ℝ :=
  ∑ i : Fin (N : ℕ), f (X.val i : UnitAddCircle)


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Lebesgue-centered statistic. -/
def fluctuation {N : ℕ+} (f : {f : UnitAddCircle → ℝ // Integrable f volume}) (X : Configuration N) : ℝ :=
  linearStatistic f.val X - (N : ℝ) * ∫ x, f.val x


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

/-- The power-observable exponent range. This is the range in Corollary 2 of the paper. -/
@[reducible] def PowerExponent (P : Parameters) := {alpha : ℝ // 0 < alpha ∧ alpha < P.val.2 / 2}


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- A power-observable exponent is a Riesz exponent (see Corollary 2). -/
def powerRieszExponent (P : Parameters) (alpha : PowerExponent P) : RieszExponent :=
  ⟨alpha.val, alpha.property.1, by linarith [alpha.property.2, P.property.2.2]⟩


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Riesz normalization. -/
def rieszConstant (s : RieszExponent) : ℝ :=
  2 ^ (1 - s.val) * Real.sqrt Real.pi * Real.Gamma ((1 - s.val) / 2) / Real.Gamma (s.val / 2)


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Power-law limiting variance. This is the variance in Corollary 2 of the paper. -/
def powerVariance (P : Parameters) (alpha : PowerExponent P) : ℝ :=
  (2 * Real.pi) ^ (-1 + 2 * alpha.val - P.val.2) *
    rieszConstant (powerRieszExponent P alpha) ^ 2 / (P.val.1 * rieszConstant (parametersExponent P)) *
      (HurwitzZeta.hurwitzZeta 0 ((1 + P.val.2 - 2 * alpha.val : ℝ) : ℂ)).re


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

/-- Power-law observable CLT, its L² membership, zero mean and positive finite
limiting variance. This is Corollary 2 of the paper. -/
theorem power_law_observable :
  ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
    let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
    ∀ (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < s / 2),
      let a : PowerExponent P := ⟨alpha, ha, ha1⟩
      ModelWellDefined P ∧
      MemLp (fun x => (rieszRepresentative (powerRieszExponent P a) x : ℂ)) 2 volume ∧
      ∃ hf : Integrable (rieszRepresentative (powerRieszExponent P a)) volume,
      (∫ x : UnitAddCircle, rieszRepresentative (powerRieszExponent P a) x) = 0 ∧
      0 < powerVariance P a ∧
      (∀ N : ℕ+,
        AEMeasurable (fun X : Configuration N => (N : ℝ) ^ (-s / 2) *
          fluctuation ⟨rieszRepresentative (powerRieszExponent P a), hf⟩ X) (gibbsMeasure P N)) ∧
      ConvergesInLaw
        (fun n => (gibbsMeasure P (particleNumber n)).map
          (fun X => (particleNumber n : ℝ) ^ (-s / 2) * fluctuation ⟨rieszRepresentative (powerRieszExponent P a), hf⟩ X))
        (normalLaw (Real.toNNReal (powerVariance P a))) :=
  sorry

end Riesz1

end

end Riesz1Audit.PowerLawObservable

end
