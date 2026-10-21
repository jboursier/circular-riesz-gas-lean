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
# Corollary 1 (CLT for interval counts and gaps): the statement

Mathlib-only statement of Corollary 1 of J. Boursier, *Optimal local laws and central limit theorem
for the circular Riesz gas* (arXiv:2112.05881).

Let `β > 0` and `0 < s < 1`, and let `σ² = cot(πs/2)/(2βπs)` (`countVariance`). Let `V_s` be the
periodic function `V_s(t) = ζ(-s, t) + ζ(-s, 1-t) - 2ζ(-s)` (`periodicZeta`, written with Mathlib's
even Hurwitz zeta function). Then the model is well defined, `σ² > 0`, and:

* *Interval counts.* For every `a ∈ (0, 1/2)` and every scale sequence `(ℓ_N)` with `Nℓ_N → ∞`, the
  number `n_N` of particles in the open arc `(-aℓ_N, aℓ_N)` satisfies
  `(n_N - 2aNℓ_N) / √(N^s V_s(2aℓ_N)) → N(0, σ²)` in law.
* *Gaps.* For every sequence `(k_N)_{N ≥ 2}` with `1 ≤ k_N ≤ ⌊N/2⌋` and `k_N → ∞`,
  `(N(x_{1+k_N} - x_1) - k_N) / √(N^s V_s(k_N/N)) → N(0, σ²)` in law.

The statement also asserts that the square roots in the denominators are positive and that the
normalized variables are almost everywhere measurable.

## How the objects are specified

The gap is based at the paper's label 1, which is label 0 here (`normalizedGap`). Convergence in law
is convergence of the integrals of every bounded continuous function (`ConvergesInLaw`). The count
sequence is indexed by `N = n + 1` and the gap sequence by `N = n + 2` (`particleNumber`). `N(0, v)`
is Mathlib's Gaussian measure (`normalLaw`).

The definitions below are copied without change, in dependency order, from the files
`Riesz1/Frozen/*.lean` of the library, inside the namespace
`Riesz1Audit.FluctuationsGapsDiscrepancy`, so that `Riesz1.gibbsMeasure` of the library is
`Riesz1Audit.FluctuationsGapsDiscrepancy.Riesz1.gibbsMeasure` here. The proof of the final theorem
is the only `sorry`.
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

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Both count and gap CLTs. Scales need no limit. The gap range starts at N=2.
All denominators in the asserted ranges are positive conclusions.
This is Corollary 1 of the paper. -/
theorem fluctuations_gaps_discrepancy :
  ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
    let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
    ModelWellDefined P ∧ 0 < countVariance P ∧
    (∀ (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2), ∀ ell : Scales, Mesoscopic ell →
      (∀ N : ℕ+, 0 < Real.sqrt ((N : ℝ) ^ s *
        periodicZeta (parametersExponent P) ((2 * a * (ell N).val : ℝ) : UnitAddCircle)) ∧
        AEMeasurable (normalizedCount P a ha ha1 ell N) (gibbsMeasure P N)) ∧
      ConvergesInLaw
        (fun n => (gibbsMeasure P (particleNumber n)).map (normalizedCount P a ha ha1 ell (particleNumber n)))
        (normalLaw (Real.toNNReal (countVariance P)))) ∧
    (∀ k : ℕ+ → ℕ,
      ∀ hk : (∀ N : ℕ+, 2 ≤ (N : ℕ) → 1 ≤ k N ∧ k N ≤ (N : ℕ) / 2),
      Tendsto (fun n => k (particleNumber n)) atTop atTop →
      (∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)),
        0 < Real.sqrt ((N : ℝ) ^ s * periodicZeta (parametersExponent P) (((k N : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)) ∧
        AEMeasurable (normalizedGap P N (k N) (hk N hN)) (gibbsMeasure P N)) ∧
      ConvergesInLaw
        (fun n => (gibbsMeasure P (particleNumber (n + 1))).map
          (normalizedGap P (particleNumber (n + 1)) (k (particleNumber (n + 1))) (hk (particleNumber (n + 1)) (Nat.le_add_left 2 n))))
        (normalLaw (Real.toNNReal (countVariance P)))) :=
  sorry

end Riesz1

end

end Riesz1Audit.FluctuationsGapsDiscrepancy

end
