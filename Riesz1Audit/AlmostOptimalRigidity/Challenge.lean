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
# Theorem 1 (near-optimal rigidity): the statement

Mathlib-only statement of Theorem 1 of J. Boursier, *Optimal local laws and central limit theorem
for the circular Riesz gas* (arXiv:2112.05881).

Let `β > 0` and `0 < s < 1`. Then the model is well defined: for every `N ≥ 1` the partition
function `Z_{N,β}` is positive and finite, and the Gibbs measure `P_{N,β}` is a probability measure.
Moreover there is `ε₀ > 0` such that for every `ε ∈ (0, ε₀)` there are `c > 0` and `C > 0` with the
following two properties, for every `N ≥ 1`.

* *Gaps.* For every label `i` and every `k` with `1 ≤ k ≤ ⌊N/2⌋`,
  `P_{N,β}(|N(x_{i+k} - x_i) - k| ≥ k^{s/2+ε}) ≤ C exp(-c k^{ε/(4(s+2))})`.
* *Discrepancy.* For every point `x` of the circle and every `ℓ ∈ (0, 1/4]`, the number `n` of
  particles in the open arc of center `x` and half-length `ℓ` satisfies
  `P_{N,β}(|n - 2Nℓ| ≥ (Nℓ)^{s/2+ε}) ≤ C exp(-c (Nℓ)^{ε/(4(s+2))})`.

## How the objects are specified

A configuration is its ordered real lift `x_0 < ... < x_{N-1} < x_0 + 1` with `0 ≤ x_0 < 1`
(`Configuration`), and `x_{i+N} = x_i + 1` for every integer label (`cyclicLift`). The paper's label
1 is label 0 here. The kernel is `g(x) = 2 Re ζ_even(x, s)`, written with Mathlib's even Hurwitz
zeta function (`rieszRepresentative`), the energy is `N^{-s} Σ_{i ≠ j} g(x_i - x_j)` (`energy`) and
the Gibbs measure is the normalized Boltzmann weight on the set of lifts (`gibbsMeasure`). The
constants `c` and `C` are chosen before `N`, the label, the gap index and the arc.

The definitions below are copied without change, in dependency order, from the files
`Riesz1/Frozen/*.lean` of the library, inside the namespace `Riesz1Audit.AlmostOptimalRigidity`, so
that `Riesz1.gibbsMeasure` of the library is `Riesz1Audit.AlmostOptimalRigidity.Riesz1.gibbsMeasure`
here. The proof of the final theorem is the only `sorry`.
-/

@[expose] public section

namespace Riesz1Audit.AlmostOptimalRigidity

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

/-- Open arc count. -/
def arcCount {N : ℕ+} (center : UnitAddCircle) (a : ℝ) (X : Configuration N) : ℝ :=
  ∑ i : Fin (N : ℕ), if dist (X.val i : UnitAddCircle) center < a then 1 else 0


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

/-- Near-optimal rigidity: both gaps and arbitrary-center interval discrepancy,
with the same c,C chosen before N. This is Theorem 1 of the paper. -/
theorem almost_optimal_rigidity :
  ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
    let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
    ModelWellDefined P ∧
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ eps : ℝ, 0 < eps → eps < eps0 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ N : ℕ+,
          (∀ (i : Fin (N : ℕ)) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
            gibbsMeasure P N {X |
              |(N : ℝ) * (cyclicLift X ((i.val : ℤ) + k) - cyclicLift X i.val) - k| ≥
                (k : ℝ) ^ (s / 2 + eps)} ≤
              ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (eps / (4 * (s + 2)))))) ∧
          (∀ (x : UnitAddCircle) (ell : ℝ), 0 < ell → ell ≤ 1 / 4 →
            gibbsMeasure P N {X |
              |arcCount x ell X - 2 * (N : ℝ) * ell| ≥
                ((N : ℝ) * ell) ^ (s / 2 + eps)} ≤
              ENNReal.ofReal (C * Real.exp (-c * ((N : ℝ) * ell) ^ (eps / (4 * (s + 2)))))) :=
  sorry

end Riesz1

end

end Riesz1Audit.AlmostOptimalRigidity

end
