/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityMembership

/-!
# Finite variances and their limit from admissibility

The circle-membership premise of the extension and variance helpers is
discharged from the admissibility predicate `Admissible`. For a compact profile the line
seminorm and every scaled circle variance are finite, with the scale-comparison rate
and the right-hand limit.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Riesz1

/-- Every relevant circle variance of an admissible profile is finite. -/
theorem admissible_circleVariance_finite (P : Parameters) (p : Profile)
    (ell : Scales) (α : ℝ) (d : TestData) (h : Admissible P p ell α d) (N : ℕ+) :
    circleVariance P p (ell N) < ⊤ := by
  obtain ⟨hf, hfin⟩ := admissible_circleSobolev P p ell α d h N
  unfold circleVariance
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- A compact admissible profile has finite line seminorm and finite variance at every
scale, with the comparison rate. No membership hypothesis is retained. -/
theorem admissible_compact_variance (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (ell : Scales) (α : ℝ) (d : TestData) (h : Admissible P p ell α d)
    (f0 : Lp ℂ 2 (volume : Measure ℝ)) (hf0 : RepresentsZeroExtension p f0) :
    LineSobolev ((1 - P.val.2) / 2) f0 ∧
      lineVariance P f0 < ⊤ ∧ ∃ C : ℝ, 0 < C ∧ ∀ a : Scale,
        CircleSobolev ((1 - P.val.2) / 2) (fun x => (testAtScale p a x : ℂ)) ∧
          circleVariance P p a < ⊤ ∧
          |(circleVariance P p a).toReal - (lineVariance P f0).toReal| ≤
            C * a.val ^ (2 - P.val.2) := by
  exact Internal.compact_variance_of_circle_membership P p hp (ell 1)
    (admissible_circleSobolev P p ell α d h 1) f0 hf0

/-- The compact admissible variances converge along every filter of scales tending
to zero. This includes the right-hand limit. -/
theorem admissible_compact_variance_tendsto (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (ell : Scales) (α : ℝ) (d : TestData)
    (h : Admissible P p ell α d)
    (f0 : Lp ℂ 2 (volume : Measure ℝ)) (hf0 : RepresentsZeroExtension p f0)
    {ι : Type*} {l : Filter ι} (a : ι → Scale)
    (ha : Tendsto (fun i => (a i).val) l (𝓝 0)) :
    Tendsto (fun i => (circleVariance P p (a i)).toReal) l (𝓝 (lineVariance P f0).toReal) := by
  exact Internal.compact_variance_tendsto_of_circle_membership P p hp (ell 1)
    (admissible_circleSobolev P p ell α d h 1) f0 hf0 a ha

end Riesz1
