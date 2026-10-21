/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.GapLawMarginal
public import Riesz1.ToMathlib.LogConcave.LocalAbsoluteContinuity

/-!
# The single-gap potential and local absolute continuity

The single-gap potential `gapPotential` is defined on its actual open-interval carrier,
using the canonical continuous density. This file also proves the
local absolute continuity part of Lemma 4.5.
Convexity of the potential after removing the singularity and the
endpoint majorant are separate assertions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The single-gap potential, for `N = n + 2`.
Its carrier contains exactly the points where the density is positive. -/
def gapPotential (P : Parameters) (n : ℕ) (y : Ioo (0 : ℝ) (n + 2 : ℝ)) : ℝ :=
  -Real.log (gapMarginalProbabilityDensity P n y) - 2 * P.val.1 * (y : ℝ) ^ (-P.val.2)

/-- The exponential representation used in Lemma 4.5. -/
theorem gapMarginalProbabilityDensity_eq_exp_potential (P : Parameters) (n : ℕ)
    (y : Ioo (0 : ℝ) (n + 2 : ℝ)) :
    gapMarginalProbabilityDensity P n y =
      Real.exp (-2 * P.val.1 * (y : ℝ) ^ (-P.val.2) - gapPotential P n y) := by
  unfold gapPotential
  rw [show -2 * P.val.1 * (y : ℝ) ^ (-P.val.2) -
      (-Real.log (gapMarginalProbabilityDensity P n y) -
        2 * P.val.1 * (y : ℝ) ^ (-P.val.2)) =
      Real.log (gapMarginalProbabilityDensity P n y) by ring]
  exact (Real.exp_log (gapMarginalProbabilityDensity_pos P n y.property)).symm

theorem continuous_gapPotential (P : Parameters) (n : ℕ) : Continuous (gapPotential P n) := by
  have hf : Continuous (fun y : Ioo (0 : ℝ) (n + 2 : ℝ) => gapMarginalProbabilityDensity P n y) :=
    (continuousOn_gapMarginalProbabilityDensity P n).domRestrict
  have hl : Continuous (fun y : Ioo (0 : ℝ) (n + 2 : ℝ) =>
      Real.log (gapMarginalProbabilityDensity P n y)) :=
    hf.log (fun y => (gapMarginalProbabilityDensity_pos P n y.property).ne')
  have hp : Continuous (fun y : Ioo (0 : ℝ) (n + 2 : ℝ) => (y : ℝ) ^ (-P.val.2)) :=
    continuous_subtype_val.rpow_const (fun y => Or.inl y.property.1.ne')
  exact hl.neg.sub (hp.const_mul _)

/-- Local absolute continuity on every compact subinterval, as required in
Lemma 4.5. -/
theorem gapMarginalProbabilityDensity_absolutelyContinuous (hPL : External.PrekopaLeindler)
    (P : Parameters) (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < n + 2) :
    AbsolutelyContinuousOnInterval (gapMarginalProbabilityDensity P n) a b := by
  apply absolutelyContinuousOnInterval_of_concaveOn_log isOpen_Ioo
    (fun y hy => gapMarginalProbabilityDensity_pos P n hy)
    (concaveOn_log_gapMarginalProbabilityDensity hPL P n)
  rw [uIcc_of_le hab]
  exact fun _ hy => ⟨ha.trans_le hy.1, hy.2.trans_lt hb⟩

/-- The gap definition gives exactly the one-particle convention. -/
theorem gap_one_particle (X : Configuration (1 : ℕ+)) (j : ℤ) : gap X j = 1 := by
  have h := blockLength_N X j
  simpa only [blockLength, gap, PNat.val_ofNat, Nat.cast_one] using h

/-- Every inverse moment is one in the one-particle case of
Lemma 4.5. -/
theorem gap_inverse_moment_one_particle (P : Parameters) (j : ℤ) (p : ℝ) :
    (∫⁻ X : Configuration (1 : ℕ+), ENNReal.ofReal (gap X j ^ (-p))
      ∂gibbsMeasure P 1) = 1 := by
  have := (modelWellDefined P 1).2.2
  simp only [gap_one_particle, Real.one_rpow, ENNReal.ofReal_one, lintegral_const,
    measure_univ, mul_one]

end Riesz1

end
end
