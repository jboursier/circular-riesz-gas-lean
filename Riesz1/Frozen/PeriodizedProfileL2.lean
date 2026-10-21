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
public import Riesz1.Frozen.Circle
public import Riesz1.Frozen.CentralRep
public import Riesz1.Frozen.Arclength
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.ZeroExtension
public import Riesz1.Frozen.PeriodizedProfile
public import Riesz1.Frozen.Scale
public import Riesz1.Frozen.ObservationLength
public import Riesz1.Frozen.ZeroExtensionL2
public import Riesz1.Frozen.LiftL2

/-!
# Periodized profile in L²: `Riesz1.periodizedProfileL2`

Periodization on each observation circle is L², derived from Profile.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Periodization on each observation circle is L², derived from Profile. -/
theorem periodizedProfileL2 (p : Profile) (ell : Scale) :
    MemLp (fun x => (periodizedProfile p (observationLength ell) x : ℂ)) 2
      (arclength (observationLength ell)) := by
  have hL : 1 ≤ (observationLength ell).val := by
    exact (one_le_inv₀ ell.property.1).mpr ell.property.2
  have : Fact (0 < (observationLength ell).val) := ⟨(observationLength ell).property⟩
  have heq (x : Circle (observationLength ell)) :
      periodizedProfile p (observationLength ell) x =
        zeroExtension p (centralRep (observationLength ell) x) := by
    unfold periodizedProfile
    rw [tsum_eq_single (0 : ℤ)]
    · simp only [Int.cast_zero, zero_mul, add_zero]
    · intro n hn
      have hu := (AddCircle.equivIco (observationLength ell).val
        (-(observationLength ell).val / 2) x).property
      have hdist : (1 / 2 : ℝ) ≤ |centralRep (observationLength ell) x +
          (n : ℝ) * (observationLength ell).val| := by
        change -(observationLength ell).val / 2 ≤ centralRep (observationLength ell) x ∧
          centralRep (observationLength ell) x <
            -(observationLength ell).val / 2 + (observationLength ell).val at hu
        rcases lt_or_gt_of_ne hn with hn | hn
        · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 from Int.le_sub_one_of_lt hn)
          have hmul := mul_le_mul_of_nonneg_right hn' (observationLength ell).property.le
          exact le_trans (by linarith [hu.2]) (neg_le_abs _)
        · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n from hn)
          have hmul := mul_le_mul_of_nonneg_right hn' (observationLength ell).property.le
          exact le_trans (by linarith [hu.1]) (le_abs_self _)
      simp only [zeroExtension, ite_eq_right (not_lt.mpr hdist)]
  have h := liftL2 (observationLength ell) _ (zeroExtensionL2 p)
  simpa only [heq] using h

end Riesz1

end
end
