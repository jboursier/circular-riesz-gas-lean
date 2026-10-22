/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.Fourier
public import Riesz1.Frozen.RieszConstant
public import Riesz1.Kernel.FundamentalHeatIntegral

/-!
# Fourier coefficients of the Riesz kernel

The periodic Riesz kernel agrees with the heat integral at every point of the circle except the
origin. The heat integral has the Fourier coefficients of the fundamental solution, which the
Fubini exchange with the heat kernel gives, so the kernel has the same coefficients.
-/

public section

open MeasureTheory Complex Set

namespace Riesz1

/-- Every nonzero point of the circle is the image of a point of `(0, 1)`. -/
lemma exists_mem_Ioo_coe_eq {x : UnitAddCircle} (hx : x ≠ 0) :
    ∃ y : ℝ, 0 < y ∧ y < 1 ∧ (y : UnitAddCircle) = x := by
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    have hfl : ((⌊a⌋ : ℝ) : UnitAddCircle) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨⌊a⌋, by simp⟩
    have hsub : ((Int.fract a : ℝ) : UnitAddCircle) = (a : UnitAddCircle) := by
      rw [Int.fract, AddCircle.coe_sub, hfl, sub_zero]
    refine ⟨Int.fract a, ?_, Int.fract_lt_one a, hsub⟩
    rcases (Int.fract_nonneg a).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hx
      rw [← hsub, ← h, AddCircle.coe_zero]

/-- Fourier coefficients of the periodic Riesz kernel, with probability Haar
measure on `AddCircle 1` (Lemma 2.1). -/
theorem fourierCoeff_rieszRepresentative (s : RieszExponent) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) k =
      if k = 0 then 0
      else ((rieszConstant s * (2 * Real.pi * |(k : ℝ)|) ^ (s.val - 1) : ℝ) : ℂ) := by
  have hnull : volume ({0} : Set UnitAddCircle) = 0 := by
    rw [← Metric.closedBall_zero (x := (0 : UnitAddCircle)), AddCircle.volume_closedBall]
    norm_num
  have hne : ∀ᵐ x : UnitAddCircle, x ≠ 0 := by
    simp only [ae_iff, not_not]
    convert hnull using 2
    ext x
    simp
  have hae : (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) =ᵐ[AddCircle.haarAddCircle]
      (fun x : UnitAddCircle => (heatIntegral s x : ℂ)) := by
    rw [show (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume by
      simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm]
    filter_upwards [hne] with x hx
    obtain ⟨y, hy0, hy1, rfl⟩ := exists_mem_Ioo_coe_eq hx
    rw [heatIntegral_eq_rieszRepresentative s hy0 hy1]
  rw [congrFun (fourierCoeff_congr_ae hae) k, fourierCoeff_heatIntegral s k]

end Riesz1

end
