/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.RieszConstant

/-!
# Normalization of the Mellin formula for the Riesz kernel

The Gamma expression obtained from the theta Mellin integral agrees with
the Riesz normalization `rieszConstant` at every positive frequency magnitude.
-/

public section

namespace Riesz1

/-- Scalar conversion from the Gaussian Mellin normalization to `rieszConstant`. -/
theorem rieszConstant_gaussian_normalization (s : RieszExponent) (q : ℝ) (hq : 0 < q) :
    (1 / (Real.pi * q ^ 2)) ^ ((1 - s.val) / 2) * Real.Gamma ((1 - s.val) / 2) /
        (Real.pi ^ (-s.val / 2) * Real.Gamma (s.val / 2)) =
      rieszConstant s * (2 * Real.pi * q) ^ (s.val - 1) := by
  have he : (1 / (Real.pi * q ^ 2)) ^ ((1 - s.val) / 2) /
      Real.pi ^ (-s.val / 2) =
      2 ^ (1 - s.val) * Real.sqrt Real.pi * (2 * Real.pi * q) ^ (s.val - 1) := by
    rw [Real.rpow_def_of_pos (by positivity : 0 < 1 / (Real.pi * q ^ 2)),
      Real.rpow_def_of_pos Real.pi_pos, ← Real.exp_sub,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.sqrt_eq_rpow,
      Real.rpow_def_of_pos Real.pi_pos, Real.rpow_def_of_pos (by positivity : 0 < 2 * Real.pi * q),
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [Real.log_div one_ne_zero (by positivity : Real.pi * q ^ 2 ≠ 0), Real.log_one,
      Real.log_mul Real.pi_ne_zero (pow_ne_zero _ hq.ne'), Real.log_pow,
      Real.log_mul (by positivity : 2 * Real.pi ≠ 0) hq.ne',
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
    ring
  calc
    _ = ((1 / (Real.pi * q ^ 2)) ^ ((1 - s.val) / 2) / Real.pi ^ (-s.val / 2)) *
        (Real.Gamma ((1 - s.val) / 2) / Real.Gamma (s.val / 2)) := by ring
    _ = _ := by rw [he]; unfold rieszConstant; ring

/-- Complex form of the normalization used by the Mellin transform. -/
theorem rieszConstant_gaussian_normalization_complex (s : RieszExponent)
    (q : ℝ) (hq : 0 < q) :
    (1 / ((Real.pi * q ^ 2 : ℝ) : ℂ)) ^ ((1 - (s.val : ℂ)) / 2) *
        Complex.Gamma ((1 - (s.val : ℂ)) / 2) / Complex.Gammaℝ (s.val : ℂ) =
      ((rieszConstant s * (2 * Real.pi * q) ^ (s.val - 1) : ℝ) : ℂ) := by
  have harg : (1 - (s.val : ℂ)) / 2 = (((1 - s.val) / 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hg : Complex.Gammaℝ (s.val : ℂ) =
      ((Real.pi ^ (-s.val / 2) * Real.Gamma (s.val / 2) : ℝ) : ℂ) := by
    rw [Complex.Gammaℝ_def]
    have he : -(s.val : ℂ) / 2 = (((-s.val / 2 : ℝ)) : ℂ) := by push_cast; rfl
    have ha : (s.val : ℂ) / 2 = ((s.val / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, ha, Complex.Gamma_ofReal, ← Complex.ofReal_cpow Real.pi_pos.le]
    push_cast
    rfl
  rw [harg, hg, Complex.Gamma_ofReal,
    show (1 / ((Real.pi * q ^ 2 : ℝ) : ℂ)) = ((1 / (Real.pi * q ^ 2) : ℝ) : ℂ) by
      push_cast; rfl,
    ← Complex.ofReal_cpow (by positivity : 0 ≤ 1 / (Real.pi * q ^ 2)),
    ← Complex.ofReal_mul, ← Complex.ofReal_div]
  exact congrArg Complex.ofReal (rieszConstant_gaussian_normalization s q hq)

end Riesz1
