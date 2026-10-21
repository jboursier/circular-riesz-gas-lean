/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Smooth scalar maps detecting individual levels

The maps `ε (arctan ((r-a)/ε) - arctan (-a/ε))` fix zero,
converge to zero, and have derivatives converging to the indicator of `{a}`.
-/

@[expose] public section

noncomputable section

open Filter Topology
open scoped ContDiff

namespace Riesz1.WeightedSobolev

/-- A smooth flattening map centered at the level `a`. -/
def levelMap (a : ℝ) (ε : ℝ) (_hε : 0 < ε) (r : ℝ) : ℝ :=
  ε * (Real.arctan ((r - a) / ε) - Real.arctan (-a / ε))

theorem contDiff_levelMap (a : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (levelMap a ε hε) :=
  contDiff_const.mul (((contDiff_id.sub contDiff_const).div_const ε).arctan.sub contDiff_const)

theorem levelMap_zero (a : ℝ) {ε : ℝ} (hε : 0 < ε) : levelMap a ε hε 0 = 0 := by
  simp [levelMap]

theorem deriv_levelMap (a : ℝ) {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    deriv (levelMap a ε hε) r = ε ^ 2 / (ε ^ 2 + (r - a) ^ 2) := by
  have hd := ((((hasDerivAt_id r).sub_const a).div_const ε).arctan.sub_const
    (Real.arctan (-a / ε))).const_mul ε
  change HasDerivAt (levelMap a ε hε) _ r at hd
  rw [hd.deriv]
  simp only [id_eq]
  have hp : 0 < ε ^ 2 + (r - a) ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hε) (sq_nonneg _)
  field_simp

theorem norm_deriv_levelMap_le (a : ℝ) {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    ‖deriv (levelMap a ε hε) r‖ ≤ 1 := by
  rw [deriv_levelMap a hε, Real.norm_of_nonneg (by positivity)]
  exact div_le_one_of_le₀ (by nlinarith [sq_nonneg (r - a)]) (by positivity)

theorem norm_levelMap_le (a : ℝ) {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    ‖levelMap a ε hε r‖ ≤ ε * Real.pi := by
  rw [levelMap, norm_mul, Real.norm_of_nonneg hε.le]
  apply mul_le_mul_of_nonneg_left _ hε.le
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [Real.arctan_lt_pi_div_two ((r - a) / ε),
    Real.neg_pi_div_two_lt_arctan ((r - a) / ε), Real.arctan_lt_pi_div_two (-a / ε),
    Real.neg_pi_div_two_lt_arctan (-a / ε)]

theorem tendsto_levelMap (a r : ℝ) :
    Tendsto (fun k : ℕ => levelMap a (1 / (k + 1)) (by positivity) r) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun k => norm_levelMap_le a (by positivity) r)
  simpa only [zero_mul] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const Real.pi

theorem tendsto_deriv_levelMap (a r : ℝ) :
    Tendsto (fun k : ℕ => deriv (levelMap a (1 / (k + 1)) (by positivity)) r)
      atTop (𝓝 (if r = a then (1 : ℝ) else 0)) := by
  by_cases hr : r = a
  · subst r
    convert tendsto_const_nhds (x := (1 : ℝ)) using 1
    · funext k
      rw [deriv_levelMap a (by positivity)]
      simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
      exact div_self (by positivity)
    · simp
  · have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
    have hh := ht.div (ht.add_const ((r - a) ^ 2)) (by
      simpa using pow_ne_zero 2 (sub_ne_zero.mpr hr))
    have he (k : ℕ) : deriv (levelMap a (1 / (k + 1)) (by positivity)) r =
        (1 / (k + 1)) ^ 2 / ((1 / (k + 1)) ^ 2 + (r - a) ^ 2) :=
      deriv_levelMap a (by positivity) r
    simpa only [he, Pi.div_def, Pi.add_def, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_add, zero_div, ite_eq_right hr] using hh

end Riesz1.WeightedSobolev

end
