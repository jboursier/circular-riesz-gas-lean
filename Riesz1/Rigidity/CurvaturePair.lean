/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ForcingPotential
public import Riesz1.HelfferSjostrand.RieszAdmissiblePairs
public import Riesz1.ToMathlib.HurwitzKernel.CurvatureTerms
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Uniform curvature of a convexified pair

The scalar curvature estimate. The constant depends only on the Riesz exponent.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Riesz1

/-- The constant `a_s = min (2s(s+1)2^(-s-2)) 4`. -/
def rigidityCurvatureConstant (s : ℝ) : ℝ :=
  min (2 * s * (s + 1) * (2 : ℝ) ^ (-s - 2)) 4

theorem rigidityCurvatureConstant_pos (s : RieszExponent) :
    0 < rigidityCurvatureConstant s.val := by
  unfold rigidityCurvatureConstant
  exact lt_min (by have := s.2.1; positivity) (by norm_num)

/-- One summand, before the factor two, of `H_I`. -/
def curvaturePairPotential (N : ℕ+) (s : RieszExponent) (θ : ℝ → ℝ) (R r : ℝ) : ℝ :=
  (N : ℝ) ^ (-s.val) * hurwitzKernel s.val r + θ ((N : ℝ) / R * r)

theorem curvaturePairPotential_smooth (N : ℕ+) (s : RieszExponent)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (R : ℝ) :
    ContDiffOn ℝ ∞ (curvaturePairPotential N s θ R) (Ioo 0 1) :=
  (contDiffOn_const.mul (contDiffOn_hurwitzKernel_unit s.val s.2.1 s.2.2)).add
    ((hθ.1.comp (contDiff_const.mul contDiff_id)).contDiffOn)

theorem curvaturePairPotential_deriv2 (N : ℕ+) (s : RieszExponent)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (R : ℝ) {r : ℝ} (hr : r ∈ Ioo 0 1) :
    deriv (deriv (curvaturePairPotential N s θ R)) r =
      (N : ℝ) ^ (-s.val) * deriv (deriv (hurwitzKernel s.val)) r +
        ((N : ℝ) / R) ^ 2 * deriv (deriv θ) ((N : ℝ) / R * r) := by
  let c : ℝ := (N : ℝ) / R
  have hd (x : ℝ) : HasDerivAt (fun x => θ (c * x))
      (c * deriv θ (c * x)) x := by
    simpa only [Function.comp_def, one_mul, mul_comm] using
      (hθ.1.differentiable (by simp) (c * x)).hasDerivAt.comp x
        ((hasDerivAt_id x).const_mul c)
  have hdd (x : ℝ) : HasDerivAt (fun x => c * deriv θ (c * x))
      (c ^ 2 * deriv (deriv θ) (c * x)) x := by
    have hh : Differentiable ℝ (deriv θ) :=
      (hθ.1.of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)).differentiable_deriv_two
    convert ((hh (c * x)).hasDerivAt.comp x
      ((hasDerivAt_id x).const_mul c)).const_mul c using 1
    · rfl
    · ring
  have hg := contDiffOn_hurwitzKernel_unit s.val s.2.1 s.2.2
  have he : deriv (curvaturePairPotential N s θ R) =ᶠ[𝓝 r]
      fun x => (N : ℝ) ^ (-s.val) * deriv (hurwitzKernel s.val) x + c * deriv θ (c * x) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with x hx
    exact (((hg.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt
      (by simp)).hasDerivAt.const_mul _ |>.add (hd x)).deriv
  rw [he.deriv_eq]
  have hg' := hg.deriv_of_isOpen isOpen_Ioo (show (1 : ℕ∞ω) + 1 ≤ ∞ by simp)
  exact (((hg'.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt
    (by norm_num)).hasDerivAt.const_mul _ |>.add (hdd r)).deriv

/-- Small separations are controlled by the singular kernel. Large separations
are controlled by the region where `θ'' = 2`. -/
theorem curvaturePairPotential_lower (N : ℕ+) (s : RieszExponent)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 1 ≤ R)
    {r : ℝ} (hr : r ∈ Ioo 0 1) :
    rigidityCurvatureConstant s.val * (N : ℝ) ^ 2 * R ^ (-s.val - 2) ≤
      2 * deriv (deriv (curvaturePairPotential N s θ R)) r := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hk0 := hurwitzKernel_curvature_nonneg s.val s.2.1 s.2.2 hr
  have hθ0 := (hθ.2.2.2.1 ((N : ℝ) / R * r)
    (mul_nonneg (div_nonneg hN.le hR0.le) hr.1.le)).1
  rw [curvaturePairPotential_deriv2 N s hθ R hr]
  by_cases hsmall : (N : ℝ) * r ≤ 2 * R
  · have hle : r ≤ 2 * R / N := (le_div_iff₀ hN).2 (by nlinarith)
    have hp := Real.rpow_le_rpow_of_nonpos hr.1 hle (show -s.val - 2 ≤ 0 by linarith [s.2.1])
    have hk := hurwitzKernel_curvature_ge_term s.val s.2.1 s.2.2 hr 0
    simp only [Int.cast_zero, sub_zero, abs_of_pos hr.1] at hk
    have hscale : (N : ℝ) ^ (-s.val) * (s.val * (s.val + 1)) *
        (2 * R / N) ^ (-s.val - 2) =
        s.val * (s.val + 1) * (2 : ℝ) ^ (-s.val - 2) *
          (N : ℝ) ^ 2 * R ^ (-s.val - 2) := by
      have hratio : (N : ℝ) ^ (-s.val) / (N : ℝ) ^ (-s.val - 2) = (N : ℝ) ^ 2 := by
        rw [← Real.rpow_sub hN, show -s.val - (-s.val - 2) = (2 : ℝ) by ring,
          Real.rpow_two]
      rw [Real.div_rpow (by positivity) hN.le, Real.mul_rpow (by norm_num) hR0.le]
      calc _ = s.val * (s.val + 1) * (2 : ℝ) ^ (-s.val - 2) *
            ((N : ℝ) ^ (-s.val) / (N : ℝ) ^ (-s.val - 2)) * R ^ (-s.val - 2) := by ring
        _ = _ := by rw [hratio]
    have hmul := mul_le_mul_of_nonneg_left hp
      (show 0 ≤ (N : ℝ) ^ (-s.val) * (s.val * (s.val + 1)) by have := s.2.1; positivity)
    rw [hscale] at hmul
    have hk' := mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hN.le (-s.val))
    have hc := mul_le_mul_of_nonneg_right
      (min_le_left (2 * s.val * (s.val + 1) * (2 : ℝ) ^ (-s.val - 2)) 4)
      (show 0 ≤ (N : ℝ) ^ 2 * R ^ (-s.val - 2) by positivity)
    dsimp [rigidityCurvatureConstant]
    nlinarith [mul_nonneg (sq_nonneg ((N : ℝ) / R)) hθ0]
  · have harg : 2 ≤ (N : ℝ) / R * r := by
      have : 2 ≤ (N : ℝ) * r / R := (le_div_iff₀ hR0).2 (not_le.mp hsmall).le
      convert this using 1
      ring
    rw [hθ.2.2.2.2 _ harg]
    have hp : R ^ (-s.val - 2) ≤ (R ^ 2)⁻¹ := by
      calc R ^ (-s.val - 2) ≤ R ^ (-(2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hR (by linarith [s.2.1])
        _ = (R ^ 2)⁻¹ := by rw [Real.rpow_neg hR0.le, Real.rpow_two]
    have hc : rigidityCurvatureConstant s.val ≤ 4 := min_le_right _ _
    have hc0 := (rigidityCurvatureConstant_pos s).le
    have hprod := mul_le_mul hc hp (Real.rpow_nonneg hR0.le _) (by norm_num : (0 : ℝ) ≤ 4)
    have hprod' := mul_le_mul_of_nonneg_left hprod (sq_nonneg (N : ℝ))
    have hdiv : ((N : ℝ) / R) ^ 2 = (N : ℝ) ^ 2 * (R ^ 2)⁻¹ := by
      rw [div_pow, div_eq_mul_inv]
    rw [hdiv]
    nlinarith [mul_nonneg (Real.rpow_nonneg hN.le (-s.val)) hk0]

end Riesz1

end
