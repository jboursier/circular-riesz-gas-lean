/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PeriodicMarkCutoff
public import Riesz1.ToMathlib.CircDist
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Smooth positive radii on a circle

The Euclidean norm of the smoothing scale and a circle chord is smooth,
periodic, and has derivative at most one. Its comparison with the clipped
geodesic distance is uniform in the period and the smoothing scale.
-/

@[expose] public section

open scoped ContDiff

namespace Riesz1

/-- The positive radius obtained by combining a smoothing scale with the
chord distance on a circle. The period and smoothing scale are positive. -/
noncomputable def smoothCircleRadius (L h : {r : ℝ // 0 < r}) (x : ℝ) : ℝ :=
  Real.sqrt (h.val ^ 2 + (L.val / Real.pi * Real.sin (Real.pi * x / L.val)) ^ 2)

theorem smoothCircleRadius_pos (L h : {r : ℝ // 0 < r}) (x : ℝ) :
    0 < smoothCircleRadius L h x := by
  apply Real.sqrt_pos.2
  nlinarith [sq_pos_of_pos h.property,
    sq_nonneg (L.val / Real.pi * Real.sin (Real.pi * x / L.val))]

theorem contDiff_smoothCircleRadius (L h : {r : ℝ // 0 < r}) :
    ContDiff ℝ ∞ (smoothCircleRadius L h) := by
  apply ContDiff.sqrt
  · fun_prop
  · intro x
    nlinarith [sq_pos_of_pos h.property,
      sq_nonneg (L.val / Real.pi * Real.sin (Real.pi * x / L.val))]

theorem periodic_smoothCircleRadius (L h : {r : ℝ // 0 < r}) :
    Function.Periodic (smoothCircleRadius L h) L.val := by
  intro x
  unfold smoothCircleRadius
  rw [show Real.pi * (x + L.val) / L.val = Real.pi * x / L.val + Real.pi by
    field_simp [L.property.ne'], Real.sin_add_pi]
  congr 2
  ring

/-- The chord radius is at least the smoothing scale and the absolute chord. -/
theorem smoothCircleRadius_lower_basic (L h : {r : ℝ // 0 < r}) (x : ℝ) :
    h.val ≤ smoothCircleRadius L h x ∧
      |L.val / Real.pi * Real.sin (Real.pi * x / L.val)| ≤ smoothCircleRadius L h x := by
  constructor
  · exact (Real.le_sqrt h.property.le (by positivity)).mpr (by
      nlinarith [sq_nonneg (L.val / Real.pi * Real.sin (Real.pi * x / L.val))])
  · exact Real.abs_le_sqrt (by nlinarith [sq_nonneg h.val])

/-- The derivative bound does not depend on the circle length or scale. -/
theorem abs_deriv_smoothCircleRadius_le_one (L h : {r : ℝ // 0 < r}) (x : ℝ) :
    |deriv (smoothCircleRadius L h) x| ≤ 1 := by
  let c : ℝ → ℝ := fun y => L.val / Real.pi * Real.sin (Real.pi * y / L.val)
  have hc : HasDerivAt c (Real.cos (Real.pi * x / L.val)) x := by
    convert (((hasDerivAt_id x).const_mul Real.pi).div_const L.val).sin.const_mul
      (L.val / Real.pi) using 1
    · rfl
    · dsimp; field_simp [L.property.ne']
  have hp : 0 < h.val ^ 2 + c x ^ 2 := by
    nlinarith [sq_pos_of_pos h.property, sq_nonneg (c x)]
  have hd := ((hc.pow 2).const_add (h.val ^ 2)).sqrt hp.ne'
  have he : deriv (smoothCircleRadius L h) x =
      c x * Real.cos (Real.pi * x / L.val) / smoothCircleRadius L h x := by
    change deriv (fun y => Real.sqrt (h.val ^ 2 + (c ^ 2) y)) x = _
    rw [hd.deriv]
    dsimp [smoothCircleRadius]
    ring
  rw [he, abs_div, abs_mul, abs_of_pos (smoothCircleRadius_pos L h x)]
  apply (div_le_one (smoothCircleRadius_pos L h x)).mpr
  calc
    _ ≤ |c x| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
    _ ≤ _ := by simpa only [mul_one] using (smoothCircleRadius_lower_basic L h x).2

theorem smoothCircleRadius_add_int_mul (L h : {r : ℝ // 0 < r}) (x : ℝ) (k : ℤ) :
    smoothCircleRadius L h (x + k * L.val) = smoothCircleRadius L h x :=
  (periodic_smoothCircleRadius L h).int_mul k x

/-- In a central cell the chord is comparable to geodesic distance. -/
theorem smoothCircleRadius_lower_central (L h : {r : ℝ // 0 < r})
    (x : ℝ) (hx : |x| ≤ L.val / 2) :
    (2 / Real.pi) * |x| ≤ smoothCircleRadius L h x := by
  have hangle : |Real.pi * x / L.val| ≤ Real.pi / 2 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos L.property]
    apply (div_le_iff₀ L.property).mpr
    nlinarith [mul_le_mul_of_nonneg_left hx Real.pi_pos.le]
  have hs := Real.mul_abs_le_abs_sin hangle
  have hmul := mul_le_mul_of_nonneg_left hs (div_pos L.property Real.pi_pos).le
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos L.property] at hmul
  have he : L.val / Real.pi * (2 / Real.pi * (Real.pi * |x| / L.val)) =
      2 / Real.pi * |x| := by field_simp [L.property.ne']
  rw [he] at hmul
  exact hmul.trans (by
    simpa only [abs_mul, abs_of_pos (div_pos L.property Real.pi_pos)] using
      (smoothCircleRadius_lower_basic L h x).2)

/-- The chord is no longer than the geodesic radius in a central cell. -/
theorem smoothCircleRadius_upper_central (L h : {r : ℝ // 0 < r}) (x : ℝ) :
    smoothCircleRadius L h x ≤ h.val + |x| := by
  have hc : |L.val / Real.pi * Real.sin (Real.pi * x / L.val)| ≤ |x| := by
    rw [abs_mul, abs_of_pos (div_pos L.property Real.pi_pos)]
    have hh := mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := Real.pi * x / L.val))
      (div_pos L.property Real.pi_pos).le
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos L.property] at hh
    have he : L.val / Real.pi * (Real.pi * |x| / L.val) = |x| := by
      field_simp [L.property.ne']
    rwa [he] at hh
  apply (Real.sqrt_le_iff).mpr
  refine ⟨add_nonneg h.property.le (abs_nonneg x), ?_⟩
  have hh := (sq_le_sq₀ (abs_nonneg (L.val / Real.pi * Real.sin (Real.pi * x / L.val)))
    (abs_nonneg x)).mpr hc
  simp only [sq_abs] at hh
  nlinarith [sq_abs x, mul_nonneg h.property.le (abs_nonneg x)]

/-- Uniform comparison with the exact clipped distance, at every real lift. -/
theorem smoothCircleRadius_comparison (L h : {r : ℝ // 0 < r}) (x : ℝ) :
    (2 / Real.pi) * max (circDist L.val x) h.val ≤ smoothCircleRadius L h x ∧
      smoothCircleRadius L h x ≤ 2 * max (circDist L.val x) h.val := by
  let z := cutRep L.val x
  have hx : x = z + (round (x / L.val) : ℤ) * L.val := by dsimp [z, cutRep]; ring
  have he : smoothCircleRadius L h x = smoothCircleRadius L h z := by
    conv_lhs => rw [hx]
    exact smoothCircleRadius_add_int_mul L h z _
  rw [he]
  change (2 / Real.pi) * max |z| h.val ≤ _ ∧ _ ≤ 2 * max |z| h.val
  constructor
  · rw [mul_max_of_nonneg _ _ (by positivity : 0 ≤ 2 / Real.pi)]
    apply max_le
    · exact smoothCircleRadius_lower_central L h z (abs_cutRep_le_half L.property x)
    · exact (mul_le_of_le_one_left h.property.le
        ((div_le_one Real.pi_pos).mpr Real.two_le_pi)).trans
          (smoothCircleRadius_lower_basic L h z).1
  · exact (smoothCircleRadius_upper_central L h z).trans (by
      linarith [le_max_left |z| h.val, le_max_right |z| h.val])

end Riesz1
