/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HeatKernel.OperatorsSingular
public import Riesz1.Frozen.RieszConstant

/-!
# The constant of the singular formula in terms of the Riesz constant

For `0 < s < 1` and `γ = (1 - s)/2`, the constant `C_γ` of the singular integral formula for
`(-Δ)^γ` (`singularConst γ`) equals
`c_s (1 - s) / (2π tan(πs/2))`, where `c_s` is the Riesz normalization `rieszConstant s`.
This is the identity used to turn the singular formula into the transport formula.

The proof uses the Gamma reflection formula at `s/2` and `(1+s)/2`, and the recurrence
`Γ(1 - γ) = -γ Γ(-γ)`.
-/

public section

open Real

namespace Riesz1

/-- The constant `C_γ` of the singular formula at `γ = (1-s)/2`, in terms of the Riesz
normalization. -/
lemma singularConst_half_eq (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    singularConst ((1 - s) / 2) =
      rieszConstant ⟨s, hs0, hs1⟩ * (1 - s) / (2 * π * Real.tan (π * s / 2)) := by
  set γ : ℝ := (1 - s) / 2 with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hsin : 0 < Real.sin (π * s / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hcos : 0 < Real.cos (π * s / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  -- The Gamma values involved, all positive.
  have hA : 0 < Real.Gamma (s / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hD : 0 < Real.Gamma ((1 - s) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hB : 0 < Real.Gamma (1 - s / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hC : 0 < Real.Gamma ((1 + s) / 2) := Real.Gamma_pos_of_pos (by linarith)
  -- Reflection at `s/2`: `Γ(s/2) Γ(1 - s/2) = π / sin(πs/2)`.
  have r1 : Real.Gamma (s / 2) * Real.Gamma (1 - s / 2) = π / Real.sin (π * s / 2) := by
    rw [Real.Gamma_mul_Gamma_one_sub, show π * (s / 2) = π * s / 2 by ring]
  -- Reflection at `(1+s)/2`: `Γ((1+s)/2) Γ((1-s)/2) = π / cos(πs/2)`.
  have r2 : Real.Gamma ((1 + s) / 2) * Real.Gamma ((1 - s) / 2) = π / Real.cos (π * s / 2) := by
    have h := Real.Gamma_mul_Gamma_one_sub ((1 + s) / 2)
    rw [show 1 - (1 + s) / 2 = (1 - s) / 2 by ring,
      show π * ((1 + s) / 2) = π * s / 2 + π / 2 by ring, Real.sin_add_pi_div_two] at h
    exact h
  -- The modulus `|Γ(-γ)| = Γ(1 - γ)/γ`, from `Γ(1 - γ) = -γ Γ(-γ)` and `Γ(-γ) < 0`.
  have hrec : Real.Gamma (1 - γ) = -γ * Real.Gamma (-γ) := by
    have h := Real.Gamma_add_one (s := -γ) (neg_ne_zero.2 hγ0.ne')
    rw [show -γ + 1 = 1 - γ by ring] at h
    exact h
  have habs : |Real.Gamma (-γ)| = Real.Gamma (1 - γ) / γ := by
    have hG : Real.Gamma (-γ) = -(Real.Gamma (1 - γ) / γ) := by
      rw [hrec]
      field_simp
    rw [hG, abs_neg, abs_of_pos (div_pos (Real.Gamma_pos_of_pos (by linarith)) hγ0)]
  have hΓ1 : Real.Gamma (1 - γ) = Real.Gamma ((1 + s) / 2) := by
    rw [hγ, show 1 - (1 - s) / 2 = (1 + s) / 2 by ring]
  have hγ2 : γ + 1 / 2 = 1 - s / 2 := by rw [hγ]; ring
  have h2γ : (2 : ℝ) ^ (2 * γ) = 2 ^ (1 - s) := by
    rw [hγ, show 2 * ((1 - s) / 2) = 1 - s by ring]
  -- Substitute the two reflections for `Γ(1 - s/2)` and `Γ((1+s)/2)`.
  have hB' : Real.Gamma (1 - s / 2) = π / Real.sin (π * s / 2) / Real.Gamma (s / 2) := by
    rw [eq_div_iff hA.ne', mul_comm, r1]
  have hC' : Real.Gamma ((1 + s) / 2) = π / Real.cos (π * s / 2) / Real.Gamma ((1 - s) / 2) := by
    rw [eq_div_iff hD.ne']
    exact r2
  unfold singularConst rieszConstant
  rw [habs, hΓ1, hγ2, h2γ, Real.tan_eq_sin_div_cos, hB', hC', hγ]
  -- Abstract the square root of `π` and the trigonometric values, so that only the rational
  -- factors `π` are rewritten.
  set P : ℝ := Real.sqrt π with hP
  have hPP : P * P = π := Real.mul_self_sqrt Real.pi_pos.le
  have hPpos : 0 < P := Real.sqrt_pos.2 Real.pi_pos
  set S : ℝ := Real.sin (π * s / 2) with hS
  set Cc : ℝ := Real.cos (π * s / 2) with hCc
  have hS0 : S ≠ 0 := hsin.ne'
  have hCc0 : Cc ≠ 0 := hcos.ne'
  rw [← hPP]
  field_simp

end Riesz1
