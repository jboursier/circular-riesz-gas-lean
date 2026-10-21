/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Riesz1.ToMathlib.Stein.Solution

/-!
# Uniqueness of bounded solutions of the Stein equation

For `σ > 0`, two differentiable bounded functions `u₁`, `u₂` solving the same equation
`σ² u' - x u = g` coincide. The difference `w` solves the homogeneous equation, so the function
`x ↦ w x exp(-x²/(2σ²))` does not depend on `x`. Boundedness of `w` then forces this value to vanish.
-/

public section

open Real Filter Topology

namespace Riesz1

/-- Bounded differentiable solutions of `σ² u' - x u = g` are unique. -/
theorem stein_solution_unique (σ : ℝ) (hσ : 0 < σ) (g : ℝ → ℝ) (u₁ u₂ : ℝ → ℝ)
    (h₁ : Differentiable ℝ u₁) (h₂ : Differentiable ℝ u₂)
    (hb₁ : ∃ C, ∀ x, |u₁ x| ≤ C) (hb₂ : ∃ C, ∀ x, |u₂ x| ≤ C)
    (e₁ : ∀ x, σ ^ 2 * deriv u₁ x - x * u₁ x = g x)
    (e₂ : ∀ x, σ ^ 2 * deriv u₂ x - x * u₂ x = g x) : u₁ = u₂ := by
  obtain ⟨C₁, hC₁⟩ := hb₁
  obtain ⟨C₂, hC₂⟩ := hb₂
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ → ℝ, w = fun x => u₁ x - u₂ x := ⟨_, rfl⟩
  have hwx : ∀ x, w x = u₁ x - u₂ x := fun x => by rw [hwdef]
  have hwd : Differentiable ℝ w := by
    rw [hwdef]
    exact h₁.sub h₂
  -- The difference solves the homogeneous equation.
  have hode : ∀ x, σ ^ 2 * deriv w x = x * w x := by
    intro x
    have hd : deriv w x = deriv u₁ x - deriv u₂ x := by
      rw [hwdef]
      exact deriv_sub (h₁ x) (h₂ x)
    rw [hd, hwx]
    linear_combination e₁ x - e₂ x
  -- The integrating factor `w x exp(-x²/(2σ²))` has zero derivative.
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ → ℝ, H = fun x => w x * rexp (-(x ^ 2) / (2 * σ ^ 2)) :=
    ⟨_, rfl⟩
  have hHd : ∀ x, HasDerivAt H 0 x := by
    intro x
    have hq : HasDerivAt (fun y : ℝ => -(y ^ 2) / (2 * σ ^ 2)) (-(2 * x) / (2 * σ ^ 2)) x := by
      have := ((hasDerivAt_pow 2 x).neg).div_const (2 * σ ^ 2)
      convert this using 1
      norm_num
    have hprod := (hwd x).hasDerivAt.mul hq.exp
    rw [hHdef]
    convert hprod using 1
    have hσ2 : σ ^ 2 ≠ 0 := by positivity
    have key : deriv w x * rexp (-(x ^ 2) / (2 * σ ^ 2))
        + w x * (rexp (-(x ^ 2) / (2 * σ ^ 2)) * (-(2 * x) / (2 * σ ^ 2)))
        = (rexp (-(x ^ 2) / (2 * σ ^ 2)) / σ ^ 2) * (σ ^ 2 * deriv w x - x * w x) := by
      field_simp
      ring
    rw [key, hode x, sub_self, mul_zero]
  have hHconst : ∀ x, H x = H 0 := fun x =>
    is_const_of_deriv_eq_zero (fun y => (hHd y).differentiableAt)
      (fun y => (hHd y).deriv) x 0
  -- Hence `w x = w 0 exp(x²/(2σ²))`.
  have hwform : ∀ x, w x = w 0 * rexp (x ^ 2 / (2 * σ ^ 2)) := by
    intro x
    have h1 : w x * rexp (-(x ^ 2) / (2 * σ ^ 2)) = w 0 := by
      have := hHconst x
      rw [hHdef] at this
      simpa using this
    have hexp : rexp (-(x ^ 2) / (2 * σ ^ 2)) * rexp (x ^ 2 / (2 * σ ^ 2)) = 1 := by
      rw [← Real.exp_add, show -(x ^ 2) / (2 * σ ^ 2) + x ^ 2 / (2 * σ ^ 2) = 0 by ring,
        Real.exp_zero]
    calc w x = w x * (rexp (-(x ^ 2) / (2 * σ ^ 2)) * rexp (x ^ 2 / (2 * σ ^ 2))) := by
          rw [hexp, mul_one]
      _ = (w x * rexp (-(x ^ 2) / (2 * σ ^ 2))) * rexp (x ^ 2 / (2 * σ ^ 2)) := by ring
      _ = w 0 * rexp (x ^ 2 / (2 * σ ^ 2)) := by rw [h1]
  -- Boundedness of `w` forces `w 0 = 0`.
  have hw_bd : ∀ x, |w x| ≤ C₁ + C₂ := fun x => by
    rw [hwx]
    exact (abs_sub _ _).trans (add_le_add (hC₁ x) (hC₂ x))
  have hc : w 0 = 0 := by
    by_contra hne
    have hcpos : 0 < |w 0| := abs_pos.2 hne
    have hBnn : 0 ≤ C₁ + C₂ := (abs_nonneg _).trans (hw_bd 0)
    obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (C₁ + C₂) / |w 0| := ⟨_, rfl⟩
    have ht : 0 ≤ t := by
      rw [htdef]
      exact div_nonneg hBnn hcpos.le
    obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = σ * √(2 * t) := ⟨_, rfl⟩
    have hx2 : x ^ 2 / (2 * σ ^ 2) = t := by
      rw [hxdef, mul_pow, Real.sq_sqrt (by positivity)]
      field_simp
    have h1 := hw_bd x
    rw [hwform x, hx2, abs_mul, abs_of_nonneg (Real.exp_nonneg _)] at h1
    have h2 : t + 1 ≤ rexp t := by linarith [Real.add_one_le_exp t]
    have h3 : |w 0| * (t + 1) ≤ C₁ + C₂ :=
      (mul_le_mul_of_nonneg_left h2 hcpos.le).trans h1
    have h4 : |w 0| * t = C₁ + C₂ := by
      rw [htdef]
      field_simp
    have h5 : |w 0| * (t + 1) = |w 0| * t + |w 0| := by ring
    linarith
  funext x
  have hx : w x = 0 := by
    rw [hwform x, hc, zero_mul]
  rw [hwx] at hx
  linarith

end Riesz1
