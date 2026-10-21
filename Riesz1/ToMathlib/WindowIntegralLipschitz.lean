/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

/-!
# Lipschitz bounds for convolution on a fixed window

A derivative bound for a kernel gives a Lipschitz bound for its convolution
against an integrable function on a compact interval. No regularity of the density
beyond integrability is required.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- A continuous kernel on a compact window can be multiplied by an integrable
density there. -/
theorem integrableOn_window_mul {ρ : ℝ} {ζ H : ℝ → ℝ}
    (hζ : IntegrableOn ζ (Ioc (-ρ) ρ))
    (hH : ContinuousOn H (Icc (-ρ) ρ)) :
    IntegrableOn (fun y => ζ y * H y) (Ioc (-ρ) ρ) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hH
  exact hζ.mul_bdd ((hH.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        exact hM y (Ioc_subset_Icc_self hy))

/-- Integrating against a fixed density preserves a local Lipschitz bound, with
the integral norm of the density as the factor. -/
theorem lipschitzOnWith_windowIntegral {ρ σ θ C : ℝ} {ζ H : ℝ → ℝ}
    (hC : 0 ≤ C) (hσθ : σ + ρ < θ)
    (hζ : IntegrableOn ζ (Ioc (-ρ) ρ))
    (hH : ∀ x : ℝ, |x| < θ → DifferentiableAt ℝ H x ∧ |deriv H x| ≤ C) :
    LipschitzOnWith ⟨C * (∫ y in Ioc (-ρ) ρ, |ζ y|),
      mul_nonneg hC (integral_nonneg fun _ => abs_nonneg _)⟩
      (fun x : ℝ => ∫ y in Ioc (-ρ) ρ, ζ y * H (x - y)) (Ioo (-σ) σ) := by
  have hwin (x y : ℝ) (hx : x ∈ Ioo (-σ) σ) (hy : y ∈ Icc (-ρ) ρ) :
      |x - y| < θ := by
    have hxa : |x| < σ := abs_lt.mpr hx
    have hya : |y| ≤ ρ := abs_le.mpr hy
    exact (abs_sub x y).trans_lt (by linarith)
  have hcont (x : ℝ) (hx : x ∈ Ioo (-σ) σ) :
      ContinuousOn (fun y => H (x - y)) (Icc (-ρ) ρ) := by
    intro y hy
    exact ((hH _ (hwin x y hx hy)).1.continuousAt.comp
      (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
  have hint (x : ℝ) (hx : x ∈ Ioo (-σ) σ) :
      IntegrableOn (fun y => ζ y * H (x - y)) (Ioc (-ρ) ρ) :=
    integrableOn_window_mul hζ (hcont x hx)
  have hLip : LipschitzOnWith ⟨C, hC⟩ H (Ioo (-θ) θ) :=
    (convex_Ioo (-θ) θ).lipschitzOnWith_of_nnnorm_deriv_le
      (fun x hx => (hH x (abs_lt.mpr hx)).1)
      (fun x hx => by exact_mod_cast (hH x (abs_lt.mpr hx)).2)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx z hz
  rw [Real.dist_eq, Real.dist_eq, ← integral_sub (hint x hx) (hint z hz)]
  have hbound : ∀ᵐ y ∂volume.restrict (Ioc (-ρ) ρ),
      ‖ζ y * H (x - y) - ζ y * H (z - y)‖ ≤
        (C * |x - z|) * |ζ y| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hh := hLip.dist_le_mul (x - y)
      (abs_lt.mp (hwin x y hx (Ioc_subset_Icc_self hy)))
      (z - y) (abs_lt.mp (hwin z y hz (Ioc_subset_Icc_self hy)))
    simp only [Real.dist_eq, sub_sub_sub_cancel_right] at hh
    change |H (x - y) - H (z - y)| ≤ C * |x - z| at hh
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (ζ y))]
  have hh := norm_integral_le_of_norm_le (hζ.abs.const_mul (C * |x - z|)) hbound
  rw [Real.norm_eq_abs, integral_const_mul] at hh
  change _ ≤ (C * (∫ y in Ioc (-ρ) ρ, |ζ y|)) * |x - z|
  convert hh using 1; ring

end Riesz1
