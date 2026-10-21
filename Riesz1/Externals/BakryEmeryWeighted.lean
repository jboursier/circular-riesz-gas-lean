/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Externals.BakryEmeryComparison
public import Riesz1.ToMathlib.PrekopaWeightedExp

/-!
# Weighted integral comparisons for the Bakry–Émery proof

These prove the varying-weight comparison needed for the Bakry–Émery criterion.
The argument follows Bobkov–Ledoux, *From Brunn–Minkowski
to Brascamp–Lieb and to logarithmic Sobolev inequalities* (2000), Proposition 3.1,
https://www.math.univ-toulouse.fr/~ledoux/BrunnMinkowski.pdf . No external proof
hypothesis is needed. No external code is copied in this module.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace Riesz1.Externals

variable {d : ℕ} {w : ℝ} {V : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The normalized weighted comparison under a uniformly convex density. -/
theorem bakry_emery_weighted_comparison (hd : 0 < d) (hw : 0 < w)
    (hV : ContDiff ℝ ∞ V)
    (hH : ∀ x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {A B C : EuclideanSpace ℝ (Fin d) → ℝ}
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C)
    (hbA : Bornology.IsBounded (range A)) (hbB : Bornology.IsBounded (range B))
    (hbC : Bornology.IsBounded (range C))
    (hABC : ∀ x y, (1 - s) * A x + s * B y ≤
      C ((1 - s) • x + s • y) + w⁻¹ / 2 * (1 - s) * s * ‖x - y‖ ^ 2) :
    let ν : Measure (EuclideanSpace ℝ (Fin d)) := volume.withDensity (fun x =>
      ENNReal.ofReal (Real.exp (-V x) / ∫ y, Real.exp (-V y)))
    (∫ x, Real.exp (A x) ∂ν) ^ (1 - s) * (∫ x, Real.exp (B x) ∂ν) ^ s ≤
      ∫ x, Real.exp (C x) ∂ν := by
  have hi := prekopa_exp_integral_weighted hd hs hs1
    (hV.continuous.neg.add hA) (hV.continuous.neg.add hB) (hV.continuous.neg.add hC)
    (bakry_emery_integrable_exp_perturbation hw hV hH hA hbA)
    (bakry_emery_integrable_exp_perturbation hw hV hH hB hbB)
    (bakry_emery_integrable_exp_perturbation hw hV hH hC hbC) (by
      intro x y
      have hc := bakry_emery_weighted_curvature
        (hV.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)) hH
        (sub_pos.mpr hs1).le hs.le (by ring : 1 - s + s = 1) x y
      change (1 - s) * (-V x + A x) + s * (-V y + B y) ≤
        -V ((1 - s) • x + s • y) + C ((1 - s) • x + s • y)
      linarith [hABC x y])
  let Z := ∫ x, Real.exp (-V x)
  have hZ : 0 < Z := bakry_emery_normalization_pos hw hV hH
  have hm : Measurable (fun x => Real.exp (-V x)) :=
    (Real.continuous_exp.comp hV.continuous.neg).measurable
  have hden : ∀ x, 0 ≤ Real.exp (-V x) := fun _ => (Real.exp_pos _).le
  dsimp only
  rw [Gaussian.integral_normalized_density hm hden hZ,
    Gaussian.integral_normalized_density hm hden hZ,
    Gaussian.integral_normalized_density hm hden hZ]
  have hi' := div_le_div_of_nonneg_right hi hZ.le
  simp only [Pi.add_apply, Pi.neg_apply, Real.exp_add] at hi'
  rw [Real.div_rpow (integral_nonneg fun _ => mul_nonneg (hden _) (Real.exp_pos _).le) hZ.le,
    Real.div_rpow (integral_nonneg fun _ => mul_nonneg (hden _) (Real.exp_pos _).le) hZ.le,
    div_mul_div_comm, ← Real.rpow_add hZ, sub_add_cancel, Real.rpow_one]
  exact hi'

/-- The optimized varying-weight estimate, before differentiation in the weight.
The Hessian bound on `g` is an internal regularity assumption to be removed by approximation. -/
theorem bakry_emery_interpolation_integral (hd : 0 < d) (hw : 0 < w)
    (hV : ContDiff ℝ ∞ V)
    (hH : ∀ x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h)
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ 2 g)
    (hbg : Bornology.IsBounded (range g)) (hbG : Bornology.IsBounded (range (gradient g)))
    {M s : ℝ} (hgH : ∀ x h, (fderiv ℝ (fderiv ℝ g) x h) h ≤ M * ‖h‖ ^ 2)
    (hs : 0 < s) (hs1 : s < 1) (hD : 0 < w⁻¹ * (1 - s) - M * s) :
    let ν : Measure (EuclideanSpace ℝ (Fin d)) := volume.withDensity (fun x =>
      ENNReal.ofReal (Real.exp (-V x) / ∫ y, Real.exp (-V y)))
    (∫ x, Real.exp (g x / (1 - s)) ∂ν) ^ (1 - s) ≤
      ∫ x, Real.exp (g x + s / (2 * (w⁻¹ * (1 - s) - M * s)) *
        ‖gradient g x‖ ^ 2) ∂ν := by
  have hg' : Continuous (gradient g) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.comp
      (hg.continuous_fderiv (by norm_num))
  obtain ⟨K, hK⟩ := hbg.exists_norm_le
  obtain ⟨L, hL⟩ := hbG.exists_norm_le
  have hK' (x) : |g x| ≤ K := hK _ (mem_range_self x)
  have hL' (x) : ‖gradient g x‖ ≤ L := hL _ (mem_range_self x)
  have hba : Bornology.IsBounded (range (fun x => g x / (1 - s))) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨K / |1 - s|, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [norm_div]
    exact div_le_div_of_nonneg_right (hK' x) (abs_nonneg _)
  have hbc : Bornology.IsBounded (range (fun x => g x +
      s / (2 * (w⁻¹ * (1 - s) - M * s)) * ‖gradient g x‖ ^ 2)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨K + |s / (2 * (w⁻¹ * (1 - s) - M * s))| * L ^ 2, ?_⟩
    rintro _ ⟨x, rfl⟩
    apply (norm_add_le _ _).trans
    apply add_le_add (hK' x)
    rw [norm_mul, norm_pow, Real.norm_eq_abs, norm_norm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hL' x) 2) (abs_nonneg _)
  have hc := bakry_emery_weighted_comparison hd hw hV hH hs hs1
    (hg.continuous.div_const _) continuous_const
    (hg.continuous.add (continuous_const.mul (hg'.norm.pow 2)))
    hba (by simpa only [range_const] using Bornology.isBounded_singleton (x := (0 : ℝ))) hbc (by
      intro x y
      -- Use the Taylor and square-completion proof directly with the curvature quadratic.
      have hxz : x - ((1 - s) • x + s • y) = s • (x - y) := by module
      have hTaylor := le_quadratic_tangent_of_hessian_upper convex_univ isOpen_univ
        hg.contDiffOn (fun z _ h => hgH z h)
        (mem_univ ((1 - s) • x + s • y)) (mem_univ x)
      rw [hxz, map_smul, smul_eq_mul, norm_smul, Real.norm_of_nonneg hs.le,
        mul_pow, ← inner_gradient_left] at hTaylor
      have hquad := mul_le_mul_of_nonneg_left
        (inner_sub_quadratic_le hD (gradient g ((1 - s) • x + s • y)) (x - y)) hs.le
      rw [mul_div_cancel₀ _ (sub_pos.mpr hs1).ne', mul_zero, add_zero]
      have he : s * (‖gradient g ((1 - s) • x + s • y)‖ ^ 2 /
          (2 * (w⁻¹ * (1 - s) - M * s))) =
          s / (2 * (w⁻¹ * (1 - s) - M * s)) * ‖gradient g ((1 - s) • x + s • y)‖ ^ 2 := by ring
      rw [he] at hquad
      simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at *
      nlinarith)
  let := bakry_emery_isProbabilityMeasure hw hV hH
  simpa only [Real.exp_zero, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul,
    mul_one, Real.one_rpow, Pi.add_apply, Pi.mul_apply, Pi.pow_apply] using hc

end Riesz1.Externals

end
