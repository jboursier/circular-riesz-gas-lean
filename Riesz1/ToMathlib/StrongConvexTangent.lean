/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.ConvexHessian
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Quadratic support from a Hessian lower bound

The Hessian lower bound implies strong convexity and a quadratic tangent inequality.
These estimates apply to every real curvature, including zero and negative curvature.
They supply the normalization and interpolation estimates for the Bakry–Émery criterion.
-/

public section

noncomputable section

open Set
open scoped ContDiff

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A Hessian lower bound on an open convex domain gives strong convexity. -/
theorem strongConvexOn_of_hessian_lower {U : Set E} (hc : Convex ℝ U)
    (ho : IsOpen U) {V : E → ℝ} (hV : ContDiffOn ℝ 2 V U) {κ : ℝ}
    (hH : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h) :
    StrongConvexOn U κ V :=
  strongConvexOn_iff_convex.mpr (convexOn_sub_norm_sq_of_hessian_lower hc ho hV hH)

/-- The tangent plane plus the curvature quadratic supports a smooth function from below. -/
theorem quadratic_tangent_le_of_hessian_lower {U : Set E} (hc : Convex ℝ U)
    (ho : IsOpen U) {V : E → ℝ} (hV : ContDiffOn ℝ 2 V U) {κ : ℝ}
    (hH : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    V x + fderiv ℝ V x (y - x) + κ / 2 * ‖y - x‖ ^ 2 ≤ V y := by
  let p : ℝ → E := fun t => x + t • (y - x)
  let f : ℝ → ℝ := fun t => V (p t) - κ / 2 * t ^ 2 * ‖y - x‖ ^ 2
  have hp (t : ℝ) : HasDerivAt p (y - x) t := by
    simpa [p] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hpU {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : p t ∈ U := by
    have he : p t = (1 - t) • x + t • y := by dsimp [p]; module
    rw [he]
    exact hc hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  let f' : ℝ → ℝ := fun t =>
    fderiv ℝ V (p t) (y - x) - κ * t * ‖y - x‖ ^ 2
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f (f' t) t := by
    have hv := ((hV.contDiffAt (ho.mem_nhds (hpU ht))).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hp t)
    convert hv.sub ((((hasDerivAt_id t).pow 2).const_mul (κ / 2)).mul_const
      (‖y - x‖ ^ 2)) using 1
    · rfl
    · dsimp [f']
      ring
  have hdd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt f'
        ((fderiv ℝ (fderiv ℝ V) (p t) (y - x)) (y - x) - κ * ‖y - x‖ ^ 2) t := by
    have hVd := (((hV.fderiv_of_isOpen (m := 1) ho (by norm_num)).contDiffAt
      (ho.mem_nhds (hpU ht))).differentiableAt (by norm_num)).hasFDerivAt
    have hv := (hVd.comp_hasDerivAt t (hp t)).clm_apply (hasDerivAt_const t (y - x))
    convert hv.sub (((hasDerivAt_id t).const_mul κ).mul_const (‖y - x‖ ^ 2)) using 1
    · rfl
    · simp only [map_zero, add_zero, mul_one]
  have hfc : ConvexOn ℝ (Icc (0 : ℝ) 1) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => (hdd t (interior_subset ht)).hasDerivWithinAt)
    exact fun t ht => sub_nonneg.mpr (hH _ (hpU (interior_subset ht)) _)
  have hi := hfc.le_slope_of_hasDerivAt (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) zero_lt_one (hd 0 (by norm_num))
  simp [slope_def_field, f, f', p] at hi
  rw [map_sub]
  linarith

/-- The corresponding upper quadratic Taylor estimate. -/
theorem le_quadratic_tangent_of_hessian_upper {U : Set E} (hc : Convex ℝ U)
    (ho : IsOpen U) {g : E → ℝ} (hg : ContDiffOn ℝ 2 g U) {M : ℝ}
    (hH : ∀ x ∈ U, ∀ h, (fderiv ℝ (fderiv ℝ g) x h) h ≤ M * ‖h‖ ^ 2)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    g y ≤ g x + fderiv ℝ g x (y - x) + M / 2 * ‖y - x‖ ^ 2 := by
  have he : fderiv ℝ (fun z => -g z) = fun z => -fderiv ℝ g z := by
    funext z
    exact fderiv_fun_neg
  have he₂ (z : E) :
      fderiv ℝ (fderiv ℝ (fun z => -g z)) z = -fderiv ℝ (fderiv ℝ g) z := by
    rw [he]
    exact fderiv_fun_neg
  have hi := quadratic_tangent_le_of_hessian_lower hc ho hg.neg
    (κ := -M) (by
      intro z hz h
      rw [he₂ z]
      simpa only [neg_apply, neg_mul, neg_le_neg_iff] using hH z hz h) hx hy
  rw [he] at hi
  simp only [neg_apply, neg_div, neg_mul] at hi
  linarith

/-- The scalar quadratic optimization needed for exponential interpolation. -/
theorem inner_sub_quadratic_le {a : ℝ} (ha : 0 < a) (g h : E) :
    inner ℝ g h - a / 2 * ‖h‖ ^ 2 ≤ ‖g‖ ^ 2 / (2 * a) := by
  apply (le_div_iff₀ (by positivity : 0 < 2 * a)).mpr
  have hi := mul_le_mul_of_nonneg_left (real_inner_le_norm g h)
    (by positivity : 0 ≤ 2 * a)
  nlinarith [sq_nonneg (‖g‖ - a * ‖h‖)]

end Riesz1

end
