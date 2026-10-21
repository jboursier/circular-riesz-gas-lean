/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Convexity after subtracting a quadratic

A lower bound on the Hessian on an open convex set implies convexity after subtracting
the corresponding squared-norm quadratic. The proof uses scalar derivatives along segments.
-/

public section

noncomputable section

open Set
open scoped Topology RealInnerProductSpace

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Hessian criterion for convexity, with a quadratic of any real curvature subtracted.
No condition on the boundary of the open convex set is needed. -/
theorem convexOn_sub_norm_sq_of_hessian_lower {U : Set E} (hU : Convex ℝ U)
    (ho : IsOpen U) {V : E → ℝ} (hV : ContDiffOn ℝ 2 V U) {κ : ℝ}
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h) :
    ConvexOn ℝ U (fun x => V x - κ / 2 * ‖x‖ ^ 2) := by
  refine ⟨hU, fun x hx y hy a b ha hb' hab => ?_⟩
  let p : ℝ → E := fun t => x + t • (y - x)
  have hpU (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : p t ∈ U := by
    have he : p t = (1 - t) • x + t • y := by dsimp [p]; module
    rw [he]
    exact hU hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hpD (t : ℝ) : HasDerivAt p (y - x) t := by
    simpa [p] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hV1 : ContDiffOn ℝ 1 (fderiv ℝ V) U := hV.fderiv_of_isOpen ho (by norm_num)
  let q : ℝ → ℝ := fun t => V (p t) - κ / 2 * ‖p t‖ ^ 2
  let q' : ℝ → ℝ := fun t => fderiv ℝ V (p t) (y - x) - κ * inner ℝ (p t) (y - x)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt q (q' t) t := by
    have hv := ((hV.differentiableOn (by norm_num)).differentiableAt
      (ho.mem_nhds (hpU t ht))).hasFDerivAt.comp_hasDerivAt t (hpD t)
    convert hv.sub ((hpD t).norm_sq.const_mul (κ / 2)) using 1
    · rfl
    · dsimp [q']
      ring
  have hdd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt q' (fderiv ℝ (fderiv ℝ V) (p t) (y - x) (y - x) - κ * ‖y - x‖ ^ 2) t := by
    have hv := ((hV1.differentiableOn (by norm_num)).differentiableAt
      (ho.mem_nhds (hpU t ht))).hasFDerivAt.comp_hasDerivAt t (hpD t)
    have hi := (hpD t).inner ℝ (hasDerivAt_const t (y - x))
    convert (hv.clm_apply (hasDerivAt_const t (y - x))).sub (hi.const_mul κ) using 1
    · rfl
    · simp only [inner_zero_right, real_inner_self_eq_norm_sq, map_zero, add_zero, zero_add]
  have hq : ConvexOn ℝ (Icc (0 : ℝ) 1) q := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => (hdd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    exact sub_nonneg.mpr (hb (p t) (hpU t (interior_subset ht)) (y - x))
  have he : p b = a • x + b • y := by
    have he' : p b = (1 - b) • x + b • y := by dsimp [p]; module
    rw [he', show 1 - b = a by linarith]
  have hi := hq.2 (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) ha hb' hab
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, q, he, p, zero_smul,
    add_zero, one_smul, add_sub_cancel] using hi

end Riesz1

end
