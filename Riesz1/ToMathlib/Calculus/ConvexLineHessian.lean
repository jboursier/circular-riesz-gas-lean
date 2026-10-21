/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Deriv

/-!
# Second derivatives along lines, and the Hessian of a convex function

For a real normed space `E`, a point `p`, and a direction `v`, the line `t ↦ p + t • v` gives
one-variable restrictions of a function `f : E → ℝ`. This file proves the two chain-rule facts
that identify directional derivatives with Hessian quadratic forms:

* `Riesz1.hasDerivAt_comp_line`: `t ↦ f (p + t • v)` has derivative `Df(p + s • v) v` at `s`.
* `Riesz1.hasDerivAt_fderiv_comp_line`: `t ↦ Df(p + t • v) v` has derivative `D²f(p)(v, v)` at `0`.

It also proves that the Hessian of a convex `C²` function on an open convex set is positive
semidefinite, `Riesz1.fderiv_fderiv_nonneg_of_convexOn`. The proof restricts the function to the
line, applies the monotonicity of the derivative of a convex function, and passes to the limit
in the difference quotients of the derivative.
-/

@[expose] public section

open Filter Topology Set

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of `t ↦ f (p + t • v)` at `s` is the derivative of `f` at `p + s • v` in the
direction `v`. -/
theorem hasDerivAt_comp_line {f : E → ℝ} {p v : E} {s : ℝ}
    (hf : DifferentiableAt ℝ f (p + s • v)) :
    HasDerivAt (fun t : ℝ => f (p + t • v)) (fderiv ℝ f (p + s • v) v) s := by
  have hline : HasDerivAt (fun t : ℝ => p + t • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add p
  exact hf.hasFDerivAt.comp_hasDerivAt s hline

/-- The derivative of `t ↦ Df (p + t • v) v` at `0` is the second derivative `D²f(p)(v, v)`. -/
theorem hasDerivAt_fderiv_comp_line {f : E → ℝ} {p v : E}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) p) :
    HasDerivAt (fun t : ℝ => fderiv ℝ f (p + t • v) v)
      (fderiv ℝ (fderiv ℝ f) p v v) 0 := by
  have hline : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hf' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) p)
      ((fun t : ℝ => p + t • v) 0) := by
    simpa using hf.hasFDerivAt
  have hD : HasDerivAt (fun t : ℝ => fderiv ℝ f (p + t • v))
      (fderiv ℝ (fderiv ℝ f) p v) 0 :=
    hf'.comp_hasDerivAt (0 : ℝ) hline
  simpa using hD.clm_apply (hasDerivAt_const (0 : ℝ) v)

/-- The derivative of `s ↦ Df (p + s • v) v` at a parameter `t₀` is `D²f(p + t₀ • v)(v, v)`. -/
theorem hasDerivAt_fderiv_comp_line_at {f : E → ℝ} {p v : E} {t₀ : ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (p + t₀ • v)) :
    HasDerivAt (fun s : ℝ => fderiv ℝ f (p + s • v) v)
      (fderiv ℝ (fderiv ℝ f) (p + t₀ • v) v v) t₀ := by
  have hline : HasDerivAt (fun s : ℝ => p + s • v) v t₀ := by
    simpa using ((hasDerivAt_id t₀).smul_const v).const_add p
  have hD : HasDerivAt (fun s : ℝ => fderiv ℝ f (p + s • v))
      (fderiv ℝ (fderiv ℝ f) (p + t₀ • v) v) t₀ :=
    hf.hasFDerivAt.comp_hasDerivAt t₀ hline
  simpa using hD.clm_apply (hasDerivAt_const t₀ v)

/-- The derivative of `t ↦ Df (p + t • v) w` at `0` is `D²f(p)(v, w)`, for a fixed vector `w`. -/
theorem hasDerivAt_fderiv_apply_comp_line {f : E → ℝ} {p v w : E}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) p) :
    HasDerivAt (fun t : ℝ => fderiv ℝ f (p + t • v) w)
      (fderiv ℝ (fderiv ℝ f) p v w) 0 := by
  have hline : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hf' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) p)
      ((fun t : ℝ => p + t • v) 0) := by
    simpa using hf.hasFDerivAt
  have hD : HasDerivAt (fun t : ℝ => fderiv ℝ f (p + t • v))
      (fderiv ℝ (fderiv ℝ f) p v) 0 :=
    hf'.comp_hasDerivAt (0 : ℝ) hline
  simpa using hD.clm_apply (hasDerivAt_const (0 : ℝ) w)

/-- The Hessian of a convex `C²` function on an open convex set is positive semidefinite:
`0 ≤ D²f(p)(v, v)` for every `p` in the set and every direction `v`. -/
theorem fderiv_fderiv_nonneg_of_convexOn {U : Set E} (hU : IsOpen U) (hUc : Convex ℝ U)
    {f : E → ℝ} (hf : ConvexOn ℝ U f) (hC : ContDiffOn ℝ 2 f U) {p : E} (hp : p ∈ U) (v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) p v v := by
  -- The domain of the restriction to the line through `p` in direction `v`.
  set S : Set ℝ := {t : ℝ | p + t • v ∈ U} with hS_def
  have hSo : IsOpen S := hU.preimage (by fun_prop)
  have h0 : (0 : ℝ) ∈ S := by simpa [S] using hp
  have hdiffU : ∀ x ∈ U, DifferentiableAt ℝ f x := fun x hx =>
    (hC.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)
  have hdiffS : ∀ t ∈ S, DifferentiableAt ℝ (fun s : ℝ => f (p + s • v)) t := fun t ht =>
    (hasDerivAt_comp_line (hdiffU _ ht)).differentiableAt
  have hcomb : ∀ x y a b : ℝ, a + b = 1 →
      p + (a * x + b * y) • v = a • (p + x • v) + b • (p + y • v) := by
    intro x y a b hab
    obtain rfl : b = 1 - a := by linarith
    module
  have hconv : ConvexOn ℝ S (fun t : ℝ => f (p + t • v)) := by
    refine ⟨fun x hx y hy a b ha hb hab => ?_, fun x hx y hy a b ha hb hab => ?_⟩
    · show p + (a * x + b * y) • v ∈ U
      rw [hcomb x y a b hab]
      exact hUc hx hy ha hb hab
    · show f (p + (a * x + b * y) • v) ≤ a * f (p + x • v) + b * f (p + y • v)
      rw [hcomb x y a b hab]
      simpa [smul_eq_mul] using hf.2 hx hy ha hb hab
  have hmono : MonotoneOn (deriv fun t : ℝ => f (p + t • v)) S :=
    hconv.monotoneOn_deriv hdiffS
  have hderiv : ∀ t ∈ S, deriv (fun s : ℝ => f (p + s • v)) t = fderiv ℝ f (p + t • v) v :=
    fun t ht => (hasDerivAt_comp_line (hdiffU _ ht)).deriv
  -- The second derivative at `0` is the derivative of `deriv` of the restriction.
  have hfp : DifferentiableAt ℝ (fderiv ℝ f) p :=
    ((hC.fderiv_of_isOpen (m := 1) hU (by norm_num)).differentiableOn (by norm_num)).differentiableAt
      (hU.mem_nhds hp)
  have hD2 : HasDerivAt (deriv fun s : ℝ => f (p + s • v))
      (fderiv ℝ (fderiv ℝ f) p v v) 0 := by
    refine (hasDerivAt_fderiv_comp_line hfp).congr_of_eventuallyEq ?_
    filter_upwards [hSo.mem_nhds h0] with t ht
    exact hderiv t ht
  -- Nonnegative difference quotients of `deriv` pass to the limit.
  refine ge_of_tendsto hD2.tendsto_slope_zero_right ?_
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ S := nhdsWithin_le_nhds (hSo.mem_nhds h0)
  filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
  have htpos' : 0 < t := Set.mem_Ioi.1 htpos
  rw [smul_eq_mul, zero_add]
  exact mul_nonneg (inv_nonneg.2 htpos'.le) (sub_nonneg.2 (hmono h0 ht htpos'.le))

end Riesz1

end
