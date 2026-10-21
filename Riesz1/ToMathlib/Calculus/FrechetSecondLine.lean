/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Calculus.ConvexLineHessian

/-!
# Second Fréchet derivative as a second line derivative

If a real function `f` on a normed space is differentiable near `z`, and its derivative is
differentiable at `z`, then the second Fréchet derivative `D²f(z)(b, b)` is the second derivative
at `0` of the restriction `s ↦ f(z + s • b)`. Here the second derivative is taken as the derivative
of its first derivative, `t ↦ deriv (fun s ↦ f (z + s • b)) t`, at `0`.

The statement is the bridge between Fréchet and line formulations used in the Hessian identity
(Lemma 3.7).
-/

@[expose] public section

open Filter Topology

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For a function `f` that is differentiable near `z`, with differentiable derivative at `z`,
the second Fréchet derivative in direction `b` is the second derivative of the restriction to the
line through `z` in direction `b`. -/
theorem fderiv_fderiv_apply_eq_deriv_deriv_line {f : E → ℝ} {z b : E}
    (hf : ∀ᶠ x in 𝓝 z, DifferentiableAt ℝ f x) (hf' : DifferentiableAt ℝ (fderiv ℝ f) z) :
    fderiv ℝ (fderiv ℝ f) z b b =
      deriv (fun t : ℝ => deriv (fun s : ℝ => f (z + s • b)) t) 0 := by
  have hcont : Tendsto (fun t : ℝ => z + t • b) (𝓝 0) (𝓝 z) := by
    have hc : Continuous (fun t : ℝ => z + t • b) := by fun_prop
    simpa using hc.tendsto 0
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (z + t • b) := hcont.eventually hf
  have hderiv_eq : deriv (fun s : ℝ => f (z + s • b)) =ᶠ[𝓝 (0 : ℝ)]
      fun t : ℝ => fderiv ℝ f (z + t • b) b := by
    filter_upwards [hev] with t ht
    have hline : HasDerivAt (fun s : ℝ => z + s • b) b t := by
      simpa using ((hasDerivAt_id t).smul_const b).const_add z
    exact (HasFDerivAt.comp_hasDerivAt t ht.hasFDerivAt hline).deriv
  rw [show deriv (fun t : ℝ => deriv (fun s : ℝ => f (z + s • b)) t) 0 =
      deriv (deriv (fun s : ℝ => f (z + s • b))) 0 from rfl, hderiv_eq.deriv_eq,
    (hasDerivAt_fderiv_apply_comp_line (v := b) (w := b) hf').deriv]

end Riesz1

end
