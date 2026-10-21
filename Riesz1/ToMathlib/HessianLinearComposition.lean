/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# The Hessian under continuous linear changes of variables
-/

public section

open Filter
open scoped Topology

namespace Riesz1

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A linear change of variables acts on both arguments of the Hessian. -/
theorem hessian_comp_continuousLinearMap (f : F → G) (L : E →L[𝕜] F) (y u v : E)
    (hf : ContDiffAt 𝕜 2 f (L y)) :
    fderiv 𝕜 (fderiv 𝕜 (fun z => f (L z))) y u v =
      fderiv 𝕜 (fderiv 𝕜 f) (L y) (L u) (L v) := by
  have he : ∀ᶠ z in 𝓝 y, ContDiffAt 𝕜 2 f (L z) :=
    L.continuous.continuousAt.tendsto.eventually (hf.eventually (by simp))
  have hg : fderiv 𝕜 (fun z => f (L z)) =ᶠ[𝓝 y]
      fun z => (fderiv 𝕜 f (L z)).comp L := by
    filter_upwards [he] with z hz
    change fderiv 𝕜 (f ∘ L) z = _
    rw [fderiv_comp z (hz.differentiableAt (by norm_num)) L.differentiableAt, L.fderiv]
  rw [hg.fderiv_eq]
  have hd : HasFDerivAt (fun z => fderiv 𝕜 f (L z))
      ((fderiv 𝕜 (fderiv 𝕜 f) (L y)).comp L) y :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp y L.hasFDerivAt
  rw [(hd.clm_comp (hasFDerivAt_const (c := L) y)).fderiv]
  simp

end Riesz1

end
