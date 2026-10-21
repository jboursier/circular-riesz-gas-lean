/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.LocalH2
public import Riesz1.ToMathlib.EllipticRegularity.LinearMaps

/-!
# Euclidean interior H² regularity

The real and complex Euclidean H² assertions of interior regularity.
These theorems assert only its regularity clause. The Lipschitz energy
identity and the cyclic quotient version are not asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The complex Euclidean H² clause of interior regularity.
The lower bound for the smooth potential and the positive-dimension
restriction are unnecessary for interior regularity. -/
theorem interiorRegularity_complex_h2 {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ) {u : E → ℂ}
    (huL : MemLp u 2 (volume.restrict U))
    (hu : IsDistributionalSchrodingerSolution U W lam u) : IsLocalH2 U u :=
  isLocalH2_of_distributional_schrodinger hU hW lam huL hu

/-- The real Euclidean H² clause of interior regularity, in the
same weak-derivative encoding as the complex clause. -/
theorem interiorRegularity_real_h2 {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ) {u : E → ℝ}
    (huL : MemLp u 2 (volume.restrict U))
    (hu : IsDistributionalSchrodingerSolution U W lam u) : IsLocalH2 U u := by
  have hc := interiorRegularity_complex_h2 hU hW lam
    (Complex.ofRealCLM.comp_memLp' huL) (hu.map Complex.ofRealCLM)
  have hr := hc.map Complex.reCLM
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.reCLM_apply,
    Complex.ofReal_re] using hr

end Riesz1
