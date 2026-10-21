/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleSobolevZero
public import Riesz1.ToMathlib.WeightedSobolev.ProductSlices

/-!
# Vanishing weak circle derivatives on a product

The circle argument in Lemma 3.9, for a completed graph on an arbitrary
radial measure times the uniform circle. The graph hypothesis is on the product, rather
than being imposed on its individual slices.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace Riesz1

variable {α S : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
  {T : ℝ} [Fact (0 < T)]

/-- Zero circle derivative in the product graph implies almost everywhere equality to
the rotation average. No regularity of the limiting representative is needed. -/
theorem circleProductGraphH1_eq_rotation_mean
    {P : S → Prop} {test : S → α → CircleC1Function T}
    {F : α × AddCircle T → ℝ}
    (hF : WeightedSobolev.IsGraphH1 (μ.prod AddCircle.haarAddCircle) P
      (fun s p => (test s p.1).val p.2)
      (fun s p => circleLiftDerivative T (test s p.1) p.2) F (fun _ => 0))
    (hv : ∀ s, P s → MemLp (fun p : α × AddCircle T => (test s p.1).val p.2) 2
      (μ.prod AddCircle.haarAddCircle))
    (hg : ∀ s, P s → MemLp (fun p : α × AddCircle T =>
      circleLiftDerivative T (test s p.1) p.2) 2 (μ.prod AddCircle.haarAddCircle)) :
    F =ᵐ[μ.prod AddCircle.haarAddCircle]
      (fun p => ∫ w, F (p.1, w) ∂AddCircle.haarAddCircle) := by
  have hslice := hF.ae_slice hv hg
  have he : ∀ᵐ x ∂μ, (fun w => F (x, w)) =ᵐ[AddCircle.haarAddCircle]
      (fun _ => ∫ w, F (x, w) ∂AddCircle.haarAddCircle) := by
    filter_upwards [hslice] with x hx
    obtain ⟨hxF, hxG, φ, hφ, hφv, hφg⟩ := hx
    apply circleGraphH1_eq_mean_of_derivative_zero T
    exact ⟨hxF, hxG, fun k => test (φ k) x, fun _ => trivial, hφv, hφg⟩
  exact WeightedSobolev.ae_eq_prod_of_ae_eq_slices hF.memLp_fun.aestronglyMeasurable
    hF.memLp_fun.aestronglyMeasurable.integral_prod_right'.comp_fst he

end Riesz1

end
