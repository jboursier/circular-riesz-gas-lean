/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.Sobolev
public import Riesz1.HelfferSjostrand.SobolevComposition
public import Riesz1.ToMathlib.WeightedSobolev.CompositionLimits

/-!
# The C¹ chain rule in the periodic Sobolev completion

Composition with a `C¹` scalar map fixing zero and
having bounded derivative, including the exact value and gradient formulas.
The theorem holds for every finite measure on the quotient.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Riesz1

variable {N : ℕ+} (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]

/-- C¹ scalar composition satisfies the chain rule in the completed graph. -/
theorem hsSobolev_comp_C1_graph (f : HsSobolev μ)
    {T : ℝ → ℝ} (hT : ContDiff ℝ 1 T) (h0 : T 0 = 0) {C : ℝ≥0}
    (hb : ∀ r, ‖deriv T r‖₊ ≤ C) :
    WeightedSobolev.IsGraphH1 μ (fun _ : hsSmoothCore N => True)
      (fun φ => hsSmoothValue φ.val) hsSmoothGradient
      (fun x => T (hsSobolevValue μ f x))
      (fun x => deriv T (hsSobolevValue μ f x) • hsSobolevGradient μ f x) := by
  exact WeightedSobolev.Internal.graph_comp_C1
    (fun φ _ => φ.property.memLp_value μ) (fun φ _ => φ.property.memLp_gradient μ)
    (Lp.memLp _) (Lp.memLp _)
    (fun _ hS hS0 _ hSb => hsSobolev_comp_smooth_graph μ f hS hS0 hSb) hT h0 hb

/-- Composition with a C¹ map with bounded derivative, as an actual completed Sobolev jet. -/
def hsSobolevCompC1 (f : HsSobolev μ)
    (T : ℝ → ℝ) (hT : ContDiff ℝ 1 T) (h0 : T 0 = 0) (C : ℝ≥0)
    (hb : ∀ r, ‖deriv T r‖₊ ≤ C) : HsSobolev μ := by
  let h := hsSobolev_comp_C1_graph μ f hT h0 hb
  exact ⟨WithLp.toLp 2 (h.1.toLp (fun x => T (hsSobolevValue μ f x)),
    h.2.1.toLp (fun x => deriv T (hsSobolevValue μ f x) • hsSobolevGradient μ f x)),
    (hsSobolev_iff_graph μ _ _ h.1 h.2.1).mpr h⟩

/-- The value of C¹ composition is the pointwise scalar composition, almost everywhere. -/
theorem hsSobolevValue_compC1 (f : HsSobolev μ)
    (T : ℝ → ℝ) (hT : ContDiff ℝ 1 T) (h0 : T 0 = 0) (C : ℝ≥0)
    (hb : ∀ r, ‖deriv T r‖₊ ≤ C) :
    (hsSobolevValue μ (hsSobolevCompC1 μ f T hT h0 C hb) : HsConfiguration N → ℝ) =ᵐ[μ]
      fun x => T (hsSobolevValue μ f x) :=
  (hsSobolev_comp_C1_graph μ f hT h0 hb).1.coeFn_toLp

/-- The gradient formula for C¹ composition in the completion. -/
theorem hsSobolevGradient_compC1 (f : HsSobolev μ)
    (T : ℝ → ℝ) (hT : ContDiff ℝ 1 T) (h0 : T 0 = 0) (C : ℝ≥0)
    (hb : ∀ r, ‖deriv T r‖₊ ≤ C) :
    (hsSobolevGradient μ (hsSobolevCompC1 μ f T hT h0 C hb) :
      HsConfiguration N → HsEuclidean N) =ᵐ[μ]
      fun x => deriv T (hsSobolevValue μ f x) • hsSobolevGradient μ f x :=
  (hsSobolev_comp_C1_graph μ f hT h0 hb).2.1.coeFn_toLp

end Riesz1

end
