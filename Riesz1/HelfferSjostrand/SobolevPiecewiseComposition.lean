/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SobolevLevelSets
public import Riesz1.ToMathlib.WeightedSobolev.PiecewiseComposition

/-!
# The finitely piecewise C¹ chain rule for the Gibbs completion

The finite set contains all break values. At those
values the gradient vanishes, so the formula is independent of the
convention for the scalar derivative there.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff NNReal

namespace Riesz1

variable {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)

/-- Composition by a Lipschitz map that is `C¹` off a finite set belongs to the graph,
with the chain rule on the whole measured space. -/
theorem hsSobolev_comp_piecewise_graph
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    {T : ℝ → ℝ} {C : ℝ≥0} (hT : LipschitzWith C T) (h0 : T 0 = 0)
    {B : Set ℝ} (hB : B.Finite) (hTC : ContDiffOn ℝ 1 T Bᶜ) :
    WeightedSobolev.IsGraphH1
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
      (fun _ : hsSmoothCore N => True) (fun φ => hsSmoothValue φ.val) hsSmoothGradient
      (fun x => T (hsSobolevValue _ f x))
      (fun x => deriv T (hsSobolevValue _ f x) • hsSobolevGradient _ f x) := by
  exact WeightedSobolev.Internal.graph_comp_piecewise
    (fun φ _ => φ.property.memLp_value _) (fun φ _ => φ.property.memLp_gradient _)
    (Lp.memLp _) (Lp.memLp _)
    (fun _ hS hS0 _ hSb => hsSobolev_comp_smooth_graph _ f hS hS0 hSb) hT h0 hB hTC
    (fun a _ => hsSobolevGradient_eq_zero_on_level χ hc f a)

/-- Finitely piecewise `C¹` composition, as an actual completed Sobolev element. -/
def hsSobolevCompPiecewise
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (T : ℝ → ℝ) (C : ℝ≥0) (hT : LipschitzWith C T) (h0 : T 0 = 0)
    (B : Set ℝ) (hB : B.Finite) (hTC : ContDiffOn ℝ 1 T Bᶜ) :
    HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
  let h := hsSobolev_comp_piecewise_graph χ hc f hT h0 hB hTC
  exact ⟨WithLp.toLp 2 (h.1.toLp _, h.2.1.toLp _),
    (hsSobolev_iff_graph _ _ _ h.1 h.2.1).mpr h⟩

theorem hsSobolevValue_compPiecewise
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (T : ℝ → ℝ) (C : ℝ≥0) (hT : LipschitzWith C T) (h0 : T 0 = 0)
    (B : Set ℝ) (hB : B.Finite) (hTC : ContDiffOn ℝ 1 T Bᶜ) :
    (hsSobolevValue _ (hsSobolevCompPiecewise χ hc f T C hT h0 B hB hTC) :
      HsConfiguration N → ℝ) =ᵐ[(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))]
        fun x => T (hsSobolevValue _ f x) :=
  (hsSobolev_comp_piecewise_graph χ hc f hT h0 hB hTC).1.coeFn_toLp

theorem hsSobolevGradient_compPiecewise
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (T : ℝ → ℝ) (C : ℝ≥0) (hT : LipschitzWith C T) (h0 : T 0 = 0)
    (B : Set ℝ) (hB : B.Finite) (hTC : ContDiffOn ℝ 1 T Bᶜ) :
    (hsSobolevGradient _ (hsSobolevCompPiecewise χ hc f T C hT h0 B hB hTC) :
      HsConfiguration N → HsEuclidean N) =ᵐ[(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))]
        fun x => deriv T (hsSobolevValue _ f x) • hsSobolevGradient _ f x :=
  (hsSobolev_comp_piecewise_graph χ hc f hT h0 hB hTC).2.1.coeFn_toLp

end Riesz1

end
