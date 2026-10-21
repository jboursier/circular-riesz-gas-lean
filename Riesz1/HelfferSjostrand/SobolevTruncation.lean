/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SobolevLevelSets
public import Riesz1.ToMathlib.WeightedSobolev.TruncationGraph

/-!
# Truncations in the periodic Gibbs Sobolev space

Clipping belongs to the completion, its gradient
is the strict-sublevel indicator times the original gradient, and the
truncations converge in the full Sobolev norm.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set

namespace Riesz1

variable {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)

/-- Clipping, including both threshold levels, belongs to the completed graph. -/
theorem hsSobolev_clip_graph
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    {R : ℝ} (hR : 0 ≤ R) :
    WeightedSobolev.IsGraphH1
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
      (fun _ : hsSmoothCore N => True) (fun φ => hsSmoothValue φ.val) hsSmoothGradient
      (fun x => WeightedSobolev.clipReal R (hsSobolevValue _ f x))
      ({x | |hsSobolevValue _ f x| < R}.indicator (hsSobolevGradient _ f)) := by
  exact WeightedSobolev.Internal.graph_clip
    (fun φ _ => φ.property.memLp_value _) (fun φ _ => φ.property.memLp_gradient _)
    (Lp.memLp _) (Lp.memLp _)
    (fun _ hS hS0 _ hSb => hsSobolev_comp_smooth_graph _ f hS hS0 hSb) hR
    (hsSobolevGradient_eq_zero_on_level χ hc f (-R))
    (hsSobolevGradient_eq_zero_on_level χ hc f R)

/-- The actual Sobolev truncation at radius `R ≥ 0`. -/
def hsSobolevClip
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (R : ℝ) (hR : 0 ≤ R) :
    HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
  let h := hsSobolev_clip_graph χ hc f hR
  exact ⟨WithLp.toLp 2 (h.1.toLp _, h.2.1.toLp _),
    (hsSobolev_iff_graph _ _ _ h.1 h.2.1).mpr h⟩

theorem hsSobolevValue_clip
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (R : ℝ) (hR : 0 ≤ R) :
    (hsSobolevValue _ (hsSobolevClip χ hc f R hR) : HsConfiguration N → ℝ) =ᵐ[(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))]
      fun x => WeightedSobolev.clipReal R (hsSobolevValue _ f x) :=
  (hsSobolev_clip_graph χ hc f hR).1.coeFn_toLp

theorem hsSobolevGradient_clip
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (R : ℝ) (hR : 0 ≤ R) :
    (hsSobolevGradient _ (hsSobolevClip χ hc f R hR) : HsConfiguration N → HsEuclidean N) =ᵐ[(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))]
      {x | |hsSobolevValue _ f x| < R}.indicator (hsSobolevGradient _ f) :=
  (hsSobolev_clip_graph χ hc f hR).2.1.coeFn_toLp

/-- Truncations converge in the full `H¹(μ)` norm. -/
theorem tendsto_hsSobolevClip
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    Tendsto (fun n : ℕ => hsSobolevClip χ hc f n (Nat.cast_nonneg n)) atTop (𝓝 f) := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  let fR := fun n : ℕ => hsSobolevClip χ hc f n (Nat.cast_nonneg n)
  have he (n : ℕ) : ‖fR n - f‖ ^ 2 = ∫ x,
      (WeightedSobolev.clipReal n (hsSobolevValue μ f x) - hsSobolevValue μ f x) ^ 2 +
        ‖({x | |hsSobolevValue μ f x| < n}.indicator (hsSobolevGradient μ f)) x -
          hsSobolevGradient μ f x‖ ^ 2 ∂μ := by
    rw [hsSobolev_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (hsSobolevValue μ (fR n)) (hsSobolevValue μ f),
      Lp.coeFn_sub (hsSobolevGradient μ (fR n)) (hsSobolevGradient μ f),
      hsSobolevValue_clip χ hc f n (Nat.cast_nonneg n),
      hsSobolevGradient_clip χ hc f n (Nat.cast_nonneg n)] with x hv hg hc1 hc2
    simp only [map_sub]
    rw [hv, hg]
    simp only [Pi.sub_apply]
    rw [hc1, hc2]
  have ht : Tendsto (fun n => ‖fR n - f‖ ^ 2) atTop (𝓝 0) := by
    simp only [he]
    exact WeightedSobolev.tendsto_truncation_pair_error (Lp.memLp _) (Lp.memLp _)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht.sqrt

end Riesz1

end
