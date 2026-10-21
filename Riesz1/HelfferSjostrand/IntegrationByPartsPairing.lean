/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.Sobolev

/-!
# Extension of local pairings to the completed smooth jets

An internal continuity lemma. The analytic identity on smooth generators
is supplied separately by local Gibbs integration by parts.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1.Internal

variable {N : ℕ+} (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]

theorem hsSobolev_pairing_of_smooth
    (t : HsConfiguration N → HsEuclidean N) (ht : MemLp t 2 μ)
    (q : HsConfiguration N → ℝ) (hq : MemLp q 2 μ)
    (hcore : ∀ φ : hsSmoothCore N,
      (∫ x, inner ℝ (hsSmoothGradient φ x) (t x) ∂μ) =
        ∫ x, hsSmoothValue φ.val x * q x ∂μ) (f : HsSobolev μ) :
    (∫ x, inner ℝ (hsSobolevGradient μ f x) (t x) ∂μ) =
      ∫ x, hsSobolevValue μ f x * q x ∂μ := by
  let T := ht.toLp t
  let Q := hq.toLp q
  have hcore' (φ : hsSmoothCore N) :
      inner ℝ (hsSobolevGradient μ (hsSobolevOfSmooth μ φ)) T =
        inner ℝ (hsSobolevValue μ (hsSobolevOfSmooth μ φ)) Q := by
    have hgrad : (hsSobolevGradient μ (hsSobolevOfSmooth μ φ) : HsConfiguration N → HsEuclidean N)
        =ᵐ[μ] hsSmoothGradient φ := (φ.property.memLp_gradient μ).coeFn_toLp
    have hval : (hsSobolevValue μ (hsSobolevOfSmooth μ φ) : HsConfiguration N → ℝ)
        =ᵐ[μ] hsSmoothValue φ.val := (φ.property.memLp_value μ).coeFn_toLp
    rw [L2.inner_def, L2.inner_def]
    calc
      _ = ∫ x, inner ℝ (hsSmoothGradient φ x) (t x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hgrad, ht.coeFn_toLp] with x hx htx
        rw [hx, htx]
      _ = _ := hcore φ
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hval, hq.coeFn_toLp] with x hx hqx
        rw [hx, hqx, Real.inner_apply]
  have heq : (fun g : HsSobolev μ => inner ℝ (hsSobolevGradient μ g) T) =
      (fun g => inner ℝ (hsSobolevValue μ g) Q) :=
    (denseRange_hsSobolevOfSmooth μ).equalizer
      ((hsSobolevGradient μ).continuous.inner continuous_const)
      ((hsSobolevValue μ).continuous.inner continuous_const) (funext hcore')
  calc
    _ = inner ℝ (hsSobolevGradient μ f) T := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [ht.coeFn_toLp] with x hx
      rw [hx]
    _ = inner ℝ (hsSobolevValue μ f) Q := congrFun heq f
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hq.coeFn_toLp] with x hx
      rw [hx, Real.inner_apply]

end Riesz1.Internal

end
