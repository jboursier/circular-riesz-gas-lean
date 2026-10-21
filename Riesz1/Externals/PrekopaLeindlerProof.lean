/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PrekopaLeindler.Core
public import Riesz1.Frozen.External.PrekopaLeindler
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Proof of the midpoint Prékopa–Leindler inequality

This file proves `Riesz1.External.PrekopaLeindler` (the Prékopa–Leindler inequality,
Bobkov–Ledoux 2000, equation (1.1)). The proof specializes the
general inequality `Riesz1.PrekopaLeindler.prekopa_leindler` (module
`Riesz1.ToMathlib.PrekopaLeindler.Core`) to the exponent `θ = 1/2`, and then:

1. The dilation `z ↦ (1/2) • z` on `Fin N → ℝ` multiplies lower integrals by `2 ^ N`
   (`Riesz1.Externals.lintegral_half_smul`). This constant cancels the constant of the
   general inequality.
2. A bounded measurable function with bounded support is integrable
   (`Riesz1.Externals.integrable_of_bounded_support`).
3. The map `WithLp.toLp 2 : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N)` is measure preserving,
   so lower integrals agree on the two spaces.

The general inequality is ported from `hojonathanho/isoperimetric` at commit `29768f8`,
which is distributed under the Apache License 2.0. The module docstring of
`Riesz1.ToMathlib.PrekopaLeindler.Core` records the port.
-/

@[expose] public section

open MeasureTheory

namespace Riesz1.Externals

open Riesz1.PrekopaLeindler

/-- Dilation by `1/2` on `Fin N → ℝ` multiplies the lower integral of `w` by `2 ^ N`. -/
lemma lintegral_half_smul {N : ℕ} {w : (Fin N → ℝ) → ENNReal} (hw : Measurable w) :
    ∫⁻ z, w ((1 / 2 : ℝ) • z) = 2 ^ N * ∫⁻ z, w z := by
  have hmap : Measure.map (fun z : Fin N → ℝ => (1 / 2 : ℝ) • z) volume
      = ENNReal.ofReal |((1 / 2 : ℝ) ^ Module.finrank ℝ (Fin N → ℝ))⁻¹| • volume :=
    Measure.map_addHaar_smul (volume : Measure (Fin N → ℝ)) (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hval : ENNReal.ofReal |((1 / 2 : ℝ) ^ Module.finrank ℝ (Fin N → ℝ))⁻¹| = 2 ^ N := by
    rw [Module.finrank_fin_fun, one_div, inv_pow, inv_inv,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ N), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
  calc ∫⁻ z, w ((1 / 2 : ℝ) • z)
      = ∫⁻ y, w y ∂Measure.map (fun z : Fin N → ℝ => (1 / 2 : ℝ) • z) volume :=
        (lintegral_map hw (measurable_const_smul _)).symm
    _ = 2 ^ N * ∫⁻ z, w z := by
        rw [hmap, lintegral_smul_measure, hval, smul_eq_mul]

/-- The midpoint Prékopa–Leindler inequality for extended nonnegative functions on
`Fin (n + 1) → ℝ`, with the exponent `1/2` in both factors. -/
lemma midpoint_lintegral {n : ℕ} {f g w : (Fin (n + 1) → ℝ) → ENNReal}
    (hf : Measurable f) (hg : Measurable g) (hw : Measurable w)
    (hfgw : ∀ x y, f x ^ (1 - (1 / 2 : ℝ)) * g y ^ (1 / 2 : ℝ) ≤ w ((1 / 2 : ℝ) • (x + y))) :
    (∫⁻ x, f x) ^ (1 - (1 / 2 : ℝ)) * (∫⁻ x, g x) ^ (1 / 2 : ℝ) ≤ ∫⁻ x, w x := by
  have hH : Measurable (fun z : Fin (n + 1) → ℝ => w ((1 / 2 : ℝ) • z)) :=
    hw.comp (measurable_const_smul _)
  have key := prekopa_leindler (d := n) (θ := 1 / 2) ⟨by norm_num, by norm_num, hf, hg, hH, hfgw⟩
  have hC : ENNReal.ofReal ((1 - (1 / 2 : ℝ)) ^ (((n : ℝ) + 1) * (1 - 1 / 2)) *
      (1 / 2 : ℝ) ^ (((n : ℝ) + 1) * (1 / 2)))⁻¹ = 2 ^ (n + 1) := by
    have h12 : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
    have hexp : ((n : ℝ) + 1) * (1 / 2) + ((n : ℝ) + 1) * (1 / 2) = ((n + 1 : ℕ) : ℝ) := by
      push_cast; ring
    rw [h12, ← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2), hexp, Real.rpow_natCast,
      one_div, inv_pow, inv_inv, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  rw [hC, lintegral_half_smul hw, mul_assoc] at key
  exact (ENNReal.mul_le_mul_iff_right (pow_ne_zero _ two_ne_zero)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)).1 key

/-- A bounded measurable function with bounded support is integrable for Lebesgue measure. -/
lemma integrable_of_bounded_support {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Measurable f) (hb : Bornology.IsBounded (Set.range f))
    (hs : Bornology.IsBounded (Function.support f)) : Integrable f volume := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hb
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin d)) |>.mp hs
  rw [← integrableOn_iff_integrable_of_support_subset hR]
  exact Measure.integrableOn_of_bounded measure_closedBall_lt_top.ne hf.aestronglyMeasurable
    (ae_of_all _ fun x => hM (f x) ⟨x, rfl⟩)

/-- The Prékopa–Leindler inequality with `θ = 1/2` for Euclidean space. -/
theorem prekopa_leindler_proof : Riesz1.External.PrekopaLeindler := by
  unfold Riesz1.External.PrekopaLeindler
  intro d hd u v w hu hv hw hu0 hv0 hw0 hbu hbv hbw hsu hsv hsw hmid
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hiu := integrable_of_bounded_support hu hbu hsu
  have hiv := integrable_of_bounded_support hv hbv hsv
  have hiw := integrable_of_bounded_support hw hbw hsw
  refine ⟨hiu, hiv, hiw, ?_⟩
  have hT : MeasurePreserving (WithLp.toLp 2 : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)))
      volume volume :=
    PiLp.volume_preserving_toLp (Fin (n + 1))
  have hint : ∀ f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, Measurable f →
      ∫⁻ x, ENNReal.ofReal (f (WithLp.toLp 2 x)) = ∫⁻ y, ENNReal.ofReal (f y) := fun f hf =>
    hT.lintegral_comp (ENNReal.measurable_ofReal.comp hf)
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h12 : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  have hmid' : ∀ x y : Fin (n + 1) → ℝ,
      ENNReal.ofReal (u (WithLp.toLp 2 x)) ^ (1 - (1 / 2 : ℝ)) *
        ENNReal.ofReal (v (WithLp.toLp 2 y)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (w (WithLp.toLp 2 ((1 / 2 : ℝ) • (x + y)))) := by
    intro x y
    have hsum : WithLp.toLp 2 ((1 / 2 : ℝ) • (x + y)) =
        (1 / 2 : ℝ) • (WithLp.toLp 2 x + WithLp.toLp 2 y : EuclideanSpace ℝ (Fin (n + 1))) := by
      ext i; simp [mul_add]
    rw [hsum, h12, ENNReal.ofReal_rpow_of_nonneg (hu0 _) hhalf,
      ENNReal.ofReal_rpow_of_nonneg (hv0 _) hhalf,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (hu0 (WithLp.toLp 2 x)) _),
      ← Real.mul_rpow (hu0 (WithLp.toLp 2 x)) (hv0 (WithLp.toLp 2 y)), ← Real.sqrt_eq_rpow]
    exact ENNReal.ofReal_le_ofReal (hmid _ _)
  have hmain := midpoint_lintegral
    (f := fun x => ENNReal.ofReal (u (WithLp.toLp 2 x)))
    (g := fun x => ENNReal.ofReal (v (WithLp.toLp 2 x)))
    (w := fun x => ENNReal.ofReal (w (WithLp.toLp 2 x)))
    (ENNReal.measurable_ofReal.comp (hu.comp hT.measurable))
    (ENNReal.measurable_ofReal.comp (hv.comp hT.measurable))
    (ENNReal.measurable_ofReal.comp (hw.comp hT.measurable)) hmid'
  rw [hint u hu, hint v hv, hint w hw] at hmain
  have hIu := ofReal_integral_eq_lintegral_ofReal hiu (ae_of_all _ hu0)
  have hIv := ofReal_integral_eq_lintegral_ofReal hiv (ae_of_all _ hv0)
  have hIw := ofReal_integral_eq_lintegral_ofReal hiw (ae_of_all _ hw0)
  rw [← hIu, ← hIv, ← hIw] at hmain
  have hu_nn : 0 ≤ ∫ x, u x := integral_nonneg hu0
  have hv_nn : 0 ≤ ∫ x, v x := integral_nonneg hv0
  have hw_nn : 0 ≤ ∫ x, w x := integral_nonneg hw0
  rw [h12, ENNReal.ofReal_rpow_of_nonneg hu_nn hhalf, ENNReal.ofReal_rpow_of_nonneg hv_nn hhalf,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hu_nn _), ENNReal.ofReal_le_ofReal_iff hw_nn] at hmain
  rw [Real.sqrt_eq_rpow, Real.mul_rpow hu_nn hv_nn]
  exact hmain

end Riesz1.Externals

end
