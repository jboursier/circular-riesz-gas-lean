/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

/-!
# Averaging a stationary weighted expectation

An internal inequality for bounded Lipschitz tests. The hypotheses describe
integrability and stationarity of arbitrary families of random variables.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset

namespace Riesz1.Internal

lemma inversion_bias_averaging_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (w x : ℕ → Ω → ℝ)
    (m : ℕ) (hm : 1 ≤ m)
    (hw : ∀ j, Measurable (w j)) (hx : ∀ j, Measurable (x j))
    (hw0 : ∀ j z, 0 ≤ w j z) (hwi : ∀ j, Integrable (w j) μ)
    (hwd : ∀ j ∈ range m, Integrable (fun z => w j z * |x j z - x 0 z|) μ)
    (f : ℝ → ℝ) (hf : LipschitzWith 1 f) (hfb : ∀ t, |f t| ≤ 1)
    (hstat : ∀ j, (∫ z, w j z * f (x j z) ∂μ) = ∫ z, w 0 z * f (x 0 z) ∂μ)
    :
    |(∫ z, w 0 z * f (x 0 z) ∂μ) - ∫ z, f (x 0 z) ∂μ| ≤
      ((∫ z, |(∑ j ∈ range m, w j z) - m| ∂μ) +
        ∑ j ∈ range m, ∫ z, w j z * |x j z - x 0 z| ∂μ) / m := by
  have hfm := hf.continuous.measurable
  have hfi : Integrable (fun z => f (x 0 z)) μ :=
    (integrable_const (1 : ℝ)).mono' (hfm.comp (hx 0)).aestronglyMeasurable
      (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hfb (x 0 z))
  have hwfi (j : ℕ) : Integrable (fun z => w j z * f (x j z)) μ := by
    refine (hwi j).mono' ((hw j).mul (hfm.comp (hx j))).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 j z)]
    exact mul_le_of_le_one_right (hw0 j z) (hfb _)
  have hsum : Integrable (fun z => ∑ j ∈ range m, w j z) μ :=
    integrable_finsetSum _ fun j _ => hwi j
  have hierr : Integrable (fun z => |(∑ j ∈ range m, w j z) - m|) μ :=
    (hsum.sub (integrable_const (m : ℝ))).abs
  have hiwd : Integrable (fun z => ∑ j ∈ range m, w j z * |x j z - x 0 z|) μ :=
    integrable_finsetSum _ fun j hj => hwd j hj
  let H := fun z => (∑ j ∈ range m, w j z * f (x j z)) - (m : ℝ) * f (x 0 z)
  have hiH : Integrable H μ :=
    (integrable_finsetSum _ fun j _ => hwfi j).sub (hfi.const_mul m)
  have heq : (∫ z, H z ∂μ) = (m : ℝ) *
      ((∫ z, w 0 z * f (x 0 z) ∂μ) - ∫ z, f (x 0 z) ∂μ) := by
    dsimp only [H]
    rw [integral_sub (integrable_finsetSum _ fun j _ => hwfi j) (hfi.const_mul m),
      integral_finsetSum _ fun j _ => hwfi j, integral_const_mul]
    simp only [hstat, sum_const, card_range, nsmul_eq_mul]
    ring
  have hpt (z : Ω) : |H z| ≤ |(∑ j ∈ range m, w j z) - m| +
      ∑ j ∈ range m, w j z * |x j z - x 0 z| := by
    have hidentity : H z = (∑ j ∈ range m, w j z * (f (x j z) - f (x 0 z))) +
        ((∑ j ∈ range m, w j z) - m) * f (x 0 z) := by
      dsimp only [H]
      simp only [mul_sub, sum_sub_distrib, ← sum_mul]
      ring
    rw [hidentity]
    have htest : |((∑ j ∈ range m, w j z) - m) * f (x 0 z)| ≤
        |(∑ j ∈ range m, w j z) - m| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hfb _)
    have hsum' : |∑ j ∈ range m, w j z * (f (x j z) - f (x 0 z))| ≤
        ∑ j ∈ range m, w j z * |x j z - x 0 z| := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hw0 j z)]
      apply mul_le_mul_of_nonneg_left _ (hw0 j z)
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hf.dist_le_mul (x j z) (x 0 z)
    exact (abs_add_le _ _).trans (by linarith)
  have hbound := (abs_integral_le_integral_abs (f := H) (μ := μ)).trans
    (integral_mono hiH.abs (hierr.add hiwd) hpt)
  simp only [Pi.add_apply] at hbound
  rw [heq, abs_mul, abs_of_pos (show (0 : ℝ) < m by exact_mod_cast hm),
    integral_add hierr hiwd, integral_finsetSum _ fun j hj => hwd j hj] at hbound
  exact (le_div_iff₀ (show (0 : ℝ) < m by exact_mod_cast hm)).mpr (by
    simpa only [mul_comm] using hbound)

end Riesz1.Internal

end
end
