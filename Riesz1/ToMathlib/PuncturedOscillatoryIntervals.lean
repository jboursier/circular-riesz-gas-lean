/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PuncturedOscillatoryIntegral

/-!
# Oscillatory estimates on intervals with two singular endpoints

Splitting at the midpoint reduces two endpoint singularities to the half-interval
estimate. The constants depend only on the function, interval and power bound, and are
chosen before the oscillation. This is an assembly tool.
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1.PuncturedDerivative

/-- A power bound at both endpoints implies integrability and an oscillatory estimate.
The endpoints themselves need not be differentiability points. -/
theorem oscillatory_bound_of_two_endpoint_bounds {q : ℝ → ℝ} {a z b C : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hC : 0 ≤ C) (haz : a < z)
    (hq : ∀ x ∈ Ioo a z, DifferentiableAt ℝ q x)
    (hbound : ∀ x ∈ Ioo a z,
      |deriv q x| ≤ C * ((x - a) ^ (-1 - b) + (z - x) ^ (-1 - b))) :
    IntervalIntegrable q volume a z ∧
      ∃ K W : ℝ, 0 ≤ K ∧ 1 ≤ W ∧
        ∀ (χ : ℝ → ℂ) (c : ℂ), W ≤ ‖c‖ →
          (∀ t : ℝ, HasDerivAt χ (c * χ t) t) → (∀ t : ℝ, ‖χ t‖ = 1) →
          ‖∫ t in a..z, (q t : ℂ) * χ t‖ ≤ K * ‖c‖ ^ (b - 1) := by
  let R := (z - a) / 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hleft : ∀ t ∈ Ioc 0 R, a + t ∈ Ioo a z := by
    intro t ht
    constructor <;> dsimp [R] at * <;> linarith [ht.1, ht.2]
  have hright : ∀ t ∈ Ioc 0 R, z - t ∈ Ioo a z := by
    intro t ht
    constructor <;> dsimp [R] at * <;> linarith [ht.1, ht.2]
  have hdl : ∀ t ∈ Ioc 0 R, DifferentiableAt ℝ (fun u => q (a + u)) t := by
    intro t ht
    exact (hq (a + t) (hleft t ht)).comp t (by fun_prop)
  have hdr : ∀ t ∈ Ioc 0 R, DifferentiableAt ℝ (fun u => q (z - u)) t := by
    intro t ht
    exact (hq (z - t) (hright t ht)).comp t (by fun_prop)
  have hbl : ∀ t ∈ Ioc 0 R,
      |deriv (fun u => q (a + u)) t| ≤ (2 * C) * t ^ (-1 - b) := by
    intro t ht
    rw [deriv_comp_const_add]
    have hp : (z - (a + t)) ^ (-1 - b) ≤ t ^ (-1 - b) :=
      Real.rpow_le_rpow_of_nonpos ht.1 (by dsimp [R] at ht; linarith [ht.2]) (by linarith)
    have he := hbound (a + t) (hleft t ht)
    simp only [add_sub_cancel_left] at he
    nlinarith [mul_le_mul_of_nonneg_left hp hC]
  have hbr : ∀ t ∈ Ioc 0 R,
      |deriv (fun u => q (z - u)) t| ≤ (2 * C) * t ^ (-1 - b) := by
    intro t ht
    rw [deriv_comp_const_sub, abs_neg]
    have hp : (z - t - a) ^ (-1 - b) ≤ t ^ (-1 - b) :=
      Real.rpow_le_rpow_of_nonpos ht.1 (by dsimp [R] at ht; linarith [ht.2]) (by linarith)
    have he := hbound (z - t) (hright t ht)
    rw [sub_sub_cancel] at he
    nlinarith [mul_le_mul_of_nonneg_left hp hC]
  have hil : IntervalIntegrable (fun t => q (a + t)) volume 0 R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
    exact integrableOn_of_deriv_rpow_bound hb hb1 (by positivity) hR hdl hbl
  have hir : IntervalIntegrable (fun t => q (z - t)) volume 0 R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
    exact integrableOn_of_deriv_rpow_bound hb hb1 (by positivity) hR hdr hbr
  have hi₁ : IntervalIntegrable q volume a (a + R) := by
    simpa [add_comm, add_left_comm, add_assoc] using hil.comp_add_left (-a)
  have hi₂ : IntervalIntegrable q volume (a + R) z := by
    have heq : z - R = a + R := by dsimp [R]; ring
    simpa [heq] using (hir.comp_sub_left z).symm
  refine ⟨hi₁.trans hi₂, ?_⟩
  let Kl := 3 * |q (a + R)| + (2 * C) / b / (1 - b) + 2 * ((2 * C) / b)
  let Kr := 3 * |q (z - R)| + (2 * C) / b / (1 - b) + 2 * ((2 * C) / b)
  refine ⟨Kl + Kr, max 1 R⁻¹, by dsimp [Kl, Kr]; positivity, le_max_left _ _, ?_⟩
  intro χ c hfreq hχ hn
  have hf : 1 ≤ ‖c‖ := (le_max_left _ _).trans hfreq
  have hcp : 0 < ‖c‖ := lt_of_lt_of_le zero_lt_one hf
  have hfR : ‖c‖⁻¹ ≤ R := (inv_le_comm₀ hcp hR).mpr ((le_max_right _ _).trans hfreq)
  have hl := norm_oscillatory_integral_le_rpow hb hb1 (by positivity : 0 ≤ 2 * C)
    hR hdl hbl hf hfR
    (χ := fun t => χ (a + t)) (c := c)
    (fun t => (hχ (a + t)).comp_const_add a t)
    (fun t => hn (a + t))
  have hr := norm_oscillatory_integral_le_rpow hb hb1 (by positivity : 0 ≤ 2 * C)
    hR hdr hbr (c := -c) (by simpa using hf) (by simpa using hfR)
    (χ := fun t => χ (z - t))
    (fun t => by simpa only [neg_mul] using (hχ (z - t)).comp_const_sub z t)
    (fun t => hn (z - t))
  have hχc : Continuous χ := continuous_iff_continuousAt.mpr fun t => (hχ t).continuousAt
  have hp₁ : IntervalIntegrable (fun t => (q t : ℂ) * χ t) volume a (a + R) :=
    (show IntervalIntegrable (fun t => (q t : ℂ)) volume a (a + R) from
      ⟨Complex.ofRealCLM.integrable_comp hi₁.1, Complex.ofRealCLM.integrable_comp hi₁.2⟩).mul_continuousOn hχc.continuousOn
  have hp₂ : IntervalIntegrable (fun t => (q t : ℂ) * χ t) volume (a + R) z :=
    (show IntervalIntegrable (fun t => (q t : ℂ)) volume (a + R) z from
      ⟨Complex.ofRealCLM.integrable_comp hi₂.1, Complex.ofRealCLM.integrable_comp hi₂.2⟩).mul_continuousOn hχc.continuousOn
  rw [intervalIntegral.integral_comp_add_left (fun u => (q u : ℂ) * χ u) a] at hl
  simp only [add_zero] at hl
  rw [intervalIntegral.integral_comp_sub_left (fun u => (q u : ℂ) * χ u) z] at hr
  simp only [sub_zero, norm_neg] at hr
  rw [show z - R = a + R by dsimp [R]; ring] at hr
  rw [← integral_add_adjacent_intervals hp₁ hp₂]
  apply (norm_add_le _ _).trans
  dsimp [Kl, Kr]
  rw [show z - R = a + R by dsimp [R]; ring]
  nlinarith [hl, hr]

end Riesz1.PuncturedDerivative
