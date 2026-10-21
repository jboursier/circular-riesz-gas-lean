/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Herbst.Herbst
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Gaussian concentration from the Herbst bound

The Chernoff method turns the Herbst bound `Riesz1.herbst_log_mgf_le` into a tail bound.
For a bounded `C¹` function `F` with gradient bounded by `L > 0` and `t ≥ 0`, the mass of
`{x | t ≤ F x - ∫ F}` is at most `exp (-t² / (2 w L²))`. The proof evaluates the Herbst bound at
the parameter `s = t / (w L²)`, which minimises the Chernoff exponent.
-/

public section

open MeasureTheory Filter Topology Set
namespace Riesz1

/-- **Gaussian concentration.** Let `μ` be a probability measure on `ℝ^d` satisfying the
logarithmic Sobolev inequality of `Riesz1.herbst_log_mgf_le` with coefficient `w > 0`. Let `F` be a
bounded `C¹` function whose gradient is bounded by `L > 0`. Then for every `t ≥ 0`,
`μ {x | t ≤ F x - ∫ F dμ} ≤ exp (-t² / (2 w L²))`. -/
theorem herbst_concentration {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] (w : ℝ) (hw : 0 < w)
    (hLSI : ∀ q : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 q →
      (∃ C, ∀ x, |q x| ≤ C) → (∃ C, ∀ x, ‖fderiv ℝ q x‖ ≤ C) →
      ∫ x, q x ^ 2 * Real.log (q x ^ 2) ∂μ -
          (∫ x, q x ^ 2 ∂μ) * Real.log (∫ x, q x ^ 2 ∂μ)
        ≤ 2 * w * ∫ x, ‖fderiv ℝ q x‖ ^ 2 ∂μ)
    (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ContDiff ℝ 1 F) (hFb : ∃ C, ∀ x, |F x| ≤ C)
    (L : ℝ) (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (hLpos : 0 < L) {t : ℝ} (ht : 0 ≤ t) :
    μ {x | t ≤ F x - ∫ y, F y ∂μ} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * w * L ^ 2))) := by
  obtain ⟨C, hC⟩ := hFb
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∫ y, F y ∂μ := ⟨_, rfl⟩
  rw [← hA]
  have hwne : w ≠ 0 := hw.ne'
  have hLne : L ≠ 0 := hLpos.ne'
  -- The Chernoff parameter.
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = t / (w * L ^ 2) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by
    rw [hs]
    exact div_nonneg ht (mul_nonneg hw.le (sq_nonneg L))
  have hcont : Continuous F := hF.continuous
  -- The centred function `F - A` is bounded and continuous, so its exponential moments exist.
  have hX : ∀ x, |F x - A| ≤ C + |A| := fun x => by
    rw [sub_eq_add_neg]
    exact (abs_add_le _ _).trans (by rw [abs_neg]; linarith [hC x])
  have hint : Integrable (fun ω => Real.exp (s * (F ω - A))) μ :=
    herbst_integrable_of_bounded (C := Real.exp (|s| * (C + |A|)))
      (Real.continuous_exp.comp (continuous_const.mul (hcont.sub continuous_const)))
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact herbst_exp_le hX s x)
  -- The Chernoff bound with the centred function.
  have hchern := ProbabilityTheory.measure_ge_le_exp_mul_mgf (μ := μ)
    (X := fun x => F x - A) t hs0 hint
  -- The moment generating function of the centred function factors as `M(s) exp (-s A)`.
  have hfac : ∀ x, Real.exp (s * (F x - A)) = Real.exp (s * F x) * Real.exp (-(s * A)) :=
    fun x => by
      rw [← Real.exp_add]
      congr 1
      ring
  have hmgf : ProbabilityTheory.mgf (fun x => F x - A) μ s
      = (∫ x, Real.exp (s * F x) ∂μ) * Real.exp (-(s * A)) := by
    simp only [ProbabilityTheory.mgf, hfac, integral_mul_const]
  -- The Herbst bound at the parameter `s` gives `M(s) ≤ exp (s A + (w/2) s² L²)`.
  have hmain := herbst_log_mgf_le μ w hw hLSI F hF ⟨C, hC⟩ L hL s
  rw [← hA] at hmain
  have hpos := herbst_integral_exp_pos (μ := μ) hcont hC s
  have hle : ∫ x, Real.exp (s * F x) ∂μ ≤ Real.exp (s * A + w / 2 * s ^ 2 * L ^ 2) :=
    (Real.log_le_iff_le_exp hpos).mp hmain
  -- Combine the Chernoff bound with the Herbst bound.
  have hbound : μ.real {x | t ≤ F x - A}
      ≤ Real.exp (-(s * t) + w / 2 * s ^ 2 * L ^ 2) := by
    calc μ.real {x | t ≤ F x - A}
        ≤ Real.exp (-s * t) * ProbabilityTheory.mgf (fun x => F x - A) μ s := hchern
      _ = Real.exp (-s * t) * ((∫ x, Real.exp (s * F x) ∂μ) * Real.exp (-(s * A))) := by
          rw [hmgf]
      _ ≤ Real.exp (-s * t) * (Real.exp (s * A + w / 2 * s ^ 2 * L ^ 2) * Real.exp (-(s * A))) := by
          gcongr
      _ = Real.exp (-(s * t) + w / 2 * s ^ 2 * L ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
  -- The exponent at the chosen parameter is `-t² / (2 w L²)`.
  have hval : -(s * t) + w / 2 * s ^ 2 * L ^ 2 = -t ^ 2 / (2 * w * L ^ 2) := by
    rw [hs]
    field_simp
    ring
  rw [hval] at hbound
  calc μ {x | t ≤ F x - A}
      = ENNReal.ofReal (μ.real {x | t ≤ F x - A}) :=
        (ofReal_measureReal (measure_ne_top μ _)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * w * L ^ 2))) :=
        ENNReal.ofReal_le_ofReal hbound

end Riesz1
