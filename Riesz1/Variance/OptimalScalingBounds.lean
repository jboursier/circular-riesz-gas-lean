/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityConsequences
public import Riesz1.Bridges.FluctuationSquare
public import Riesz1.ToMathlib.VarianceFrozenIntegral
public import Mathlib.Tactic

/-!
# Finiteness and exponent arithmetic for optimal variance

The unconditional parts of Theorem 2 and
the final exponent calculation, including unit scale and endpoint exponents.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- The real representative in the profile carrier is square integrable. -/
theorem optimalScaling_profile_memLp (v : Profile) : MemLp v.val 2 volume := by
  have hv := v.property.re
  change MemLp (fun x => (v.val x : ℂ).re) 2 volume at hv
  simpa only [Complex.ofReal_re] using hv

/-- Every real square-integrable circle profile gives an integrable statistic. -/
theorem optimalScaling_fluctuation_integrable (P : Parameters) (N : ℕ+) (v : Profile) :
    Integrable (fluctuation ⟨v.val, (optimalScaling_profile_memLp v).integrable one_le_two⟩)
      (gibbsMeasure P N) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  exact (memLp_fluctuation P N (optimalScaling_profile_memLp v)).integrable one_le_two

/-- Finiteness is established before the extended variance is converted to a real. -/
theorem optimalScaling_fluctuation_variance_finite (P : Parameters) (N : ℕ+) (v : Profile) :
    variance (gibbsMeasure P N)
      (fluctuation ⟨v.val, (optimalScaling_profile_memLp v).integrable one_le_two⟩)
      (optimalScaling_fluctuation_integrable P N v) < ⊤ := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  rw [variance_eq_ofReal_integral_sq _ _
    (memLp_fluctuation P N (optimalScaling_profile_memLp v))]
  exact ENNReal.ofReal_lt_top

/-- The circle and normalization assertions of Theorem 2. -/
theorem optimalScaling_circle_finiteness (P : Parameters) (p : Profile)
    (ell : Scales) (α : ℝ) (d : TestData) (h : Admissible P p ell α d) :
    ModelWellDefined P ∧ ∀ N,
      CircleSobolev ((1 - P.val.2) / 2) (fun x => (testAtScale p (ell N) x : ℂ)) ∧
        circleVariance P p (ell N) < ⊤ :=
  ⟨modelWellDefined P, fun N => ⟨admissible_circleSobolev P p ell α d h N,
    admissible_circleVariance_finite P p ell α d h N⟩⟩

/-- The complete compact-profile assertion of Theorem 2. -/
theorem optimalScaling_compact_comparison (P : Parameters) (p : Profile) (α : ℝ)
    (d : TestData) (hex : ∃ ell : Scales, Admissible P p ell α d)
    (hp : CompactProfile p) :
    ∃ f0 : Lp ℂ 2 (volume : Measure ℝ),
      RepresentsZeroExtension p f0 ∧ LineSobolev ((1 - P.val.2) / 2) f0 ∧
      lineVariance P f0 < ⊤ ∧ ∃ C1 : ℝ, 0 < C1 ∧ ∀ a : Scale,
        CircleSobolev ((1 - P.val.2) / 2) (fun x => (testAtScale p a x : ℂ)) ∧
        circleVariance P p a < ⊤ ∧
        |(circleVariance P p a).toReal - (lineVariance P f0).toReal| ≤
          C1 * a.val ^ (2 - P.val.2) := by
  obtain ⟨ell, h⟩ := hex
  let f0 := (zeroExtensionL2 p).toLp _
  have hf0 : RepresentsZeroExtension p f0 := (zeroExtensionL2 p).coeFn_toLp
  exact ⟨f0, hf0, admissible_compact_variance P p hp ell α d h f0 hf0⟩

namespace Internal

/-- Exact exponent identity in the final proof of optimal variance. -/
theorem optimalScaling_exponent (s α : ℝ) :
    2 * s - 2 + max 1 (2 * (1 - s + α)) = max (2 * s - 1) (2 * α) := by
  rw [add_max]
  congr 1 <;> ring

/-- Multiplication by the master-equation factor gives the target rate. -/
theorem optimalScaling_loop_power {K : ℝ} (hK : 0 < K) (s α δ : ℝ) :
    K ^ (2 * s - 2) * K ^ (δ + max 1 (2 * (1 - s + α))) =
      K ^ (max (2 * s - 1) (2 * α) + δ) := by
  rw [← Real.rpow_add hK]
  congr 1
  linarith [optimalScaling_exponent s α]

/-- Combine the reduction and loop estimates without losing the small exponent. -/
theorem optimalScaling_combine {K s α δ ε A B E V : ℝ}
    (hK : 1 ≤ K) (hδε : δ ≤ ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hred : E ≤ A * (K ^ (2 * s - 2) * V +
      K ^ (max (2 * s - 1) (2 * α) + δ)))
    (hloop : V ≤ B * K ^ (δ + max 1 (2 * (1 - s + α)))) :
    E ≤ A * (B + 1) * K ^ (max (2 * s - 1) (2 * α) + ε) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hr : K ^ (2 * s - 2) * V ≤
      B * K ^ (max (2 * s - 1) (2 * α) + δ) := by
    calc
      _ ≤ K ^ (2 * s - 2) * (B * K ^ (δ + max 1 (2 * (1 - s + α)))) :=
        mul_le_mul_of_nonneg_left hloop (Real.rpow_nonneg hK0.le _)
      _ = _ := by rw [mul_left_comm, optimalScaling_loop_power hK0]
  calc
    E ≤ A * ((B + 1) * K ^ (max (2 * s - 1) (2 * α) + δ)) :=
      hred.trans (mul_le_mul_of_nonneg_left (by linarith) hA)
    _ = A * (B + 1) * K ^ (max (2 * s - 1) (2 * α) + δ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hK (add_le_add_right hδε _))
      (mul_nonneg hA (by linarith))

end Internal
end Riesz1
