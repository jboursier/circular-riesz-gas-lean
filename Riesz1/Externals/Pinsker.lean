/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.External.Pinsker
public import Riesz1.ToMathlib.PinskerCore

/-!
# Pinsker's inequality: proof of the external statement

This file proves Pinsker's inequality `Riesz1.External.Pinsker` as
`Riesz1.Externals.pinsker_proof`, with the standard axioms only. The statement is not restated:
the theorem has the type `Riesz1.External.Pinsker` itself.

Proof outline. Let `f = dμ/dν`, which is measurable, nonnegative and of integral `1`.

* If `μ` is not absolutely continuous with respect to `ν`, the relative entropy is infinite and
  the claim is trivial.
* Otherwise `etvDist μ ν = ENNReal.ofReal (∫ |1 - f| dν)` and
  `klDiv μ ν = ENNReal.ofReal (∫ klFun ∘ f dν)` by Mathlib's density formulas.
* The analytic core `Riesz1.integral_abs_one_sub_sq_le` gives `(∫ |1 - f|)² ≤ 4 ∫ klFun ∘ f`.
  Hence `(etvDist μ ν / 2)² ≤ ∫ klFun ∘ f ≤ 2 klDiv μ ν`.

The constant obtained is `1` in place of the constant `2` in the statement, so the claim, which
is weaker, follows.
-/

@[expose] public section

open MeasureTheory InformationTheory
open scoped ENNReal

namespace Riesz1.Externals

/-- Pinsker's inequality in the form `Riesz1.External.Pinsker`. -/
theorem pinsker_proof : Riesz1.External.Pinsker := by
  intro Ω _ μ ν hμ hν
  by_cases hac : μ ≪ ν
  swap
  · simp [klDiv_of_not_ac hac]
  -- The density `f = dμ/dν`, as a real function.
  have hf_meas : Measurable fun x => (μ.rnDeriv ν x).toReal :=
    (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hf_nonneg : ∀ x, 0 ≤ (μ.rnDeriv ν x).toReal := fun x => ENNReal.toReal_nonneg
  have hf_int : Integrable (fun x => (μ.rnDeriv ν x).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv μ ν).aemeasurable
      Measure.integrable_rnDeriv.hasFiniteIntegral.ne
  have hf_one : ∫ x, (μ.rnDeriv ν x).toReal ∂ν = 1 := by
    rw [Measure.integral_toReal_rnDeriv hac, probReal_univ]
  -- The relative entropy as the integral of `klFun ∘ f`.
  have hk_nonneg : 0 ≤ᵐ[ν] fun x => klFun (μ.rnDeriv ν x).toReal :=
    ae_of_all _ fun x => klFun_nonneg ENNReal.toReal_nonneg
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  by_cases hK : ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν = ⊤
  · rw [hK, ENNReal.mul_top two_ne_zero]
    exact le_top
  have hk_int : Integrable (fun x => klFun (μ.rnDeriv ν x).toReal) ν :=
    (lintegral_ofReal_ne_top_iff_integrable
      (measurable_klFun.comp hf_meas).aestronglyMeasurable hk_nonneg).1 hK
  have hK_eq : ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν
      = ENNReal.ofReal (∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal hk_int hk_nonneg).symm
  -- The total variation as the integral of `|1 - f|`.
  have htv : etvDist μ ν = ENNReal.ofReal (∫ x, |1 - (μ.rnDeriv ν x).toReal| ∂ν) := by
    rw [← ofReal_tvDist, tvDist_eq_integral_abs_rnDeriv_of_ac hac]
  rw [hK_eq, htv]
  -- The analytic core, then the arithmetic of the `ENNReal` inequality.
  have hcore := Riesz1.integral_abs_one_sub_sq_le hf_meas hf_nonneg hf_int hf_one hk_int
  have hT0 : 0 ≤ ∫ x, |1 - (μ.rnDeriv ν x).toReal| ∂ν := integral_nonneg fun x => abs_nonneg _
  have hK0 : 0 ≤ ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν :=
    integral_nonneg fun x => klFun_nonneg ENNReal.toReal_nonneg
  have h2 : ENNReal.ofReal (∫ x, |1 - (μ.rnDeriv ν x).toReal| ∂ν) / 2
      = ENNReal.ofReal ((∫ x, |1 - (μ.rnDeriv ν x).toReal| ∂ν) / 2) := by
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
  have h3 : (2 : ℝ≥0∞) * ENNReal.ofReal (∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν)
      = ENNReal.ofReal (2 * ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν) := by
    rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
  rw [h2, h3, ← ENNReal.ofReal_pow (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [hcore, hK0])

end Riesz1.Externals

end
