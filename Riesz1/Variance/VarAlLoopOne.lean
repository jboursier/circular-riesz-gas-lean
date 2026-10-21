/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPKernel
public import Riesz1.Variance.LoopIBPMoments
public import Riesz1.Frozen.Variance
import all Riesz1.Variance.LoopForce
import all Riesz1.Variance.LoopForceKernel

/-!
# Uniform one-particle loop variance

The small-particle step of Proposition 5.9. The coefficient is
chosen before the profile and its Lipschitz amplitude. No external
statement is required in this case.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Riesz1

/-- The background bound with its coefficient before the profile and
its Lipschitz amplitude. -/
theorem varAlLoop_background_uniform (s : RieszExponent) :
    ∃ B : ℝ, 0 < B ∧ ∀ (M : NNReal) (f : ℝ → ℝ),
      LipschitzWith M f → Function.Periodic f 1 → ∀ a : ℝ,
        |∫ y in (0 : ℝ)..1, loopKernel s.val f a y| ≤ B * M := by
  obtain ⟨C, hC, hgb⟩ := deriv_hurwitzKernel_bound s.val s.property.1 s.property.2
  let g := fun u : ℝ => u ^ (-s.val) + (1 - u) ^ (-s.val)
  have hg : IntervalIntegrable g volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    exact integrableOn_rpow_majorant s.property.2
  have hg0 : 0 ≤ ∫ u in (0 : ℝ)..1, g u :=
    intervalIntegral.integral_nonneg zero_le_one (fun u hu => by
      dsimp [g]
      exact add_nonneg (Real.rpow_nonneg hu.1 _) (Real.rpow_nonneg (by linarith [hu.2]) _))
  refine ⟨C * (∫ u in (0 : ℝ)..1, g u) + 1, by positivity, ?_⟩
  intro M f hf hp a
  have hbound (u : ℝ) (h0 : 0 < u) (h1 : u < 1) :
      |pvIntegrand s.val f a u| ≤ (C * M) * g u := by
    have hne : (u : UnitAddCircle) ≠ 0 := coe_ne_zero_of_mem_Ioo01 h0 h1
    have hd : 0 < dist (u : UnitAddCircle) 0 := dist_pos.mpr hne
    have hf' : |f (a - u) - f a| ≤ (M : ℝ) * dist (u : UnitAddCircle) 0 := by
      have h := loopScale_lipschitz_increment hf hp a (-u)
      simpa only [← sub_eq_add_neg, AddCircle.coe_neg, dist_zero_right, norm_neg] using h
    have he : dist (u : UnitAddCircle) 0 ^ (-s.val - 1) * dist (u : UnitAddCircle) 0 =
        dist (u : UnitAddCircle) 0 ^ (-s.val) := by
      rw [Real.rpow_sub_one hd.ne', div_mul_cancel₀ _ hd.ne']
    change |deriv (hurwitzKernel s.val) u * (f (a - u) - f a)| ≤ _
    rw [abs_mul]
    calc
      _ ≤ (C * dist (u : UnitAddCircle) 0 ^ (-s.val - 1)) *
          ((M : ℝ) * dist (u : UnitAddCircle) 0) :=
        mul_le_mul (hgb u hne) hf' (abs_nonneg _)
          (mul_nonneg hC.le (Real.rpow_nonneg dist_nonneg _))
      _ = (C * M) * dist (u : UnitAddCircle) 0 ^ (-s.val) := by rw [← he]; ring
      _ ≤ (C * M) * g u := mul_le_mul_of_nonneg_left
        (dist_rpow_le_majorant h0 h1) (by positivity)
  have hae : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 1 := by rw [ae_iff]; simp
  have hb := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (f := pvIntegrand s.val f a) (g := fun u => (C * M) * g u)
    (by
      filter_upwards [hae] with u hu1 hu
      rw [Real.norm_eq_abs]
      exact hbound u hu.1 (lt_of_le_of_ne hu.2 hu1)) (hg.const_mul (C * M))
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hb
  rw [loopScale_integral_kernel_eq s.val hp a, abs_neg]
  exact hb.trans (by nlinarith [M.property])

/-- Proposition 5.9, the one-particle variance estimate for every
Lipschitz periodic transport. The same coefficient works for all profiles
with a common Lipschitz amplitude, including amplitude zero. -/
theorem varAlLoop_one_variance (P : Parameters) :
    letI := (modelWellDefined P 1).2.2
    ∃ C : ℝ, 0 < C ∧ ∀ (M : NNReal) (ψ : ℝ → ℝ),
      LipschitzWith M ψ → Function.Periodic ψ 1 →
      ∃ hF : MemLp (fun X : Configuration 1 => loopFunctional P.val.2 1 ψ X.val)
          2 (gibbsMeasure P 1),
        variance (gibbsMeasure P 1) _ (hF.integrable one_le_two) ≤
          ENNReal.ofReal (C * (M : ℝ) ^ 2) := by
  have := (modelWellDefined P 1).2.2
  obtain ⟨B, hB, hb⟩ := varAlLoop_background_uniform (parametersExponent P)
  refine ⟨9 * B ^ 2, by positivity, ?_⟩
  intro M ψ hψ hp
  have hpt (X : Configuration 1) : |loopFunctional P.val.2 1 ψ X.val| ≤ 3 * B * M := by
    have h1 := hb M ψ hψ hp (X.val 0)
    change |∫ y in (0 : ℝ)..1, loopKernel P.val.2 ψ (X.val 0) y| ≤ B * M at h1
    have h2 : |∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1,
        loopKernel P.val.2 ψ u v| ≤ B * M := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1)
        (f := fun u => ∫ v in (0 : ℝ)..1, loopKernel P.val.2 ψ u v)
        (C := B * M) (fun u _ => by rw [Real.norm_eq_abs]; exact hb M ψ hψ hp u)
      simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h
    have he : loopFunctional P.val.2 1 ψ X.val =
        -(∫ y in (0 : ℝ)..1, loopKernel P.val.2 ψ (X.val 0) y) -
          (∫ u in (0 : ℝ)..1, loopKernel P.val.2 ψ u (X.val 0)) +
          ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, loopKernel P.val.2 ψ u v := by
      simp [loopFunctional]
      rfl
    rw [he, integral_kernel_left_eq]
    have ha := abs_le.mp h1
    have hc := abs_le.mp h2
    exact abs_le.mpr (by constructor <;> linarith)
  let F := fun X : Configuration 1 => loopFunctional P.val.2 1 ψ X.val
  have hm : AEStronglyMeasurable F (gibbsMeasure P 1) :=
    ((measurable_loopFunctional (parametersExponent P) 1 hψ.continuous).comp
      measurable_subtype_coe).aestronglyMeasurable
  have hF : MemLp F 2 (gibbsMeasure P 1) := MemLp.of_bound hm (3 * B * M)
    (ae_of_all _ fun X => by simpa only [Real.norm_eq_abs] using hpt X)
  refine ⟨hF, ?_⟩
  have hvar : ProbabilityTheory.variance F (gibbsMeasure P 1) ≤ 9 * B ^ 2 * (M : ℝ) ^ 2 := by
    calc
      _ ≤ ∫ X, F X ^ 2 ∂gibbsMeasure P 1 :=
        ProbabilityTheory.variance_le_expectation_sq hm
      _ ≤ ∫ _X : Configuration 1, (3 * B * (M : ℝ)) ^ 2 ∂gibbsMeasure P 1 := by
        apply integral_mono (hF.integrable_sq) (integrable_const _)
        intro X
        have h := hpt X
        nlinarith [sq_nonneg (F X - 3 * B * (M : ℝ)),
          sq_nonneg (F X + 3 * B * (M : ℝ)), abs_le.mp h]
      _ = _ := by rw [integral_const]; simp only [probReal_univ, one_smul]; ring
  rw [Riesz1.variance, ← ProbabilityTheory.evariance_eq_lintegral_ofReal,
    ← ProbabilityTheory.ofReal_variance hF]
  exact ENNReal.ofReal_le_ofReal hvar

end Riesz1

end
