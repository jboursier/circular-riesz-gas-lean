/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Tactic

/-!
# Absolutely convergent singular integrals of bounded Hölder functions

The continuity argument in the paper uses a singular integral of order `τ`
applied to a bounded function of Hölder exponent `r > τ`. Its integrand has an integrable
majorant independent of the evaluation point. These lemmas prove absolute convergence,
continuity, and a uniform bound without smoothness or a principal value.
-/

public section

open MeasureTheory Set Metric

namespace Riesz1

/-- An integrable envelope for the singular residual: the local Hölder bound plus a
bounded-function tail, with the tail extended continuously across the origin. -/
noncomputable def holderSingularEnvelope (τ r B : ℝ) (u : ℝ) : ℝ :=
  (ball (0 : ℝ) 1).indicator (fun v => B * |v| ^ (r - 1 - τ)) u +
    (2 * B * 2 ^ (1 + τ)) * (1 + |u|) ^ (-(1 + τ))

theorem holderSingularEnvelope_nonneg {τ r B : ℝ} (hB : 0 ≤ B) (u : ℝ) :
    0 ≤ holderSingularEnvelope τ r B u := by
  unfold holderSingularEnvelope
  apply add_nonneg
  · exact indicator_nonneg (fun v _ => mul_nonneg hB (Real.rpow_nonneg (abs_nonneg v) _)) u
  · positivity

theorem integrable_holderSingularEnvelope {τ r B : ℝ} (hτ : 0 < τ) (hr : τ < r) :
    Integrable (holderSingularEnvelope τ r B) := by
  have hlocal : IntegrableOn (fun u : ℝ => B * |u| ^ (r - 1 - τ)) (ball 0 1) := by
    apply integrableOn_ball_of_norm_le_rpow (C := |B|) (α := 1 + τ - r) (by simp)
      (by norm_num; linarith)
    · filter_upwards [] with u
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg u) _)]
      simp only [Real.norm_eq_abs]
      have he : -(1 + τ - r) = r - 1 - τ := by ring
      rw [he]
    · exact (measurable_const.mul ((continuous_abs.measurable : Measurable (fun u : ℝ => |u|)).pow_const _)).aestronglyMeasurable
  have htail : Integrable (fun u : ℝ => (1 + |u|) ^ (-(1 + τ))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (μ := volume) (E := ℝ) (r := 1 + τ) (by simp; linarith))
  exact (hlocal.integrable_indicator measurableSet_ball).add (htail.const_mul _)

/-- The envelope estimate only needs bounds on the residual. It applies to parameters in
any space, including a circle of arbitrary length. -/
theorem norm_singular_residual_le_envelope {τ r B : ℝ} (hτ : 0 < τ) (hB : 0 ≤ B)
    {v u : ℝ} (hsmall : |v| ≤ B * |u| ^ r) (hlarge : |v| ≤ 2 * B) (hu : u ≠ 0) :
    ‖v * |u| ^ (-(1 + τ))‖ ≤ holderSingularEnvelope τ r B u := by
  have hu0 : 0 < |u| := abs_pos.mpr hu
  have hpow : 0 ≤ |u| ^ (-(1 + τ)) := Real.rpow_nonneg hu0.le _
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hpow]
  unfold holderSingularEnvelope
  by_cases hnear : |u| < 1
  · rw [indicator_of_mem (mem_ball_zero_iff.mpr (by simpa only [Real.norm_eq_abs] using hnear))]
    have he : r + -(1 + τ) = r - 1 - τ := by ring
    calc |v| * |u| ^ (-(1 + τ))
        ≤ (B * |u| ^ r) * |u| ^ (-(1 + τ)) := mul_le_mul_of_nonneg_right hsmall hpow
      _ = B * |u| ^ (r - 1 - τ) := by rw [mul_assoc, ← Real.rpow_add hu0, he]
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · rw [indicator_of_notMem (by simpa only [mem_ball_zero_iff, Real.norm_eq_abs] using hnear),
      zero_add]
    have hbase : 0 < 1 + |u| := by positivity
    have hexp : |u| ^ (-(1 + τ)) ≤ 2 ^ (1 + τ) * (1 + |u|) ^ (-(1 + τ)) := by
      have hrat : (1 + |u|) / |u| ≤ 2 := (div_le_iff₀ hu0).mpr (by linarith)
      have h := Real.rpow_le_rpow (by positivity) hrat (show 0 ≤ 1 + τ by linarith)
      rw [Real.div_rpow hbase.le hu0.le] at h
      rw [Real.rpow_neg hu0.le, Real.rpow_neg hbase.le]
      have hp := Real.rpow_pos_of_pos hu0 (1 + τ)
      have hq := Real.rpow_pos_of_pos hbase (1 + τ)
      rw [← div_eq_mul_inv, le_div_iff₀ hq, inv_mul_eq_div, div_le_iff₀ hp]
      exact (div_le_iff₀ hp).mp h
    calc |v| * |u| ^ (-(1 + τ)) ≤ (2 * B) * |u| ^ (-(1 + τ)) :=
        mul_le_mul_of_nonneg_right hlarge hpow
      _ ≤ (2 * B) * (2 ^ (1 + τ) * (1 + |u|) ^ (-(1 + τ))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring

/-- A bounded Hölder residual of order strictly larger than `τ` gives an absolutely
integrable singular kernel, uniformly in its parameter. -/
theorem integrable_singular_residual {X : Type*} {F : X → ℝ → ℝ} {τ r B : ℝ}
    (hτ : 0 < τ) (hr : τ < r) (hB : 0 ≤ B)
    (hmeas : ∀ x, Measurable (F x))
    (hsmall : ∀ x u, |F x u| ≤ B * |u| ^ r)
    (hlarge : ∀ x u, |F x u| ≤ 2 * B) (x : X) :
    Integrable (fun u => F x u * |u| ^ (-(1 + τ))) := by
  refine Integrable.mono' (integrable_holderSingularEnvelope (B := B) hτ hr)
    ((hmeas x).mul ((continuous_abs.measurable : Measurable (fun u : ℝ => |u|)).pow_const _)).aestronglyMeasurable ?_
  filter_upwards [show ∀ᵐ u : ℝ, u ≠ 0 by rw [ae_iff]; simp] with u hu
  exact norm_singular_residual_le_envelope hτ hB (hsmall x u) (hlarge x u) hu

/-- Continuity of the singular integral follows by dominated convergence. The same envelope
works for every parameter and hence for every length in an application to enlarged circles. -/
theorem continuous_singular_residual_integral {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {F : X → ℝ → ℝ} {τ r B : ℝ}
    (hτ : 0 < τ) (hr : τ < r) (hB : 0 ≤ B)
    (hmeas : ∀ x, Measurable (F x)) (hcont : ∀ u, Continuous (fun x => F x u))
    (hsmall : ∀ x u, |F x u| ≤ B * |u| ^ r)
    (hlarge : ∀ x u, |F x u| ≤ 2 * B) :
    Continuous (fun x => ∫ u, F x u * |u| ^ (-(1 + τ))) := by
  apply continuous_of_dominated (bound := holderSingularEnvelope τ r B)
  · intro x
    exact ((hmeas x).mul ((continuous_abs.measurable : Measurable (fun u : ℝ => |u|)).pow_const _)).aestronglyMeasurable
  · intro x
    filter_upwards [show ∀ᵐ u : ℝ, u ≠ 0 by rw [ae_iff]; simp] with u hu
    exact norm_singular_residual_le_envelope hτ hB (hsmall x u) (hlarge x u) hu
  · exact integrable_holderSingularEnvelope hτ hr
  · exact ae_of_all _ (fun u => (hcont u).mul continuous_const)

/-- A uniform bound for the singular integral. Its right side depends only on the Hölder
data and the two exponents. -/
theorem abs_singular_residual_integral_le {X : Type*} {F : X → ℝ → ℝ} {τ r B : ℝ}
    (hτ : 0 < τ) (hB : 0 ≤ B)
    (hr : τ < r) (hsmall : ∀ x u, |F x u| ≤ B * |u| ^ r)
    (hlarge : ∀ x u, |F x u| ≤ 2 * B) (x : X) :
    |∫ u, F x u * |u| ^ (-(1 + τ))| ≤ ∫ u, holderSingularEnvelope τ r B u := by
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (integrable_holderSingularEnvelope hτ hr)
  filter_upwards [show ∀ᵐ u : ℝ, u ≠ 0 by rw [ae_iff]; simp] with u hu
  exact norm_singular_residual_le_envelope hτ hB (hsmall x u) (hlarge x u) hu

end Riesz1
