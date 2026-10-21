/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleMollifyBounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Smoothing commutes with an absolutely continuous derivative

The derivative of the original transport can be singular at its marked points.
Absolute continuity suffices for commuting its weak derivative with the
circle regularization. Global classical differentiability is not assumed.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1.Internal

theorem deriv_mollifyLine_of_absolutelyContinuous {ρ f : ℝ → ℝ}
    (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) (hf : Continuous f)
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) (x : ℝ) :
    deriv (mollifyLine ρ h f) x = mollifyLine ρ h (deriv f) x := by
  let κ := scaledMollifier ρ h
  let a := x - h
  let b := x + h
  have hκ : ContDiff ℝ ∞ κ := contDiff_scaledMollifier hρ
  have hcomp : ContDiff ℝ 1 (fun y : ℝ => κ (x - y)) :=
    (hκ.of_le (by simp)).comp (contDiff_const.sub contDiff_id)
  have hdκ (y : ℝ) : deriv (fun z : ℝ => κ (x - z)) y = -deriv κ (x - y) := by
    have hd := ((hκ.differentiable (by simp)) (x - y)).hasDerivAt
    simpa only [Function.comp_def, mul_neg_one] using
      (hd.comp y ((hasDerivAt_id y).const_sub x)).deriv
  have hend (y : ℝ) (hy : h / 2 ≤ |x - y|) : κ (x - y) = 0 :=
    scaledMollifier_eq_zero hρ hh hy
  have hea : κ (x - a) = 0 := hend a (by dsimp [a]; rw [sub_sub_cancel, abs_of_pos hh]; linarith)
  have heb : κ (x - b) = 0 := hend b (by
    dsimp [b]
    rw [show x - (x + h) = -h by ring, abs_neg, abs_of_pos hh]
    linarith)
  have hparts := (hAC a b).integral_mul_deriv_eq_deriv_mul
    hcomp.contDiffOn.absolutelyContinuousOnInterval
  simp_rw [hdκ, mul_neg] at hparts
  rw [intervalIntegral.integral_neg, hea, heb, mul_zero, mul_zero,
    sub_self, zero_sub, neg_inj] at hparts
  have hsupport (φ : ℝ → ℝ) (hφ : ∀ y, h / 2 ≤ |y| → φ y = 0)
      (g : ℝ → ℝ) : Function.support (fun y => g y * φ (x - y)) ⊆ Ioc a b := by
    intro y hy
    have hne : φ (x - y) ≠ 0 := fun he => hy (by simp [he])
    have ht : |x - y| < h / 2 := lt_of_not_ge (fun he => hne (hφ _ he))
    have hxy := abs_lt.mp ht
    dsimp [a, b]
    exact ⟨by linarith, by linarith⟩
  have hfull (φ : ℝ → ℝ) (hφ : ∀ y, h / 2 ≤ |y| → φ y = 0) (g : ℝ → ℝ) :
      (∫ y in a..b, g y * φ (x - y)) = ∫ y, g y * φ (x - y) :=
    intervalIntegral.integral_eq_integral_of_support_subset (hsupport φ hφ g)
  rw [hfull (deriv κ) (fun _ hy => deriv_scaledMollifier_eq_zero hρ hh hy),
    hfull κ (fun _ hy => scaledMollifier_eq_zero hρ hh hy)] at hparts
  rw [(hasDerivAt_mollifyLine hρ hh hf.locallyIntegrable x).deriv]
  exact hparts

theorem deriv_circleMollify_of_absolutelyContinuous {ρ f : ℝ → ℝ}
    (hρ : IsMollifier ρ) {L h : ℝ} (hL : 0 < L) (hh : 0 < h)
    (hf : Continuous f) (hp : Function.Periodic f L)
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) (x : ℝ) :
    deriv (circleMollify ρ L h f) x = circleMollify ρ L h (deriv f) x := by
  have hd : LocallyIntegrable (deriv f) volume := by
    intro y
    refine ⟨Icc (y - 1) (y + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
      (hAC (y - 1) (y + 1)).intervalIntegrable_deriv
  have he : circleMollify ρ L h f = mollifyLine ρ h f :=
    funext (circleMollify_eq_mollifyLine hρ hL hh hf.locallyIntegrable hp)
  rw [he, deriv_mollifyLine_of_absolutelyContinuous hρ hh hf hAC,
    circleMollify_eq_mollifyLine hρ hL hh hd (periodic_deriv hp)]

end Riesz1.Internal
