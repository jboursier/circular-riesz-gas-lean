/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BLGlobal
public import Riesz1.HelfferSjostrand.BLContinuity
public import Riesz1.HelfferSjostrand.BLPrekopa
public import Mathlib.Probability.Moments.Basic

/-!
# Normalized exponential comparison for Brascamp–Lieb

The midpoint Prékopa–Leindler statement and the uniform midpoint
majorant imply the comparison whose second variation is the variance bound.
-/

public section

noncomputable section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology

namespace Riesz1

variable {d : ℕ} {U W : Set (EuclideanSpace ℝ (Fin d))}
variable {V F : EuclideanSpace ℝ (Fin d) → ℝ}

/-- Squared, normalized form of the midpoint integral comparison. -/
theorem bl_prekopa_tilted (hPL : Riesz1.External.PrekopaLeindler) (hd : 0 < d)
    (hU : Bornology.IsBounded U) (ho : IsOpen U) (hc : Convex ℝ U)
    (hV : ContinuousOn V (closure U))
    (A B C : EuclideanSpace ℝ (Fin d) → ℝ)
    (hA : ContinuousOn A (closure U)) (hB : ContinuousOn B (closure U))
    (hC : ContinuousOn C (closure U))
    (hmid : ∀ x ∈ U, ∀ y ∈ U,
      (-V x + A x) + (-V y + B y) ≤
        2 * (-V ((1 / 2 : ℝ) • (x + y)) + C ((1 / 2 : ℝ) • (x + y)))) :
    (∫ x, Real.exp (A x) ∂((volume.restrict U).tilted (fun x => -V x))) *
        (∫ x, Real.exp (B x) ∂((volume.restrict U).tilted (fun x => -V x))) ≤
      (∫ x, Real.exp (C x) ∂((volume.restrict U).tilted (fun x => -V x))) ^ 2 := by
  obtain ⟨_, _, _, hi⟩ := bl_prekopa_integral hPL hd hU ho hc
    (fun x => -V x + A x) (fun x => -V x + B x) (fun x => -V x + C x)
    (hV.neg.add hA) (hV.neg.add hB) (hV.neg.add hC) hmid
  have hn (D : EuclideanSpace ℝ (Fin d) → ℝ) :
      0 ≤ ∫ x in U, Real.exp (D x) := integral_nonneg (fun x => (Real.exp_pos _).le)
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hi 2
  rw [Real.sq_sqrt (mul_nonneg (hn _) (hn _))] at hs
  rw [integral_exp_tilted, integral_exp_tilted, integral_exp_tilted]
  convert div_le_div_of_nonneg_right hs
    (sq_nonneg (∫ x in U, Real.exp (-V x))) using 1 <;>
    simp only [Pi.add_apply, div_eq_mul_inv, mul_pow, inv_pow]; ring

/-- The exponential comparison holds in a neighborhood of zero, for every
positive quadratic error, with only the Prékopa–Leindler inequality as a hypothesis. -/
theorem bl_mgf_comparison (hPL : Riesz1.External.PrekopaLeindler) (hd : 0 < d)
    (hU : Bornology.IsBounded U) (ho : IsOpen U) (hc : Convex ℝ U)
    (hW : IsOpen W) (hUW : closure U ⊆ W)
    (hV : ContDiffOn ℝ 2 V W) (hF : ContDiffOn ℝ 2 F W)
    {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      mgf F ((volume.restrict U).tilted (fun x => -V x)) ε *
          mgf F ((volume.restrict U).tilted (fun x => -V x)) (-ε) ≤
        (mgf (fun x => sSup (Set.range (fun h : EuclideanSpace ℝ (Fin d) =>
          2 * fderiv ℝ F x h - fderiv ℝ (fderiv ℝ V) x h h)) / 2 + a)
          ((volume.restrict U).tilted (fun x => -V x)) (ε ^ 2)) ^ 2 := by
  let Q (x : EuclideanSpace ℝ (Fin d)) := sSup (Set.range
    (fun h : EuclideanSpace ℝ (Fin d) =>
      2 * fderiv ℝ F x h - fderiv ℝ (fderiv ℝ V) x h h))
  have hQ : ContinuousOn Q (closure U) :=
    bl_hessian_energy_continuousOn hU hW hUW hV hF hκ hb
  obtain ⟨ε₀, hε₀, hmaj⟩ := bl_uniform_midpoint_majorant hU hc hW hUW hV hF hκ hb ha
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε₀] with ε hε
  have hε' : |ε| < ε₀ := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hε
  apply bl_prekopa_tilted hPL hd hU ho hc (hV.continuousOn.mono hUW)
    (fun x => ε * F x) (fun x => -ε * F x) (fun x => ε ^ 2 * (Q x / 2 + a))
    (continuousOn_const.mul (hF.continuousOn.mono hUW))
    (continuousOn_const.mul (hF.continuousOn.mono hUW))
    (continuousOn_const.mul ((hQ.div_const 2).add continuousOn_const))
  intro x hx y hy
  let z := (1 / 2 : ℝ) • (x + y)
  let h := (1 / 2 : ℝ) • (x - y)
  have hz : z ∈ U := by
    simpa only [z, smul_add] using hc hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hp : z + h = x := by dsimp [z, h]; module
  have hm : z - h = y := by dsimp [z, h]; module
  have hi := hmaj ε hε' z hz h (hp ▸ hx) (hm ▸ hy)
  rw [hp, hm] at hi
  change (-V x + ε * F x) + (-V y + -ε * F y) ≤
    2 * (-V z + ε ^ 2 * (Q z / 2 + a))
  dsimp only [Q] at *
  linarith

end Riesz1

end
