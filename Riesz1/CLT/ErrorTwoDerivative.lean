/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorTwoInput
public import Riesz1.CLT.ErrorTwoRates
public import Riesz1.ToMathlib.BoundedCovarianceVariance
public import Riesz1.Variance.VarAlPiecesCompleteMacro
public import Riesz1.Kernel.TransportScaledConvolution
import all Riesz1.Variance.LoopForce

/-!
# The a-priori estimate for one transport derivative piece

The second variance step in the proof of the second error bound in Theorem 3,
for a single piece satisfying the `gradWeightTwo` envelope. Constants
precede `N`, the scale and the envelope amplitude. This file does not
assert a uniform decomposition of the complete regularized transport.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace Riesz1.Internal

/-- The circular distance agrees with the absolute value of the central representative. -/
theorem errorTwo_circDist_centralRep (L : Length) (x : ℝ) :
    circDist L.val x = |centralRep L (x : Circle L)| := by
  obtain ⟨n, hn⟩ := centralRep_coe_eq L x
  have hc := centralRep_mem_Ico L (x : Circle L)
  set c := centralRep L (x : Circle L)
  have habs : |c| ≤ L.val / 2 := by
    rw [abs_le]
    constructor <;> dsimp only [c] <;> linarith [hc.1, hc.2]
  have hx : x = c + (n : ℝ) * L.val := by rw [hn]; ring
  rw [hx, circDist_add_int_mul L.property c n, circDist_eq_abs L.property habs]

/-- The second gradient-splitting envelope is bounded by the a-priori
envelope with radius one, including its common boundary point. -/
theorem errorTwo_weightTwo_le (s b K L x : ℝ) :
    gradWeightTwo s b K L x ≤
      (if circDist L x ≤ 1 then ((max (circDist L x) K⁻¹) ^ (1 + b))⁻¹ else 0) +
        (if 1 ≤ circDist L x then (circDist L x ^ (3 - s))⁻¹ else 0) := by
  unfold gradWeightTwo
  by_cases hd : circDist L x < 1
  · simp only [hd, hd.le, not_le.mpr hd, ite_true, ite_false, add_zero]
    rw [Real.rpow_neg (le_trans (circDist_nonneg L x) (le_max_left _ _))]
  · simp only [hd, not_lt.mp hd, ite_false, ite_true]
    rw [show s - 3 = -(3 - s) by ring, Real.rpow_neg (circDist_nonneg L x)]
    apply le_add_of_nonneg_left
    split_ifs
    · exact inv_nonneg.mpr (Real.rpow_nonneg (le_trans (circDist_nonneg L x) (le_max_left _ _)) _)
    · exact le_rfl

/-- The variance estimate for a single translated envelope-bounded
transport derivative. This is the a-priori application in the proof of the
second error bound in Theorem 3, with both centering and integrability proved.
The constant precedes the scale and the piece. -/
theorem clt_error2_derivative_piece_of_input (hAP : ErrorTwoAPrioriInput)
    (P : Parameters) (b ε c : ℝ) (hb : 0 ≤ b) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (a : Scale), 1 ≤ (N : ℝ) * a.val →
      ∀ (M : ℝ), 0 ≤ M → ∀ ψ : ℝ → ℝ,
        ContDiff ℝ ∞ ψ → Function.Periodic ψ a.val⁻¹ →
        (∀ u, |deriv (deriv ψ) u| ≤
          M * gradWeightTwo P.val.2 b ((N : ℝ) * a.val) a.val⁻¹ (u - c)) →
        ∃ hF : Integrable (fun X : Configuration N =>
          fluctIntegral (fun u => deriv ψ (u / a.val)) N X.val) (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ hF ≤
            ENNReal.ofReal (C * M ^ 2 * (((N : ℝ) * a.val) ^ ε *
              ((N : ℝ) * a.val + ((N : ℝ) * a.val) ^ (2 * b)))) := by
  obtain ⟨C, hC, hbound⟩ := hAP P b hb ε hε 1 one_pos c
  refine ⟨C, hC, fun N a hK M hM ψ hψ hp hd => ?_⟩
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hpd : Function.Periodic (deriv ψ) (observationLength a).val := Riesz1.periodic_deriv hp
  let f : Circle (observationLength a) → ℝ := hpd.lift
  have hf : (fun u : ℝ => f (u : Circle (observationLength a))) = deriv ψ := by
    funext u
    exact hpd.lift_coe u
  have hfc : ContDiff ℝ 1 (fun u : ℝ => f (u : Circle (observationLength a))) := by
    rw [hf]
    exact hdψ.of_le (by simp)
  have hfd : ∀ u : ℝ, |deriv (fun t : ℝ => f (t : Circle (observationLength a))) u| ≤
      M * ((if |centralRep (observationLength a) ((u - c : ℝ) : Circle (observationLength a))| ≤ 1
        then ((max |centralRep (observationLength a) ((u - c : ℝ) : Circle (observationLength a))|
          ((N : ℝ) * a.val)⁻¹) ^ (1 + b))⁻¹ else 0) +
        (if 1 ≤ |centralRep (observationLength a) ((u - c : ℝ) : Circle (observationLength a))|
          then (|centralRep (observationLength a) ((u - c : ℝ) : Circle (observationLength a))| ^
            (3 - P.val.2))⁻¹ else 0)) := by
    intro u
    rw [hf]
    have hh := (hd u).trans (mul_le_mul_of_nonneg_left
      (errorTwo_weightTwo_le P.val.2 b ((N : ℝ) * a.val) (observationLength a).val (u - c)) hM)
    simpa only [errorTwo_circDist_centralRep] using hh
  obtain ⟨hS, hSV⟩ := (hbound N a hK M hM f hfc hfd).2
  let S : Configuration N → ℝ := fun X => ∑ i : Fin (N : ℕ),
    f (((X.val i / a.val : ℝ)) : Circle (observationLength a))
  let m : ℝ := (N : ℝ) * ∫ t in (0 : ℝ)..1, deriv ψ (t / a.val)
  have he : (fun X : Configuration N => fluctIntegral (fun u => deriv ψ (u / a.val)) N X.val) =
      fun X => S X - m := by
    funext X
    unfold fluctIntegral
    dsimp only [S, m]
    congr 1
  rw [he]
  refine ⟨hS.sub (integrable_const m), ?_⟩
  rw [frozenVariance_sub_const hS m]
  apply hSV.trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_left (errorTwo_derivative_power_bound hK P.property.2.2.le b ε)
    (by positivity)

end Riesz1.Internal
