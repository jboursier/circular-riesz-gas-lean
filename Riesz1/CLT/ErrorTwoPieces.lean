/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorTwoDerivative
public import Riesz1.CLT.ErrorTwoCovariance
public import Riesz1.ToMathlib.VarianceFiniteSum
import all Riesz1.Variance.LoopForce

/-!
# Finite assembly of the transport-derivative variance estimate

The variance triangle step in the proof of the second error bound in Theorem 3, with
the centres and number of pieces fixed before `N` and the scale.
The analytic construction of such pieces is not asserted here.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace Riesz1.Internal

/-- The nonanchored variance assertion for a finite sum of smooth pieces,
each with a translated `gradWeightTwo` envelope. The coefficient precedes
the scale, the particle number, the pieces and their common amplitude.
This includes the empty family and amplitude zero. -/
theorem clt_error2_derivative_pieces_of_input (hAP : ErrorTwoAPrioriInput)
    (P : Parameters) (b ε : ℝ) (hb : 0 ≤ b) (hε : 0 < ε)
    (m : ℕ) (c : Fin m → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (a : Scale), 1 ≤ (N : ℝ) * a.val →
      ∀ (M : ℝ), 0 ≤ M → ∀ φ : Fin m → ℝ → ℝ,
        (∀ j, ContDiff ℝ ∞ (φ j)) →
        (∀ j, Function.Periodic (φ j) a.val⁻¹) →
        (∀ j u, |deriv (deriv (φ j)) u| ≤
          M * gradWeightTwo P.val.2 b ((N : ℝ) * a.val) a.val⁻¹ (u - c j)) →
        ∃ hF : Integrable (fun X : Configuration N =>
          fluctIntegral (fun u => ∑ j, deriv (φ j) (u / a.val)) N X.val) (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ hF ≤
            ENNReal.ofReal (C * M ^ 2 * (((N : ℝ) * a.val) ^ ε *
              ((N : ℝ) * a.val + ((N : ℝ) * a.val) ^ (2 * b)))) := by
  classical
  choose D hD hbound using fun j : Fin m =>
    clt_error2_derivative_piece_of_input hAP P b ε (c j) hb hε
  have hDsum : 0 ≤ ∑ j, D j := Finset.sum_nonneg fun j _ => (hD j).le
  refine ⟨1 + (m : ℝ) * ∑ j, D j, by positivity, fun N a hK M hM φ hφ hp hd => ?_⟩
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  let R := ((N : ℝ) * a.val) ^ ε * ((N : ℝ) * a.val + ((N : ℝ) * a.val) ^ (2 * b))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let F : Fin m → Configuration N → ℝ := fun j X =>
    fluctIntegral (fun u => deriv (φ j) (u / a.val)) N X.val
  have hmem : ∀ j, MemLp (F j) 2 (gibbsMeasure P N) := by
    intro j
    have hderiv : ContDiff ℝ ∞ (deriv (φ j)) := (contDiff_infty_iff_deriv.mp (hφ j)).2
    apply errorTwo_memLp_fluctIntegral P N (hderiv.continuous.comp (continuous_id.div_const _))
    intro u
    change deriv (φ j) ((u + 1) / a.val) = deriv (φ j) (u / a.val)
    rw [add_div, one_div, Riesz1.periodic_deriv (hp j)]
  have hV : ∀ j, variance (gibbsMeasure P N) (F j) ((hmem j).integrable one_le_two) ≤
      ENNReal.ofReal (D j * M ^ 2 * R) := by
    intro j
    exact (hbound j N a hK M hM (φ j) (hφ j) (hp j) (hd j)).choose_spec
  have he : (fun X : Configuration N =>
      fluctIntegral (fun u => ∑ j, deriv (φ j) (u / a.val)) N X.val) = fun X => ∑ j, F j X := by
    funext X
    dsimp only [F]
    unfold fluctIntegral
    rw [Finset.sum_comm, intervalIntegral.integral_finsetSum,
      Finset.sum_sub_distrib, Finset.mul_sum]
    intro j _
    exact ((contDiff_infty_iff_deriv.mp (hφ j)).2.continuous.comp
      (continuous_id.div_const _)).intervalIntegrable _ _
  rw [he]
  obtain ⟨hS, hSV⟩ := variance_finsetSum_le (gibbsMeasure P N) m F hmem
  refine ⟨hS, hSV.trans ?_⟩
  calc
    _ ≤ (m : ℝ≥0∞) * ∑ j, ENNReal.ofReal (D j * M ^ 2 * R) :=
      mul_le_mul_right (Finset.sum_le_sum fun j _ => hV j) _
    _ = ENNReal.ofReal ((m : ℝ) * (∑ j, D j) * M ^ 2 * R) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
          mul_nonneg (mul_nonneg (hD j).le (sq_nonneg M)) hR),
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
      congr 1
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      dsimp only [R]
      nlinarith [mul_nonneg (sq_nonneg M) hR])

end Riesz1.Internal
