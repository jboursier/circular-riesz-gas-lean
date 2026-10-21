/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroVarianceFar
public import Riesz1.Variance.AuxiliaryReductionFinalBridge
public import Riesz1.ToMathlib.BoundedCovarianceVariance
import all Riesz1.Variance.LoopIBPUniform

/-!
# The a priori estimate for derivative pieces

The finite-sum variance step of Proposition 5.6. The tests
are arbitrary smooth periodic pieces with the spatial envelope.
Only `RegMicroAPrioriInput` is taken as a hypothesis. Constructing the actual
transport pieces with common constants is a separate analytic step.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- The spatial a priori bound controls the centered statistic of a
fixed finite collection of smooth pieces. Its constant precedes every
center, amplitude, scale and test. Zero pieces and amplitude zero are
included. -/
theorem auxiliary_derivative_variance_of_pieces (hInput : RegMicroAPrioriInput)
    (P : Parameters) (b ε : ℝ) (hb : 0 ≤ b) (hε : 0 < ε) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (a : Scale), 1 ≤ cltK N a →
      ∀ M : ℝ, 0 ≤ M → ∀ (c : Fin m → ℝ) (q : Fin m → ℝ → ℝ),
        (∀ j, ContDiff ℝ ∞ (q j)) →
        (∀ j, Function.Periodic (q j) a.val⁻¹) →
        (∀ j u, |deriv (q j) u| ≤ M * cutoffMajorant P.val.2 b (cltK N a)
          |centralRep (observationLength a) ((u - c j : ℝ) : Circle (observationLength a))|) →
        let Q := fun X : Configuration N =>
          fluctIntegral (fun u => ∑ j, q j (u / a.val)) N X.val
        ∃ hQ : MemLp Q 2 (gibbsMeasure P N),
          variance (gibbsMeasure P N) Q (hQ.integrable one_le_two) ≤
            ENNReal.ofReal (C * M ^ 2 * cltK N a ^ (ε + max (2 * b) P.val.2)) := by
  obtain ⟨C, hC, hbound⟩ := reg_micro_far_variance_of_input hInput P b ε hb hε m
  refine ⟨C, hC, fun N a hK M hM c q hq hp hd => ?_⟩
  intro Q
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  let f : Fin m → Circle (observationLength a) → ℝ := fun j => (hp j).lift
  have he (j : Fin m) : (fun u : ℝ => f j (u : Circle (observationLength a))) = q j := by
    funext u
    exact (hp j).lift_coe u
  obtain ⟨hF, hV⟩ := hbound N a hK M hM c f
    (fun j => by rw [he j]; exact (hq j).of_le (by simp))
    (fun j u => by rw [he j]; exact hd j u)
  have hcont : Continuous (fun u : ℝ => ∑ j, q j (u / a.val)) :=
    continuous_finsetSum _ fun j _ => (hq j).continuous.comp (continuous_id.div_const _)
  have hper : Function.Periodic (fun u : ℝ => ∑ j, q j u) a.val⁻¹ := by
    intro u
    exact Finset.sum_congr rfl fun j _ => hp j u
  have hper1 := periodic_div_scale hper
  have hLp := memLp_lift_of_continuous hcont hper1
  have hQ : MemLp Q 2 (gibbsMeasure P N) := by
    have hEq : Q = fluctuation ⟨hper1.lift, hLp.integrable one_le_two⟩ := by
      funext X
      exact (fluctuation_eq_fluctIntegral hcont hper1 X).symm
    rw [hEq]
    exact memLp_fluctuation P N hLp
  refine ⟨hQ, ?_⟩
  let F := fun X : Configuration N => ∑ j : Fin m, ∑ i : Fin (N : ℕ),
    f j ((X.val i / a.val : ℝ) : Circle (observationLength a))
  let B := (N : ℝ) * ∫ u in (0 : ℝ)..1, ∑ j, q j (u / a.val)
  have hEq : Q = fun X => F X - B := by
    funext X
    dsimp [Q, F, B, fluctIntegral]
    rw [Finset.sum_comm]
    congr 1
  have hvar := frozenVariance_sub_const hF B
  change variance (gibbsMeasure P N) (fun X => F X - B) _ =
    variance (gibbsMeasure P N) F hF at hvar
  have hvEq : variance (gibbsMeasure P N) Q (hQ.integrable one_le_two) =
      variance (gibbsMeasure P N) (fun X => F X - B) (hF.sub (integrable_const B)) := by
    apply auxiliary_variance_congr
    exact Filter.Eventually.of_forall (congrFun hEq)
  exact (hvEq.trans hvar).trans_le hV

end Riesz1.Internal

end
