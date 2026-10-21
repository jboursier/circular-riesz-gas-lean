/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsUnconditional
public import Riesz1.Auxiliary.LoopSizeBiasOffsets

/-!
# Linearity and the crude estimate for differences of loop tests

The global-tail reduction in the proof of the localization part of
Lemma 5.8. All integrals in the linearity identity
are justified by the arc representation.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1

/-- The loop is linear under subtraction of periodic `C¹` tests. -/
theorem loopArcL_sub {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (N : ℕ+)
    {b c : ℝ → ℝ} (hb : ContDiff ℝ 1 b) (hc : ContDiff ℝ 1 c)
    (hbp : Function.Periodic b (N : ℝ)) (hcp : Function.Periodic c (N : ℝ))
    (X : Configuration N) :
    loopArcL s N (b - c) X = loopArcL s N b X - loopArcL s N c X := by
  have hΛ : IntervalIntegrable (loopArcLambda s N X) volume 0 N :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr
      (integrable_loopArcLambda s hs hs1 N X)
  have hdb (t : ℝ) : DifferentiableAt ℝ b t :=
    (hb.differentiable (by norm_num)).differentiableAt
  have hdc (t : ℝ) : DifferentiableAt ℝ c t :=
    (hc.differentiable (by norm_num)).differentiableAt
  have hder : deriv (b - c) = fun t => deriv b t - deriv c t :=
    funext fun t => deriv_sub (hdb t) (hdc t)
  rw [loopArcL_eq_integral_lambda s hs hs1 N (b - c) (hb.sub hc) (hbp.sub hcp) X,
    loopArcL_eq_integral_lambda s hs hs1 N b hb hbp X,
    loopArcL_eq_integral_lambda s hs hs1 N c hc hcp X, hder]
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub
    (hΛ.continuousOn_mul (hb.continuous_deriv le_rfl).continuousOn)
    (hΛ.continuousOn_mul (hc.continuous_deriv le_rfl).continuousOn)]
  ring

/-- Crude control of the global-loop difference on the actual preceding-particle
carrier. This reduces the tail step to a deterministic sum of cell suprema. -/
theorem Internal.loopLocalization_crude_difference
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    {β s : ℝ} (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (b c : ℝ → ℝ),
      ContDiff ℝ 1 b → ContDiff ℝ 1 c → Function.Periodic b (N : ℝ) →
      Function.Periodic c (N : ℝ) →
      eLpNorm (fun X : LoopPrecedingConfiguration N => loopArcL s N b X.val - loopArcL s N c X.val)
        (ENNReal.ofReal p) (loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N) ≤
        ENNReal.ofReal (C * ∑ m ∈ Finset.range (N : ℕ),
          sSup ((fun z => |deriv (b - c) z|) '' Icc (m : ℝ) ((m : ℝ) + 1))) := by
  obtain ⟨C, hC, hcrude⟩ := auxiliary_Loop_crude hBE hPL hβ hs hs1 hp
  refine ⟨C, hC, fun N b c hb hc hbp hcp => ?_⟩
  have hf := stronglyMeasurable_loopArcL hs hs1 N (hb.sub hc) (hbp.sub hcp)
  have hmap := eLpNorm_map_measure (μ := loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N)
    hf.aestronglyMeasurable measurable_subtype_coe.aemeasurable (p := ENNReal.ofReal p)
  rw [map_loopPrecedingMeasure] at hmap
  change eLpNorm (fun X : Configuration N => loopArcL s N (b - c) X)
      (ENNReal.ofReal p) (gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N) =
    eLpNorm (fun X : LoopPrecedingConfiguration N => loopArcL s N (b - c) X.val)
      (ENNReal.ofReal p) (loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N) at hmap
  have h := hcrude N (b - c) (hb.sub hc) (hbp.sub hcp)
  rw [hmap] at h
  simpa only [Function.comp_def, loopArcL_sub hs hs1 N hb hc hbp hcp] using h

end Riesz1

end
