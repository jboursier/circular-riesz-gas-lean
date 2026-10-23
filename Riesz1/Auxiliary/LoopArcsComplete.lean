/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsLpCellLp

/-!
# The complete arc lemma: identity, integrability and `L^p` bound

Lemma B.2, assembled from its three claims:

* `Λ` is arclength integrable on `N𝕋` (here: `IntegrableOn` on `(0, N]`), for every configuration.
* the loop functional is the arc integral `L(b) = -2 ∫_{N𝕋} b' Λ`, for every configuration.
* the `L^p` bound `‖∫_m^{m+1} |Λ| dt‖_p ≤ C_{β,s,p}` for every integer `0 ≤ m < N`, with `C` chosen
  before `N`, `b` and `m`.

The statement is conditional on the rigidity conclusion and takes the Prékopa–Leindler inequality
`External.PrekopaLeindler` as an explicit argument. The smooth test function is taken of class
`C¹` and `N`-periodic, which is more general than the smooth `b` in the paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- **Complete arc lemma**, Lemma B.2, conditional on the rigidity
conclusion. There is `C > 0` such that for every `N ≥ 2`, every `C¹` `N`-periodic `b` and every
integer `0 ≤ m < N`: the function `Λ` is arclength integrable on `N𝕋` for every configuration,
`L(b) = -2 ∫_{N𝕋} b' Λ` for every configuration, and the `L^p` norm of `∫_m^{m+1} |Λ|` is at most
`C`. -/
theorem loopArc_complete_of_rigidity {beta s : ℝ} (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hRig : Internal.RigidityConclusion beta s hbeta hs hs1) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (hPL : External.PrekopaLeindler) (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (b : ℝ → ℝ), ContDiff ℝ 1 b → Function.Periodic b (N : ℝ) →
        ∀ (m : ℕ), m < N →
          (∀ X : Configuration N, IntegrableOn (fun t => loopArcLambda s N X t) (Ioc (0 : ℝ) N)) ∧
          (∀ X : Configuration N, loopArcL s N b X
              = -2 * ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcLambda s N X t) ∧
          eLpNorm (fun X : Configuration N =>
              ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t|)
            (ENNReal.ofReal p) (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N)
            ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hcell⟩ := loopArcLambda_cell_lp_of_rigidity hbeta hs hs1 hRig hp
  refine ⟨C, hC, fun hPL N hN b hb hper m hm => ⟨fun X => integrable_loopArcLambda s hs hs1 N X,
    fun X => loopArcL_eq_integral_lambda s hs hs1 N b hb hper X, hcell hPL N hN m hm⟩⟩

end Riesz1

end
end
