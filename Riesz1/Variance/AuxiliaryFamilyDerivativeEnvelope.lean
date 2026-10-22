/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorTwoFinalVariance
public import Riesz1.Variance.APrioriComplete
import all Riesz1.Variance.LoopForce

/-!
# Sharp derivative variance from fixed cutoffs

The cutoff pieces use the singular exponent in the a priori estimate.
The regular remainder uses exponent zero and its decaying derivative.
The complete a priori conclusion is supplied by the two external inputs.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace Riesz1.Internal

/-- The fixed-cutoff derivative estimate from the two external inputs. -/
theorem auxiliary_family_derivative_envelopes (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler)
    (P : Parameters) (n : ℕ) (marks : Fin n → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (b ε : ℝ) (hb : 0 ≤ b) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (a : Scale), 1 ≤ (N : ℝ) * a.val →
      (∀ i k, i ≠ k → δ ≤ circDist a.val⁻¹ (marks i - marks k)) →
      ∀ (h A : ℝ), 0 < h → ((N : ℝ) * a.val)⁻¹ ≤ h → 0 ≤ A →
      ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → Function.Periodic F a.val⁻¹ →
      (∀ x, |F x| ≤ A * (1 + ∑ j,
        max (circDist a.val⁻¹ (x - marks j)) h ^ (-b))) →
      (∀ x, |deriv F x| ≤ A * (1 + ∑ j,
        max (circDist a.val⁻¹ (x - marks j)) h ^ (-1 - b))) →
      (∀ x, 2 ≤ circDist a.val⁻¹ x →
        |F x| ≤ A * circDist a.val⁻¹ x ^ (P.val.2 - 2) ∧
          |deriv F x| ≤ A * circDist a.val⁻¹ x ^ (P.val.2 - 3)) →
      ∃ hF : Integrable (fun X : Configuration N =>
        fluctIntegral (fun u => F (u / a.val)) N X.val) (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ hF ≤
          ENNReal.ofReal (C * A ^ 2 * (((N : ℝ) * a.val) ^ ε *
            (((N : ℝ) * a.val) ^ P.val.2 + ((N : ℝ) * a.val) ^ (2 * b)))) := by
  exact errorTwo_variance_of_envelopes (aPrioriConclusion_of_externals hBE hPL)
    P n marks δ hδ b ε hb hε

end Riesz1.Internal
