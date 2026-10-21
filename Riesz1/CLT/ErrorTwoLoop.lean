/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorTwoInput
public import Riesz1.CLT.ErrorTwoRates

/-!
# The loop variance at the CLT smoothing radius

The first variance in the proof of the second error bound in Theorem 3, conditional only
on the precise loop-variance assertion of Proposition 5.9. The constant
precedes the scale sequence, the particle number and the transport.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace Riesz1.Internal

/-- First variance assertion in the proof of the second error bound in Theorem 3, from
Proposition 5.9. One can take `K₀ = 1`. The transport has exactly the coefficients
of the regularized profile used by the Gaussian identity. -/
theorem clt_error2_loop_of_input (hLoop : ErrorTwoLoopVarianceInput)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales, Admissible P p ell α d →
      ∀ N : ℕ+, 1 ≤ (N : ℝ) * (ell N).val →
        ∀ ψ : Circle (loopMasterLength (ell N)) → ℝ,
          ∀ hψ : ContDiff ℝ ∞ (fun t : ℝ => ψ (t : Circle (loopMasterLength (ell N)))),
            (∀ k : ℤ, coeff (loopMasterLength (ell N))
              ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _
                (loopMasterLengthTest _ ψ hψ).property⟩ k =
              transportCoeffs P (loopMasterLength (ell N))
                (loopMasterLengthTest _ (cltReg hρ P N (ell N)
                  ⟨periodizedProfile p (observationLength (ell N)),
                    periodizedProfileL2 p (ell N)⟩)
                  (cltReg_contDiff hρ P N (ell N) _)) k) →
            ∃ hL : Integrable
              (loopOnConfiguration (parametersExponent P) N (ell N)
                (loopMasterProfile (ell N) ψ hψ)) (gibbsMeasure P N),
              variance (gibbsMeasure P N) _ hL ≤
                ENNReal.ofReal (C * (((N : ℝ) * (ell N).val) ^ (2 * τ) *
                  ((N : ℝ) * (ell N).val +
                    ((N : ℝ) * (ell N).val) ^ (2 * (1 - P.val.2 + α))))) := by
  obtain ⟨C, hC, hb⟩ := hLoop P p α d ρ hρ (2 * τ) (by linarith)
  refine ⟨C, hC, fun ell hadm N hK ψ hψ hcoeff => ?_⟩
  obtain ⟨hL, hLbound⟩ := hb ell hadm N (cltDelta P N (ell N))
    (cltDelta_pos P N (ell N)) hK (cltDelta_ge_inv P N (ell N) hK)
    (cltDelta_le_one P N (ell N) hK) ψ hψ hcoeff
  refine ⟨hL, hLbound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  exact mul_le_mul_of_nonneg_left (errorTwo_loop_power_bound hK (1 - P.val.2 + α) τ) hC.le

end Riesz1.Internal
