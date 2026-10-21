/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorTwoFinalMacro
public import Riesz1.CLT.ErrorTwoLoop

/-!
# The derivative assertion of the loop-error theorem

A proposition packaging the already defined regularized transport and
its fluctuation variance. It is used only as a conclusion. The exponent
comparison includes the endpoint of the admissible singularity range.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

namespace Riesz1.Internal

/-- The second variance assertion in the proof of the second error bound in Theorem 3,
with its loss exponent written explicitly. Every transport is specified
by the Fourier coefficients of the regularized profile. -/
def ErrorTwoDerivativeConclusion {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (P : Parameters) (p : Profile) (α ε C : ℝ) (a : Scale) (N : ℕ+) : Prop :=
  ∀ ψ : Circle (loopMasterLength a) → ℝ,
    ∀ hψ : ContDiff ℝ ∞ (fun x : ℝ => ψ (x : Circle (loopMasterLength a))),
      (∀ k : ℤ, coeff (loopMasterLength a)
        ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _
          (loopMasterLengthTest _ ψ hψ).property⟩ k =
        transportCoeffs P (loopMasterLength a)
          (loopMasterLengthTest _ (cltReg hρ P N a
            ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩)
            (cltReg_contDiff hρ P N a _)) k) →
      ∃ hi : Integrable (fun X : Configuration N =>
        fluctIntegral (fun u => deriv (loopMasterProfile a ψ hψ).val
          (u / a.val)) N X.val) (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ hi ≤ ENNReal.ofReal
          (C * (((N : ℝ) * a.val) ^ ε * ((N : ℝ) * a.val +
            ((N : ℝ) * a.val) ^ (2 * (1 - P.val.2 + α)))))

/-- An arbitrarily small increase of the singularity exponent can be
absorbed in the requested loss. No strict lower bound on `b` is needed. -/
theorem errorTwo_rate_increase {K : ℝ} (hK : 1 ≤ K)
    (b η ε τ : ℝ) (hη : 0 ≤ η) (hloss : ε + 2 * η ≤ 2 * τ) :
    K ^ ε * (K + K ^ (2 * (b + η))) ≤
      K ^ (2 * τ) * (K + K ^ (2 * b)) := by
  have hp : 0 < K := by linarith
  have hηpow : 1 ≤ K ^ (2 * η) := Real.one_le_rpow hK (by linarith)
  have he : K ^ (2 * (b + η)) = K ^ (2 * η) * K ^ (2 * b) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  calc
    _ ≤ K ^ ε * (K ^ (2 * η) * (K + K ^ (2 * b))) := by
      rw [he]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hηpow hp.le]
    _ = K ^ (ε + 2 * η) * (K + K ^ (2 * b)) := by rw [Real.rpow_add hp]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hK hloss) (by positivity)

/-- Enlarge the variance coefficient and absorb an increase of `α`.
This is a conclusion transformation, not an additional proof input. -/
theorem errorTwo_derivative_enlarge {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (P : Parameters) (p : Profile) (a : Scale) (N : ℕ+)
    {α ε τ η C D : ℝ} (hK : 1 ≤ (N : ℝ) * a.val)
    (hη : 0 ≤ η) (hloss : ε + 2 * η ≤ 2 * τ) (hC : 0 ≤ C) (hCD : C ≤ D)
    (h : ErrorTwoDerivativeConclusion hρ P p (α + η) ε C a N) :
    ErrorTwoDerivativeConclusion hρ P p α (2 * τ) D a N := by
  intro ψ hψ htr
  obtain ⟨hi, hv⟩ := h ψ hψ htr
  refine ⟨hi, hv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hh := errorTwo_rate_increase hK (1 - P.val.2 + α) η ε τ hη hloss
  rw [show 1 - P.val.2 + α + η = 1 - P.val.2 + (α + η) by ring] at hh
  exact (mul_le_mul_of_nonneg_left hh hC).trans
    (mul_le_mul_of_nonneg_right hCD (by positivity))

end Riesz1.Internal
