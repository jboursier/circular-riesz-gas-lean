/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlCompactInput
public import Riesz1.Frozen.TestAtScaleL2

/-!
# The loop variance theorem for every admissible fixed profile

Proposition 5.9, with the coefficient before the scale sequence,
particle count and smoothing radius. The actual smooth regularized
transport is specified by its Fourier coefficients.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace Riesz1

/-- Proposition 5.9, in both admissible regimes and including
`N = 1`, bounded `K`, and the endpoint exponent. -/
theorem varAl_loop_variance
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales, Admissible P p ell α d →
      ∀ (N : ℕ+), 1 ≤ cltK N (ell N) → ∀ (h : ℝ) (hh : 0 < h),
        (cltK N (ell N))⁻¹ ≤ h → h ≤ 1 →
        ∀ (ψ : Circle (loopMasterLength (ell N)) → ℝ)
          (hψ : ContDiff ℝ ∞ (fun x : ℝ => ψ (x : Circle (loopMasterLength (ell N))))),
          (∀ k, coeff (loopMasterLength (ell N)) ⟨(fun x => (ψ x : ℂ)),
            complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
              transportCoeffs P (loopMasterLength (ell N))
                (loopMasterLengthTest _ (cltRegCircle hρ _ hh
                  ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩)
                  (cltRegCircle_contDiff hρ _ hh _)) k) →
          ∃ hi : Integrable (loopOnConfiguration (parametersExponent P) N (ell N)
              (loopMasterProfile (ell N) ψ hψ)) (gibbsMeasure P N),
            variance (gibbsMeasure P N) _ hi < ⊤ ∧
            variance (gibbsMeasure P N) _ hi ≤ ENNReal.ofReal
              (C * cltK N (ell N) ^ (ε + max 1 (2 * (1 - P.val.2 + α)))) := by
  obtain ⟨C, hC, hall⟩ := Internal.varAlVarianceInput_of_externals hBE hPL P p α d ρ hρ
    (1 / 4) (by norm_num) (by norm_num) ε hε
  refine ⟨C, hC, fun ell hadm N hK h hh hKh hh1 ψ hψ htr => ?_⟩
  let v : Profile := ⟨testAtScale p (ell N), testAtScaleL2 p (ell N)⟩
  obtain ⟨hi, hf, hb⟩ := hall ell hadm N hK v
    ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
    (Or.inl ⟨rfl, rfl⟩) h hh hKh hh1 ψ hψ htr
  refine ⟨hi, hf, (ENNReal.toReal_le_toReal hf.ne ENNReal.ofReal_ne_top).mp ?_⟩
  rwa [ENNReal.toReal_ofReal (mul_nonneg hC.le
    (Real.rpow_nonneg (cltK_pos N (ell N)).le _))]

end Riesz1
