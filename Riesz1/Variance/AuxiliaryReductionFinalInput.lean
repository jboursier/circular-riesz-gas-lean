/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryVarianceInput
public import Riesz1.Variance.QuantitativeVarianceInput

/-!
# Remaining analytic inputs for the uniform loop reduction

Faithful copies of the microscopic variance, derivative variance, and
transport energy estimates in the proof of Proposition 5.6,
with the uniformity over the families. They concern the
existing objects and do not assume the final variance expansion.
The smoothing estimate is proved separately and is not an input.
These propositions are used only by internal conditional theorems.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- Lemma 5.3, uniformly over the original profile and both
families, on the existing observation-circle statistic. -/
def AuxiliaryMicroFamilyVarianceInput : Prop :=
  ∀ (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (r : ℝ), 0 < r → r < 1 / 2 →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (ell : Scales), Admissible P p ell α d →
      ∀ (N : ℕ+), 1 ≤ cltK N (ell N) → ∀ (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∃ hE : MemLp (mixedStat P N (ell N) (subCircleL2 f (mixedReg hρ N (ell N) f))) 2
            (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
            ENNReal.ofReal (C * cltK N (ell N) ^ ε *
              (cltK N (ell N) ^ (2 * α) + cltK N (ell N) ^ (3 * P.val.2 - 2)))

/-- The derivative-statistic bound in Proposition 5.6, with a common
constant before the optional family radius. -/
def AuxiliaryDerivativeFamilyVarianceInput : Prop :=
  ∀ (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (r : ℝ), 0 < r → r < 1 / 2 →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (ell : Scales), Admissible P p ell α d →
      ∀ (N : ℕ+), 1 ≤ cltK N (ell N) → ∀ (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∀ (ψh : Circle (loopMasterLength (ell N)) → ℝ)
          (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength (ell N))))),
          (∀ k : ℤ, coeff (loopMasterLength (ell N))
            ⟨(fun z => (ψh z : ℂ)), complexL2Integrable _ _
              (loopMasterLengthTest _ ψh hψh).property⟩ k =
            transportCoeffs P (loopMasterLength (ell N)) (mixedReg hρ N (ell N) f) k) →
          let Q : Configuration N → ℝ := fun X =>
            fluctIntegral (fun u => deriv (loopMasterProfile (ell N) ψh hψh).val
              (u / (ell N).val)) N X.val
          ∃ hQ : MemLp Q 2 (gibbsMeasure P N),
            variance (gibbsMeasure P N) Q (hQ.integrable one_le_two) ≤
              ENNReal.ofReal (C * cltK N (ell N) ^ ε *
                (cltK N (ell N) ^ P.val.2 + cltK N (ell N) ^ (2 * (1 - P.val.2 + α))))

/-- The integrated transport bound in Proposition 5.6, including its
arbitrary positive power loss at the logarithmic endpoint. -/
def AuxiliaryTransportEnergyFamilyInput : Prop :=
  ∀ (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (r : ℝ), 0 < r → r < 1 / 2 →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (ell : Scales), Admissible P p ell α d →
      ∀ (N : ℕ+), 1 ≤ cltK N (ell N) → ∀ (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∀ (ψh : Circle (loopMasterLength (ell N)) → ℝ)
          (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength (ell N))))),
          (∀ k : ℤ, coeff (loopMasterLength (ell N))
            ⟨(fun z => (ψh z : ℂ)), complexL2Integrable _ _
              (loopMasterLengthTest _ ψh hψh).property⟩ k =
            transportCoeffs P (loopMasterLength (ell N)) (mixedReg hρ N (ell N) f) k) →
          bellEnergy (ell N).val (loopMasterProfile (ell N) ψh hψh).val ≤
            C * (cltK N (ell N) ^ ε *
              (1 + cltK N (ell N) ^ (2 * (1 - P.val.2 + α) - 1)))

end Riesz1.Internal

end
