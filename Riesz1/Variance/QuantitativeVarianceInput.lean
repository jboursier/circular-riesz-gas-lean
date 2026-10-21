/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.OptimalScalingBounds
public import Riesz1.Variance.AuxiliaryMixedProfile
public import Riesz1.Variance.LoopMasterExistence
public import Riesz1.Variance.QuantitativeVarianceUniformConclusion
public import Riesz1.Frozen.External.BakryEmery
public import Riesz1.Frozen.External.PrekopaLeindler

/-!
# Inputs to optimal variance, uniform over the two convolution families

The two inputs are the estimates of Proposition 5.6 and Proposition 5.9,
with the uniform dependence required by the uniform form of Theorem 2.
They refer exclusively to the profiles, regularizations, Fourier transports,
and loop functionals. The test relation below describes their domain. It does
not define another regularization or transport. Constants precede the scale
sequence, particle number, and optional extra smoothing radius.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- The original test, or one of the two actual convolution-family tests,
paired with its function on the observation circle. The original branch
allows the representative discrepancy at the antipode. -/
def OptimalScalingTest (p : Profile) (ell : Scales) (N : ℕ+)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (r : ℝ) (v : Profile)
    (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))}) : Prop :=
  let ξ := (⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ :
    {f : Circle (loopMasterLength (ell N)) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
  (v.val = testAtScale p (ell N) ∧ f = ξ) ∨
    ∃ (t : ℝ) (ht : 0 < t), t ≤ 1 ∧
      ((∀ M, (ell M).val = 1) ∨
        ((∀ᵐ x : ℝ, r ≤ |x| → zeroExtension p x = 0) ∧ t < 1 / 2 - r)) ∧
      let g := loopMasterLengthTest (loopMasterLength (ell N))
        (cltRegCircle hρ (loopMasterLength (ell N)) ht ξ)
        (cltRegCircle_contDiff hρ (loopMasterLength (ell N)) ht ξ)
      ((v.val = cltScaledLift hρ (ell N) ht ξ ∧ f = g) ∨
        ((∀ x, v.val x = testAtScale p (ell N) x - cltScaledLift hρ (ell N) ht ξ x) ∧
          f = subCircleL2 ξ g))

/-- Proposition 5.6, also uniform over the two convolution families.
The only residual random term is the actual microscopic loop.
Analytic finiteness is proved separately in `OptimalScalingFiniteness`. -/
def AuxiliaryVarianceReductionInput : Prop :=
  ∀ (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (r : ℝ), 0 < r → r < 1 / 2 →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (ell : Scales), Admissible P p ell α d →
      ∀ (N : ℕ+), 1 ≤ cltK N (ell N) → ∀ (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∀ (ψ : Circle (loopMasterLength (ell N)) → ℝ)
          (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength (ell N))))),
          (∀ k, coeff (loopMasterLength (ell N))
            ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _
              (loopMasterLengthTest _ ψ hψ).property⟩ k =
            transportCoeffs P (loopMasterLength (ell N)) (mixedReg hρ N (ell N) f) k) →
          ∀ hL : Integrable (loopOnConfiguration (parametersExponent P) N (ell N)
            (loopMasterProfile (ell N) ψ hψ)) (gibbsMeasure P N),
          let V := variance (gibbsMeasure P N)
            (fluctuation ⟨v.val, (optimalScaling_profile_memLp v).integrable one_le_two⟩)
            (optimalScaling_fluctuation_integrable P N v)
          let σ := cltVariance P (ell N) ⟨(fun x => (v.val x : ℂ)), v.property⟩
          |V.toReal - cltK N (ell N) ^ P.val.2 * σ.toReal| ≤
            C * (cltK N (ell N) ^ (2 * P.val.2 - 2) *
              (variance (gibbsMeasure P N) _ hL).toReal +
              cltK N (ell N) ^ (max (2 * P.val.2 - 1) (2 * α) + ε))

/-- Proposition 5.9, retaining every radius in `[K⁻¹,1]` and
uniform over the two convolution families. Both the integrability
certificate and finiteness precede conversion of the loop variance. -/
def VarAlVarianceInput : Prop :=
  ∀ (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (r : ℝ), 0 < r → r < 1 / 2 →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (ell : Scales), Admissible P p ell α d →
      ∀ (N : ℕ+), 1 ≤ cltK N (ell N) → ∀ (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∀ (h : ℝ) (hh : 0 < h), (cltK N (ell N))⁻¹ ≤ h → h ≤ 1 →
        ∀ (ψ : Circle (loopMasterLength (ell N)) → ℝ)
          (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength (ell N))))),
          (∀ k, coeff (loopMasterLength (ell N))
            ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _
              (loopMasterLengthTest _ ψ hψ).property⟩ k =
            transportCoeffs P (loopMasterLength (ell N))
              (loopMasterLengthTest _ (cltRegCircle hρ _ hh f)
                (cltRegCircle_contDiff hρ _ hh f)) k) →
          ∃ hL : Integrable (loopOnConfiguration (parametersExponent P) N (ell N)
            (loopMasterProfile (ell N) ψ hψ)) (gibbsMeasure P N),
            variance (gibbsMeasure P N) _ hL < ⊤ ∧
            (variance (gibbsMeasure P N) _ hL).toReal ≤
              C * cltK N (ell N) ^ (ε + max 1 (2 * (1 - P.val.2 + α)))

end Riesz1.Internal

end
