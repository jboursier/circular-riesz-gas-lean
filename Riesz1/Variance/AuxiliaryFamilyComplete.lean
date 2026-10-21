/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryFamilyCompact
public import Riesz1.Variance.AuxiliaryFamilyMacroscopicInput
public import Riesz1.Variance.AuxiliaryReductionFinalInput

/-!
# Discharge the two auxiliary family inputs

The derivative variance and transport energy assertions in Proposition 5.6, including the
uniformity over admissible scale sequences required by Theorem 2. The constant is chosen
before the scale sequence and the particle number.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- Both analytic auxiliary estimates, with exactly the family carrier. They take the
Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler inequality
`External.PrekopaLeindler` as their only hypotheses. -/
theorem auxiliary_family_estimates_of_externals
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler) :
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
          let Q := fun X : Configuration N =>
            fluctIntegral (fun u => deriv (loopMasterProfile (ell N) ψh hψh).val
              (u / (ell N).val)) N X.val
          (∃ hQ : MemLp Q 2 (gibbsMeasure P N),
            variance (gibbsMeasure P N) Q (hQ.integrable one_le_two) ≤
              ENNReal.ofReal (C * cltK N (ell N) ^ ε *
                (cltK N (ell N) ^ P.val.2 +
                  cltK N (ell N) ^ (2 * (1 - P.val.2 + α))))) ∧
          bellEnergy (ell N).val (loopMasterProfile (ell N) ψh hψh).val ≤
            C * (cltK N (ell N) ^ ε *
              (1 + cltK N (ell N) ^ (2 * (1 - P.val.2 + α) - 1))) := by
  classical
  intro P p α d ρ hρ r hr hrhalf ε hε
  by_cases hex : ∃ ell : Scales, Admissible P p ell α d
  · obtain ⟨ell₀, hα, hα2, hη, _, hB, hC₀, _⟩ := hex
    obtain ⟨CM, hCM, hmacro⟩ := auxiliary_family_macroscopic_of_externals
      hBE hPL P p α d ρ hρ ε hε
    by_cases hp : CompactProfile p
    · obtain ⟨CC, hCC, hcompact⟩ := auxiliary_family_compact_estimates
        hBE hPL P p hp α d hα hα2 hη hB.le hC₀.le ρ hρ ε hε
      let C := max CM CC
      refine ⟨C, lt_max_of_lt_left hCM, fun ell hadm N hK v f hv ψh hψh htr => ?_⟩
      let Q := fun X : Configuration N =>
        fluctIntegral (fun u => deriv (loopMasterProfile (ell N) ψh hψh).val
          (u / (ell N).val)) N X.val
      let H : ℝ → Prop := fun B =>
        (∃ hQ : MemLp Q 2 (gibbsMeasure P N),
          variance (gibbsMeasure P N) Q (hQ.integrable one_le_two) ≤
            ENNReal.ofReal (B * cltK N (ell N) ^ ε *
              (cltK N (ell N) ^ P.val.2 + cltK N (ell N) ^ (2 * (1 - P.val.2 + α))))) ∧
        bellEnergy (ell N).val (loopMasterProfile (ell N) ψh hψh).val ≤
          B * (cltK N (ell N) ^ ε * (1 + cltK N (ell N) ^ (2 * (1 - P.val.2 + α) - 1)))
      have hbound : ∃ B : ℝ, B ≤ C ∧ H B := by
        rcases hadm.2.2.2.2.2.2 with ⟨hone, _, _⟩ | ⟨_, hell, hdata⟩
        · exact ⟨CM, le_max_left _ _, hmacro ell hadm hone N r v f hv ψh hψh htr⟩
        · exact ⟨CC, le_max_right _ _, hcompact ell hell hdata N hK r hr v f hv ψh hψh htr⟩
      obtain ⟨B, hBC, ⟨hQ, hV⟩, hJ⟩ := hbound
      refine ⟨⟨hQ, hV.trans (ENNReal.ofReal_le_ofReal ?_)⟩, hJ.trans ?_⟩
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBC (by positivity)) (by positivity)
      · exact mul_le_mul_of_nonneg_right hBC (by positivity)
    · refine ⟨CM, hCM, fun ell hadm N hK v f hv ψh hψh htr => ?_⟩
      rcases hadm.2.2.2.2.2.2 with ⟨hone, _, _⟩ | ⟨hpc, _, _⟩
      · exact hmacro ell hadm hone N r v f hv ψh hψh htr
      · exact False.elim (hp hpc)
  · refine ⟨1, one_pos, fun ell hadm => ?_⟩
    exact False.elim (hex ⟨ell, hadm⟩)

/-- The derivative-family input of Proposition 5.6. It takes `External.BakryEmery` and
`External.PrekopaLeindler` as its only hypotheses, and includes every original and
convolution-family test. -/
theorem auxiliaryDerivativeFamilyVarianceInput_of_externals
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler) :
    AuxiliaryDerivativeFamilyVarianceInput := by
  intro P p α d ρ hρ r hr hrhalf ε hε
  obtain ⟨C, hC, hbound⟩ := auxiliary_family_estimates_of_externals hBE hPL
    P p α d ρ hρ r hr hrhalf ε hε
  exact ⟨C, hC, fun ell hadm N hK v f hv ψh hψh htr =>
    (hbound ell hadm N hK v f hv ψh hψh htr).1⟩

/-- The transport-energy family input of Proposition 5.6. It takes `External.BakryEmery` and
`External.PrekopaLeindler` as its only hypotheses, and includes the logarithmic energy
endpoint. -/
theorem auxiliaryTransportEnergyFamilyInput_of_externals
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler) :
    AuxiliaryTransportEnergyFamilyInput := by
  intro P p α d ρ hρ r hr hrhalf ε hε
  obtain ⟨C, hC, hbound⟩ := auxiliary_family_estimates_of_externals hBE hPL
    P p α d ρ hρ r hr hrhalf ε hε
  exact ⟨C, hC, fun ell hadm N hK v f hv ψh hψh htr =>
    (hbound ell hadm N hK v f hv ψh hψh htr).2⟩

end Riesz1.Internal

end
