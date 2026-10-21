/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryReductionFinalInput
public import Riesz1.Variance.AuxiliarySmoothingFamily
public import Riesz1.Variance.AuxiliaryReductionRates
public import Riesz1.Variance.AuxiliaryReductionBounds

/-!
# Uniform variance reduction from the remaining analytic estimates

Proposition 5.6, including both families.
The smoothing and statistic-identification steps are proved. The three
remaining estimates are explicit propositions on the actual objects.
This is an internal conditional assembly.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- The full input used by the quantitative variance theorem follows
from the three remaining uniform estimates. Loop finiteness is proved
using the Prékopa–Leindler inequality `hPL`. No loop-variance rate input
is required for this assembly. -/
theorem auxiliaryVarianceReductionInput_of_input (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (hMicro : AuxiliaryMicroFamilyVarianceInput)
    (hDer : AuxiliaryDerivativeFamilyVarianceInput)
    (hJ : AuxiliaryTransportEnergyFamilyInput) : AuxiliaryVarianceReductionInput := by
  intro P p α d ρ hρ r hr hrhalf ε hε
  obtain ⟨C₀, hC₀, hred⟩ := auxiliary_reduction_bound hBE hPL P
  obtain ⟨CE, hCE, hE⟩ := hMicro P p α d ρ hρ r hr hrhalf ε hε
  obtain ⟨CQ, hCQ, hQ⟩ := hDer P p α d ρ hρ r hr hrhalf ε hε
  obtain ⟨CS, hCS, hSb⟩ := auxiliary_smoothing_family_bound P p α d ρ hρ ε hε
  obtain ⟨CJ, hCJ, hJb⟩ := hJ P p α d ρ hρ r hr hrhalf ε hε
  have hβ : 0 < P.val.1 := P.property.1
  have hs0 : 0 < P.val.2 := P.property.2.1
  have hs1 : P.val.2 ≤ 1 := P.property.2.2.le
  have hs1' : P.val.2 < 1 := P.property.2.2
  have hX : 0 < 6 * CE + 6 * CQ + CS + 2 * C₀ * CJ := by
    have := mul_pos hC₀ hCJ
    linarith
  refine ⟨3 * P.val.1 ^ 2 + (6 * CE + 6 * CQ + CS + 2 * C₀ * CJ), ?_, ?_⟩
  · have : 0 ≤ 3 * P.val.1 ^ 2 := by positivity
    linarith
  intro ell hadm N hK v ξ hv ψh hψh hcoef hL
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hK0 : 0 < cltK N (ell N) := cltK_pos N (ell N)
  have hK1 : 1 ≤ cltK N (ell N) := hK
  have hR0 : 0 ≤ cltK N (ell N) ^ (max (2 * P.val.2 - 1) (2 * α) + ε) :=
    Real.rpow_nonneg hK0.le _
  have hcov : ∀ (F : Configuration N → ℝ) (hF : MemLp F 2 (gibbsMeasure P N)),
      gibbsCov (gibbsMeasure P N) F F =
        (variance (gibbsMeasure P N) F (hF.integrable one_le_two)).toReal := by
    intro F hF
    rw [variance_toReal_of_memLp _ hF]
    simp only [gibbsCov, sq]
  -- Microscopic statistic `E`, from `hMicro`.
  obtain ⟨hEm, hEv⟩ := hE ell hadm N hK v ξ hv
  have hEb : gibbsCov (gibbsMeasure P N)
      (mixedStat P N (ell N) (subCircleL2 ξ (mixedReg hρ N (ell N) ξ)))
      (mixedStat P N (ell N) (subCircleL2 ξ (mixedReg hρ N (ell N) ξ))) ≤
      CE * (2 * cltK N (ell N) ^ (max (2 * P.val.2 - 1) (2 * α) + ε)) := by
    rw [hcov _ hEm]
    have hX0 : 0 ≤ CE * cltK N (ell N) ^ ε *
        (cltK N (ell N) ^ (2 * α) + cltK N (ell N) ^ (3 * P.val.2 - 2)) :=
      mul_nonneg (mul_nonneg hCE.le (Real.rpow_nonneg hK0.le _))
        (add_nonneg (Real.rpow_nonneg hK0.le _) (Real.rpow_nonneg hK0.le _))
    have hr := auxiliary_micro_rate (K := cltK N (ell N)) (s := P.val.2) (α := α)
      (δ := ε) (ε := ε) hK1 hs1 le_rfl
    refine (ENNReal.toReal_le_of_le_ofReal hX0 hEv).trans ?_
    calc CE * cltK N (ell N) ^ ε *
          (cltK N (ell N) ^ (2 * α) + cltK N (ell N) ^ (3 * P.val.2 - 2))
        = CE * (cltK N (ell N) ^ ε *
          (cltK N (ell N) ^ (2 * α) + cltK N (ell N) ^ (3 * P.val.2 - 2))) := by ring
      _ ≤ CE * (2 * cltK N (ell N) ^ (max (2 * P.val.2 - 1) (2 * α) + ε)) :=
          mul_le_mul_of_nonneg_left hr hCE.le
  -- Derivative statistic `Q`, from `hDer`.
  obtain ⟨hQm, hQv⟩ := hQ ell hadm N hK v ξ hv ψh hψh hcoef
  have hQb : cltK N (ell N) ^ (2 * P.val.2 - 2) *
      gibbsCov (gibbsMeasure P N)
        (fun X : Configuration N => fluctIntegral
          (fun u => deriv (loopMasterProfile (ell N) ψh hψh).val (u / (ell N).val)) N X.val)
        (fun X : Configuration N => fluctIntegral
          (fun u => deriv (loopMasterProfile (ell N) ψh hψh).val (u / (ell N).val)) N X.val) ≤
      CQ * (2 * cltK N (ell N) ^ (max (2 * P.val.2 - 1) (2 * α) + ε)) := by
    rw [hcov _ hQm]
    have hX0 : 0 ≤ CQ * cltK N (ell N) ^ ε *
        (cltK N (ell N) ^ P.val.2 + cltK N (ell N) ^ (2 * (1 - P.val.2 + α))) :=
      mul_nonneg (mul_nonneg hCQ.le (Real.rpow_nonneg hK0.le _))
        (add_nonneg (Real.rpow_nonneg hK0.le _) (Real.rpow_nonneg hK0.le _))
    have hr := auxiliary_derivative_rate (K := cltK N (ell N)) (s := P.val.2) (α := α)
      (δ := ε) (ε := ε) hK1 hs1 le_rfl
    refine le_trans (mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal hX0 hQv)
      (Real.rpow_nonneg hK0.le _)) ?_
    calc cltK N (ell N) ^ (2 * P.val.2 - 2) * (CQ * cltK N (ell N) ^ ε *
          (cltK N (ell N) ^ P.val.2 + cltK N (ell N) ^ (2 * (1 - P.val.2 + α))))
        = CQ * (cltK N (ell N) ^ (2 * P.val.2 - 2) * (cltK N (ell N) ^ ε *
          (cltK N (ell N) ^ P.val.2 + cltK N (ell N) ^ (2 * (1 - P.val.2 + α))))) := by ring
      _ ≤ CQ * (2 * cltK N (ell N) ^ (max (2 * P.val.2 - 1) (2 * α) + ε)) :=
          mul_le_mul_of_nonneg_left hr hCQ.le
  -- Smoothing seminorm `S(ξ - ξ_h)`, from `hS`.
  have hSb' := hSb ell hadm N hK r v ξ hv
  have hSr : (scaledVariance P (ell N) (subCircleL2 ξ (mixedReg hρ N (ell N) ξ))).toReal ≤
      CS * cltK N (ell N) ^ (2 * α + ε - P.val.2) :=
    ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg hCS.le (Real.rpow_nonneg hK0.le _)) hSb'
  have hSS : cltK N (ell N) ^ P.val.2 *
      (scaledVariance P (ell N) (subCircleL2 ξ (mixedReg hρ N (ell N) ξ))).toReal ≤
      CS * cltK N (ell N) ^ (max (2 * P.val.2 - 1) (2 * α) + ε) := by
    refine (mul_le_mul_of_nonneg_left hSr (Real.rpow_nonneg hK0.le _)).trans ?_
    have hid : cltK N (ell N) ^ P.val.2 * (CS * cltK N (ell N) ^ (2 * α + ε - P.val.2)) =
        CS * cltK N (ell N) ^ (2 * α + ε) := by
      rw [← mul_assoc, mul_comm (cltK N (ell N) ^ P.val.2) CS, mul_assoc, ← Real.rpow_add hK0]
      congr 2
      ring
    rw [hid]
    refine mul_le_mul_of_nonneg_left ?_ hCS.le
    exact Real.rpow_le_rpow_of_exponent_le hK1 (by linarith [le_max_right (2 * P.val.2 - 1) (2 * α)])
  -- Transport energy `J`, from `hJ`.
  have hJb' := hJb ell hadm N hK v ξ hv ψh hψh hcoef
  have hJS : cltK N (ell N) ^ (2 * P.val.2 - 1) * bellEnergy (ell N).val
      (loopMasterProfile (ell N) ψh hψh).val ≤
      CJ * (2 * cltK N (ell N) ^ (max (2 * P.val.2 - 1) (2 * α) + ε)) := by
    have hJ0 : 0 ≤ cltK N (ell N) ^ (2 * P.val.2 - 1) := Real.rpow_nonneg hK0.le _
    have hr := auxiliary_energy_rate (K := cltK N (ell N)) (s := P.val.2) (α := α)
      (δ := ε) (ε := ε) hK1 le_rfl
    calc cltK N (ell N) ^ (2 * P.val.2 - 1) * bellEnergy (ell N).val
          (loopMasterProfile (ell N) ψh hψh).val
        ≤ cltK N (ell N) ^ (2 * P.val.2 - 1) * (CJ * (cltK N (ell N) ^ ε *
          (1 + cltK N (ell N) ^ (2 * (1 - P.val.2 + α) - 1)))) :=
          mul_le_mul_of_nonneg_left hJb' hJ0
      _ = CJ * (cltK N (ell N) ^ (2 * P.val.2 - 1) * (cltK N (ell N) ^ ε *
          (1 + cltK N (ell N) ^ (2 * (1 - P.val.2 + α) - 1)))) := by ring
      _ ≤ CJ * (2 * cltK N (ell N) ^ (max (2 * P.val.2 - 1) (2 * α) + ε)) :=
          mul_le_mul_of_nonneg_left hr hCJ.le
  -- Loop statistic `A`: square integrable, so its variance is the real `gibbsCov`.
  have hA : MemLp (loopOnConfiguration (parametersExponent P) N (ell N)
      (loopMasterProfile (ell N) ψh hψh)) 2 (gibbsMeasure P N) := by
    obtain ⟨M, hM⟩ := loopScaleField_lipschitz (loopMasterProfile (ell N) ψh hψh)
    exact memLp_loopFunctional_gibbs P hPL N hs0 hs1' hM
      (loopScaleField_periodic (loopMasterProfile (ell N) ψh hψh).property.1)
  have hAv := hcov _ hA
  -- The probabilistic reduction, then the four bounds.
  have hfin : scaledVariance P (ell N) ξ ≠ ⊤ := by
    rw [auxiliary_scaledVariance_of_optimalScalingTest P p ell N hρ r v ξ hv]
    exact (optimalScaling_test_variance_finite P p ell α d hadm N hρ r v ξ hv).ne
  obtain ⟨hF, -, hrd⟩ := hred N (ell N) hK ρ hρ ξ hfin ψh hψh hcoef
  rw [auxiliary_variance_of_optimalScalingTest P p ell N hρ r v ξ hv hF,
    auxiliary_scaledVariance_of_optimalScalingTest P p ell N hρ r v ξ hv] at hrd
  apply hrd.trans
  have hAv' : gibbsCov (gibbsMeasure P N)
      (loopOnConfiguration (parametersExponent P) N (ell N) (loopMasterProfile (ell N) ψh hψh))
      (loopOnConfiguration (parametersExponent P) N (ell N) (loopMasterProfile (ell N) ψh hψh)) =
      (variance (gibbsMeasure P N) _ hL).toReal := hAv
  rw [hAv']
  have hVA : 0 ≤ (variance (gibbsMeasure P N) _ hL).toReal := ENNReal.toReal_nonneg
  have ha : 0 ≤ cltK N (ell N) ^ (2 * P.val.2 - 2) := Real.rpow_nonneg hK0.le _
  have hJ2 := mul_le_mul_of_nonneg_left hJS hC₀.le
  have hfinal : 0 ≤ (6 * CE + 6 * CQ + CS + 2 * C₀ * CJ) *
        (cltK N (ell N) ^ (2 * P.val.2 - 2) * (variance (gibbsMeasure P N) _ hL).toReal) +
      3 * P.val.1 ^ 2 * cltK N (ell N) ^ (max (2 * P.val.2 - 1) (2 * α) + ε) :=
    add_nonneg (mul_nonneg hX.le (mul_nonneg ha hVA))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hR0)
  nlinarith [hEb, hQb, hSS, hJ2, hfinal]

/-- The family microscopic input implies the original microscopic input.
The original branch needs no support restriction on the auxiliary radius. -/
theorem auxiliaryMicroVarianceInput_of_family (h : AuxiliaryMicroFamilyVarianceInput) :
    AuxiliaryMicroVarianceInput := by
  intro P p α d ρ hρ ε hε
  obtain ⟨C, hC, hb⟩ := h P p α d ρ hρ (1 / 4) (by norm_num) (by norm_num) ε hε
  refine ⟨C, hC, fun ell hadm N hK => ?_⟩
  exact hb ell hadm N hK ⟨testAtScale p (ell N), testAtScaleL2 p (ell N)⟩ _
    (Or.inl ⟨rfl, rfl⟩)

/-- The family derivative input implies the original derivative input,
with the identical quantitative constant on the original branch. -/
theorem auxiliaryDerivativeVarianceInput_of_family (h : AuxiliaryDerivativeFamilyVarianceInput) :
    AuxiliaryDerivativeVarianceInput := by
  intro P p α d ρ hρ ε hε
  obtain ⟨C, hC, hb⟩ := h P p α d ρ hρ (1 / 4) (by norm_num) (by norm_num) ε hε
  refine ⟨C, hC, fun ell hadm N hK => ?_⟩
  exact hb ell hadm N hK ⟨testAtScale p (ell N), testAtScaleL2 p (ell N)⟩ _
    (Or.inl ⟨rfl, rfl⟩)

end Riesz1.Internal

end
