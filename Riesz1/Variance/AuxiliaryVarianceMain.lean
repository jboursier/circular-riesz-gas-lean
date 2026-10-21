/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryVarianceInput
public import Riesz1.Variance.AuxiliaryReductionBounds
public import Riesz1.Variance.AuxiliaryReductionRates
public import Riesz1.Variance.AuxiliaryMixedProfile

/-!
# Variance reduction of Proposition 5.6, conditional on two microscopic estimates

Proposition 5.6 for the original profile. The probabilistic reduction
`Riesz1.Internal.auxiliary_reduction_bound` leaves four terms: the mixed statistic of
`ξ - ξ_h`, the derivative statistic `Q`, the smoothing seminorm `S(ξ - ξ_h)`, and the
transport energy `J`. The rate lemmas of `AuxiliaryReductionRates` bound these by the
single power `K^{max(2s-1, 2α)+ε}`. The two estimates of
`Riesz1/Variance/AuxiliaryVarianceInput.lean` are assumed here, and the smoothing and
energy estimates are supplied as hypotheses.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- Proposition 5.6 for one admissible profile on the original branch, with the
variance statistic `Fluct_N[ξ(ℓ⁻¹ ·)]` of the periodized profile `ξ` and the Gibbs variance
of `σ_ℓ²(ξ)`. The conditional hypotheses are the two microscopic estimates and the two
analytic bounds `hS`, `hJ`. -/
theorem auxiliary_variance_reduction_of_input (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (hMicro : AuxiliaryMicroVarianceInput)
    (hDer : AuxiliaryDerivativeVarianceInput)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (ε : ℝ) (hε : 0 < ε)
    (hS : ∃ C : ℝ, 0 < C ∧ ∀ (ell : Scales), Admissible P p ell α d → ∀ (N : ℕ+),
      1 ≤ cltK N (ell N) →
      let ξ : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))} :=
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
      scaledVariance P (ell N) (subCircleL2 ξ (mixedReg hρ N (ell N) ξ)) ≤
        ENNReal.ofReal (C * cltK N (ell N) ^ (2 * α + ε - P.val.2)))
    (hJ : ∃ C : ℝ, 0 < C ∧ ∀ (ell : Scales), Admissible P p ell α d → ∀ (N : ℕ+),
      1 ≤ cltK N (ell N) →
      ∀ (ψh : Circle (loopMasterLength (ell N)) → ℝ)
        (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength (ell N))))),
        (∀ k : ℤ, coeff (loopMasterLength (ell N))
          ⟨(fun z => (ψh z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψh hψh).property⟩ k =
          transportCoeffs P (loopMasterLength (ell N))
            (mixedReg hρ N (ell N) ⟨periodizedProfile p (observationLength (ell N)),
              periodizedProfileL2 p (ell N)⟩) k) →
        bellEnergy (ell N).val (loopMasterProfile (ell N) ψh hψh).val ≤
          C * (cltK N (ell N) ^ ε * (1 + cltK N (ell N) ^ (2 * (1 - P.val.2 + α) - 1)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ell : Scales), Admissible P p ell α d → ∀ (N : ℕ+),
      1 ≤ cltK N (ell N) →
      ∀ (ψh : Circle (loopMasterLength (ell N)) → ℝ)
        (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength (ell N))))),
        (∀ k : ℤ, coeff (loopMasterLength (ell N))
          ⟨(fun z => (ψh z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψh hψh).property⟩ k =
          transportCoeffs P (loopMasterLength (ell N))
            (mixedReg hρ N (ell N) ⟨periodizedProfile p (observationLength (ell N)),
              periodizedProfileL2 p (ell N)⟩) k) →
        ∀ hL : Integrable (loopOnConfiguration (parametersExponent P) N (ell N)
          (loopMasterProfile (ell N) ψh hψh)) (gibbsMeasure P N),
        let ξ : {f : Circle (loopMasterLength (ell N)) → ℝ //
            MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))} :=
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
        ∃ hF : Integrable (mixedStat P N (ell N) ξ) (gibbsMeasure P N),
          |(variance (gibbsMeasure P N) _ hF).toReal -
              cltK N (ell N) ^ P.val.2 * (scaledVariance P (ell N) ξ).toReal| ≤
            C * (cltK N (ell N) ^ (2 * P.val.2 - 2) *
                (variance (gibbsMeasure P N) _ hL).toReal +
              cltK N (ell N) ^ (max (2 * P.val.2 - 1) (2 * α) + ε)) := by
  obtain ⟨C₀, hC₀, hred⟩ := auxiliary_reduction_bound hBE hPL P
  obtain ⟨CE, hCE, hE⟩ := hMicro P p α d ρ hρ ε hε
  obtain ⟨CQ, hCQ, hQ⟩ := hDer P p α d ρ hρ ε hε
  obtain ⟨CS, hCS, hSb⟩ := hS
  obtain ⟨CJ, hCJ, hJb⟩ := hJ
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
  intro ell hadm N hK ψh hψh hcoef hL ξ
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
  obtain ⟨hEm, hEv⟩ := hE ell hadm N hK
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
  obtain ⟨hQm, hQv⟩ := hQ ell hadm N hK ψh hψh hcoef
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
  have hSb' := hSb ell hadm N hK
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
  have hJb' := hJb ell hadm N hK ψh hψh hcoef
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
    rw [show ξ = ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
      from rfl, scaledVariance_periodizedProfile]
    exact (admissible_circleVariance_finite P p ell α d hadm N).ne
  obtain ⟨hF, -, hrd⟩ := hred N (ell N) hK ρ hρ ξ hfin ψh hψh hcoef
  refine ⟨hF, hrd.trans ?_⟩
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

end Riesz1.Internal

end
end
