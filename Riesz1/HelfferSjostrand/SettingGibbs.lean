/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SettingHamiltonian
public import Riesz1.Gibbs.AnchoredCoordinates

/-!
# Gibbs probabilities on the cyclic quotient

Normalization for the pair-potential class is proved
before bundling a probability measure. The final theorem identifies the
Riesz law with the normalized Gibbs density on the quotient.
It does not assert the boundary-growth inequality for the Riesz Hamiltonian.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- The quotient Gibbs weight of a pair Hamiltonian. -/
def hsGibbsWeight {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) :
    Measure (HsConfiguration N) :=
  (hsConfigurationVolume N).withDensity (fun x => ENNReal.ofReal (Real.exp (-hsHamiltonian χ x)))

theorem hsGibbsWeight_eq_map {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) :
    hsGibbsWeight χ = (hsFundamentalWeight χ).map (hsConfigurationMap N) := by
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-hsHamiltonian χ x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_hsHamiltonian χ).neg)
  rw [hsGibbsWeight, hsConfigurationVolume, ← map_withDensity_comp _
    (measurable_hsConfigurationMap N) hm]
  simp only [hsHamiltonian_configurationMap, hsFundamentalWeight]

theorem hsPartitionFunction_eq_quotient_integral {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) :
    hsPartitionFunction χ = ∫⁻ x, ENNReal.ofReal (Real.exp (-hsHamiltonian χ x))
      ∂hsConfigurationVolume N := by
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-hsHamiltonian χ x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_hsHamiltonian χ).neg)
  rw [hsConfiguration_lintegral N _ hm]
  simp only [hsHamiltonian_configurationMap, hsPartitionFunction_eq_lintegral]

/-- The quotient law is a probability, with no finiteness premise added to admissibility. -/
def hsQuotientGibbsProbability {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c) :
    ProbabilityMeasure (HsConfiguration N) :=
  ⟨(hsPartitionFunction χ)⁻¹ • hsGibbsWeight χ, by
    rw [isProbabilityMeasure_iff, Measure.smul_apply, smul_eq_mul, hsGibbsWeight_eq_map,
      Measure.map_apply (measurable_hsConfigurationMap N) MeasurableSet.univ, preimage_univ]
    exact ENNReal.inv_mul_cancel (hsPartitionFunction_pos χ).ne'
      (hsPartitionFunction_lt_top χ hc).ne⟩

theorem hsQuotientGibbsProbability_eq_map {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (hc : 0 < c) :
    (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      (hsGibbsProbability χ hc : Measure (Configuration N)).map (hsConfigurationMap N) := by
  change _ = ((hsPartitionFunction χ)⁻¹ • hsFundamentalWeight χ).map _
  rw [Measure.map_smul, ← hsGibbsWeight_eq_map]
  rfl
  exact (measurable_hsConfigurationMap N).aemeasurable

/-- The Riesz energy, including inverse temperature, as a Hamiltonian on the quotient. -/
def hsRieszHamiltonian (P : Parameters) (N : ℕ+) (x : HsConfiguration N) : ℝ :=
  P.val.1 * energy (parametersExponent P) ((hsConfigurationEquiv N).symm x)

theorem measurable_hsRieszHamiltonian (P : Parameters) (N : ℕ+) :
    Measurable (hsRieszHamiltonian P N) :=
  ((measurable_energy _ N).comp (measurable_hsConfigurationEquiv_symm N)).const_mul _

theorem hsRieszHamiltonian_configurationMap (P : Parameters) (N : ℕ+) (X : Configuration N) :
    hsRieszHamiltonian P N (hsConfigurationMap N X) =
      P.val.1 * energy (parametersExponent P) X := by
  change P.val.1 * energy _ ((hsConfigurationEquiv N).symm ((hsConfigurationEquiv N) X)) = _
  rw [Equiv.symm_apply_apply]

/-- The exact Riesz weight under the fundamental-region equivalence. -/
theorem hsRieszWeight_eq_map (P : Parameters) (N : ℕ+) :
    (hsConfigurationVolume N).withDensity (fun x => ENNReal.ofReal
      (Real.exp (-hsRieszHamiltonian P N x))) = (gibbsWeight P N).map (hsConfigurationMap N) := by
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-hsRieszHamiltonian P N x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_hsRieszHamiltonian P N).neg)
  rw [hsConfigurationVolume, ← map_withDensity_comp _ (measurable_hsConfigurationMap N) hm]
  simp only [hsRieszHamiltonian_configurationMap, neg_mul, gibbsWeight]

theorem hsRieszPartitionFunction_eq (P : Parameters) (N : ℕ+) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-hsRieszHamiltonian P N x)) ∂hsConfigurationVolume N) =
      partitionFunction P N := by
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-hsRieszHamiltonian P N x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_hsRieszHamiltonian P N).neg)
  rw [hsConfiguration_lintegral N _ hm]
  simp only [hsRieszHamiltonian_configurationMap, neg_mul, partitionFunction_eq_lintegral]

/-- The Gibbs law is exactly the Gibbs probability for `H = β × energy` on the quotient,
transported from the fundamental region. -/
theorem hsRieszGibbsMeasure_eq_map (P : Parameters) (N : ℕ+) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-hsRieszHamiltonian P N x))
        ∂hsConfigurationVolume N)⁻¹ •
      (hsConfigurationVolume N).withDensity (fun x => ENNReal.ofReal
        (Real.exp (-hsRieszHamiltonian P N x))) =
      (gibbsMeasure P N).map (hsConfigurationMap N) := by
  rw [hsRieszPartitionFunction_eq, hsRieszWeight_eq_map, gibbsMeasure, Measure.map_smul]
  exact (measurable_hsConfigurationMap N).aemeasurable

/-- Pulling the quotient Gibbs formula back to the fundamental region recovers the law. -/
theorem hsRieszGibbsMeasure_comap (P : Parameters) (N : ℕ+) :
    Measure.comap (hsConfigurationMap N)
      ((∫⁻ x, ENNReal.ofReal (Real.exp (-hsRieszHamiltonian P N x))
          ∂hsConfigurationVolume N)⁻¹ •
        (hsConfigurationVolume N).withDensity (fun x => ENNReal.ofReal
          (Real.exp (-hsRieszHamiltonian P N x)))) = gibbsMeasure P N := by
  rw [hsRieszGibbsMeasure_eq_map, (measurableEmbedding_hsConfigurationMap N).comap_map]

end Riesz1

end
