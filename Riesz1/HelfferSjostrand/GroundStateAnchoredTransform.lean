/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GroundStateAnchored
public import Riesz1.ToMathlib.AESquareDensityL2
public import Riesz1.ToMathlib.GroundStateProductRule

/-!
# The normalized anchored ground-state transform

The multiplier is given by its formula on the entire Euclidean space.
Only its almost everywhere measurability for the restricted volume is
needed. No boundary value for the Hamiltonian is imposed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Laplacian ENNReal

namespace Riesz1

variable {n : ℕ} {c : ℝ} (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)

/-- The normalized anchored ground-state multiplier. -/
def anchoredGroundStateMultiplier (y : AnchoredEuclidean n) : ℝ :=
  (Real.sqrt (hsPartitionFunction χ).toReal)⁻¹ * Real.exp (-hsAnchoredHamiltonianE χ y / 2)

include hc in
theorem anchoredGroundStateMultiplier_pos (y : AnchoredEuclidean n) :
    0 < anchoredGroundStateMultiplier χ y := by
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (ENNReal.toReal_pos
    (hsPartitionFunction_pos χ).ne' (hsPartitionFunction_lt_top χ hc).ne))) (Real.exp_pos _)

theorem aemeasurable_anchoredGroundStateMultiplier :
    AEMeasurable (anchoredGroundStateMultiplier χ) (volume.restrict (anchoredSimplex n)) := by
  exact ((contDiffOn_const.mul (((contDiffOn_hsAnchoredHamiltonianE χ).neg.div_const 2).exp)).continuousOn
    ).aemeasurable (measurableSet_anchoredSimplex n)

include hc in
/-- Exact normalized square-density formula for the anchored law. -/
theorem anchoredMeasureE_eq_groundStateDensity :
    anchoredMeasureE χ = (volume.restrict (anchoredSimplex n)).withDensity
      (fun y => ENNReal.ofReal (anchoredGroundStateMultiplier χ y ^ 2)) := by
  let dx : Measure (AnchoredEuclidean n) := volume.restrict (anchoredSimplex n)
  let ρ : AnchoredEuclidean n → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-hsAnchoredHamiltonianE χ y))
  have hρ : AEMeasurable ρ dx :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (contDiffOn_hsAnchoredHamiltonianE χ).neg.exp.continuousOn).aemeasurable
        (measurableSet_anchoredSimplex n)
  have he : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → AnchoredEuclidean n) :=
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm.measurableEmbedding
  have hm : (volume.restrict (anchoredDomain n)).map (WithLp.toLp 2) = dx := by
    have ht := ((PiLp.volume_preserving_toLp (Fin n)).restrict_preimage
      (measurableSet_anchoredSimplex n)).map_eq
    have hp : (WithLp.toLp 2 : (Fin n → ℝ) → AnchoredEuclidean n) ⁻¹' anchoredSimplex n =
        anchoredDomain n := by ext y; rfl
    rw [hp] at ht
    exact ht
  have hweight : (hsAnchoredWeight χ).map (WithLp.toLp 2) = dx.withDensity ρ := by
    ext B hB
    rw [Measure.map_apply he.measurable hB, hsAnchoredWeight, withDensity_apply _ (he.measurable hB),
      withDensity_apply _ hB, ← lintegral_indicator (he.measurable hB), ← lintegral_indicator hB,
      ← hm, lintegral_map' (by rw [hm]; exact hρ.indicator hB) he.measurable.aemeasurable]
    apply lintegral_congr
    intro y
    by_cases hy : WithLp.toLp 2 y ∈ B
    · simp only [indicator_of_mem hy, indicator_of_mem (show y ∈ WithLp.toLp 2 ⁻¹' B from hy)]
      rfl
    · simp only [indicator_of_notMem hy,
        indicator_of_notMem (show y ∉ WithLp.toLp 2 ⁻¹' B from hy)]
  change (hsAnchoredLaw χ).map (WithLp.toLp 2) = _
  rw [hsAnchoredLaw, Measure.map_smul _ he.measurable.aemeasurable, hweight,
    ← hsPartitionFunction_eq_hsAnchoredWeight, ← withDensity_smul' _ _ (ENNReal.inv_ne_top.mpr (hsPartitionFunction_pos χ).ne')]
  apply withDensity_congr_ae
  apply Eventually.of_forall
  intro y
  have hsq : anchoredGroundStateMultiplier χ y ^ 2 =
      (hsPartitionFunction χ).toReal⁻¹ * Real.exp (-hsAnchoredHamiltonianE χ y) := by
    unfold anchoredGroundStateMultiplier
    rw [mul_pow, inv_pow, Real.sq_sqrt ENNReal.toReal_nonneg, ← Real.exp_nat_mul]
    congr 2
    ring
  change (hsPartitionFunction χ)⁻¹ * ρ y = ENNReal.ofReal (anchoredGroundStateMultiplier χ y ^ 2)
  rw [hsq, ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg),
    ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos (hsPartitionFunction_pos χ).ne'
      (hsPartitionFunction_lt_top χ hc).ne),
    ENNReal.ofReal_toReal (hsPartitionFunction_lt_top χ hc).ne]

/-- The real normalized ground-state unitary on the whole anchored L² space. -/
def anchoredGroundStateEquiv : Lp ℝ 2 (anchoredMeasureE χ) ≃ₗᵢ[ℝ]
    Lp ℝ 2 (volume.restrict (anchoredSimplex n)) :=
  aeSquareDensityL2Equiv (aemeasurable_anchoredGroundStateMultiplier χ)
    (anchoredGroundStateMultiplier_pos χ hc) (anchoredMeasureE_eq_groundStateDensity χ hc)

theorem anchoredGroundStateEquiv_coeFn (f : Lp ℝ 2 (anchoredMeasureE χ)) :
    (anchoredGroundStateEquiv χ hc f : AnchoredEuclidean n → ℝ)
      =ᵐ[volume.restrict (anchoredSimplex n)] fun y => anchoredGroundStateMultiplier χ y * f y :=
  aeSquareDensityL2Equiv_coeFn (aemeasurable_anchoredGroundStateMultiplier χ)
    (anchoredGroundStateMultiplier_pos χ hc) (anchoredMeasureE_eq_groundStateDensity χ hc) f

/-- The complex normalized anchored unitary, with the same real multiplier. -/
def anchoredGroundStateUnitary : Lp ℂ 2 (anchoredMeasureE χ) ≃ₗᵢ[ℂ]
    Lp ℂ 2 (volume.restrict (anchoredSimplex n)) :=
  aeSquareDensityL2ScalarEquiv ℂ (aemeasurable_anchoredGroundStateMultiplier χ)
    (anchoredGroundStateMultiplier_pos χ hc) (anchoredMeasureE_eq_groundStateDensity χ hc)

theorem anchoredGroundStateUnitary_coeFn (f : Lp ℂ 2 (anchoredMeasureE χ)) :
    (anchoredGroundStateUnitary χ hc f : AnchoredEuclidean n → ℂ)
      =ᵐ[volume.restrict (anchoredSimplex n)] fun y => anchoredGroundStateMultiplier χ y • f y :=
  aeSquareDensityL2Equiv_coeFn (aemeasurable_anchoredGroundStateMultiplier χ)
    (anchoredGroundStateMultiplier_pos χ hc) (anchoredMeasureE_eq_groundStateDensity χ hc) f

end Riesz1
