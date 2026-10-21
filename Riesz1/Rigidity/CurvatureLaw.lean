/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.CurvatureForcing
public import Riesz1.Rigidity.GapLawSimplex
public import Riesz1.HelfferSjostrand.RieszAdmissiblePerturbation
public import Riesz1.ToMathlib.Poincare.Isometry

/-!
# The actual constrained Gibbs law as an exponential tilt

Measure identities for the constrained law. The
Helffer--Sjostrand Riesz pair law is exactly the Gibbs law, and
forcing is a second exponential tilt, with its actual normalizer.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- The pair Hamiltonian has exactly the energy normalization. -/
theorem hsRieszFundamentalHamiltonian_eq (P : Parameters) (N : ℕ+)
    (X : Configuration N) :
    hsFundamentalHamiltonian
      (hsRieszPairPotentials N P.val.1 P.2.1 (parametersExponent P)) X =
      P.val.1 * energy (parametersExponent P) X := by
  let s := parametersExponent P
  let f : Fin (N : ℕ) → Fin (N : ℕ) → ℝ := fun i j =>
    rieszRepresentative s ((X.val i - X.val j : ℝ) : UnitAddCircle)
  have hf (i j) : f i j = f j i := by
    dsimp only [f]
    rw [show X.val i - X.val j = -(X.val j - X.val i) by ring,
      AddCircle.coe_neg, rieszRepresentative_neg]
  rw [hsFundamentalHamiltonian, hsPairExpression_hsRieszPairPotentials]
  change _ = P.val.1 * ((N : ℝ) ^ (-s.val) * ∑ i, ∑ j ∈ Finset.univ.erase i, f i j)
  rw [sum_offDiagonal_eq_two_sum_lt f hf]
  have he : (∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.filter (i < ·),
      rieszRepresentative s ((X.val j - X.val i : ℝ) : UnitAddCircle)) =
      ∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.filter (i < ·), f i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact (hf j i)
  rw [he]
  ring

/-- Identification of the two Gibbs constructions as measures. -/
theorem hsRieszGibbsProbability_eq (P : Parameters) (N : ℕ+) :
    (hsGibbsProbability
      (hsRieszPairPotentials N P.val.1 P.2.1 (parametersExponent P))
      (hsRieszPairPotentials_curvature_pos N P.2.1 (parametersExponent P)) : Measure _) =
      gibbsMeasure P N := by
  have hw : hsFundamentalWeight
      (hsRieszPairPotentials N P.val.1 P.2.1 (parametersExponent P)) = gibbsWeight P N := by
    unfold hsFundamentalWeight gibbsWeight
    congr 1
    funext X
    rw [hsRieszFundamentalHamiltonian_eq]
    congr 2
    ring
  change (hsPartitionFunction _)⁻¹ • hsFundamentalWeight _ = _
  rw [hsPartitionFunction, hw]
  rfl

namespace Internal

/-- A pair Gibbs probability is the normalized exponential tilt of volume. -/
theorem hsGibbs_eq_tilted {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c) :
    (hsGibbsProbability χ hc : Measure _) =
      (configurationVolume N).tilted (fun X => -hsFundamentalHamiltonian χ X) := by
  have hmeas := (Real.continuous_exp.comp (continuous_hsFundamentalHamiltonian χ).neg).measurable
  have hi : Integrable (fun X => Real.exp (-hsFundamentalHamiltonian χ X))
      (configurationVolume N) := by
    apply (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)).mp
    change (∫⁻ X, ENNReal.ofReal (Real.exp (-hsFundamentalHamiltonian χ X))
      ∂configurationVolume N) ≠ ⊤
    rw [← hsPartitionFunction_eq_lintegral]
    exact (hsPartitionFunction_lt_top χ hc).ne
  have hp : 0 < ∫ X, Real.exp (-hsFundamentalHamiltonian χ X) ∂configurationVolume N := by
    apply ENNReal.ofReal_pos.mp
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le),
      ← hsPartitionFunction_eq_lintegral]
    exact hsPartitionFunction_pos χ
  rw [poincare_tilted_eq_normalized _ _ hi hp, ← hsPartitionFunction_eq_lintegral]
  rfl

end Internal

/-- The Gibbs probability is exactly the volume tilt by its energy. -/
theorem gibbsMeasure_eq_tilted (P : Parameters) (N : ℕ+) :
    gibbsMeasure P N = (configurationVolume N).tilted
      (fun X => -P.val.1 * energy (parametersExponent P) X) := by
  rw [← hsRieszGibbsProbability_eq P N, Internal.hsGibbs_eq_tilted]
  congr 1
  funext X
  rw [hsRieszFundamentalHamiltonian_eq]
  ring

/-- Forcing tilts the actual Gibbs law, with precisely `constrainedNormalizer`. -/
theorem constrainedLaw_eq_tilted (P : Parameters) (N : ℕ+) (θ : ℝ → ℝ)
    (i0 : ℤ) (L : ℕ) (R : ℝ) :
    constrainedLaw P N θ i0 L R = (gibbsMeasure P N).tilted
      (fun X => -P.val.1 * forcingPotential θ i0 L R X) := by
  unfold constrainedLaw Measure.tilted constrainedNormalizer
  congr 1
  funext X
  congr 1
  ring

/-- Full-energy density for the constrained law, including normalization.
This holds for every integer block start. -/
theorem constrainedLaw_eq_volume_tilted (P : Parameters) (N : ℕ+)
    (θ : ℝ → ℝ) (i0 : ℤ) (L : ℕ) (R : ℝ) :
    constrainedLaw P N θ i0 L R = (configurationVolume N).tilted
      (fun X => -P.val.1 *
        (energy (parametersExponent P) X + forcingPotential θ i0 L R X)) := by
  have hi : Integrable (fun X => Real.exp (-P.val.1 * energy (parametersExponent P) X))
      (configurationVolume N) := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      ((Real.measurable_exp.comp ((measurable_energy _ _).const_mul _))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)).mp
    change (∫⁻ X, ENNReal.ofReal (Real.exp (-P.val.1 * energy (parametersExponent P) X))
      ∂configurationVolume N) ≠ ⊤
    rw [← partitionFunction_eq_lintegral]
    exact (partitionFunction_lt_top P N).ne
  rw [constrainedLaw_eq_tilted, gibbsMeasure_eq_tilted, tilted_tilted hi]
  congr 1
  funext X
  simp only [Pi.add_apply]
  ring

end Riesz1

end
