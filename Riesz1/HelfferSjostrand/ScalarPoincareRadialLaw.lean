/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.ScalarPoincareRadial
public import Riesz1.ToMathlib.Poincare.Isometry

/-!
# The radial law in orthonormal coordinates

The normalized Euclidean measure used by `scalar_poincare_radial`
pushes forward to the actual radial factor of the Gibbs product law.
This is a measure identity.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

theorem scalarPoincareRadialMeasure_eq {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) :
    hsRadialMeasure χ = (volume.restrict (hsRadialDomain N)).withDensity
      (fun z => ENNReal.ofReal (Real.exp (-hsPairExpression χ (z : HsEuclidean N)))) := by
  unfold hsRadialMeasure hsRadialDensity
  exact withDensity_indicator (measurableSet_hsRadialDomain N) _

theorem scalarPoincareRadialProbability_eq_tilted {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) :
    (hsRadialProbability χ hc : Measure _) = (volume.restrict (hsRadialDomain N)).tilted
      (fun z => -hsPairExpression χ (z : HsEuclidean N)) := by
  let W : hsOrthSubspace N → ℝ := fun z => Real.exp (-hsPairExpression χ (z : HsEuclidean N))
  have hmass : hsRadialMeasure χ univ = ∫⁻ z in hsRadialDomain N, ENNReal.ofReal (W z) := by
    rw [scalarPoincareRadialMeasure_eq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hcont : ContinuousOn W (hsRadialDomain N) :=
    Real.continuous_exp.comp_continuousOn
      (((hsPairExpression_contDiffOn χ).continuousOn.comp
        continuous_subtype_val.continuousOn (fun _ hz => hz)).neg)
  have hW : IntegrableOn W (hsRadialDomain N) :=
    (lintegral_ofReal_ne_top_iff_integrable
      (hcont.aestronglyMeasurable (measurableSet_hsRadialDomain N))
      (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)).mp
        (hmass ▸ hsRadialMeasure_univ_ne_top χ hc)
  have hZ : 0 < ∫ z in hsRadialDomain N, W z := by
    have he := ofReal_integral_eq_lintegral_ofReal hW
      (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)
    rw [← hmass] at he
    exact ENNReal.ofReal_pos.mp (he.symm ▸ bot_lt_iff_ne_bot.mpr (hsRadialMeasure_univ_ne_zero χ))
  rw [poincare_tilted_eq_normalized _ _ hW hZ]
  change (hsRadialMeasure χ univ)⁻¹ • hsRadialMeasure χ = _
  rw [← hmass, scalarPoincareRadialMeasure_eq]

/-- The orthonormal-coordinate probability is exactly the radial factor
of the Gibbs product law after applying its isometric chart. -/
theorem scalarPoincareRadialChart_map {N : ℕ+} {c : ℝ}
    (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace N))) ℝ (hsOrthSubspace N))
    (χ : HsPairPotentials N c) (hc : 0 < c) :
    (((volume.restrict (scalarPoincareRadialDomain basis)).tilted
      (fun y => -scalarPoincareRadialPotential basis χ y)).map (scalarPoincareRadialChart basis)) =
        (hsRadialProbability χ hc : Measure _) := by
  have ho : IsOpen (hsRadialDomain N) :=
    (isOpen_hsChamber N).preimage continuous_subtype_val
  rw [scalarPoincareRadialProbability_eq_tilted]
  exact poincare_isometry_tilted (scalarPoincareRadialChart basis) ho
    (fun z => -hsPairExpression χ (z : HsEuclidean N))

end Riesz1

end
