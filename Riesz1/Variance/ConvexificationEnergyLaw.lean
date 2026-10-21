/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.ConvexificationEnergyPairs
public import Riesz1.HelfferSjostrand.AnchoredInverseBL

/-!
# Identification of the tilted anchored law

The nearest-neighbour pair datum gives exactly the
actual tilted law and its anchored Euclidean image, including normalization.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

theorem nearestLaw_eq_tilted (P : Parameters) (N : ℕ+) (θ : ℝ → ℝ) (K γ ε : ℝ) :
    nearestLaw P θ N K γ ε = (gibbsMeasure P N).tilted
      (fun X => -P.val.1 * nearestForcing θ N K γ ε X) := by
  unfold nearestLaw forcedLaw forcedNormalizer Measure.tilted
  congr 1
  funext X
  congr 1
  ring

theorem nearestLaw_eq_volume_tilted (P : Parameters) (N : ℕ+) (θ : ℝ → ℝ) (K γ ε : ℝ) :
    nearestLaw P θ N K γ ε = (configurationVolume N).tilted
      (fun X => -P.val.1 * energy (parametersExponent P) X -
        P.val.1 * nearestForcing θ N K γ ε X) := by
  have hi : Integrable (fun X => Real.exp (-P.val.1 * energy (parametersExponent P) X))
      (configurationVolume N) := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      ((Real.measurable_exp.comp ((measurable_energy _ _).const_mul _))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)).mp
    change (∫⁻ X, ENNReal.ofReal (Real.exp (-P.val.1 * energy (parametersExponent P) X))
      ∂configurationVolume N) ≠ ⊤
    rw [← partitionFunction_eq_lintegral]
    exact (partitionFunction_lt_top P N).ne
  rw [nearestLaw_eq_tilted, gibbsMeasure_eq_tilted, tilted_tilted hi]
  congr 1
  funext X
  simp only [Pi.add_apply]
  ring

/-- The constructed pairs have the actual nearest-neighbour Gibbs law. -/
theorem nearestTiltedPairs_gibbs (P : Parameters) {n : ℕ} (hn : 1 ≤ n)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (K γ ε : ℝ) (hK : 0 < K) :
    (hsGibbsProbability (nearestTiltedPairs P n.succPNat hθ K γ ε hK)
      (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P)) : Measure _) =
      nearestLaw P θ n.succPNat K γ ε := by
  rw [Internal.hsGibbs_eq_tilted, nearestLaw_eq_volume_tilted]
  congr 1
  funext X
  rw [nearestTiltedPairs_hamiltonian P hn hθ K γ ε hK]
  ring

/-- The two anchoring maps agree, with the zero-based label convention. -/
theorem anchorMap_eq_anchorCoords (n : ℕ) (X : Configuration n.succPNat) :
    anchorMap n.succPNat X = (anchorCoords n X.val).2 := by
  funext j
  change cyclicLift X ((j.val : ℤ) + 1) - cyclicLift X 0 = X.val j.succ - X.val 0
  have hj := cyclicLift_natCast X j.succ
  rw [cyclicLift_zero]
  have hzero : (⟨0, n.succPNat.pos⟩ : Fin (n.succPNat : ℕ)) = 0 := Fin.ext (by simp)
  rw [hzero]
  simpa only [Fin.val_succ, Nat.cast_add, Nat.cast_one] using
    congrArg (fun t => t - X.val 0) hj

/-- Exact identification of the actual anchored tilt on its original carrier. -/
theorem nearestTiltedPairs_anchoredLaw (P : Parameters) {n : ℕ} (hn : 1 ≤ n)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (K γ ε : ℝ) (hK : 0 < K) :
    hsAnchoredLaw (nearestTiltedPairs P n.succPNat hθ K γ ε hK) =
      nearestAnchoredLaw P θ n.succPNat K γ ε := by
  rw [← map_snd_hsGibbs _ (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1
    (parametersExponent P)), nearestTiltedPairs_gibbs P hn hθ K γ ε hK]
  unfold nearestAnchoredLaw
  congr 1
  funext X
  exact (anchorMap_eq_anchorCoords n X).symm

/-- Exact identification on the Euclidean carrier used by the inverse. -/
theorem nearestTiltedPairs_anchoredMeasureE (P : Parameters) {n : ℕ} (hn : 1 ≤ n)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (K γ ε : ℝ) (hK : 0 < K) :
    anchoredMeasureE (nearestTiltedPairs P n.succPNat hθ K γ ε hK) =
      (nearestAnchoredLaw P θ n.succPNat K γ ε).map (WithLp.toLp 2) := by
  rw [anchoredMeasureE, nearestTiltedPairs_anchoredLaw P hn hθ K γ ε hK]
  rfl

end Riesz1

end
