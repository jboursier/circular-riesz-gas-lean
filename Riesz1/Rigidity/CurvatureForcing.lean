/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.Curvature
public import Riesz1.Rigidity.ForcingComparison
public import Riesz1.ToMathlib.IntegerBlockSum
public import Riesz1.Gibbs.AnchoredCoordinates

/-!
# The constrained law on the lifted block

Exact reindexing of the forcing by the retained coordinates and the
corresponding push-forward density identity. These bridge the forcing
and the constrained law to the block energy used in the curvature estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped ENNReal

namespace Riesz1

/-- The forcing is exactly the pair cutoff sum in the
lifted block coordinates, for every integer starting label. -/
theorem forcingPotential_eq_liftedBlock {N : ℕ+} (θ : ℝ → ℝ) (i0 : ℤ)
    {L : ℕ} (hL : L < (N : ℕ)) (R : ℝ) (X : Configuration N) :
    forcingPotential θ i0 L R X =
      2 * ∑ i : Fin (L + 1), ∑ j ∈ univ.filter (i < ·),
        θ ((N : ℝ) * ((liftedBlock i0 hL X).val j - (liftedBlock i0 hL X).val i) / R) := by
  unfold forcingPotential
  rw [← Internal.sum_integer_block_pairs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  change (N : ℝ) * (cyclicLift X (i0 + j.val) - cyclicLift X (i0 + i.val)) =
    (N : ℝ) * ((cyclicLift X (i0 + j.val) - (⌊cyclicLift X i0⌋ : ℝ)) -
      (cyclicLift X (i0 + i.val) - (⌊cyclicLift X i0⌋ : ℝ)))
  ring

/-- On actual configurations the internal energy is the unforced
retained Riesz energy plus exactly `forcingPotential`. -/
theorem internalConvexifiedEnergy_liftedBlock {N : ℕ+} (s : RieszExponent)
    (θ : ℝ → ℝ) (i0 : ℤ) {L : ℕ} (hL : L < (N : ℕ)) (R : ℝ) (X : Configuration N) :
    internalConvexifiedEnergy N L.succPNat s θ R
        (WithLp.toLp 2 (liftedBlock i0 hL X).val) =
      2 * (N : ℝ) ^ (-s.val) *
        (∑ i : Fin (L + 1), ∑ j ∈ univ.filter (i < ·),
          rieszRepresentative s ((liftedBlock i0 hL X).val j - (liftedBlock i0 hL X).val i)) +
        forcingPotential θ i0 L R X := by
  rw [internalConvexifiedEnergy_eq, forcingPotential_eq_liftedBlock θ i0 hL R X]
  change 2 * (∑ i : Fin (L + 1), ∑ j ∈ univ.filter (i < ·),
      ((N : ℝ) ^ (-s.val) * rieszRepresentative s
        ((liftedBlock i0 hL X).val j - (liftedBlock i0 hL X).val i) +
        θ ((N : ℝ) * ((liftedBlock i0 hL X).val j - (liftedBlock i0 hL X).val i) / R))) = _
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The actual constrained block law is the original block marginal with
the cutoff density. No replacement measure or assumed density identity. -/
theorem map_constrainedLaw_liftedBlock (P : Parameters) (N : ℕ+)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (i0 : ℤ) {L : ℕ} (hL : L < (N : ℕ)) (R : ℝ) :
    (constrainedLaw P N θ i0 L R).map (liftedBlock i0 hL) =
      ((gibbsMeasure P N).map (liftedBlock i0 hL)).withDensity
        (fun Z : Configuration L.succPNat => ENNReal.ofReal
          ((constrainedNormalizer P N θ i0 L R)⁻¹ * Real.exp
            (-P.val.1 * (2 * ∑ i : Fin (L + 1), ∑ j ∈ univ.filter (i < ·),
              θ ((N : ℝ) * (Z.val j - Z.val i) / R))))) := by
  let d : Configuration L.succPNat → ℝ≥0∞ := fun Z => ENNReal.ofReal
    ((constrainedNormalizer P N θ i0 L R)⁻¹ * Real.exp
      (-P.val.1 * (2 * ∑ i : Fin (L + 1), ∑ j ∈ univ.filter (i < ·),
        θ ((N : ℝ) * (Z.val j - Z.val i) / R))))
  have hz (j : Fin (L + 1)) : Measurable (fun Z : Configuration L.succPNat => Z.val j) :=
    (measurable_pi_apply j).comp measurable_subtype_coe
  have hd : Measurable d := by
    apply ENNReal.measurable_ofReal.comp
    apply measurable_const.mul
    apply Real.measurable_exp.comp
    apply measurable_const.mul
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    apply hθ.1.continuous.measurable.comp
    exact (measurable_const.mul ((hz j).sub (hz i))).div_const R
  have he : (fun X : Configuration N => ENNReal.ofReal
      ((constrainedNormalizer P N θ i0 L R)⁻¹ *
        Real.exp (-P.val.1 * forcingPotential θ i0 L R X))) =
      fun X => d (liftedBlock i0 hL X) := by
    funext X
    dsimp [d]
    rw [forcingPotential_eq_liftedBlock θ i0 hL R X]
  unfold constrainedLaw
  rw [he]
  exact map_withDensity_comp _ (measurable_liftedBlock i0 hL) hd

end Riesz1

end
