/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriCutoffAnchored
public import Riesz1.Variance.ConvexificationHessianForm
public import Riesz1.Variance.APrioriGoodGradientVanishing

/-!
# The affine anchored gap map and its cutoff chain rule

The deterministic chain rule needed for the cutoff estimate in Lemma 5.2.
The conditional helper is confined to `Internal`: differentiability of the
ambient cutoff at almost every anchored gap vector still needs proof.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- The two anchored lifts agree on their entire carriers. -/
theorem anchoredLift_eq_anchorVector (n : ℕ) (y : Fin n → ℝ) :
    anchoredLift n.succPNat y = anchorVector y := by
  funext i
  induction i using Fin.cases with
  | zero =>
      change 0 = anchorVector y 0
      exact (anchorVector_zero y).symm
  | succ j => simp [anchoredLift, anchorVector_succ]

/-- The gap vector in the cutoff is the affine anchored gap map. -/
theorem vectorGap_anchoredLift_eq (n : ℕ) (y : Fin n → ℝ) :
    vectorGap n.succPNat (anchoredLift n.succPNat y) = anchoredGapVector n y := by
  rw [anchoredLift_eq_anchorVector]
  funext i
  unfold vectorGap anchoredGapVector liftedAt anchoredCyclicOffset
  simp only [Nat.succPNat_coe, Nat.cast_succ]

/-- The anchored cutoff is the ambient gap cutoff composed with the affine gap map. -/
theorem anchoredCutoff_eq_comp_gapVector (n : ℕ) (s K γ ε : ℝ) :
    anchoredCutoff n.succPNat s K γ ε =
      fun y => gapCutoff n.succPNat s K γ ε (anchoredGapVector n y) := by
  change (fun y : Fin n → ℝ => gapCutoff n.succPNat s K γ ε
    (vectorGap n.succPNat (anchoredLift n.succPNat y))) = _
  funext y
  rw [vectorGap_anchoredLift_eq n y]

/-- The linear part of the anchored gap map, including the wrapping edge. -/
def anchoredGapLinear (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n.succPNat : ℕ) → ℝ) :=
  ContinuousLinearMap.pi fun e => ((n : ℝ) + 1) • edgeForm n e

theorem anchoredGapLinear_apply (n : ℕ) (U : Fin n → ℝ) (e : Fin (n.succPNat : ℕ)) :
    anchoredGapLinear n U e = ((n : ℝ) + 1) * edgeForm n e U := rfl

/-- The period offset contributes zero when differentiating the cyclic gaps. -/
theorem anchoredGapVector_hasFDerivAt (n : ℕ) (y : Fin n → ℝ) :
    HasFDerivAt (anchoredGapVector n) (anchoredGapLinear n) y := by
  apply hasFDerivAt_pi.mpr
  intro e
  have heq : (fun z => anchoredGapVector n z e) =
      fun z => ((n : ℝ) + 1) * (edgeForm n e z + wrapOffset n e) := by
    funext z
    exact anchoredGapAt_label n z e
  rw [heq]
  exact ((edgeForm n e).hasFDerivAt.add_const _).const_mul _

/-- The anchored cutoff's derivative vanishes on its plateau, with no
differentiability premise: it attains its global maximum there. -/
theorem fderiv_anchoredCutoff_eq_zero_of_eq_one (N : ℕ+) (s K γ ε : ℝ)
    (y : Fin ((N : ℕ) - 1) → ℝ) (hy : anchoredCutoff N s K γ ε y = 1) :
    fderiv ℝ (anchoredCutoff N s K γ ε) y = 0 := by
  apply IsLocalMax.fderiv_eq_zero
  exact Filter.Eventually.of_forall fun z => by
    rw [hy]
    exact anchoredCutoff_le_one s K γ ε z

namespace Internal

/-- Internal deterministic chain rule, before establishing the required
almost-everywhere differentiability and selected-edge support. -/
theorem anchoredCutoff_chain_of_differentiable (n : ℕ) (s K γ ε : ℝ)
    (y : Fin n → ℝ)
    (hd : DifferentiableAt ℝ (gapCutoff n.succPNat s K γ ε) (anchoredGapVector n y))
    (U : Fin n → ℝ) :
    fderiv ℝ (anchoredCutoff n.succPNat s K γ ε) y U =
      ∑ e : Fin (n.succPNat : ℕ),
        fderiv ℝ (gapCutoff n.succPNat s K γ ε) (anchoredGapVector n y)
          (Pi.single e (1 : ℝ)) * (((n : ℝ) + 1) * edgeForm n e U) := by
  rw [anchoredCutoff_eq_comp_gapVector]
  change fderiv ℝ (fun z : Fin n → ℝ => gapCutoff n.succPNat s K γ ε
    (anchoredGapVector n z)) y U = _
  have h := hd.hasFDerivAt.comp y (anchoredGapVector_hasFDerivAt n y)
  change HasFDerivAt (fun z => gapCutoff n.succPNat s K γ ε (anchoredGapVector n z)) _ y at h
  rw [h.fderiv, ContinuousLinearMap.comp_apply]
  let L := fderiv ℝ (gapCutoff n.succPNat s K γ ε) (anchoredGapVector n y)
  have hvec : anchoredGapLinear n U =
      ∑ e : Fin (n.succPNat : ℕ), (((n : ℝ) + 1) * edgeForm n e U) • Pi.single e (1 : ℝ) := by
    ext i
    change ((n : ℝ) + 1) * edgeForm n i U = _
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left rfl, mul_one]
    · intro j _ hji
      rw [ite_eq_right (Ne.symm hji), mul_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  change L (anchoredGapLinear n U) = _
  rw [hvec, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_smul, smul_eq_mul, mul_comm]

end Internal

end Riesz1

end
