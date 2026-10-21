/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.StrictConvRepresentation
public import Riesz1.HelfferSjostrand.AnchoredCalculus
public import Riesz1.Variance.APrioriComparisonComparator
public import Mathlib.Probability.Moments.Variance

/-!
# The comparator gradient and its inverse energy

The analytic step in the proof of Lemma 5.2: the
anchored covariance representation identifies gradient inverse energy
with variance. The affine comparator belongs to the
smooth core on the bounded anchored simplex.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace Filter Set Topology Classical
open scoped ENNReal
open scoped ContDiff

namespace Riesz1.APrioriComparison

variable {n : ℕ} {c : ℝ}

/-- The gradient energy of any anchored Sobolev function is its variance. -/
theorem gradient_energy_eq_variance (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (hPL : External.PrekopaLeindler) (hn : 0 < n) {C : ℝ} (hadm : HsAdmissible χ C)
    (F : AnchoredSobolev χ) :
    anchoredInverseEnergy χ hc F.val.2 = ProbabilityTheory.variance F.val.1 (anchoredMeasureE χ) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  have h := (anchoredRepresentation χ hc hPL hn hadm F F).2.2
  rw [ProbabilityTheory.variance_eq_integral (Lp.memLp F.val.1).aemeasurable]
  change (∫ y, inner ℝ (F.val.2 y)
    (anchoredInverseValues (anchoredMeasureE χ) (anchoredInverse χ hc F.val.2).val y)
      ∂anchoredMeasureE χ) = _
  simpa only [pow_two] using h.symm

/-- Smoothness of the affine comparator for arbitrary fixed weights. -/
theorem comparator_smooth (n : ℕ) (J : Finset (Fin (n + 1)))
    (w : Fin (n + 1) → ℝ) :
    ContDiff ℝ ∞ (fun y : AnchoredEuclidean n =>
      ∑ i ∈ J, w i * (((n : ℝ) + 1) * anchorVector (WithLp.ofLp y) i - (i : ℕ))) := by
  apply ContDiff.sum
  intro i _
  have ha : ContDiff ℝ ∞ (fun y : AnchoredEuclidean n => anchorVector (WithLp.ofLp y) i) := by
    induction i using Fin.cases with
    | zero => exact contDiff_const
    | succ j => exact (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
  exact contDiff_const.mul ((contDiff_const.mul ha).sub contDiff_const)

/-- The unpinned coordinates of the comparator gradient, including its
zero coordinates off the selected labels. -/
theorem comparator_gradient_apply (n : ℕ) (J : Finset (Fin (n + 1)))
    (w : Fin (n + 1) → ℝ) (y : AnchoredEuclidean n) (i : Fin n) :
    gradient (fun z : AnchoredEuclidean n =>
      ∑ j ∈ J, w j * (((n : ℝ) + 1) * anchorVector (WithLp.ofLp z) j - (j : ℕ))) y i =
      if i.succ ∈ J then ((n : ℝ) + 1) * w i.succ else 0 := by
  classical
  let f := fun z : AnchoredEuclidean n =>
    ∑ j ∈ J, w j * (((n : ℝ) + 1) * anchorVector (WithLp.ofLp z) j - (j : ℕ))
  have hd := (hasFDerivAt_comparator n J w (WithLp.ofLp y)).comp y
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).hasFDerivAt
  dsimp only [Nat.succPNat] at hd
  have he := hd.differentiableAt.hasGradientAt.fderiv_apply (y := EuclideanSpace.single i 1)
  rw [hd.fderiv] at he
  have hinner : inner ℝ (gradient f y) (EuclideanSpace.single i 1) = gradient f y i := by
    rw [EuclideanSpace.inner_single_right]
    simp only [RCLike.conj_to_real, one_mul]
  change _ = inner ℝ (gradient f y) (EuclideanSpace.single i 1) at he
  rw [hinner] at he
  rw [← he]
  change (∑ j ∈ J, (w j * ((n : ℝ) + 1)) • anchorCoord n j)
    (WithLp.ofLp (EuclideanSpace.single i 1)) = _
  rw [sum_apply]
  simp only [smul_apply, smul_eq_mul]
  have hc (j : Fin (n + 1)) (z : Fin n → ℝ) : anchorCoord n j z = anchorVector z j :=
    anchorCoord_apply n z j
  simp only [hc]
  have ha (j : Fin (n + 1)) :
      anchorVector (WithLp.ofLp (EuclideanSpace.single i (1 : ℝ))) j =
        if j = i.succ then 1 else 0 := by
    induction j using Fin.cases with
    | zero =>
      have hz : (0 : Fin (n + 1)) ≠ i.succ := by
        intro h
        have := congrArg Fin.val h
        simp at this
      change 0 = if (0 : Fin (n + 1)) = i.succ then 1 else 0
      rw [ite_eq_right hz]
    | succ j => simp [anchorVector, Pi.single_apply, eq_comm]
  change (∑ j ∈ J, w j * ((n : ℝ) + 1) * anchorVector (WithLp.ofLp (EuclideanSpace.single i 1)) j) = _
  simp only [ha, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs <;> ring

end Riesz1.APrioriComparison

end
