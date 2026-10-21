/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GradientConvergenceAnchoredTests

/-! # The integrated commutator in anchored coordinates

The anchored vector energy identity in the proof of Proposition 3.1,
on the vector test jets.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ContDiff Laplacian

namespace Riesz1

variable {n : ℕ} {c : ℝ}

theorem anchoredGradient_hessian_commutator (χ : HsPairPotentials n.succPNat c)
    (f : anchoredTestSubmodule n) {x : AnchoredEuclidean n} (hx : x ∈ anchoredSimplex n) :
    fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) x (gradient f.val x) (gradient f.val x) =
      ∑ i : Fin n,
        ((anchoredGradientTestDirection (anchoredGradientLangevinTest χ f)
          (EuclideanSpace.single i 1)).val x -
          anchoredLangevinExpr χ (anchoredGradientTestDirection f (EuclideanSpace.single i 1)).val x) *
            (anchoredGradientTestDirection f (EuclideanSpace.single i 1)).val x := by
  have he := hsCommutator_linear_coordinates
    ((fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) x).flip (gradient f.val x)) (gradient f.val x)
  simp only [ContinuousLinearMap.flip_apply] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  have h := langevin_direction_commutator
    ((contDiffOn_hsAnchoredHamiltonianE χ).contDiffAt ((isOpen_anchoredSimplex n).mem_nhds hx))
    f.property.1 (EuclideanSpace.single i 1)
  change fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) x (EuclideanSpace.single i 1)
      (gradient f.val x) * gradient f.val x i = _
  rw [← h]
  congr 1
  exact (anchoredGradientTestTuple_apply f x i).symm

theorem anchoredGradient_form_integral (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : anchoredTestSubmodule n) :
    anchoredVectorForm χ (anchoredGradientTestTuple f) (anchoredGradientTestTuple f) =
      ∫ y, inner ℝ (gradient (anchoredGradientLangevinTest χ f).val y) (gradient f.val y)
        ∂anchoredMeasureE χ := by
  have hμ := isProbabilityMeasure_anchoredMeasureE χ hc
  let μ := anchoredMeasureE χ
  let g (i : Fin n) := anchoredGradientTestDirection f (EuclideanSpace.single i 1)
  let L := anchoredGradientLangevinTest χ f
  let A (i : Fin n) := anchoredLangevinExpr χ (g i).val
  let B (i : Fin n) := (g i).val
  let C (i : Fin n) := (anchoredGradientTestDirection L (EuclideanSpace.single i 1)).val
  have hA (i) : MemLp (A i) 2 μ :=
    memLp_anchoredLangevinExpr χ hc (g i).property.1 (g i).property.2.1 (g i).property.2.2
  have hB (i) : MemLp (B i) 2 μ :=
    ((g i).property.1.continuous).memLp_of_hasCompactSupport (g i).property.2.1
  have hC (i) : MemLp (C i) 2 μ :=
    (anchoredGradientTestDirection L (EuclideanSpace.single i 1)).property.1.continuous.memLp_of_hasCompactSupport
      (anchoredGradientTestDirection L (EuclideanSpace.single i 1)).property.2.1
  have hab (i) : Integrable (fun y => A i y * B i y) μ := (hA i).integrable_mul (hB i)
  have hdiff (i) : Integrable (fun y => (C i y - A i y) * B i y) μ :=
    ((hC i).sub (hA i)).integrable_mul (hB i)
  have hgrad (i) : MemLp (gradient (g i).val) 2 μ :=
    (isAnchoredH1_of_testFunction χ (g i).val (g i).property.1 (g i).property.2.1 inferInstance).2.1
  have hgi (i) : Integrable (fun y => inner ℝ (gradient (g i).val y) (gradient (g i).val y)) μ :=
    (hgrad i).norm.integrable_sq.congr (Eventually.of_forall fun y =>
      (real_inner_self_eq_norm_sq (gradient (g i).val y)).symm)
  have hi (i : Fin n) : (∫ y, inner ℝ (gradient (g i).val y) (gradient (g i).val y) ∂μ) =
      ∫ y, A i y * B i y ∂μ :=
    (anchoredIntegrationByParts χ hc (g i).property.1 (g i).property.2.1 (g i).property.2.2
      (isAnchoredH1_of_testFunction χ (g i).val (g i).property.1 (g i).property.2.1 inferInstance)).symm
  have hpoint (y : AnchoredEuclidean n) : (∑ i, C i y * B i y) =
      inner ℝ (gradient L.val y) (gradient f.val y) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    have hb := anchoredGradientTestTuple_apply f y i
    have hc' := anchoredGradientTestTuple_apply L y i
    change (g i).val y = _ at hb
    change (anchoredGradientTestDirection L (EuclideanSpace.single i 1)).val y = _ at hc'
    change (anchoredGradientTestDirection L (EuclideanSpace.single i 1)).val y * (g i).val y = _
    rw [hc', hb]
    exact (Real.inner_apply _ _).symm
  have hformula : anchoredVectorForm χ (anchoredGradientTestTuple f) (anchoredGradientTestTuple f) =
      ∫ y, (∑ i, inner ℝ (gradient (g i).val y) (gradient (g i).val y)) +
        ∑ i, (C i y - A i y) * B i y ∂μ := by
    unfold anchoredVectorForm
    apply integral_congr_ae
    filter_upwards [ae_mem_anchoredSimplex χ] with y hy
    change (∑ i, inner ℝ (gradient (g i).val y) (gradient (g i).val y)) +
      fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) y
        (anchoredTestVector (anchoredGradientTestTuple f) y)
        (anchoredTestVector (anchoredGradientTestTuple f) y) = _
    rw [anchoredTestVector_gradientTestTuple, anchoredGradient_hessian_commutator χ f hy]
  rw [hformula, integral_add (integrable_finsetSum _ (fun i _ => hgi i))
    (integrable_finsetSum _ (fun i _ => hdiff i)),
    integral_finsetSum _ (fun i _ => hgi i)]
  simp_rw [hi]
  rw [← integral_finsetSum _ (fun i _ => hab i),
    ← integral_add (integrable_finsetSum _ (fun i _ => hab i))
      (integrable_finsetSum _ (fun i _ => hdiff i))]
  apply integral_congr_ae
  filter_upwards with y
  rw [← hpoint y, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- All anchored tests satisfy `q(∇f,∇f) = ‖L₀f‖²`. -/
theorem anchoredGradient_vector_energy (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : anchoredTestSubmodule n) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    let μ := anchoredMeasureE χ
    let u := anchoredVectorJet χ μ (anchoredGradientTestTuple f)
    anchoredVectorSobolevForm μ u u =
      ‖(memLp_anchoredLangevinExpr χ hc f.property.1 f.property.2.1 f.property.2.2).toLp
        (anchoredLangevinExpr χ f.val)‖ ^ 2 := by
  have hμ := isProbabilityMeasure_anchoredMeasureE χ hc
  dsimp only
  rw [anchoredVectorSobolevForm_jet χ hc, anchoredGradient_form_integral χ hc]
  let L := anchoredGradientLangevinTest χ f
  have h := anchoredIntegrationByParts χ hc f.property.1 f.property.2.1 f.property.2.2
    (isAnchoredH1_of_testFunction χ L.val L.property.1 L.property.2.1 inferInstance)
  rw [poisson_norm_sq (anchoredMeasureE χ)]
  calc
    _ = ∫ y, inner ℝ (gradient f.val y) (gradient L.val y) ∂anchoredMeasureE χ :=
      integral_congr_ae (Eventually.of_forall fun y => real_inner_comm _ _)
    _ = ∫ y, anchoredLangevinExpr χ f.val y * L.val y ∂anchoredMeasureE χ := h.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_anchoredLangevinExpr χ hc f.property.1 f.property.2.1 f.property.2.2).coeFn_toLp]
        with y hy
      rw [hy, pow_two]
      rfl

end Riesz1
