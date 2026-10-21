/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.IntegrationByPartsCutoff

/-!
# Full Gibbs integration by parts

The Langevin expression on every smooth
collision-separated periodic test pairs with every completed Sobolev
function by the Dirichlet form. A smooth partition on the cover handles
the seam before summing directional identities in an orthonormal basis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The Langevin differential expression is the sum of its directional contributions. -/
theorem hsLangevin_eq_sum_directional {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (f : HsTestFunction N)
    {ι : Type*} [Fintype ι] (B : OrthonormalBasis ι ℝ (HsEuclidean N))
    (x : HsConfiguration N) :
    hsLangevin χ f x = ∑ i, hsSmoothValue
      (fun y => fderiv ℝ f.toFun y (B i) * fderiv ℝ (hsPairExpression χ) y (B i) -
        fderiv ℝ (fun z => fderiv ℝ f.toFun z (B i)) y (B i)) x := by
  let y := hsLiftPoint N x
  have hdd : Differentiable ℝ (fderiv ℝ f.toFun) :=
    (contDiff_infty_iff_fderiv.mp f.smooth).2.differentiable (by norm_num)
  have hdiag (v : HsEuclidean N) :
      fderiv ℝ (fun z => fderiv ℝ f.toFun z v) y v =
        iteratedFDeriv ℝ 2 f.toFun y ![v, v] := by
    rw [fderiv_clm_apply (hdd y) (differentiableAt_const v), iteratedFDeriv_two_apply]
    simp
  change inner ℝ (gradient (hsPairExpression χ) y) (gradient f.toFun y) -
    Laplacian.laplacian f.toFun y = _
  rw [real_inner_comm (gradient f.toFun y) (gradient (hsPairExpression χ) y),
    ← B.sum_inner_mul_inner (gradient f.toFun y) (gradient (hsPairExpression χ) y),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f.toFun B,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (gradient (hsPairExpression χ) y) (B i), inner_gradient_left,
    inner_gradient_left]
  simp only [hsSmoothValue, hdiag, y]

/-- Full integration by parts against every element of the completed `H¹` space. -/
theorem hsIntegrationByParts {N : ℕ+} {c : ℝ}
    (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : HsTestFunction N)
    (h : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    ∫ x, hsLangevin χ f x * hsSobolevValue
        (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) h x
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      ∫ x, inner ℝ (hsSmoothGradient ⟨f.toFun, f.smoothOnClosure⟩ x)
        (hsSobolevGradient
          (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) h x)
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  let B := stdOrthonormalBasis ℝ (HsEuclidean N)
  let G := hsSobolevGradient μ h
  let F := hsSobolevValue μ h
  let a := fun i => hsSmoothValue (fun y => fderiv ℝ f.toFun y (B i))
  let b := fun i => hsSmoothValue (fun y =>
    fderiv ℝ f.toFun y (B i) * fderiv ℝ (hsPairExpression χ) y (B i) -
      fderiv ℝ (fun z => fderiv ℝ f.toFun z (B i)) y (B i))
  have ha (i : Fin (Module.finrank ℝ (HsEuclidean N))) : MemLp (a i) 2 μ := by
    apply memLp_hsLiftPoint (f := fun y => fderiv ℝ f.toFun y (B i)) μ 2
    exact ((f.smooth.continuous_fderiv (by norm_num)).clm_apply
      (continuous_const : Continuous (fun _ : HsEuclidean N => B i))).continuousOn
  have hb (i : Fin (Module.finrank ℝ (HsEuclidean N))) : MemLp (b i) 2 μ := by
    apply memLp_hsLiftPoint (f := fun y =>
      fderiv ℝ f.toFun y (B i) * fderiv ℝ (hsPairExpression χ) y (B i) -
        fderiv ℝ (fun z => fderiv ℝ f.toFun z (B i)) y (B i)) μ 2
    exact (continuous_hsLocalCoefficient χ
      ((contDiff_infty_iff_fderiv.mp f.smooth).2.clm_apply contDiff_const)
      ((tsupport_fderiv_apply_subset ℝ (B i)).trans (f.tsupport_subset_chamber hN))
      (B i)).continuousOn
  have hsumG (x) : inner ℝ (hsSmoothGradient ⟨f.toFun, f.smoothOnClosure⟩ x) (G x) =
      ∑ i, a i x * inner ℝ (G x) (B i) := by
    rw [← B.sum_inner_mul_inner (hsSmoothGradient ⟨f.toFun, f.smoothOnClosure⟩ x) (G x)]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (G x) (B i), hsSmoothGradient, inner_gradient_left]
    rfl
  change (∫ x, hsLangevin χ f x * F x ∂μ) = _
  calc
    _ = ∫ x, ∑ i, F x * b i x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hsLangevin_eq_sum_directional χ f B x, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ = ∑ i, ∫ x, F x * b i x ∂μ := integral_finsetSum _
      (fun i _ => (Lp.memLp F).integrable_mul (hb i))
    _ = ∑ i, ∫ x, a i x * inner ℝ (G x) (B i) ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hsSobolev_test_directional_integrationByParts hN χ hc f h (B i)).symm
    _ = ∫ x, ∑ i, a i x * inner ℝ (G x) (B i) ∂μ :=
      (integral_finsetSum _ (fun i _ =>
        (ha i).integrable_mul ((Lp.memLp G).inner_const (B i)))).symm
    _ = _ := integral_congr_ae (Eventually.of_forall (fun x => (hsumG x).symm))

end Riesz1

end
