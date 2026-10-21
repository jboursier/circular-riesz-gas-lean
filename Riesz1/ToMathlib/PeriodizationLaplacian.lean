/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Chamber.PeriodizationDerivative
public import Riesz1.ToMathlib.EllipticRegularity.LocalTesting

/-!
# Second derivatives of compact vector periodizations

The classical Laplacian commutes with periodization of a compact smooth
real function. These identities include points on the rotation seam.
-/

@[expose] public section

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Laplacian

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Compact support is preserved by the classical Laplacian. -/
theorem hasCompactSupport_laplacian {f : E → ℝ} (hs : HasCompactSupport f) :
    HasCompactSupport (Δ f) :=
  hs.isCompact.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset f)

omit [FiniteDimensional ℝ E] in
/-- Two directional derivatives commute with compact periodization. -/
theorem fderiv_fderiv_vectorPeriodize_apply {v : E} (hv : v ≠ 0) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (x a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (vectorPeriodize v hv f hs) y a) x b =
      vectorPeriodize v hv (fun y => fderiv ℝ (fun z => fderiv ℝ f z a) y b)
        ((hs.fderiv_apply ℝ a).fderiv_apply ℝ b) x := by
  have hg : ContDiff ℝ ∞ (fun y => fderiv ℝ f y a) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  simp_rw [fderiv_vectorPeriodize_apply hv (hf.differentiable (by norm_num)) hs]
  exact fderiv_vectorPeriodize_apply hv (hg.differentiable (by norm_num)) _ x b

/-- The Laplacian commutes with the locally finite periodization sum. -/
theorem laplacian_vectorPeriodize {v : E} (hv : v ≠ 0) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (x : E) :
    Δ (vectorPeriodize v hv f hs) x =
      vectorPeriodize v hv (Δ f) (hasCompactSupport_laplacian hs) x := by
  classical
  let B := stdOrthonormalBasis ℝ E
  have hdiag (g : E → ℝ) (hg : ContDiff ℝ ∞ g) (y a : E) :
      iteratedFDeriv ℝ 2 g y ![a, a] =
        fderiv ℝ (fun z => fderiv ℝ g z a) y a := by
    have hd : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
    rw [fderiv_clm_apply
      (hd.differentiable (by norm_num) y)
      (differentiableAt_const a), iteratedFDeriv_two_apply]
    simp
  have htrace (g : E → ℝ) (hg : ContDiff ℝ ∞ g) (y : E) :
      Δ g y = ∑ i, fderiv ℝ (fun z => fderiv ℝ g z (B i)) y (B i) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g B]
    exact Finset.sum_congr rfl (fun i _ => hdiag g hg y (B i))
  rw [htrace _ (contDiff_vectorPeriodize hv hf hs)]
  simp_rw [fderiv_fderiv_vectorPeriodize_apply hv hf hs]
  unfold vectorPeriodize
  simp_rw [htrace f hf]
  exact (finsum_sum_comm Finset.univ _ (fun i _ =>
    vectorPeriodize_finite_support hv ((hs.fderiv_apply ℝ (B i)).fderiv_apply ℝ (B i)) x)).symm

/-- A smooth real function has a smooth Laplacian. -/
theorem contDiff_laplacian {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Δ f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := hd.fderiv_right (by simp)
  have he : Δ f = fun y => ∑ i, fderiv ℝ (fderiv ℝ f) y
      (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) := by
    ext y
    simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [he]
  exact ContDiff.sum fun i _ => (hdd.clm_apply contDiff_const).clm_apply contDiff_const

end Riesz1
