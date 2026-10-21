/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.ScalarPoincareRadial
public import Riesz1.HelfferSjostrand.Sobolev
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Smooth slices in radial and common-rotation coordinates

The calculus part of the product proof of the scalar Poincaré inequality:
smoothness, periodicity, and the exact orthogonal decomposition of
the gradient energy. These are statements about the actual smooth core.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology Submodule
open scoped ContDiff InnerProductSpace

namespace Riesz1

variable {N : ℕ+}
variable (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace N))) ℝ (hsOrthSubspace N))

theorem scalarPoincare_slice_mem {q : EuclideanSpace ℝ
    (Fin (Module.finrank ℝ (hsOrthSubspace N)))}
    (hq : q ∈ scalarPoincareRadialDomain basis) (t : ℝ) :
    scalarPoincareRadialEmbedding basis q + t • hsUnitVector N ∈ hsChamber N := by
  rw [add_smul_hsUnitVector]
  exact (hsTranslate_mem_chamber_iff _ _).mpr hq

theorem scalarPoincare_radialSlice_smooth {f : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f) (t : ℝ) :
    WeightedSobolev.SmoothNearClosure (scalarPoincareRadialDomain basis)
      (fun q => f (scalarPoincareRadialEmbedding basis q + t • hsUnitVector N)) := by
  obtain ⟨_, W, hW, hsub, hfs⟩ := hf
  let A := fun q => scalarPoincareRadialEmbedding basis q + t • hsUnitVector N
  have hA : ContDiff ℝ ∞ A := (scalarPoincareRadialEmbedding basis).contDiff.add contDiff_const
  have hmap : MapsTo A (scalarPoincareRadialDomain basis) (hsChamber N) :=
    fun _ hq => scalarPoincare_slice_mem basis hq t
  refine ⟨A ⁻¹' W, hW.preimage hA.continuous, ?_, ?_⟩
  · intro q hq
    exact hsub (hmap.closure hA.continuous hq)
  · exact hfs.comp hA.contDiffOn (fun _ hx => hx)

theorem scalarPoincare_circleSlice_smooth {f : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f)
    {q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))}
    (hq : q ∈ scalarPoincareRadialDomain basis) :
    ContDiff ℝ ∞ (fun t : ℝ => f (scalarPoincareRadialEmbedding basis q + t • hsUnitVector N)) := by
  obtain ⟨_, W, _, hsub, hfs⟩ := hf
  exact hfs.comp_contDiff (contDiff_const.add (contDiff_id.smul contDiff_const))
    (fun t => hsub (subset_closure (scalarPoincare_slice_mem basis hq t)))

theorem scalarPoincare_circleSlice_periodic {f : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f)
    (q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))) :
    Function.Periodic (fun t : ℝ => f (scalarPoincareRadialEmbedding basis q + t • hsUnitVector N))
      (Real.sqrt (N : ℕ)) := by
  intro t
  have hx : scalarPoincareRadialEmbedding basis q + (t + Real.sqrt (N : ℕ)) • hsUnitVector N =
      hsTranslate 1 (scalarPoincareRadialEmbedding basis q + t • hsUnitVector N) := by
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, hsUnitVector, hsRotationVector, smul_eq_mul,
      hsTranslate_apply]
    have hs := (sqrt_N_pos N).ne'
    field_simp
    ring
  dsimp only
  rw [hx]
  simpa only [Int.cast_one] using hf.1 (1 : ℤ)
    (scalarPoincareRadialEmbedding basis q + t • hsUnitVector N)

theorem scalarPoincare_circleSlice_deriv {f : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f)
    {q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))}
    (hq : q ∈ scalarPoincareRadialDomain basis) (t : ℝ) :
    deriv (fun s : ℝ => f (scalarPoincareRadialEmbedding basis q + s • hsUnitVector N)) t =
      inner ℝ (gradient f (scalarPoincareRadialEmbedding basis q + t • hsUnitVector N))
        (hsUnitVector N) := by
  have hd := ((hasDerivAt_id t).smul_const (hsUnitVector N)).const_add
    (scalarPoincareRadialEmbedding basis q)
  have hcomp := (hf.differentiableAt (scalarPoincare_slice_mem basis hq t)).hasFDerivAt.comp_hasDerivAt t hd
  rw [inner_gradient_eq_fderiv]
  simpa only [Function.comp_def, id_eq, one_smul] using hcomp.deriv

theorem scalarPoincare_radialSlice_gradient {f : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f)
    {q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))}
    (hq : q ∈ scalarPoincareRadialDomain basis) (t : ℝ) :
    gradient (fun p => f (scalarPoincareRadialEmbedding basis p + t • hsUnitVector N)) q =
      (scalarPoincareRadialChart basis).symm
        (hsOrthComp N (gradient f (scalarPoincareRadialEmbedding basis q + t • hsUnitVector N))) := by
  let A := (scalarPoincareRadialEmbedding basis).toContinuousLinearMap
  let X := scalarPoincareRadialEmbedding basis q + t • hsUnitVector N
  let w := gradient f X
  have hd := (hf.differentiableAt (scalarPoincare_slice_mem basis hq t)).hasFDerivAt.comp q
    (A.hasFDerivAt.add_const (t • hsUnitVector N))
  apply (InnerProductSpace.toDual ℝ _).injective
  simp only [gradient, LinearIsometryEquiv.apply_symm_apply]
  change fderiv ℝ (fun p => f (A p + t • hsUnitVector N)) q = _
  have hdeq : fderiv ℝ (fun p => f (A p + t • hsUnitVector N)) q =
      (fderiv ℝ f X).comp A := by
    convert hd.fderiv using 1
    rfl
  rw [hdeq]
  ext h
  change fderiv ℝ f X (A h) = inner ℝ ((scalarPoincareRadialChart basis).symm (hsOrthComp N w)) h
  rw [← inner_gradient_eq_fderiv, ← (scalarPoincareRadialChart basis).inner_map_map,
    LinearIsometryEquiv.apply_symm_apply]
  change inner ℝ w (A h) = inner ℝ (hsOrthComp N w : HsEuclidean N) (A h)
  rw [hsOrthComp_coe, inner_sub_left, real_inner_smul_left]
  have hh : inner ℝ (hsUnitVector N) (A h) = 0 :=
    mem_orthogonal_singleton_iff_inner_right.mp (scalarPoincareRadialChart basis h).property
  rw [hh, mul_zero, sub_zero]

/-- The two slice derivatives recover precisely the full gradient energy. -/
theorem scalarPoincare_slice_energy {f : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f)
    {q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))}
    (hq : q ∈ scalarPoincareRadialDomain basis) (t : ℝ) :
    ‖gradient (fun p => f (scalarPoincareRadialEmbedding basis p + t • hsUnitVector N)) q‖ ^ 2 +
      (deriv (fun s : ℝ => f (scalarPoincareRadialEmbedding basis q + s • hsUnitVector N)) t) ^ 2 =
      ‖gradient f (scalarPoincareRadialEmbedding basis q + t • hsUnitVector N)‖ ^ 2 := by
  rw [scalarPoincare_radialSlice_gradient basis hf hq, scalarPoincare_circleSlice_deriv basis hf hq,
    LinearIsometryEquiv.norm_map]
  exact (norm_sq_hsOrthComp N _).symm

end Riesz1

end
