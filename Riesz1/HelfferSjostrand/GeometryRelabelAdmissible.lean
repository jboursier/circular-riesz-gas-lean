/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GeometryRelabelPairs
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Cyclic relabeling preserves admissibility, gradient norms and the Laplacian

The relabeled Hamiltonian `H' = hsPairExpression (hsRelabelPairs χ k)` satisfies
`H'(T_k x) = H(x)` on the whole lift space (`hsPairExpression_relabel`). The relabeling
`T_k` is an affine map whose linear part is a coordinate permutation, that is a linear isometry.
Hence the gradient norm and the Laplacian at `T_k x` are those at `x`, and the boundary distance is
invariant (`hsBoundaryDistance_relabel`). These give the admissibility of the relabeled potentials
with the same constants `c` and `C_N`.

This is the relabeling assertion in the proof of Lemma 3.6.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Finset
open scoped Topology ContDiff InnerProductSpace

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

/-- The coordinate permutation `(L z)_i = z_{σ i}` of the lift space, as a linear isometry. -/
def hsCycLinear (N : ℕ+) (k : ℕ) : HsEuclidean N ≃ₗᵢ[ℝ] HsEuclidean N :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (hsCycEquiv N k).symm

theorem hsCycLinear_apply (N : ℕ+) (k : ℕ) (z : HsEuclidean N) (i : Fin (N : ℕ)) :
    hsCycLinear N k z i = z (hsCycIdx N k i) := rfl

/-- The linear part of the relabeling, as a continuous linear map. -/
def hsCycCLM (N : ℕ+) (k : ℕ) : HsEuclidean N →L[ℝ] HsEuclidean N :=
  (hsCycLinear N k).toContinuousLinearEquiv.toContinuousLinearMap

/-- The shift `(⌊(i + k)/N⌋)_i` of the relabeling. -/
def hsCycShiftVec (N : ℕ+) (k : ℕ) : HsEuclidean N :=
  WithLp.toLp 2 (fun i => (hsCycShift N k i : ℝ))

/-- The relabeling is the affine map with linear part `hsCycCLM` and shift `hsCycShiftVec`. -/
theorem hsRelabel_eq_affine (N : ℕ+) (k : ℕ) (z : HsEuclidean N) :
    hsRelabel N k z = hsCycCLM N k z + hsCycShiftVec N k := by
  ext i
  rw [hsRelabel_apply, PiLp.add_apply]
  rfl

/-- Second derivative of a composition with an affine map, on the chamber. -/
theorem fderiv_fderiv_pairExpression_affine (χ : HsPairPotentials N c)
    (L : HsEuclidean N →L[ℝ] HsEuclidean N) (v : HsEuclidean N) {x : HsEuclidean N}
    (hx : L x + v ∈ hsChamber N) (u w : HsEuclidean N) :
    fderiv ℝ (fderiv ℝ (fun z => hsPairExpression χ (L z + v))) x u w =
      fderiv ℝ (fderiv ℝ (hsPairExpression χ)) (L x + v) (L u) (L w) := by
  have hgrad : fderiv ℝ (fun z => hsPairExpression χ (L z + v)) =ᶠ[𝓝 x]
      fun z => (hsPairGradient χ (L z + v)).comp L := by
    have hopen : IsOpen ((fun z => L z + v) ⁻¹' hsChamber N) :=
      (isOpen_hsChamber N).preimage (L.continuous.add continuous_const)
    filter_upwards [hopen.mem_nhds hx] with z hz
    exact ((hasFDerivAt_hsPairExpression χ hz).comp z (L.hasFDerivAt.add_const v)).fderiv
  rw [hgrad.fderiv_eq]
  have hc := HasFDerivAt.comp (g := hsPairGradient χ) (f := fun z => L z + v) x
    (hasFDerivAt_hsPairGradient χ hx) (L.hasFDerivAt.add_const v)
  have hd := hc.clm_comp (hasFDerivAt_const L x)
  have key : fderiv ℝ (fun z => (hsPairGradient χ (L z + v)).comp L) x = _ := hd.fderiv
  rw [key, fderiv_fderiv_hsPairExpression χ hx]
  simp

/-- The Laplacian is the trace of the second derivative in any orthonormal basis. -/
theorem laplacian_eq_sum_fderiv_fderiv (f : HsEuclidean N → ℝ)
    (v : OrthonormalBasis (Fin (N : ℕ)) ℝ (HsEuclidean N)) (x : HsEuclidean N) :
    Laplacian.laplacian f x = ∑ i, fderiv ℝ (fderiv ℝ f) x (v i) (v i) := by
  have h := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f v) x
  rw [h]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The gradient norm is the operator norm of the derivative. -/
theorem norm_gradient_eq_norm_fderiv (f : HsEuclidean N → ℝ) (x : HsEuclidean N) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  unfold gradient
  exact LinearIsometryEquiv.norm_map _ _

/-- The gradient norm is invariant under the cyclic relabeling. -/
theorem norm_gradient_relabel (χ : HsPairPotentials N c) (k : ℕ) {x : HsEuclidean N}
    (hx : x ∈ hsChamber N) :
    ‖gradient (hsPairExpression (hsRelabelPairs χ k)) (hsRelabel N k x)‖ =
      ‖gradient (hsPairExpression χ) x‖ := by
  rw [norm_gradient_eq_norm_fderiv, norm_gradient_eq_norm_fderiv, hsRelabel_eq_affine]
  have hTx : hsCycCLM N k x + hsCycShiftVec N k ∈ hsChamber N := by
    rw [← hsRelabel_eq_affine]
    exact hsRelabel_mem_chamber N k hx
  have hfun : hsPairExpression χ = fun z =>
      hsPairExpression (hsRelabelPairs χ k) (hsCycCLM N k z + hsCycShiftVec N k) := by
    funext z
    rw [← hsRelabel_eq_affine, hsPairExpression_relabel]
  have hD : HasFDerivAt (hsPairExpression χ)
      ((hsPairGradient (hsRelabelPairs χ k) (hsCycCLM N k x + hsCycShiftVec N k)).comp
        (hsCycCLM N k)) x := by
    rw [hfun]
    exact ((hasFDerivAt_hsPairExpression (hsRelabelPairs χ k) hTx).comp x
      ((hsCycCLM N k).hasFDerivAt.add_const _))
  rw [hD.fderiv, (hasFDerivAt_hsPairExpression (hsRelabelPairs χ k) hTx).fderiv]
  exact (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv
    (hsPairGradient (hsRelabelPairs χ k) (hsCycCLM N k x + hsCycShiftVec N k)) (hsCycLinear N k)).symm

/-- The Laplacian is invariant under the cyclic relabeling. -/
theorem laplacian_relabel (χ : HsPairPotentials N c) (k : ℕ) {x : HsEuclidean N}
    (hx : x ∈ hsChamber N) :
    Laplacian.laplacian (hsPairExpression (hsRelabelPairs χ k)) (hsRelabel N k x) =
      Laplacian.laplacian (hsPairExpression χ) x := by
  have hTx : hsCycCLM N k x + hsCycShiftVec N k ∈ hsChamber N := by
    rw [← hsRelabel_eq_affine]
    exact hsRelabel_mem_chamber N k hx
  have hfun : hsPairExpression χ = fun z =>
      hsPairExpression (hsRelabelPairs χ k) (hsCycCLM N k z + hsCycShiftVec N k) := by
    funext z
    rw [← hsRelabel_eq_affine, hsPairExpression_relabel]
  let b : OrthonormalBasis (Fin (N : ℕ)) ℝ (HsEuclidean N) := EuclideanSpace.basisFun _ ℝ
  rw [laplacian_eq_sum_fderiv_fderiv _ (b.map (hsCycLinear N k)), hsRelabel_eq_affine,
    laplacian_eq_sum_fderiv_fderiv _ b, hfun]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_fderiv_pairExpression_affine (hsRelabelPairs χ k) (hsCycCLM N k) _ hTx]
  rfl

/-- The Hessian of the relabeled Hamiltonian, read through the linear isometry, is the Hessian of
the old one: `∇²H(u, w) = ∇²H'(T_k x)(L u, L w)`. -/
theorem hessian_relabel_identity (χ : HsPairPotentials N c) (k : ℕ) {x : HsEuclidean N}
    (hx : x ∈ hsChamber N) (u w : HsEuclidean N) :
    fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x u w =
      fderiv ℝ (fderiv ℝ (hsPairExpression (hsRelabelPairs χ k))) (hsRelabel N k x)
        (hsCycLinear N k u) (hsCycLinear N k w) := by
  have hTx : hsCycCLM N k x + hsCycShiftVec N k ∈ hsChamber N := by
    rw [← hsRelabel_eq_affine]
    exact hsRelabel_mem_chamber N k hx
  have hfun : hsPairExpression χ = fun z =>
      hsPairExpression (hsRelabelPairs χ k) (hsCycCLM N k z + hsCycShiftVec N k) := by
    funext z
    rw [← hsRelabel_eq_affine, hsPairExpression_relabel]
  rw [hfun, fderiv_fderiv_pairExpression_affine (hsRelabelPairs χ k) (hsCycCLM N k) _ hTx,
    hsRelabel_eq_affine]
  rfl

/-- A bilinear form transported by a linear isometry has operator norm at most that of the
transported form. -/
theorem opNorm_bilinear_le_of_isometry (e : HsEuclidean N ≃ₗᵢ[ℝ] HsEuclidean N)
    (B B' : HsEuclidean N →L[ℝ] (HsEuclidean N →L[ℝ] ℝ))
    (h : ∀ u w, B u w = B' (e u) (e w)) : ‖B‖ ≤ ‖B'‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B') fun u => ?_
  refine ContinuousLinearMap.opNorm_le_bound (B u) (by positivity) fun w => ?_
  rw [h]
  calc ‖B' (e u) (e w)‖ ≤ ‖B' (e u)‖ * ‖e w‖ := (B' (e u)).le_opNorm (e w)
    _ ≤ (‖B'‖ * ‖e u‖) * ‖e w‖ :=
        mul_le_mul_of_nonneg_right (B'.le_opNorm (e u)) (norm_nonneg _)
    _ = ‖B'‖ * ‖u‖ * ‖w‖ := by rw [e.norm_map, e.norm_map]

/-- The operator norm of the Hessian is invariant under the cyclic relabeling. -/
theorem norm_fderiv_fderiv_relabel (χ : HsPairPotentials N c) (k : ℕ) {x : HsEuclidean N}
    (hx : x ∈ hsChamber N) :
    ‖fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x‖ =
      ‖fderiv ℝ (fderiv ℝ (hsPairExpression (hsRelabelPairs χ k))) (hsRelabel N k x)‖ := by
  have h1 := hessian_relabel_identity χ k hx
  apply le_antisymm
  · exact opNorm_bilinear_le_of_isometry (hsCycLinear N k) _ _ h1
  · refine opNorm_bilinear_le_of_isometry (hsCycLinear N k).symm _ _ (fun u w => ?_)
    rw [h1 ((hsCycLinear N k).symm u) ((hsCycLinear N k).symm w),
      LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

/-- The cyclic relabeling preserves admissibility, with the same constants `c` and `C_N`. -/
theorem hsAdmissible_relabel (χ : HsPairPotentials N c) {C_N : ℝ} (h : HsAdmissible χ C_N)
    (k : ℕ) : HsAdmissible (hsRelabelPairs χ k) C_N := by
  obtain ⟨hN, hc, hC, hbound⟩ := h
  refine ⟨hN, hc, hC, fun y hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hsRelabel_exists_preimage N k hy
  rw [norm_gradient_relabel χ k hx, laplacian_relabel χ k hx,
    hsBoundaryDistance_relabel N hN k x]
  exact hbound x hx

end Riesz1

end
