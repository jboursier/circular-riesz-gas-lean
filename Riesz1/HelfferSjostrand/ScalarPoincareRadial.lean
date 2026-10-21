/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Poincare.Euclidean
public import Riesz1.HelfferSjostrand.GeometryLawBijection

/-!
# Euclidean Poincaré in orthonormal radial coordinates

All geometric facts are
proved here under distinct names, independently of the
anchored and radial-domain modules. The orthonormal chart
takes an explicit basis of `eᗮ`. Every such basis gives the same Euclidean metric.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Submodule
open scoped ContDiff InnerProductSpace

namespace Riesz1

variable {N : ℕ+}
variable (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace N))) ℝ (hsOrthSubspace N))

/-- Orthonormal Euclidean coordinates on `eᗮ`. -/
def scalarPoincareRadialChart :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N))) ≃ₗᵢ[ℝ] hsOrthSubspace N :=
  basis.repr.symm

/-- The orthonormal radial chart followed by inclusion in ambient space. -/
def scalarPoincareRadialEmbedding :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N))) →ₗᵢ[ℝ] HsEuclidean N :=
  (hsOrthSubspace N).subtypeₗᵢ.comp (scalarPoincareRadialChart basis).toLinearIsometry

/-- The radial domain in orthonormal Euclidean coordinates. -/
def scalarPoincareRadialDomain :
    Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))) :=
  (scalarPoincareRadialEmbedding basis) ⁻¹' hsChamber N

theorem scalarPoincare_radial_dimension {N : ℕ+} (hN : 2 ≤ (N : ℕ)) :
    0 < Module.finrank ℝ (hsOrthSubspace N) := by
  have he : hsUnitVector N ≠ 0 := by
    intro h
    have hn := hsUnitVector_norm N
    rw [h, norm_zero] at hn
    norm_num at hn
  have hdim := (ℝ ∙ hsUnitVector N).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton he, finrank_euclideanSpace, Fintype.card_fin] at hdim
  change 0 < Module.finrank ℝ (ℝ ∙ hsUnitVector N)ᗮ
  omega

theorem isOpen_scalarPoincareRadialDomain :
    IsOpen (scalarPoincareRadialDomain basis) :=
  (isOpen_hsChamber N).preimage (scalarPoincareRadialEmbedding basis).continuous

theorem convex_scalarPoincareRadialDomain :
    Convex ℝ (scalarPoincareRadialDomain basis) := by
  intro x hx y hy a b ha hb hab
  change scalarPoincareRadialEmbedding basis (a • x + b • y) ∈ hsChamber N
  rw [map_add, map_smul, map_smul]
  constructor
  · intro i j hij
    change a * _ + b * _ < a * _ + b * _
    rcases ha.eq_or_lt with h | h
    · have hb1 : b = 1 := by linarith
      simpa [← h, hb1] using hy.1 hij
    · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hx.1 hij) h)
        (mul_le_mul_of_nonneg_left (hy.1 hij).le hb)
  · intro i
    change a * (scalarPoincareRadialEmbedding basis x) i + b * (scalarPoincareRadialEmbedding basis y) i <
      a * (scalarPoincareRadialEmbedding basis x) ⟨0, N.pos⟩ +
        b * (scalarPoincareRadialEmbedding basis y) ⟨0, N.pos⟩ + 1
    rcases ha.eq_or_lt with h | h
    · have hb1 : b = 1 := by linarith
      simpa [← h, hb1] using hy.2 i
    · have hp := mul_lt_mul_of_pos_left (hx.2 i) h
      have hq := mul_le_mul_of_nonneg_left (hy.2 i).le hb
      nlinarith

theorem scalarPoincare_radial_sum_zero {N : ℕ+} (z : hsOrthSubspace N) :
    ∑ i, (z : HsEuclidean N) i = 0 := by
  have hz := mem_orthogonal_singleton_iff_inner_left.mp z.property
  have hs : (Real.sqrt (N : ℕ))⁻¹ ≠ 0 := inv_ne_zero (sqrt_N_pos N).ne'
  have hinner : inner ℝ (z : HsEuclidean N) (hsUnitVector N) =
      (Real.sqrt (N : ℕ))⁻¹ * ∑ i, (z : HsEuclidean N) i := by
    simp [hsUnitVector, hsRotationVector, PiLp.inner_apply, inner_smul_right, Finset.mul_sum]
  rw [hinner] at hz
  exact (mul_eq_zero.mp hz).resolve_left hs

theorem scalarPoincare_radial_coord_bounds {N : ℕ+} {z : hsOrthSubspace N}
    (hz : z ∈ hsRadialDomain N) (i : Fin (N : ℕ)) :
    -1 < (z : HsEuclidean N) i ∧ (z : HsEuclidean N) i < 1 := by
  have hzero := scalarPoincare_radial_sum_zero z
  have hlo : (N : ℝ) * (z : HsEuclidean N) ⟨0, N.pos⟩ ≤ 0 := by
    calc (N : ℝ) * (z : HsEuclidean N) ⟨0, N.pos⟩ =
        ∑ _j : Fin (N : ℕ), (z : HsEuclidean N) ⟨0, N.pos⟩ := by simp
      _ ≤ ∑ j, (z : HsEuclidean N) j :=
        Finset.sum_le_sum fun j _ => hz.1.monotone (Fin.zero_le j)
      _ = 0 := hzero
  have hhi : (0 : ℝ) < (N : ℝ) * ((z : HsEuclidean N) ⟨0, N.pos⟩ + 1) := by
    have hh := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hz.2 j)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hzero] using hh
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr N.pos
  have h0 : (z : HsEuclidean N) ⟨0, N.pos⟩ ≤ 0 := by nlinarith
  have h1 : -1 < (z : HsEuclidean N) ⟨0, N.pos⟩ := by
    have := (mul_pos_iff_of_pos_left hN).mp hhi
    linarith
  exact ⟨h1.trans_le (hz.1.monotone (Fin.zero_le i)), by linarith [hz.2 i]⟩

theorem bounded_scalarPoincareRadialDomain :
    Bornology.IsBounded (scalarPoincareRadialDomain basis) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨Real.sqrt (N : ℕ), fun x hx => ?_⟩
  have hb := fun i => scalarPoincare_radial_coord_bounds
    (z := scalarPoincareRadialChart basis x) hx i
  have hsq : ‖scalarPoincareRadialEmbedding basis x‖ ^ 2 ≤ (N : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖(scalarPoincareRadialEmbedding basis x) i‖ ^ 2 ≤ ∑ _i : Fin (N : ℕ), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [Real.norm_eq_abs, sq_abs]
          have hi := hb i
          change -1 < (scalarPoincareRadialEmbedding basis x) i ∧
            (scalarPoincareRadialEmbedding basis x) i < 1 at hi
          nlinarith [hi.1, hi.2]
      _ = _ := by simp
  rw [LinearIsometry.norm_map] at hsq
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity), Real.sqrt_nonneg (N : ℕ)]

theorem nonempty_scalarPoincareRadialDomain :
    (scalarPoincareRadialDomain basis).Nonempty := by
  let x : HsEuclidean N := WithLp.toLp 2 (fun i : Fin (N : ℕ) => (i : ℝ) / N)
  have hx : x ∈ hsChamber N := by
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr N.pos
    constructor
    · intro i j hij
      exact (div_lt_div_iff_of_pos_right hN).mpr (by exact_mod_cast hij)
    · intro i
      dsimp only [x]
      norm_num only [Fin.val_zero, Nat.cast_zero, zero_div, zero_add]
      exact (div_lt_one hN).mpr (by exact_mod_cast i.isLt)
  refine ⟨(scalarPoincareRadialChart basis).symm (hsOrthComp N x), ?_⟩
  change ((scalarPoincareRadialChart basis)
    ((scalarPoincareRadialChart basis).symm (hsOrthComp N x)) : HsEuclidean N) ∈ hsChamber N
  rw [LinearIsometryEquiv.apply_symm_apply]
  change hsOrthProj N x ∈ hsChamber N
  rw [hsOrthProj_eq_translate]
  exact (hsTranslate_mem_chamber_iff _ _).mpr hx

/-- The pair Hamiltonian in orthonormal radial coordinates. -/
def scalarPoincareRadialPotential {c : ℝ} (χ : HsPairPotentials N c)
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))) : ℝ :=
  hsPairExpression χ (scalarPoincareRadialEmbedding basis x)

theorem contDiffOn_scalarPoincareRadialPotential {c : ℝ}
    (χ : HsPairPotentials N c) :
    ContDiffOn ℝ ∞ (scalarPoincareRadialPotential basis χ) (scalarPoincareRadialDomain basis) :=
  (hsPairExpression_contDiffOn χ).comp (scalarPoincareRadialEmbedding basis).contDiff.contDiffOn
    (fun _ hx => hx)

theorem hessian_scalarPoincareRadialPotential {c : ℝ} (χ : HsPairPotentials N c)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))}
    (hy : y ∈ scalarPoincareRadialDomain basis)
    (u v : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))) :
    fderiv ℝ (fderiv ℝ (scalarPoincareRadialPotential basis χ)) y u v =
      fderiv ℝ (fderiv ℝ (hsPairExpression χ)) (scalarPoincareRadialEmbedding basis y)
        (scalarPoincareRadialEmbedding basis u) (scalarPoincareRadialEmbedding basis v) := by
  let A := (scalarPoincareRadialEmbedding basis).toContinuousLinearMap
  have hgrad : fderiv ℝ (scalarPoincareRadialPotential basis χ) =ᶠ[𝓝 y]
      fun z => (hsPairGradient χ (A z)).comp A := by
    filter_upwards [(isOpen_scalarPoincareRadialDomain basis).mem_nhds hy] with z hz
    exact ((hasFDerivAt_hsPairExpression χ hz).comp z A.hasFDerivAt).fderiv
  rw [hgrad.fderiv_eq]
  have hc : HasFDerivAt (fun z => hsPairGradient χ (A z))
      ((hsPairHessian χ (A y)).comp A) y :=
    (hasFDerivAt_hsPairGradient χ hy).comp y A.hasFDerivAt
  rw [(hc.clm_comp (hasFDerivAt_const A y)).fderiv, fderiv_fderiv_hsPairExpression χ hy]
  simp [A, ContinuousLinearMap.comp_apply]

theorem hessian_scalarPoincareRadialPotential_lower {c : ℝ}
    (χ : HsPairPotentials N c)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))}
    (hy : y ∈ scalarPoincareRadialDomain basis)
    (b : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))) :
    2 * c * N * ‖b‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (scalarPoincareRadialPotential basis χ)) y b b := by
  rw [hessian_scalarPoincareRadialPotential basis χ hy]
  have hb := mem_orthogonal_singleton_iff_inner_left.mp (scalarPoincareRadialChart basis b).property
  have hh := hessian_hsPairExpression_lower_bound χ hy (scalarPoincareRadialEmbedding basis b) hb
  simpa only [LinearIsometry.norm_map] using hh

/-- Radial Poincaré with constant `(2cN)⁻¹`, in orthonormal Euclidean
coordinates, for every function in the weighted `H¹` completion. -/
theorem scalar_poincare_radial (hPL : External.PrekopaLeindler)
    (hN : 2 ≤ (N : ℕ)) {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)
    {F : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N))) → ℝ}
    {G : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N))) →
      EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))}
    (hFG : WeightedSobolev.IsWeightedH1
      ((volume.restrict (scalarPoincareRadialDomain basis)).tilted
        (fun y => -scalarPoincareRadialPotential basis χ y)) (scalarPoincareRadialDomain basis) F G) :
    let ν := (volume.restrict (scalarPoincareRadialDomain basis)).tilted
      (fun y => -scalarPoincareRadialPotential basis χ y)
    (∫ y, (F y - ∫ z, F z ∂ν) ^ 2 ∂ν) ≤ (2 * c * N)⁻¹ * ∫ y, ‖G y‖ ^ 2 ∂ν :=
  poincare_euclidean_H1 hPL (scalarPoincare_radial_dimension hN)
    (bounded_scalarPoincareRadialDomain basis) (isOpen_scalarPoincareRadialDomain basis)
    (nonempty_scalarPoincareRadialDomain basis) (convex_scalarPoincareRadialDomain basis)
    ((contDiffOn_scalarPoincareRadialPotential basis χ).of_le (by norm_num))
    (by positivity) (fun _ hy b => hessian_scalarPoincareRadialPotential_lower basis χ hy b) hFG

end Riesz1

end
