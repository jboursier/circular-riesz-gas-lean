/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.ScalarPoincareProductCore
public import Riesz1.HelfferSjostrand.ScalarPoincareCompletion
public import Riesz1.ToMathlib.Poincare.ProductEnergy

/-!
# Scalar Poincaré on the radial and rotation product

The smooth-core tensorization step of the scalar Poincaré inequality, with
the exact maximum constant.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff InnerProductSpace

namespace Riesz1

variable {N : ℕ+}
variable (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace N))) ℝ (hsOrthSubspace N))

local instance : Fact (0 < Real.sqrt (N : ℕ)) := ⟨sqrt_N_pos N⟩

theorem scalarPoincareRadial_isProbabilityMeasure {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c) :
    IsProbabilityMeasure ((volume.restrict (scalarPoincareRadialDomain basis)).tilted
      (fun y => -scalarPoincareRadialPotential basis χ y)) := by
  apply (Measure.isProbabilityMeasure_map_iff
    (scalarPoincareRadialChart basis).continuous.measurable.aemeasurable).mp
  rw [scalarPoincareRadialChart_map basis χ hc]
  infer_instance

theorem scalarPoincare_gradient_continuousOn {f : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f) : ContinuousOn (gradient f) (closure (hsChamber N)) := by
  obtain ⟨_, W, hW, hsub, hfs⟩ := hf
  exact ((InnerProductSpace.toDual ℝ (HsEuclidean N)).symm.continuous.comp_continuousOn
    (hfs.continuousOn_fderiv_of_isOpen hW (by norm_num))).mono hsub

/-- The smooth-core estimate on the actual radial and uniform-circle
product. The radial chart is arbitrary and orthonormal. -/
theorem scalar_poincare_product (hPL : External.PrekopaLeindler)
    (hN : 2 ≤ (N : ℕ)) {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)
    {f : HsEuclidean N → ℝ} (hf : HsSmoothOnClosure N f) :
    let ν := (volume.restrict (scalarPoincareRadialDomain basis)).tilted
      (fun y => -scalarPoincareRadialPotential basis χ y)
    let η : Measure (AddCircle (Real.sqrt (N : ℕ))) := AddCircle.haarAddCircle
    let F := scalarPoincareProductExtension basis f
    let G := scalarPoincareProductExtension basis (gradient f)
    (∫ p, (F p - ∫ q, F q ∂ν.prod η) ^ 2 ∂ν.prod η) ≤
      hsPoincareConstant N c * ∫ p, ‖G p‖ ^ 2 ∂ν.prod η := by
  classical
  dsimp only
  let ν := (volume.restrict (scalarPoincareRadialDomain basis)).tilted
    (fun y => -scalarPoincareRadialPotential basis χ y)
  let η : Measure (AddCircle (Real.sqrt (N : ℕ))) := AddCircle.haarAddCircle
  have : IsProbabilityMeasure ν := scalarPoincareRadial_isProbabilityMeasure basis χ hc
  have : IsProbabilityMeasure η := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
  let F := scalarPoincareProductExtension basis f
  let G := scalarPoincareProductExtension basis (gradient f)
  let T := fun p => (inner ℝ (G p) (hsUnitVector N)) ^ 2
  let R := fun p => ‖G p‖ ^ 2 - T p
  obtain ⟨hFm, C, hC⟩ := scalarPoincareProductExtension_properties basis f
    (hf.2.choose_spec.2.2.continuousOn.mono hf.2.choose_spec.2.1)
  obtain ⟨hGm, D, hD⟩ := scalarPoincareProductExtension_properties basis (gradient f)
    (scalarPoincare_gradient_continuousOn hf)
  have hG : MemLp G 2 (ν.prod η) :=
    MemLp.of_bound hGm.aestronglyMeasurable D (Eventually.of_forall hD)
  have hJ : MemLp (fun p => inner ℝ (G p) (hsUnitVector N)) 2 (ν.prod η) := by
    apply MemLp.of_bound (hGm.inner stronglyMeasurable_const).aestronglyMeasurable D
    exact Eventually.of_forall fun p => (by
      simpa only [Real.norm_eq_abs, hsUnitVector_norm, mul_one] using
        (abs_real_inner_le_norm (G p) (hsUnitVector N)).trans
          (by simpa only [hsUnitVector_norm, mul_one] using hD p))
  have hTi : Integrable T (ν.prod η) := hJ.integrable_sq
  have hRi : Integrable R (ν.prod η) := hG.norm.integrable_sq.sub hTi
  have hν := scalarPoincareRadial_ae_mem basis χ
  have hradial : ∀ w : AddCircle (Real.sqrt (N : ℕ)),
      (∫ q, (F (q, w) - ∫ z, F (z, w) ∂ν) ^ 2 ∂ν) ≤
        (2 * c * (N : ℝ))⁻¹ * ∫ q, R (q, w) ∂ν := by
    intro w
    let t : ℝ := AddCircle.equivIoc (Real.sqrt (N : ℕ)) 0 w
    let fw := fun q => f (scalarPoincareRadialEmbedding basis q + t • hsUnitVector N)
    have hfw := Poincare.isWeightedH1_of_smoothNearClosure
      (bounded_scalarPoincareRadialDomain basis) hν
      (scalarPoincare_radialSlice_smooth basis hf t)
    have hF : (fun q => F (q, w)) =ᵐ[ν] fw := hν.mono fun q hq =>
      scalarPoincareProductExtension_of_mem basis f hq w
    have hR : (fun q => R (q, w)) =ᵐ[ν] (fun q => ‖gradient fw q‖ ^ 2) := by
      filter_upwards [hν] with q hq
      dsimp only [R, T, G]
      rw [scalarPoincareProductExtension_of_mem basis (gradient f) hq]
      dsimp only [fw]
      rw [scalarPoincare_radialSlice_gradient basis hf hq t, LinearIsometryEquiv.norm_map]
      exact sub_eq_iff_eq_add.mpr (norm_sq_hsOrthComp N _)
    have hv : (∫ q, (F (q, w) - ∫ z, F (z, w) ∂ν) ^ 2 ∂ν) =
        ∫ q, (fw q - ∫ z, fw z ∂ν) ^ 2 ∂ν := by
      rw [integral_congr_ae hF]
      exact integral_congr_ae (hF.mono fun _ h =>
        congrArg (fun a => (a - ∫ z, fw z ∂ν) ^ 2) h)
    rw [hv, integral_congr_ae hR]
    exact scalar_poincare_radial basis hPL hN χ hc hfw
  have hcircle : ∀ᵐ q ∂ν,
      (∫ w, (F (q, w) - ∫ z, F (q, z) ∂η) ^ 2 ∂η) ≤
        ((N : ℝ) / (4 * Real.pi ^ 2)) * ∫ w, T (q, w) ∂η := by
    filter_upwards [hν] with q hq
    have hfc : (fun t : ℝ => F (q, (t : AddCircle (Real.sqrt (N : ℕ))))) =
        fun t : ℝ => f (scalarPoincareRadialEmbedding basis q + t • hsUnitVector N) := by
      funext t
      dsimp only [F]
      rw [scalarPoincareProductExtension_of_mem basis f hq,
        scalarPoincareProductLift_coe basis f hf.1]
    have hgc : ∀ t : ℝ, G (q, (t : AddCircle (Real.sqrt (N : ℕ)))) =
        gradient f (scalarPoincareRadialEmbedding basis q + t • hsUnitVector N) := by
      intro t
      dsimp only [G]
      rw [scalarPoincareProductExtension_of_mem basis (gradient f) hq,
        scalarPoincareProductLift_coe basis (gradient f) (scalarPoincare_gradient_translate hf)]
    have hderiv : ∀ t : ℝ,
        deriv (fun s : ℝ => F (q, (s : AddCircle (Real.sqrt (N : ℕ))))) t =
          inner ℝ (G (q, (t : AddCircle (Real.sqrt (N : ℕ))))) (hsUnitVector N) := by
      intro t
      rw [hfc, scalarPoincare_circleSlice_deriv basis hf hq, hgc]
    have he : (∫ w, T (q, w) ∂η) = (Real.sqrt (N : ℕ))⁻¹ *
        ∫ t in (0 : ℝ)..Real.sqrt (N : ℕ),
          deriv (fun s : ℝ => F (q, (s : AddCircle (Real.sqrt (N : ℕ))))) t ^ 2 := by
      rw [AddCircle.integral_haarAddCircle,
        ← AddCircle.intervalIntegral_preimage (Real.sqrt (N : ℕ)) 0]
      simp only [zero_add, smul_eq_mul, hderiv, T]
    have hk : (Real.sqrt (N : ℕ) / (2 * Real.pi)) ^ 2 =
        (N : ℝ) / (4 * Real.pi ^ 2) := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      ring
    rw [he, ← hk]
    exact integral_sub_mean_sq_le_haarAddCircle _ (fun w => F (q, w))
      (by rw [hfc]; exact (scalarPoincare_circleSlice_smooth basis hf hq).of_le (by norm_num))
  have hprod := Poincare.product_energy_bound ν η hFm hC hRi hTi
    (Eventually.of_forall hradial) hcircle
  have hT0 : 0 ≤ ∫ p, T p ∂ν.prod η := integral_nonneg fun _ => sq_nonneg _
  have hR0 : 0 ≤ ∫ p, R p ∂ν.prod η := integral_nonneg fun p => by
    have hn := norm_sq_hsOrthComp N (G p)
    change (0 : ℝ) ≤ ‖G p‖ ^ 2 - (inner ℝ (G p) (hsUnitVector N)) ^ 2
    nlinarith [sq_nonneg ‖(hsOrthComp N (G p) : HsEuclidean N)‖]
  have hsum : (∫ p, T p ∂ν.prod η) + (∫ p, R p ∂ν.prod η) =
      ∫ p, ‖G p‖ ^ 2 ∂ν.prod η := by
    rw [← integral_add hTi hRi]
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => by dsimp only [R]; ring
  apply hprod.trans
  calc
    _ ≤ hsPoincareConstant N c * (∫ p, T p ∂ν.prod η) +
        hsPoincareConstant N c * (∫ p, R p ∂ν.prod η) :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hT0)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hR0)
    _ = _ := by rw [← mul_add, hsum]

end Riesz1

end
