/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.Fourier
public import Riesz1.Kernel.Normalization
public import Riesz1.ToMathlib.HurwitzKernel.MellinIntegrability

/-!
# Fourier coefficients of the Riesz kernel

The mean-subtracted theta Mellin representation is absolutely integrable
in space and time. Fubini and the Gaussian Fourier coefficients therefore
compute every nonzero coefficient. The zero coefficient is the kernel's mean.
-/

public section

open MeasureTheory Complex Set

namespace Riesz1

private lemma fourierCoeff_evenKernel_sub (t : ℝ) (ht : 0 < t) (k : ℤ) (hk : k ≠ 0) :
    fourierCoeff (fun x : UnitAddCircle => (HurwitzZeta.evenKernel x t : ℂ) -
      (t : ℂ) ^ (-(1 / 2 : ℂ))) k =
        ((1 / t ^ (1 / 2 : ℝ) * Real.exp (-Real.pi * (k : ℝ) ^ 2 / t) : ℝ) : ℂ) := by
  have hconst : (∫ x : UnitAddCircle, fourier (-k) x ∂AddCircle.haarAddCircle) = 0 := by
    have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) 0) k
    simpa [fourierCoeff, fourier_zero, smul_eq_mul, Pi.single_apply, hk] using h
  calc
    _ = fourierCoeff (fun x : UnitAddCircle => (HurwitzZeta.evenKernel x t : ℂ)) k -
        ∫ x : UnitAddCircle, fourier (-k) x * (t : ℂ) ^ (-(1 / 2 : ℂ))
          ∂AddCircle.haarAddCircle := by
      simp only [fourierCoeff, smul_eq_mul, mul_sub]
      exact integral_sub ((integrable_evenKernel_complex t ht).fourier_smul (-k))
        ((integrable_const ((t : ℂ) ^ (-(1 / 2 : ℂ)))).fourier_smul (-k))
    _ = _ := by
      rw [integral_mul_const, hconst, zero_mul, sub_zero, fourierCoeff_evenKernel t ht k]

private lemma fourierCoeff_thetaMellin (s : ℝ) (hs : s < 1) (k : ℤ) (hk : k ≠ 0) :
    fourierCoeff (fun x : UnitAddCircle =>
      mellin (fun t : ℝ => (HurwitzZeta.evenKernel x t : ℂ) -
        (t : ℂ) ^ (-(1 / 2 : ℂ))) ((s : ℂ) / 2)) k =
      mellin (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) *
        (Real.exp (- (Real.pi * (k : ℝ) ^ 2) / t) : ℂ)) ((s : ℂ) / 2) := by
  let F (t : ℝ) (x : UnitAddCircle) : ℂ :=
    (t : ℂ) ^ ((s : ℂ) / 2 - 1) *
      ((HurwitzZeta.evenKernel x t : ℂ) - (t : ℂ) ^ (-(1 / 2 : ℂ)))
  have hprod : Integrable (fun p : ℝ × UnitAddCircle => fourier (-k) p.2 * F p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod AddCircle.haarAddCircle) := by
    apply (integrable_thetaMellin s hs).bdd_mul (c := 1)
    · exact ((fourier (-k)).continuous.comp continuous_snd).aestronglyMeasurable
    · exact ae_of_all _ (fun p => by simp only [fourier_apply, Circle.norm_coe, le_refl])
  calc
    _ = ∫ x : UnitAddCircle, (∫ t : ℝ in Ioi 0, fourier (-k) x * F t x)
        ∂AddCircle.haarAddCircle := by
      simp only [fourierCoeff, mellin, smul_eq_mul, F, integral_const_mul]
    _ = ∫ t : ℝ in Ioi 0, ∫ x : UnitAddCircle, fourier (-k) x * F t x
        ∂AddCircle.haarAddCircle := (integral_integral_swap hprod).symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have hmean : ((1 / t ^ (1 / 2 : ℝ) : ℝ) : ℂ) =
          (t : ℂ) ^ (-(1 / 2 : ℂ)) := by
        rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; rfl,
          ← ofReal_cpow ht.le, Real.rpow_neg ht.le]
        simp only [one_div]
      calc
        _ = (t : ℂ) ^ ((s : ℂ) / 2 - 1) *
            fourierCoeff (fun x : UnitAddCircle => (HurwitzZeta.evenKernel x t : ℂ) -
              (t : ℂ) ^ (-(1 / 2 : ℂ))) k := by
          simp only [F, fourierCoeff, smul_eq_mul, ← integral_const_mul]
          apply integral_congr_ae
          exact ae_of_all _ (fun x => by ring)
        _ = _ := by
          rw [fourierCoeff_evenKernel_sub t ht k hk, ofReal_mul, hmean]
          simp only [smul_eq_mul, neg_mul]

/-- Mellin representation of the kernel away from its collision. -/
theorem rieszRepresentative_eq_mellin (s : RieszExponent) (x : UnitAddCircle) (hx : x ≠ 0) :
    (rieszRepresentative s x : ℂ) =
      mellin (fun t : ℝ => (HurwitzZeta.evenKernel x t : ℂ) -
        (t : ℂ) ^ (-(1 / 2 : ℂ))) ((s.val : ℂ) / 2) / Complex.Gammaℝ (s.val : ℂ) := by
  rw [rieszRepresentative_complex_eq, (hasMellin_evenKernel_sub x hx s.val s.property.2).2,
    HurwitzZeta.hurwitzZetaEven_def_of_ne_or_ne (Or.inl hx)]
  ring

/-- Fourier coefficients of the periodic Riesz kernel, with probability Haar
measure on `AddCircle 1` (Lemma 2.1). -/
theorem fourierCoeff_rieszRepresentative (s : RieszExponent) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) k =
      if k = 0 then 0
      else ((rieszConstant s * (2 * Real.pi * |(k : ℝ)|) ^ (s.val - 1) : ℝ) : ℂ) := by
  classical
  by_cases hk : k = 0
  · subst k
    simpa using fourierCoeff_rieszRepresentative_zero s
  · simp only [hk, ite_false]
    have hq : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
    have hr : 0 < Real.pi * (k : ℝ) ^ 2 := mul_pos Real.pi_pos (sq_pos_of_ne_zero (by exact_mod_cast hk))
    have hae : (fun x : UnitAddCircle => (rieszRepresentative s x : ℂ)) =ᵐ[AddCircle.haarAddCircle]
        (fun x : UnitAddCircle =>
          mellin (fun t : ℝ => (HurwitzZeta.evenKernel x t : ℂ) -
            (t : ℂ) ^ (-(1 / 2 : ℂ))) ((s.val : ℂ) / 2) / Complex.Gammaℝ (s.val : ℂ)) := by
      rw [show (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume by
        simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm]
      have hnull : volume ({0} : Set UnitAddCircle) = 0 := by
        rw [← Metric.closedBall_zero (x := (0 : UnitAddCircle)), AddCircle.volume_closedBall]
        norm_num
      have hne : ∀ᵐ x : UnitAddCircle, x ≠ 0 := by
        simp only [ae_iff, not_not]
        convert hnull using 2
        ext x
        simp
      filter_upwards [hne] with x hx
      exact rieszRepresentative_eq_mellin s x hx
    rw [congrFun (fourierCoeff_congr_ae hae) k]
    have hdiv : (fun x : UnitAddCircle =>
        mellin (fun t : ℝ => (HurwitzZeta.evenKernel x t : ℂ) -
          (t : ℂ) ^ (-(1 / 2 : ℂ))) ((s.val : ℂ) / 2) / Complex.Gammaℝ (s.val : ℂ)) =
        (fun x : UnitAddCircle => (Complex.Gammaℝ (s.val : ℂ))⁻¹ *
          mellin (fun t : ℝ => (HurwitzZeta.evenKernel x t : ℂ) -
            (t : ℂ) ^ (-(1 / 2 : ℂ))) ((s.val : ℂ) / 2)) := by
      funext x
      ring
    rw [hdiv, fourierCoeff.const_mul, fourierCoeff_thetaMellin s.val s.property.2 k hk,
      mellin_gaussian_mode s.val (Real.pi * (k : ℝ) ^ 2) s.property.2 hr]
    rw [show (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 by rw [sq_abs]]
    rw [mul_comm, ← div_eq_mul_inv]
    exact rieszConstant_gaussian_normalization_complex s |(k : ℝ)| hq

end Riesz1
