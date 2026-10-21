/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.ThetaFourier
public import Riesz1.ToMathlib.HurwitzKernel.Mellin
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Absolute integrability of the theta Mellin integral

The Fourier series at reciprocal time gives joint measurability in space
and time, including the library's zero value at nonpositive times.
The deviation at the spatial origin bounds the small-time integrand.
The spatial mean bounds the large-time integral by an integrable power.
-/

public section

open MeasureTheory Complex Set

namespace Riesz1

/-- The Gaussian periodization is jointly measurable in time and space. -/
theorem measurable_evenKernel :
    Measurable (fun p : ℝ × UnitAddCircle => HurwitzZeta.evenKernel p.2 p.1) := by
  let G (p : ℝ × UnitAddCircle) : ℝ :=
    Real.exp (Real.log p.1 * (-(1 / 2 : ℝ))) *
      (∑' n : ℤ, (Real.exp (-Real.pi * (n : ℝ) ^ 2 / p.1) : ℂ) * fourier n p.2).re
  have hG : Measurable G := by
    apply Measurable.mul
    · fun_prop
    · apply Complex.measurable_re.comp
      apply Measurable.tsum
      intro n
      exact (Complex.measurable_ofReal.comp (by fun_prop)).mul
        ((fourier n).continuous.measurable.comp measurable_snd)
  have heq : (fun p : ℝ × UnitAddCircle => HurwitzZeta.evenKernel p.2 p.1) =
      {p : ℝ × UnitAddCircle | 0 < p.1}.indicator G := by
    funext p
    by_cases ht : 0 < p.1
    · rw [indicator_of_mem (show p ∈ {p : ℝ × UnitAddCircle | 0 < p.1} from ht),
        HurwitzZeta.evenKernel_functional_equation]
      have hsum := congrArg Complex.re (hasSum_cosKernel_fourier p.2 (by positivity : 0 < 1 / p.1)).tsum_eq
      simp only [ofReal_re, mul_one_div] at hsum
      dsimp only [G]
      rw [hsum, ← Real.rpow_def_of_pos ht, Real.rpow_neg ht.le]
      simp only [one_div]
    · rw [indicator_of_notMem (show p ∉ {p : ℝ × UnitAddCircle | 0 < p.1} from ht),
        HurwitzZeta.evenKernel_undef _ (le_of_not_gt ht)]
  rw [heq]
  exact hG.indicator (isOpen_lt continuous_const continuous_fst).measurableSet

/-- Joint strong measurability of the mean-subtracted Mellin integrand. -/
theorem aestronglyMeasurable_thetaMellin (s : ℂ) :
    AEStronglyMeasurable (fun p : ℝ × UnitAddCircle =>
      (p.1 : ℂ) ^ (s / 2 - 1) *
        ((HurwitzZeta.evenKernel p.2 p.1 : ℂ) - (p.1 : ℂ) ^ (-(1 / 2 : ℂ))))
      ((volume.restrict (Ioi (0 : ℝ))).prod AddCircle.haarAddCircle) := by
  have hp (z : ℂ) : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ z)
      (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht.ne')).continuousWithinAt
  exact (hp _).comp_fst.mul
    (((Complex.measurable_ofReal.comp measurable_evenKernel).aestronglyMeasurable).sub
      (hp _).comp_fst)

/-- Absolute integrability on the product of time and space, permitting
Fourier coefficients to pass through the theta Mellin integral. -/
theorem integrable_thetaMellin (s : ℝ) (hs : s < 1) :
    Integrable (fun p : ℝ × UnitAddCircle =>
      (p.1 : ℂ) ^ ((s : ℂ) / 2 - 1) *
        ((HurwitzZeta.evenKernel p.2 p.1 : ℂ) - (p.1 : ℂ) ^ (-(1 / 2 : ℂ))))
      ((volume.restrict (Ioi (0 : ℝ))).prod AddCircle.haarAddCircle) := by
  let F (p : ℝ × UnitAddCircle) : ℂ := (p.1 : ℂ) ^ ((s : ℂ) / 2 - 1) *
    ((HurwitzZeta.evenKernel p.2 p.1 : ℂ) - (p.1 : ℂ) ^ (-(1 / 2 : ℂ)))
  let P := HurwitzZeta.hurwitzEvenFEPair 0
  let w := s / 2 - 1
  have hmod : Integrable (fun t : ℝ => ‖(t : ℂ) ^ ((s : ℂ) / 2 - 1) * P.f_modif t‖)
      (volume.restrict (Ioi 0)) :=
    (P.isStrongFEPair_toStrongFEPair.hasMellin ((s : ℂ) / 2)).1.norm
  have htail : Integrable ((Ioi (1 : ℝ)).indicator
      (fun t : ℝ => 2 * t ^ ((s - 1) / 2 - 1))) (volume.restrict (Ioi 0)) := by
    rw [integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
      Measure.restrict_restrict_of_subset (Ioi_subset_Ioi zero_le_one)]
    exact (integrableOn_Ioi_rpow_of_lt (by linarith : (s - 1) / 2 - 1 < -1)
      zero_lt_one).const_mul 2
  have hFi (t : ℝ) (ht : 0 < t) : Integrable (fun x => F (t, x)) AddCircle.haarAddCircle := by
    dsimp only [F]
    exact ((integrable_evenKernel_complex t ht).sub
      (integrable_const ((t : ℂ) ^ (-(1 / 2 : ℂ))))).const_mul
        ((t : ℂ) ^ ((s : ℂ) / 2 - 1))
  have hm := aestronglyMeasurable_thetaMellin (s : ℂ)
  apply (integrable_prod_iff hm).mpr
  refine ⟨(ae_restrict_mem measurableSet_Ioi).mono (fun t ht => hFi t ht), ?_⟩
  apply (hmod.add htail).mono' hm.norm.integral_prod_right'
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    (volume.restrict (Ioi (0 : ℝ))).ae_ne 1] with t ht ht1
  have ht0 : 0 < t := ht
  have hpow : (t : ℂ) ^ ((s : ℂ) / 2 - 1) = (t ^ w : ℝ) := by
    rw [ofReal_cpow ht0.le]
    congr 1
    dsimp [w]
    push_cast
    rfl
  have hmean : (t : ℂ) ^ (-(1 / 2 : ℂ)) = ((1 / t ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; rfl,
      ← ofReal_cpow ht0.le (-(1 / 2 : ℝ)), Real.rpow_neg ht0.le]
    simp only [one_div]
  have hKR : Integrable (fun x : UnitAddCircle => HurwitzZeta.evenKernel x t)
      AddCircle.haarAddCircle := by
    simpa using (integrable_evenKernel_complex t ht0).re
  have hnorm : (∫ x : UnitAddCircle, ‖F (t, x)‖ ∂AddCircle.haarAddCircle) =
      t ^ w * ∫ x : UnitAddCircle, |HurwitzZeta.evenKernel x t - 1 / t ^ (1 / 2 : ℝ)|
        ∂AddCircle.haarAddCircle := by
    simp only [F, hpow, hmean, ← ofReal_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), Real.norm_eq_abs]
    rw [integral_const_mul]
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), hnorm]
  rcases lt_or_gt_of_ne ht1 with hsmall | hlarge
  · have hle : (∫ x : UnitAddCircle,
        |HurwitzZeta.evenKernel x t - 1 / t ^ (1 / 2 : ℝ)| ∂AddCircle.haarAddCircle) ≤
        HurwitzZeta.evenKernel 0 t - 1 / t ^ (1 / 2 : ℝ) := by
      have h := integral_mono (hKR.sub (integrable_const _)).abs (integrable_const _)
        (fun x => abs_evenKernel_sub_le x t ht0)
      simpa using h
    have hmodEq : P.f_modif t =
        ((HurwitzZeta.evenKernel 0 t - 1 / t ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      simp only [P, WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, Pi.add_apply,
        indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from hsmall.not_gt),
        indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht0, hsmall⟩),
        zero_add, Function.comp_def, one_mul, smul_eq_mul, mul_one]
      rw [Real.rpow_neg ht0.le]
      push_cast
      simp only [one_div]
    simp only [Pi.add_apply,
      indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from hsmall.not_gt), add_zero,
      hmodEq, hpow, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hle.trans (le_abs_self _)) (Real.rpow_nonneg ht0.le _)
  · have hle : (∫ x : UnitAddCircle,
        |HurwitzZeta.evenKernel x t - 1 / t ^ (1 / 2 : ℝ)| ∂AddCircle.haarAddCircle) ≤
        2 / t ^ (1 / 2 : ℝ) := by
      have h := integral_mono (hKR.sub (integrable_const (1 / t ^ (1 / 2 : ℝ)))).abs
        (hKR.add (integrable_const (1 / t ^ (1 / 2 : ℝ))))
        (fun x => by
          simp only [Pi.sub_apply, Pi.add_apply]
          apply abs_le.mpr
          constructor
          · linarith [evenKernel_nonneg x t ht0]
          · have hm : 0 ≤ 1 / t ^ (1 / 2 : ℝ) := by positivity
            linarith)
      simp only [Pi.sub_apply, Pi.add_apply] at h
      rw [integral_add hKR (integrable_const _), integral_evenKernel t ht0] at h
      simpa [div_eq_mul_inv, two_mul] using h
    have hpower : t ^ w * (2 / t ^ (1 / 2 : ℝ)) =
        2 * t ^ ((s - 1) / 2 - 1) := by
      rw [show (s - 1) / 2 - 1 = w - 1 / 2 by dsimp [w]; ring,
        Real.rpow_sub ht0 w (1 / 2)]
      ring
    have h := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg ht0.le w)
    rw [hpower] at h
    simp only [Pi.add_apply, indicator_of_mem (show t ∈ Ioi (1 : ℝ) from hlarge)]
    exact h.trans (le_add_of_nonneg_left (norm_nonneg _))

end Riesz1
