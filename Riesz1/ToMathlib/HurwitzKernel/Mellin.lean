/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic

/-!
# Mellin representation to the left of the functional-equation weight

When the constant at infinity vanishes, subtracting the power term globally
gives a convergent Mellin representation on the other side of the weight.
For the Hurwitz theta kernel this applies at every nonzero circle point.
-/

public section

open MeasureTheory Complex Set Filter
open scoped Topology

namespace Riesz1

/-- The Mellin transform after subtracting the power term globally, for a
functional-equation pair whose constant at infinity is zero. -/
theorem hasMellin_sub_power (P : WeakFEPair ℂ) (hf₀ : P.f₀ = 0)
    (s : ℂ) (hs : s.re < P.k) :
    HasMellin (fun t => P.f t - (P.ε * (t : ℂ) ^ (-(P.k : ℂ))) * P.g₀) s
      (P.Λ s) := by
  let T : ℝ → ℂ := (Ioi 1).indicator
    (fun t => (P.ε * (t : ℂ) ^ (-(P.k : ℂ))) * P.g₀)
  have he : (s - 1 - (P.k : ℂ)).re < -1 := by
    simp only [sub_re, one_re, ofReal_re]
    linarith
  have hfun : (fun t : ℝ => (t : ℂ) ^ (s - 1) * T t) =
      (Ioi 1).indicator (fun t : ℝ =>
        (t : ℂ) ^ (s - 1 - (P.k : ℂ)) * (P.ε * P.g₀)) := by
    funext t
    by_cases ht : 1 < t
    · simp only [T, indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht)]
      rw [sub_eq_add_neg (s - 1), cpow_add _ _ (ofReal_ne_zero.mpr (by linarith))]
      ring
    · simp [T, ht]
  have hT : MellinConvergent T s := by
    unfold MellinConvergent
    simp only [smul_eq_mul, hfun]
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
      Measure.restrict_restrict_of_subset (Ioi_subset_Ioi zero_le_one)]
    exact (integrableOn_Ioi_cpow_of_lt he zero_lt_one).mul_const _
  have hTint : mellin T s = (P.ε / ((P.k : ℂ) - s)) * P.g₀ := by
    simp only [mellin, smul_eq_mul, hfun, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict_of_subset (Ioi_subset_Ioi zero_le_one)]
    rw [integral_mul_const, integral_Ioi_cpow_of_lt he zero_lt_one]
    simp only [ofReal_one, one_cpow]
    have hd : s - 1 - (P.k : ℂ) + 1 = -((P.k : ℂ) - s) := by ring
    rw [hd, neg_div_neg_eq]
    ring
  have hmod : MellinConvergent P.f_modif s :=
    (P.isStrongFEPair_toStrongFEPair.hasMellin s).1
  have hae : (fun t => P.f t - (P.ε * (t : ℂ) ^ (-(P.k : ℂ))) * P.g₀) =ᵐ[volume.restrict (Ioi 0)]
      (fun t => P.f_modif t - T t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      (volume.restrict (Ioi (0 : ℝ))).ae_ne 1] with t ht ht1
    have hp : (t : ℂ) ^ (-(P.k : ℂ)) = (t ^ (-P.k) : ℝ) := by
      simpa only [ofReal_neg] using (ofReal_cpow ht.le (-P.k)).symm
    rcases lt_or_gt_of_ne ht1 with hlt | hgt
    · simp only [WeakFEPair.f_modif, T,
        indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from hlt.not_gt),
        indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht, hlt⟩),
        hf₀, Pi.add_apply, zero_add, sub_zero, smul_eq_mul, hp]
    · simp [WeakFEPair.f_modif, T, hgt, not_lt_of_ge hgt.le, hf₀]
  refine ⟨(hmod.sub hT).congr ?_, ?_⟩
  · filter_upwards [hae] with t ht
    simpa only [Pi.sub_apply, ← smul_sub] using
      congrArg (fun z : ℂ => (t : ℂ) ^ (s - 1) • z) ht.symm
  · calc
      mellin (fun t => P.f t - (P.ε * (t : ℂ) ^ (-(P.k : ℂ))) * P.g₀) s =
          mellin (fun t => P.f_modif t - T t) s := by
        exact integral_congr_ae ((Filter.EventuallyEq.refl _ _).smul hae)
      _ = P.Λ s := by
        rw [(hasMellin_sub hmod hT).2, hTint]
        simp only [WeakFEPair.Λ, WeakFEPair.Λ₀, hf₀, smul_zero, sub_zero]
        rfl

/-- At nonzero circle points, the completed even Hurwitz function is the
Mellin transform of the theta kernel with its spatial mean subtracted. -/
theorem hasMellin_evenKernel_sub (a : UnitAddCircle) (ha : a ≠ 0)
    (s : ℝ) (hs : s < 1) :
    HasMellin (fun t : ℝ => (HurwitzZeta.evenKernel a t : ℂ) -
      (t : ℂ) ^ (-(1 / 2 : ℂ))) ((s : ℂ) / 2)
      (2 * HurwitzZeta.completedHurwitzZetaEven a (s : ℂ)) := by
  have h := hasMellin_sub_power (HurwitzZeta.hurwitzEvenFEPair a)
    (by simp [HurwitzZeta.hurwitzEvenFEPair, ha]) ((s : ℂ) / 2)
    (by change ((s : ℂ) / 2).re < (1 / 2 : ℝ)
        simpa only [Complex.div_ofNat_re, ofReal_re] using
          (div_lt_div_of_pos_right hs (by norm_num : (0 : ℝ) < 2)))
  have hv : 2 * HurwitzZeta.completedHurwitzZetaEven a (s : ℂ) =
      (HurwitzZeta.hurwitzEvenFEPair a).Λ ((s : ℂ) / 2) := by
    unfold HurwitzZeta.completedHurwitzZetaEven
    ring
  rw [hv]
  simpa [HurwitzZeta.hurwitzEvenFEPair, Function.comp_def] using h

/-- The scalar reciprocal Gaussian Mellin integral. -/
theorem mellin_exp_neg_div (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z.re < 0) :
    mellin (fun t : ℝ => (Real.exp (-r / t) : ℂ)) z =
      (1 / (r : ℂ)) ^ (-z) * Complex.Gamma (-z) := by
  have he : (fun t : ℝ => (Real.exp (-r / t) : ℂ)) =
      (fun t : ℝ => (Real.exp (-(r * t⁻¹)) : ℂ)) := by
    funext t
    rw [neg_div, div_eq_mul_inv]
  rw [he, mellin_comp_inv (fun t : ℝ => (Real.exp (-(r * t)) : ℂ)) z]
  simp only [mellin, smul_eq_mul]
  have hcast (t : ℝ) : (Real.exp (-(r * t)) : ℂ) = Complex.exp (-(r * t)) := by
    rw [ofReal_exp, ofReal_neg, ofReal_mul]
  simp only [hcast]
  exact integral_cpow_mul_exp_neg_mul_Ioi (by simpa using neg_pos.mpr hz) hr

/-- The scalar Mellin integral for a nonzero Fourier mode of the Gaussian
periodization. -/
theorem mellin_gaussian_mode (s r : ℝ) (hs : s < 1) (hr : 0 < r) :
    mellin (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) *
      (Real.exp (-r / t) : ℂ)) ((s : ℂ) / 2) =
      (1 / (r : ℂ)) ^ ((1 - (s : ℂ)) / 2) *
        Complex.Gamma ((1 - (s : ℂ)) / 2) := by
  rw [show (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) * (Real.exp (-r / t) : ℂ)) =
      (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) • (Real.exp (-r / t) : ℂ)) by rfl,
    mellin_cpow_smul, mellin_exp_neg_div r hr]
  · congr 2 <;> ring
  · simp only [add_re, Complex.div_ofNat_re, ofReal_re, neg_re, one_re]
    linarith

end Riesz1
