/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.RieszConstant
public import Riesz1.Frozen.RieszExponent
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Indicator of an arc on the circle: Fourier coefficients and the Riesz constant

This is part of Lemma 2.3. For `0 < a < 1/2` the indicator `1_{(-a,a)}` of the
arc, viewed on `UnitAddCircle`, has Fourier coefficients `sin(2πka)/(πk)` for `k ≠ 0` and
`2a` at `k = 0`. This file proves these coefficients, the square integrability of the indicator,
and the identity `Γ(s) c_s cos(πs/2) = π` for the Riesz constant `c_s`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped Real Interval

namespace Riesz1

/-- The image of the open arc `(-a, a)` in `UnitAddCircle`. -/
@[expose] def arcImage (a : ℝ) : Set UnitAddCircle := (fun x : ℝ => (x : UnitAddCircle)) '' Ioo (-a) a

/-- The indicator `1_{(-a,a)}` of the arc, as a real function on the circle. -/
@[expose] noncomputable def indicatorArc (a : ℝ) : UnitAddCircle → ℝ := (arcImage a).indicator fun _ => 1

lemma isOpen_arcImage (a : ℝ) : IsOpen (arcImage a) :=
  QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

lemma measurable_indicatorArc (a : ℝ) : Measurable (indicatorArc a) :=
  measurable_const.indicator (isOpen_arcImage a).measurableSet

lemma indicatorArc_apply_of_mem {a : ℝ} {t : UnitAddCircle} (ht : t ∈ arcImage a) :
    indicatorArc a t = 1 :=
  Set.indicator_of_mem ht _

lemma indicatorArc_apply_of_notMem {a : ℝ} {t : UnitAddCircle} (ht : t ∉ arcImage a) :
    indicatorArc a t = 0 :=
  Set.indicator_of_notMem ht _

/-- The indicator of the arc is square integrable on the circle, since it is bounded and
measurable on a finite measure space. -/
lemma memLp_indicatorArc (a : ℝ) :
    MemLp (fun t : UnitAddCircle => (indicatorArc a t : ℂ)) 2 volume := by
  refine MemLp.of_bound (Complex.measurable_ofReal.comp (measurable_indicatorArc a)).aestronglyMeasurable
    1 (ae_of_all _ fun t => ?_)
  by_cases ht : t ∈ arcImage a
  · rw [indicatorArc_apply_of_mem ht]
    simp
  · rw [indicatorArc_apply_of_notMem ht]
    simp

/-- Two points of `(-1/2, 1/2]` that agree on the circle are equal. -/
lemma eq_of_coe_eq_of_mem_Ioc {x y : ℝ} (hx : x ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1))
    (hy : y ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)) (h : (x : UnitAddCircle) = y) : x = y :=
  (AddCircle.coe_eq_coe_iff_of_mem_Ioc hx hy).mp h

/-- The indicator of the arc agrees on `(-1/2, 1/2]` with the indicator of `(-a, a)`. -/
lemma indicatorArc_coe_eq_indicator {a : ℝ} (ha1 : a < 1 / 2) {x : ℝ}
    (hx : x ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)) :
    indicatorArc a (x : UnitAddCircle) = (Ioo (-a) a).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hxa : x ∈ Ioo (-a) a
  · rw [Set.indicator_of_mem hxa, indicatorArc_apply_of_mem]
    exact ⟨x, hxa, rfl⟩
  · rw [Set.indicator_of_notMem hxa, indicatorArc_apply_of_notMem]
    rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := by
      refine eq_of_coe_eq_of_mem_Ioc ?_ hx hyx
      constructor <;> linarith [hy.1, hy.2, hx.1, hx.2]
    exact hxa (hyx' ▸ hy)

/-- The exponential of the Fourier mode, as a function of a real variable. -/
lemma fourier_integral_coe (k : ℤ) (x : ℝ) :
    fourier (-k) (x : UnitAddCircle) = Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ) * x) := by
  rw [fourier_coe_apply, Complex.ofReal_one, div_one]

/-- The integral of `exp(c x)` over `(-a, a)` for the Fourier mode of frequency `-k`, `k ≠ 0`. -/
lemma integral_exp_neg_mode (k : ℤ) (hk : k ≠ 0) (a : ℝ) :
    (∫ x in (-a)..a, Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ) * x)) =
      ((Real.sin (2 * Real.pi * k * a) / (Real.pi * k) : ℝ) : ℂ) := by
  have hc : (2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ)) ≠ 0 := by
    have hk' : ((k : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hk
    simp [Real.pi_ne_zero, hk']
  rw [integral_exp_mul_complex hc, div_eq_iff hc]
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  rw [Complex.sin]
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The Fourier coefficients of the arc indicator: `2a` at zero and `sin(2πka)/(πk)` for `k ≠ 0`. -/
theorem fourierCoeff_indicatorArc {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (k : ℤ) :
    fourierCoeff (fun t : UnitAddCircle => (indicatorArc a t : ℂ)) k =
      ((if k = 0 then 2 * a else Real.sin (2 * Real.pi * k * a) / (Real.pi * k) : ℝ) : ℂ) := by
  have hint : (∫ x in (-1 / 2 : ℝ)..(-1 / 2 + 1),
      fourier (-k) (x : UnitAddCircle) • (indicatorArc a (x : UnitAddCircle) : ℂ)) =
      ∫ x in (-a)..a, Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ) * x) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 / 2 : ℝ) ≤ -1 / 2 + 1)]
    calc ∫ x in Ioc (-1 / 2 : ℝ) (-1 / 2 + 1),
          fourier (-k) (x : UnitAddCircle) • (indicatorArc a (x : UnitAddCircle) : ℂ)
        = ∫ x in Ioc (-1 / 2 : ℝ) (-1 / 2 + 1),
          (Ioo (-a) a).indicator (fun x : ℝ =>
            Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ) * x)) x := by
          refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
          simp only [fourier_integral_coe]
          by_cases hxa : x ∈ Ioo (-a) a
          · rw [Set.indicator_of_mem hxa, indicatorArc_coe_eq_indicator ha1 hx,
              Set.indicator_of_mem hxa]
            simp
          · rw [Set.indicator_of_notMem hxa, indicatorArc_coe_eq_indicator ha1 hx,
              Set.indicator_of_notMem hxa]
            simp
      _ = ∫ x in Ioo (-a) a,
          Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ) * x) := by
          rw [setIntegral_indicator measurableSet_Ioo, Set.inter_eq_right.mpr]
          intro x hx
          constructor <;> linarith [hx.1, hx.2]
      _ = ∫ x in (-a)..a, Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ) * x) := by
          rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  rw [fourierCoeff_eq_intervalIntegral _ k (-1 / 2), one_div_one, one_smul]
  rw [hint]
  by_cases hk : k = 0
  · subst hk
    simp
    ring
  · rw [integral_exp_neg_mode k hk a, ite_eq_right_iff.mpr fun h => absurd h hk]

/-- Gamma identity for the Riesz constant: `Γ(s) c_s cos(πs/2) = π` for `0 < s < 1`. -/
theorem gamma_mul_rieszConstant_mul_cos (s : RieszExponent) :
    Real.Gamma s.val * rieszConstant s * Real.cos (Real.pi * s.val / 2) = Real.pi := by
  have hs0 := s.2.1
  have hs1 := s.2.2
  have hdup := Real.Gamma_mul_Gamma_add_half (s.val / 2)
  rw [show 2 * (s.val / 2) = s.val by ring, show s.val / 2 + 1 / 2 = (1 + s.val) / 2 by ring] at hdup
  have hrefl := Real.Gamma_mul_Gamma_one_sub ((1 + s.val) / 2)
  rw [show 1 - (1 + s.val) / 2 = (1 - s.val) / 2 by ring,
    show Real.pi * ((1 + s.val) / 2) = Real.pi * s.val / 2 + Real.pi / 2 by ring,
    Real.sin_add_pi_div_two] at hrefl
  have hG : 0 < Real.Gamma (s.val / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hcos : 0 < Real.cos (Real.pi * s.val / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hcosne : Real.cos (Real.pi * s.val / 2) ≠ 0 := hcos.ne'
  unfold rieszConstant
  have e : Real.Gamma s.val * (2 ^ (1 - s.val) * Real.sqrt Real.pi *
      Real.Gamma ((1 - s.val) / 2) / Real.Gamma (s.val / 2)) =
      Real.Gamma ((1 + s.val) / 2) * Real.Gamma ((1 - s.val) / 2) := by
    field_simp
    linear_combination (-1 : ℝ) * hdup
  calc Real.Gamma s.val * (2 ^ (1 - s.val) * Real.sqrt Real.pi * Real.Gamma ((1 - s.val) / 2) /
        Real.Gamma (s.val / 2)) * Real.cos (Real.pi * s.val / 2)
      = Real.Gamma ((1 + s.val) / 2) * Real.Gamma ((1 - s.val) / 2) *
          Real.cos (Real.pi * s.val / 2) := by
        rw [← e]
    _ = Real.pi := by
        rw [hrefl]
        field_simp

end Riesz1

end
