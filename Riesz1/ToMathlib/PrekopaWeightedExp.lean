/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PrekopaLeindler.Core
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Weighted exponential Prékopa–Leindler on Euclidean space

This bridges the additive-coordinate inequality of `PrekopaLeindler.Core` to the usual
convex-combination formulation, with real integrals of integrable exponentials. It is an
intermediate result for the proof of the Bakry–Émery criterion `External.BakryEmery`.
The imported core records its Apache-2.0 port from `hojonathanho/isoperimetric`.
No additional external code is used here.
-/

public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- The additive-coordinate form, with real exponential integrals. -/
theorem prekopa_exp_integral_add {n : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {A B C : (Fin (n + 1) → ℝ) → ℝ}
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C)
    (hiA : Integrable (fun x => Real.exp (A x)) volume)
    (hiB : Integrable (fun x => Real.exp (B x)) volume)
    (hiC : Integrable (fun x => Real.exp (C x)) volume)
    (hABC : ∀ x y, (1 - s) * A x + s * B y ≤ C (x + y)) :
    ((1 - s) ^ (((n : ℝ) + 1) * (1 - s)) * s ^ (((n : ℝ) + 1) * s))⁻¹ *
      (∫ x, Real.exp (A x)) ^ (1 - s) * (∫ x, Real.exp (B x)) ^ s ≤
        ∫ x, Real.exp (C x) := by
  have ht : 0 < 1 - s := sub_pos.mpr hs1
  have hm := PrekopaLeindler.prekopa_leindler (d := n) (θ := s)
    (f := fun x => ENNReal.ofReal (Real.exp (A x)))
    (g := fun x => ENNReal.ofReal (Real.exp (B x)))
    (h := fun x => ENNReal.ofReal (Real.exp (C x)))
    ⟨hs, hs1, ENNReal.measurable_ofReal.comp hA.exp,
      ENNReal.measurable_ofReal.comp hB.exp, ENNReal.measurable_ofReal.comp hC.exp, by
      intro x y
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
        ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos _).le _),
        ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
        simpa only [mul_comm] using hABC x y))⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hiA (ae_of_all _ fun _ => (Real.exp_pos _).le),
    ← ofReal_integral_eq_lintegral_ofReal hiB (ae_of_all _ fun _ => (Real.exp_pos _).le),
    ← ofReal_integral_eq_lintegral_ofReal hiC (ae_of_all _ fun _ => (Real.exp_pos _).le)] at hm
  have hIA : 0 ≤ ∫ x, Real.exp (A x) := integral_nonneg fun _ => (Real.exp_pos _).le
  have hIB : 0 ≤ ∫ x, Real.exp (B x) := integral_nonneg fun _ => (Real.exp_pos _).le
  have hIC : 0 ≤ ∫ x, Real.exp (C x) := integral_nonneg fun _ => (Real.exp_pos _).le
  have hK : 0 ≤ (1 - s) ^ (((n : ℝ) + 1) * (1 - s)) *
      s ^ (((n : ℝ) + 1) * s) := mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg hs.le _)
  rw [ENNReal.ofReal_rpow_of_nonneg hIA ht.le,
    ENNReal.ofReal_rpow_of_nonneg hIB hs.le] at hm
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hK, ENNReal.toReal_ofReal (inv_nonneg.mpr hK),
    ENNReal.toReal_ofReal (Real.rpow_nonneg hIA _),
    ENNReal.toReal_ofReal (Real.rpow_nonneg hIB _), ENNReal.toReal_ofReal hIC] using hr

/-- Prékopa–Leindler for integrable exponentials and every strictly interior weight. -/
theorem prekopa_exp_integral_weighted {d : ℕ} (hd : 0 < d) {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1)
    {A B C : EuclideanSpace ℝ (Fin d) → ℝ}
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C)
    (hiA : Integrable (fun x => Real.exp (A x)) volume)
    (hiB : Integrable (fun x => Real.exp (B x)) volume)
    (hiC : Integrable (fun x => Real.exp (C x)) volume)
    (hABC : ∀ x y, (1 - s) * A x + s * B y ≤ C ((1 - s) • x + s • y)) :
    (∫ x, Real.exp (A x)) ^ (1 - s) * (∫ x, Real.exp (B x)) ^ s ≤
      ∫ x, Real.exp (C x) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have ht : 0 < 1 - s := sub_pos.mpr hs1
  let T := (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm
  have hT : MeasurePreserving T volume volume := PiLp.volume_preserving_toLp _
  have hTc : Continuous T := (PiLp.continuous_toLp 2 _)
  have hia := hT.integrable_comp_of_integrable (hiA.comp_smul (inv_ne_zero ht.ne'))
  have hib := hT.integrable_comp_of_integrable (hiB.comp_smul (inv_ne_zero hs.ne'))
  have hic := hT.integrable_comp_of_integrable hiC
  have hm := prekopa_exp_integral_add hs hs1
    ((hA.comp ((continuous_const_smul _).comp hTc)).measurable)
    ((hB.comp ((continuous_const_smul _).comp hTc)).measurable)
    (hC.comp hTc).measurable hia hib hic (by
      intro x y
      simpa only [Function.comp_apply, map_add, smul_smul, mul_inv_cancel₀ ht.ne',
        mul_inv_cancel₀ hs.ne', one_smul] using
        hABC ((1 - s)⁻¹ • T x) (s⁻¹ • T y))
  simp only [Function.comp_apply] at hm
  have hEmb := (PiLp.homeomorph 2 (fun _ : Fin (n + 1) => ℝ)).symm.measurableEmbedding
  rw [hT.integral_comp hEmb (fun x => Real.exp (A ((1 - s)⁻¹ • x))),
    hT.integral_comp hEmb (fun x => Real.exp (B (s⁻¹ • x))),
    hT.integral_comp hEmb (fun x => Real.exp (C x)),
    Measure.integral_comp_inv_smul_of_nonneg volume (fun x => Real.exp (A x)) ht.le,
    Measure.integral_comp_inv_smul_of_nonneg volume (fun x => Real.exp (B x)) hs.le] at hm
  simp only [smul_eq_mul, finrank_euclideanSpace, Fintype.card_fin] at hm
  have hpow (a : ℝ) (ha : 0 < a) (b : ℝ) (hb : 0 ≤ b) (r : ℝ) :
      (a ^ (n + 1) * b) ^ r = a ^ (((n : ℝ) + 1) * r) * b ^ r := by
    rw [Real.mul_rpow (pow_nonneg ha.le _) hb, ← Real.rpow_natCast_mul ha.le]
    norm_cast
  rw [hpow _ ht _ (integral_nonneg fun _ => (Real.exp_pos _).le),
    hpow _ hs _ (integral_nonneg fun _ => (Real.exp_pos _).le)] at hm
  have hK : (1 - s) ^ (((n : ℝ) + 1) * (1 - s)) * s ^ (((n : ℝ) + 1) * s) ≠ 0 :=
    ne_of_gt (mul_pos (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos hs _))
  convert hm using 1
  field_simp

end Riesz1

end
