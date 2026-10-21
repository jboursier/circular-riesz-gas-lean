/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryTransportEnergyEnvelope

/-!
# Uniform integral norms of compact transport envelopes

Supporting Proposition 5.9: when the near exponent is
strictly less than one, each first-derivative envelope has bounded mass
independently of the period and the microscopic truncation.
-/

public section

open MeasureTheory Set

namespace Riesz1.Internal

/-- Integrate the first derivative envelope on any observation circle.
This bound has no microscopic power loss. -/
theorem compactDecomposition_envelope_mass {L K s b A : ℝ}
    (hL : 0 < L) (hK : 1 ≤ K) (hs : s < 1) (hb : b < 1) (hA : 0 ≤ A)
    (c : ℝ) {q : ℝ → ℝ} (hq : Continuous q) (hp : Function.Periodic q L)
    (hbound : ∀ y, |q y| ≤ A * gradWeightOne s b K L (y - c)) :
    ∫ y in (0 : ℝ)..L, |q y| ≤ A * (2 * (1 + 1 / (1 - b)) + 2 / (1 - s)) := by
  have hK0 : 0 < K := by linarith
  let Gn := (Iic (1 : ℝ)).indicator (fun t => max t K⁻¹ ^ (-b))
  let Gt := (Ici (1 : ℝ)).indicator (fun t => t ^ (s - 2))
  have hin : IntegrableOn (fun y => Gn (circDist L (y - c))) (Ioc (-(L / 2)) (L / 2)) :=
    integrableOn_window_circDist_comp_sub hL Gn c
      (intervalIntegrable_abs_capped_power_indicator (inv_pos.mpr hK0) (-b) (L / 2))
  have hit : IntegrableOn (fun y => Gt (circDist L (y - c))) (Ioc (-(L / 2)) (L / 2)) :=
    integrableOn_window_circDist_comp_sub hL Gt c
      (intervalIntegrable_abs_rpow_indicator_Ici (by linarith) (by norm_num) (by positivity))
  have hpt (y : ℝ) : |q y| ≤ A * (Gn (circDist L (y - c)) + Gt (circDist L (y - c))) := by
    apply (hbound y).trans
    apply mul_le_mul_of_nonneg_left _ hA
    unfold gradWeightOne
    by_cases hy : circDist L (y - c) < 1
    · rw [ite_eq_left hy]
      dsimp [Gn, Gt]
      rw [indicator_of_mem (show circDist L (y - c) ∈ Iic (1 : ℝ) from hy.le),
        indicator_of_notMem (show circDist L (y - c) ∉ Ici (1 : ℝ) from not_le.mpr hy), add_zero]
    · rw [ite_eq_right hy]
      dsimp [Gt]
      rw [indicator_of_mem (show circDist L (y - c) ∈ Ici (1 : ℝ) from not_lt.mp hy)]
      have hn : 0 ≤ Gn (circDist L (y - c)) := by
        dsimp [Gn]
        exact Set.indicator_nonneg (fun t _ => by positivity) _
      linarith
  have hv := setIntegral_mono_on (hq.abs.intervalIntegrable (μ := volume) _ _).1
    ((hin.add hit).const_mul A) measurableSet_Ioc (fun y _ => hpt y)
  simp only [Pi.add_apply] at hv
  rw [integral_const_mul, integral_add hin hit] at hv
  have hn : (∫ y in Ioc (-(L / 2)) (L / 2), Gn (circDist L (y - c))) ≤
      2 * (1 + 1 / (1 - b)) := by
    rw [setIntegral_window_circDist_comp_sub hL Gn c
      (intervalIntegrable_abs_capped_power_indicator (inv_pos.mpr hK0) (-b) (L / 2))]
    have hc : Continuous (fun t : ℝ => max t K⁻¹ ^ (-b)) :=
      Continuous.rpow_const (continuous_id.max continuous_const)
        (fun t => Or.inl (ne_of_gt ((inv_pos.mpr hK0).trans_le (le_max_right _ _))))
    have hsub : (∫ u in Ioc 0 (L / 2), Gn u) ≤
        ∫ u in Ioc (0 : ℝ) 1, max u K⁻¹ ^ (-b) := by
      dsimp [Gn]
      rw [setIntegral_indicator measurableSet_Iic]
      apply setIntegral_mono_set ((hc.intervalIntegrable (μ := volume) 0 1).1)
        (Filter.Eventually.of_forall fun u => by positivity)
      exact Filter.Eventually.of_forall fun u hu => ⟨hu.1.1, hu.2⟩
    have he := integral_max_rpow_le hb (inv_pos.mpr hK0) (by norm_num : (0 : ℝ) ≤ 1)
    rw [max_eq_left ((inv_le_one₀ hK0).mpr hK), Real.one_rpow, mul_one,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at he
    simp only [mul_one] at he
    exact mul_le_mul_of_nonneg_left (hsub.trans he) (by norm_num)
  have ht := setIntegral_window_circDist_rpow_Ici_le (e := s - 2) (ρ := 1)
    hL (by linarith) (by norm_num) c
  have ht' : (∫ y in Ioc (-(L / 2)) (L / 2), Gt (circDist L (y - c))) ≤ 2 / (1 - s) := by
    convert ht using 1
    rw [Real.one_rpow, show s - 2 + 1 = -(1 - s) by ring, neg_div_neg_eq]
    ring
  have hpabs : Function.Periodic (fun y => |q y|) L := fun y => congrArg abs (hp y)
  have hshift := hpabs.intervalIntegral_add_eq 0 (-(L / 2))
  simp only [zero_add, show -(L / 2) + L = L / 2 by ring] at hshift
  rw [hshift, intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2)]
  exact hv.trans (mul_le_mul_of_nonneg_left (add_le_add hn ht') hA)

end Riesz1.Internal
