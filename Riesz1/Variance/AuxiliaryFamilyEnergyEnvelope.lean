/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryTransportEnergyEnvelope
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Energy from finite-mark bounds and a compact tail

The energy step in the proof of Proposition 5.6. This estimate needs no
separation of marks and no decomposition of the transport itself.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1.Internal

/-- Integrate the actual finite-mark envelope with its square-integrable
tail. The coefficient is independent of circle length and smoothing radius. -/
theorem auxiliary_family_energy_envelopes (n : ℕ) (marks : Fin n → ℝ)
    {s b δ : ℝ} (hs : s < 1) (hb : 0 ≤ b) (hδ : 0 < δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (L K h A : ℝ), 0 < L → 1 ≤ K →
      0 < h → K⁻¹ ≤ h → 0 ≤ A → ∀ q : ℝ → ℝ, Continuous q →
      (∀ x, |q x| ≤ A * (1 + ∑ j,
        max (circDist L (x - marks j)) h ^ (-b))) →
      (∀ x, 2 ≤ circDist L x → |q x| ≤ A * circDist L x ^ (s - 2)) →
      (∫ x in Ioc (-(L / 2)) (L / 2), (q x) ^ 2) ≤
        D * A ^ 2 * (K ^ δ * (1 + K ^ (2 * b - 1))) := by
  classical
  let D := ((n : ℝ) + 1) * (4 * ((n : ℝ) + 1) +
    (n : ℝ) * (2 * (1 + 1 / δ))) + 2 / (3 - 2 * s) + 1
  have hden : 0 < 3 - 2 * s := by linarith
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, fun L K h A hL hK hh hhK hA q hq hnear htail => ?_⟩
  have hK0 : 0 < K := by linarith
  let G₀ : ℝ → ℝ := (Iic (2 : ℝ)).indicator (fun _ => (1 : ℝ))
  let Gn : ℝ → ℝ := (Iic (1 : ℝ)).indicator (fun t => max t K⁻¹ ^ (-2 * b))
  let Gt : ℝ → ℝ := (Ici (1 : ℝ)).indicator (fun t => t ^ (2 * s - 4))
  have h0i : IntegrableOn (fun y => G₀ (circDist L y)) (Ioc (-(L / 2)) (L / 2)) := by
    simpa only [sub_zero, Real.rpow_zero] using
      integrableOn_window_circDist_comp_sub hL
        ((Iic (2 : ℝ)).indicator (fun t : ℝ => t ^ (0 : ℝ))) 0
        (intervalIntegrable_abs_rpow_indicator_Iic (by norm_num) (by positivity))
  have hni (j : Fin n) : IntegrableOn (fun y => Gn (circDist L (y - marks j)))
      (Ioc (-(L / 2)) (L / 2)) :=
    integrableOn_window_circDist_comp_sub hL Gn (marks j)
      (intervalIntegrable_abs_capped_power_indicator (inv_pos.mpr hK0) (-2 * b) (L / 2))
  have hti : IntegrableOn (fun y => Gt (circDist L y)) (Ioc (-(L / 2)) (L / 2)) := by
    simpa only [sub_zero] using integrableOn_window_circDist_comp_sub hL Gt 0
      (intervalIntegrable_abs_rpow_indicator_Ici (by linarith) (by norm_num) (by positivity))
  have hnn (x : ℝ) : 0 ≤ Gn x := Set.indicator_nonneg (fun t _ => by positivity) x
  have htn (x : ℝ) : 0 ≤ Gt x := Set.indicator_nonneg (fun t ht =>
    Real.rpow_nonneg (by have := ht; change 1 ≤ t at this; linarith) _) x
  have hterm (x : ℝ) (j : Fin n) :
      (max (circDist L (x - marks j)) K⁻¹ ^ (-b)) ^ 2 ≤
        1 + Gn (circDist L (x - marks j)) := by
    have hr : 0 ≤ max (circDist L (x - marks j)) K⁻¹ := by positivity
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
    norm_num only [Nat.cast_ofNat]
    rw [show -b * (2 : ℝ) = -2 * b by ring]
    by_cases hd : circDist L (x - marks j) ≤ 1
    · dsimp [Gn]
      rw [indicator_of_mem (show circDist L (x - marks j) ∈ Iic (1 : ℝ) from hd)]
      linarith
    · have hd1 : 1 ≤ max (circDist L (x - marks j)) K⁻¹ := by
        linarith [le_max_left (circDist L (x - marks j)) K⁻¹]
      have hw := Real.rpow_le_one_of_one_le_of_nonpos hd1 (by linarith : -2 * b ≤ 0)
      exact hw.trans (le_add_of_nonneg_right (hnn _))
  have hsq (x : ℝ) : (q x) ^ 2 ≤ A ^ 2 *
      (((n : ℝ) + 1) * (((n : ℝ) + 1) * G₀ (circDist L x) +
        ∑ j, Gn (circDist L (x - marks j))) + Gt (circDist L x)) := by
    by_cases hx : circDist L x ≤ 2
    · have hv : |q x| ≤ A * (1 + ∑ j,
          max (circDist L (x - marks j)) K⁻¹ ^ (-b)) :=
        (hnear x).trans (mul_le_mul_of_nonneg_left (by
          apply add_le_add le_rfl
          exact Finset.sum_le_sum fun j _ => Real.rpow_le_rpow_of_nonpos
            (lt_max_of_lt_right (inv_pos.mpr hK0)) (max_le_max le_rfl hhK) (by linarith)) hA)
      let w : Fin (n + 1) → ℝ := Fin.lastCases 1
        (fun j => max (circDist L (x - marks j)) K⁻¹ ^ (-b))
      have hw := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := w)
      simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one,
        Fin.sum_univ_castSucc] at hw
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm x j)
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
      have hw' : (1 + ∑ j, max (circDist L (x - marks j)) K⁻¹ ^ (-b)) ^ 2 ≤
          ((n : ℝ) + 1) * ((n : ℝ) + 1 + ∑ j, Gn (circDist L (x - marks j))) := by
        dsimp only [w] at hw
        simp only [Fin.lastCases_castSucc, Fin.lastCases_last, one_pow] at hw
        nlinarith
      have hv' : (q x) ^ 2 ≤ A ^ 2 *
          (1 + ∑ j, max (circDist L (x - marks j)) K⁻¹ ^ (-b)) ^ 2 := by
        nlinarith [abs_nonneg (q x), sq_abs (q x),
          show 0 ≤ A * (1 + ∑ j, max (circDist L (x - marks j)) K⁻¹ ^ (-b)) by positivity]
      dsimp only [G₀]
      rw [indicator_of_mem (show circDist L x ∈ Iic (2 : ℝ) from hx), mul_one]
      have ht := htn (circDist L x)
      exact hv'.trans (by nlinarith [mul_le_mul_of_nonneg_left hw' (sq_nonneg A)])
    · have hx1 : 1 ≤ circDist L x := by linarith
      have ht := htail x (by linarith)
      have hsquare : (q x) ^ 2 ≤ A ^ 2 * circDist L x ^ (2 * s - 4) := by
        have he : (circDist L x ^ (s - 2)) ^ 2 = circDist L x ^ (2 * s - 4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (circDist_nonneg _ _)]
          norm_num only [Nat.cast_ofNat]
          congr 1; ring
        nlinarith [sq_abs (q x), abs_nonneg (q x),
          show 0 ≤ A * circDist L x ^ (s - 2) by positivity]
      have hn : 0 ≤ ((n : ℝ) + 1) * (((n : ℝ) + 1) * G₀ (circDist L x) +
          ∑ j, Gn (circDist L (x - marks j))) := by
        apply mul_nonneg (by positivity)
        apply add_nonneg
        · exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => by norm_num) _)
        · exact Finset.sum_nonneg fun j _ => hnn _
      dsimp only [Gt]
      rw [indicator_of_mem (show circDist L x ∈ Ici (1 : ℝ) from hx1)]
      nlinarith [mul_nonneg (sq_nonneg A) hn]
  have hsi : IntegrableOn (fun y => ∑ j, Gn (circDist L (y - marks j)))
      (Ioc (-(L / 2)) (L / 2)) := integrable_finsetSum Finset.univ (fun j _ => hni j)
  have hinner : IntegrableOn (fun y => ((n : ℝ) + 1) * G₀ (circDist L y) +
      ∑ j, Gn (circDist L (y - marks j))) (Ioc (-(L / 2)) (L / 2)) :=
    (h0i.const_mul ((n : ℝ) + 1)).add hsi
  have houter := hinner.const_mul ((n : ℝ) + 1)
  have hright : IntegrableOn (fun y => ((n : ℝ) + 1) *
      (((n : ℝ) + 1) * G₀ (circDist L y) + ∑ j, Gn (circDist L (y - marks j))) +
      Gt (circDist L y)) (Ioc (-(L / 2)) (L / 2)) := houter.add hti
  have hmono := setIntegral_mono_on ((hq.pow 2).intervalIntegrable (μ := volume) _ _).1
    (hright.const_mul (A ^ 2)) measurableSet_Ioc (fun x _ => hsq x)
  simp only [Pi.pow_apply] at hmono
  rw [integral_const_mul, integral_add houter hti, integral_const_mul,
    integral_add (h0i.const_mul _) hsi, integral_const_mul,
    integral_finsetSum _ (fun j _ => hni j)] at hmono
  have h0 : (∫ y in Ioc (-(L / 2)) (L / 2), G₀ (circDist L y)) ≤ 4 := by
    have ht := setIntegral_window_circDist_rpow_Iic_le (e := 0) (R := 2) hL
      (by norm_num) (by norm_num) 0
    simpa only [G₀, sub_zero, Real.rpow_zero, zero_add, Real.rpow_one, div_one,
      show (2 : ℝ) * 2 = 4 by norm_num] using ht
  have hn := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    setIntegral_window_capped_power_square_le (b := b) hL hK hδ (marks j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hn
  have ht := setIntegral_window_circDist_rpow_Ici_le (e := 2 * s - 4) (ρ := 1)
    hL (by linarith) (by norm_num) 0
  simp only [sub_zero, Real.one_rpow] at ht
  have ht' : (∫ y in Ioc (-(L / 2)) (L / 2), Gt (circDist L y)) ≤ 2 / (3 - 2 * s) := by
    convert ht using 1
    rw [show 2 * s - 4 + 1 = -(3 - 2 * s) by ring, neg_div_neg_eq]
    ring
  let R := K ^ δ * (1 + K ^ (2 * b - 1))
  have hR : 1 ≤ R := by
    have hpow := Real.one_le_rpow hK hδ.le
    have hn := Real.rpow_nonneg hK0.le (2 * b - 1)
    dsimp [R]; nlinarith
  have hN : 0 ≤ (n : ℝ) + 1 := by positivity
  have h0' := mul_le_mul_of_nonneg_left h0 hN
  have hin := mul_le_mul_of_nonneg_left (add_le_add h0' hn) hN
  have htR := mul_le_mul_of_nonneg_left hR (le_of_lt (div_pos (by norm_num : (0 : ℝ) < 2) hden))
  have hfixed : ((n : ℝ) + 1) * (4 * ((n : ℝ) + 1)) ≤
      ((n : ℝ) + 1) * (4 * ((n : ℝ) + 1)) * R :=
    le_mul_of_one_le_right (by positivity) hR
  apply hmono.trans
  have htotal : ((n : ℝ) + 1) * (((n : ℝ) + 1) *
      (∫ y in Ioc (-(L / 2)) (L / 2), G₀ (circDist L y)) +
      ∑ j, ∫ y in Ioc (-(L / 2)) (L / 2), Gn (circDist L (y - marks j))) +
      (∫ y in Ioc (-(L / 2)) (L / 2), Gt (circDist L y)) ≤ D * R := by
    dsimp [D]
    nlinarith
  exact (mul_le_mul_of_nonneg_left htotal (sq_nonneg A)).trans_eq (by ring)

/-- The same finite-mark energy estimate on the existing
`bellEnergy`, for the derivative of a smooth periodic transport. -/
theorem auxiliary_family_transport_energy_envelopes (n : ℕ) (marks : Fin n → ℝ)
    {s b δ : ℝ} (hs : s < 1) (hb : 0 ≤ b) (hδ : 0 < δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a K h A : ℝ), 0 < a → 1 ≤ K →
      0 < h → K⁻¹ ≤ h → 0 ≤ A → ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → Function.Periodic ψ a⁻¹ →
      (∀ x, |deriv ψ x| ≤ A * (1 + ∑ j,
        max (circDist a⁻¹ (x - marks j)) h ^ (-b))) →
      (∀ x, 2 ≤ circDist a⁻¹ x → |deriv ψ x| ≤ A * circDist a⁻¹ x ^ (s - 2)) →
      bellEnergy a ψ ≤ D * A ^ 2 * (K ^ δ * (1 + K ^ (2 * b - 1))) := by
  obtain ⟨D, hD, hbound⟩ := auxiliary_family_energy_envelopes n marks hs hb hδ
  refine ⟨D, hD, fun a K h A ha hK hh hhK hA ψ hψ hp hnear htail => ?_⟩
  have hper : Function.Periodic (fun y => (deriv ψ y) ^ 2) a⁻¹ :=
    fun y => congrArg (fun t : ℝ => t ^ 2) (deriv_periodic hp y)
  have hshift := hper.intervalIntegral_add_eq 0 (-(a⁻¹ / 2))
  simp only [zero_add, show -(a⁻¹ / 2) + a⁻¹ = a⁻¹ / 2 by ring] at hshift
  unfold bellEnergy
  rw [hshift, intervalIntegral.integral_of_le (by have := inv_pos.mpr ha; linarith)]
  exact hbound a⁻¹ K h A (inv_pos.mpr ha) hK hh hhK hA (deriv ψ)
    (hψ.continuous_deriv (by simp)) hnear htail

end Riesz1.Internal

end
