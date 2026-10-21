/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CappedPowerSquareIntegral
public import Riesz1.Auxiliary.BellIncrement
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Transport energy from the one-mark envelope

The integration step in Proposition 5.6: the squared first
transport derivative has a near-mark contribution of order
`K^δ (1 + K^(2b-1))` and an integrable tail. The constant is independent
of the circle length and the location of the mark.
-/

public section

open MeasureTheory Set

namespace Riesz1.Internal

/-- Integrate a continuous function with the actual transport
weight. This includes the logarithmic exponent and every `K ≥ 1`. -/
theorem auxiliary_energy_of_one_mark_envelope {L K s b δ A : ℝ}
    (hL : 0 < L) (hK : 1 ≤ K) (hs : s < 1) (hδ : 0 < δ)
    (c : ℝ) {q : ℝ → ℝ} (hq : Continuous q)
    (hbound : ∀ y, |q y| ≤ A * gradWeightOne s b K L (y - c)) :
    ∫ y in Ioc (-(L / 2)) (L / 2), (q y) ^ 2 ≤
      A ^ 2 * (2 * (1 + 1 / δ) + 2 / (3 - 2 * s)) *
        (K ^ δ * (1 + K ^ (2 * b - 1))) := by
  have hK0 : 0 < K := by linarith
  let Gn : ℝ → ℝ := (Iic (1 : ℝ)).indicator (fun t => max t K⁻¹ ^ (-2 * b))
  let Gt : ℝ → ℝ := (Ici (1 : ℝ)).indicator (fun t => t ^ (2 * s - 4))
  have hin : IntegrableOn (fun y => Gn (circDist L (y - c))) (Ioc (-(L / 2)) (L / 2)) :=
    integrableOn_window_circDist_comp_sub hL Gn c
      (intervalIntegrable_abs_capped_power_indicator (inv_pos.mpr hK0) (-2 * b) (L / 2))
  have hit : IntegrableOn (fun y => Gt (circDist L (y - c))) (Ioc (-(L / 2)) (L / 2)) :=
    integrableOn_window_circDist_comp_sub hL Gt c
      (intervalIntegrable_abs_rpow_indicator_Ici (by linarith) (by norm_num) (by positivity))
  have hpt (y : ℝ) : (q y) ^ 2 ≤ A ^ 2 *
      (Gn (circDist L (y - c)) + Gt (circDist L (y - c))) := by
    have hsq : (q y) ^ 2 ≤ A ^ 2 * gradWeightOne s b K L (y - c) ^ 2 := by
      nlinarith [hbound y, abs_nonneg (q y), sq_abs (q y)]
    apply hsq.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg A)
    unfold gradWeightOne
    by_cases hy : circDist L (y - c) < 1
    · rw [ite_eq_left hy]
      dsimp [Gn, Gt]
      rw [indicator_of_mem (show circDist L (y - c) ∈ Iic (1 : ℝ) from hy.le),
        indicator_of_notMem (show circDist L (y - c) ∉ Ici (1 : ℝ) from not_le.mpr hy), add_zero,
        ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ max (circDist L (y - c)) K⁻¹)]
      norm_num only [Nat.cast_ofNat]
      have he : -b * (2 : ℝ) = -2 * b := by ring
      rw [he]
    · rw [ite_eq_right hy]
      have hy1 : 1 ≤ circDist L (y - c) := not_lt.mp hy
      dsimp [Gt]
      rw [indicator_of_mem (show circDist L (y - c) ∈ Ici (1 : ℝ) from hy1),
        ← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ circDist L (y - c))]
      norm_num only [Nat.cast_ofNat]
      rw [show (s - 2) * (2 : ℝ) = 2 * s - 4 by ring]
      have hn : 0 ≤ Gn (circDist L (y - c)) := by
        dsimp [Gn]
        exact Set.indicator_nonneg (fun t _ => by positivity) _
      linarith
  have hv := setIntegral_mono_on ((hq.pow 2).intervalIntegrable (μ := volume) (-(L / 2)) (L / 2)).1
    ((hin.add hit).const_mul (A ^ 2)) measurableSet_Ioc (fun y _ => hpt y)
  simp only [Pi.add_apply, Pi.pow_apply] at hv
  rw [integral_const_mul, integral_add hin hit] at hv
  have hn := setIntegral_window_capped_power_square_le (b := b) hL hK hδ c
  have ht := setIntegral_window_circDist_rpow_Ici_le (e := 2 * s - 4) (ρ := 1)
    hL (by linarith) (by norm_num) c
  simp only [Real.one_rpow] at ht
  have ht' : (∫ y in Ioc (-(L / 2)) (L / 2), Gt (circDist L (y - c))) ≤ 2 / (3 - 2 * s) := by
    convert ht using 1
    rw [show 2 * s - 4 + 1 = -(3 - 2 * s) by ring, neg_div_neg_eq]
    ring
  have hrate : 1 ≤ K ^ δ * (1 + K ^ (2 * b - 1)) := by
    have hkδ := Real.one_le_rpow hK hδ.le
    have hpow := Real.rpow_nonneg hK0.le (2 * b - 1)
    nlinarith
  have htail : 0 ≤ 2 / (3 - 2 * s) := by
    have : 0 < 3 - 2 * s := by linarith
    positivity
  refine hv.trans ?_
  have hbnd := mul_le_mul_of_nonneg_left (add_le_add hn ht') (sq_nonneg A)
  have htail' := mul_le_mul_of_nonneg_left hrate htail
  nlinarith [mul_le_mul_of_nonneg_left htail' (sq_nonneg A)]

/-- Finite marked pieces retain the same energy rate, with the expected
square of their number. No separation assumption on their centers is
needed for this integration step. -/
theorem auxiliary_energy_of_mark_envelopes {L K s b δ A : ℝ}
    (hL : 0 < L) (hK : 1 ≤ K) (hs : s < 1) (hδ : 0 < δ)
    (m : ℕ) (c : Fin m → ℝ) (q : Fin m → ℝ → ℝ)
    (hq : ∀ j, Continuous (q j))
    (hbound : ∀ j y, |q j y| ≤ A * gradWeightOne s b K L (y - c j)) :
    ∫ y in Ioc (-(L / 2)) (L / 2), (∑ j, q j y) ^ 2 ≤
      (m : ℝ) ^ 2 * A ^ 2 * (2 * (1 + 1 / δ) + 2 / (3 - 2 * s)) *
        (K ^ δ * (1 + K ^ (2 * b - 1))) := by
  have hi (j : Fin m) : IntegrableOn (fun y => (q j y) ^ 2) (Ioc (-(L / 2)) (L / 2)) :=
    ((hq j).pow 2).intervalIntegrable (μ := volume) _ _ |>.1
  have hsumc : Continuous (fun y => (∑ j, q j y) ^ 2) :=
    (continuous_finsetSum _ fun j _ => hq j).pow 2
  have hv := setIntegral_mono_on (hsumc.intervalIntegrable (μ := volume) _ _).1
    ((integrable_finsetSum _ (fun j _ => hi j)).const_mul (m : ℝ)) measurableSet_Ioc
    (fun y _ => show (∑ j, q j y) ^ 2 ≤ (m : ℝ) * ∑ j, (q j y) ^ 2 from by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => q j y))
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => hi j)] at hv
  have hbnd := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    auxiliary_energy_of_one_mark_envelope hL hK hs hδ (c j) (hq j) (hbound j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hbnd
  have hmul := mul_le_mul_of_nonneg_left hbnd (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  exact hv.trans (hmul.trans_eq (by ring))

/-- The same bound on the existing `bellEnergy`, when its periodic
derivative is represented by the finite marked pieces. -/
theorem auxiliary_transportEnergy_of_pieces {ℓ K s b δ A : ℝ}
    (hℓ : 0 < ℓ) (hK : 1 ≤ K) (hs : s < 1) (hδ : 0 < δ)
    (ψ : ℝ → ℝ) (hp : Function.Periodic ψ ℓ⁻¹)
    (m : ℕ) (c : Fin m → ℝ) (q : Fin m → ℝ → ℝ)
    (hq : ∀ j, Continuous (q j))
    (hbound : ∀ j y, |q j y| ≤ A * gradWeightOne s b K ℓ⁻¹ (y - c j))
    (hsum : ∀ y, deriv ψ y = ∑ j, q j y) :
    bellEnergy ℓ ψ ≤
      (m : ℝ) ^ 2 * A ^ 2 * (2 * (1 + 1 / δ) + 2 / (3 - 2 * s)) *
        (K ^ δ * (1 + K ^ (2 * b - 1))) := by
  have hper : Function.Periodic (fun y => (deriv ψ y) ^ 2) ℓ⁻¹ :=
    fun y => congrArg (fun x : ℝ => x ^ 2) (deriv_periodic hp y)
  have hshift := hper.intervalIntegral_add_eq 0 (-(ℓ⁻¹ / 2))
  simp only [zero_add, show -(ℓ⁻¹ / 2) + ℓ⁻¹ = ℓ⁻¹ / 2 by ring] at hshift
  unfold bellEnergy
  have hhalf : -(ℓ⁻¹ / 2) ≤ ℓ⁻¹ / 2 := by have := inv_pos.mpr hℓ; linarith
  rw [hshift, intervalIntegral.integral_of_le hhalf]
  simp_rw [hsum]
  exact auxiliary_energy_of_mark_envelopes (inv_pos.mpr hℓ) hK hs hδ m c q hq hbound

end Riesz1.Internal
