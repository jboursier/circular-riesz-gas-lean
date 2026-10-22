/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryFamilyDerivativeEnvelope
public import Riesz1.Variance.AuxiliaryTransportEnergyEnvelope
public import Riesz1.Variance.VarAlPiecesUniformMacro

/-!
# Sharp auxiliary estimates on the macroscopic envelope class

The two analytic steps of Proposition 5.6, for smooth periodic
transports with the macroscopic regularization envelopes. One coefficient
precedes the particle number, smoothing radius, and transport.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- Derivative variance and transport energy on the complete macroscopic
envelope class, with the exact auxiliary powers and all `N ≥ 1`. -/
theorem auxiliary_family_macro_envelopes
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (n : ℕ) (marks : Fin n → ℝ)
    (hinj : Function.Injective (fun j => (marks j : Circle unitLength)))
    {b S A ε : ℝ} (hb : 0 < b) (hS : 0 ≤ S) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (h : ℝ), (N : ℝ)⁻¹ ≤ h →
      ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → Function.Periodic F 1 →
      (∀ x, |F x| ≤ S) →
      (∀ x, |deriv F x| ≤ A * (1 + ∑ j,
        max (circDist 1 (x - marks j)) h ^ (-b))) →
      (∀ x, |deriv (deriv F) x| ≤ A * (1 + ∑ j,
        max (circDist 1 (x - marks j)) h ^ (-1 - b))) →
      let Q := fun X : Configuration N => fluctIntegral (deriv F) N X.val
      (∃ hQ : MemLp Q 2 (gibbsMeasure P N),
        variance (gibbsMeasure P N) Q (hQ.integrable one_le_two) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ ε *
            ((N : ℝ) ^ P.val.2 + (N : ℝ) ^ (2 * b)))) ∧
      bellEnergy 1 F ≤ C * ((N : ℝ) ^ ε * (1 + (N : ℝ) ^ (2 * b - 1))) := by
  classical
  obtain ⟨δmark, hδmark, hsepmark⟩ := exists_pos_le_dist_of_injective hinj
  obtain ⟨V, hV, hv⟩ := auxiliary_family_derivative_envelopes hBE hPL P n marks δmark hδmark b ε hb.le hε
  obtain ⟨E, hE, he⟩ := varAlPiecesUniform_macro n marks hinj
    (s := P.val.2) hb hS hA
  let J := ((n + 1 : ℕ) : ℝ) ^ 2 * E ^ 2 *
    (2 * (1 + 1 / ε) + 2 / (3 - 2 * P.val.2))
  let C := V * A ^ 2 + J + 1
  have hJ : 0 ≤ J := by
    have : 0 < 3 - 2 * P.val.2 := by linarith [P.property.2.2]
    dsimp [J]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hVC : V * A ^ 2 ≤ C := by dsimp [C]; linarith
  have hJC : J ≤ C := by
    dsimp [C]; nlinarith [mul_nonneg hV.le (sq_nonneg A)]
  refine ⟨C, hC, fun N h hh F hF hp hsup h1 h2 => ?_⟩
  have hN : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ (N : ℕ) from N.pos)
  have hh0 : 0 < h := lt_of_lt_of_le (inv_pos.mpr (by linarith : 0 < (N : ℝ))) hh
  let a : Scale := ⟨1, by norm_num⟩
  have hsepc (i k : Fin n) (hik : i ≠ k) :
      δmark ≤ circDist a.val⁻¹ (marks i - marks k) := by
    have ht := hsepmark i k hik
    rw [dist_coe_eq_circDist_sub unitLength.property, show unitLength.val = 1 from rfl] at ht
    simpa only [a, inv_one] using ht
  have hfd : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  have hpd : Function.Periodic (deriv F) 1 := Riesz1.periodic_deriv hp
  have hmem : MemLp (fun X : Configuration N => fluctIntegral (deriv F) N X.val) 2
      (gibbsMeasure P N) := errorTwo_memLp_fluctIntegral P N hfd.continuous hpd
  have htail (x : ℝ) (hx : 2 ≤ circDist a.val⁻¹ x) :
      |deriv F x| ≤ A * circDist a.val⁻¹ x ^ (P.val.2 - 2) ∧
        |deriv (deriv F) x| ≤ A * circDist a.val⁻¹ x ^ (P.val.2 - 3) := by
    have hh' := circDist_le_half (by norm_num : (0 : ℝ) < 1) x
    simp only [a, inv_one] at hx
    linarith
  obtain ⟨hi, hvar⟩ := hv N a (by simpa [a] using hN) hsepc h A hh0
    (by simpa [a] using hh) hA (deriv F) hfd
    (by simpa [a] using hpd) (by simpa [a] using h1) (by simpa [a] using h2) htail
  simp only [a, mul_one, div_one] at hvar
  constructor
  · refine ⟨hmem, hvar.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    nlinarith [mul_le_mul_of_nonneg_right hVC
      (show 0 ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ P.val.2 + (N : ℝ) ^ (2 * b)) by positivity)]
  · obtain ⟨φ, hφ, hsum, henv⟩ := he (N : ℝ) h hN hh F hF hp hsup h1 h2
    choose c hc1 hc2 using henv
    let q : Fin (n + 1) → ℝ → ℝ := fun j => deriv (φ j)
    have hq (j : Fin (n + 1)) : Continuous (q j) :=
      (contDiff_infty_iff_deriv.mp (hφ j).1).2.continuous
    have hbound (j : Fin (n + 1)) (y : ℝ) :
        |q j y| ≤ E * gradWeightOne P.val.2 b (N : ℝ) 1 (y - c j) := by
      have h := hc1 j (y - c j)
      rw [deriv_comp_add_const, sub_add_cancel] at h
      exact h
    have hder (y : ℝ) : deriv F y = ∑ j, q j y := by
      rw [funext hsum]
      simpa only [q] using deriv_fun_sum (fun j _ => (hφ j).1.differentiable (by simp) y)
    have henergy := auxiliary_transportEnergy_of_pieces one_pos hN P.property.2.2 hε
      F (by simpa only [inv_one] using hp) (n + 1) c q hq
      (by simpa only [inv_one] using hbound) hder
    apply henergy.trans
    change J * _ ≤ _
    exact mul_le_mul_of_nonneg_right hJC (by positivity)

end Riesz1.Internal

end
