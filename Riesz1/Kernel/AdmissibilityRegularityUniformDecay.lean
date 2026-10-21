/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityUniformPeriod
public import Riesz1.Kernel.AdmissibilityRegularityDecay
public import Riesz1.ToMathlib.CircleFourierDerivativeShift

/-!
# Uniform high-frequency Fourier decay on enlarged circles

The full-period estimate and the exact multiplier give one constant before
all sufficiently large observation circles.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- The normalized coefficient estimate for all sufficiently large circles and high
frequencies, uniformly over every scale satisfying the fixed admissibility bounds. -/
theorem uniform_large_circle_coeff_decay (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (m : ℕ+) (marks : Fin (m : ℕ) → ℝ) (α C : ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hC : 0 ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K W L0 : ℝ, 0 < K ∧ 1 ≤ W ∧ 1 ≤ L0 ∧ ∀ a : Scale,
      L0 ≤ (observationLength a).val →
      PrimitiveRegularity (observationLength a) η P.val.2 B
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ →
      TransportRegularity P (observationLength a)
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ m marks α C →
      ∀ k : ℤ, W ≤ |2 * Real.pi * (k : ℝ) / (observationLength a).val| →
        ‖coeff (observationLength a)
          ⟨(fun x => (periodizedProfile p (observationLength a) x : ℂ)),
            complexL2Integrable _ _ (periodizedProfileL2 p a)⟩ k‖ ≤
          K * (observationLength a).val⁻¹ *
            |2 * Real.pi * (k : ℝ) / (observationLength a).val| ^ (α - 1 + ε) := by
  let δ := min ε (P.val.2 - α) / 2
  have hδ : 0 < δ := by dsimp [δ]; exact half_pos (lt_min hε (by linarith [P.property.2.1]))
  have hδε : δ ≤ ε := by dsimp [δ]; linarith [min_le_left ε (P.val.2 - α)]
  have hδ1 : δ < P.val.2 - α := by
    dsimp [δ]; linarith [min_le_right ε (P.val.2 - α), P.property.2.1]
  obtain ⟨D, W, L0, hD, hW, hL0, hestimate⟩ :=
    exists_uniform_large_circle_transport_estimate P p hp η B hη hB m marks α C δ
      hα0 hα1 hC hδ hδ1
  let A := 2 * P.val.1 * rieszConstant (parametersExponent P)
  have hA : 0 < A := mul_pos (mul_pos (by norm_num) P.property.1) (rieszConstant_pos _)
  refine ⟨A * D + 1, W, L0, by positivity, hW, hL0, fun a ha hprim hreg => ?_⟩
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨ψ, hc, hψ, hcoef, hi, hd, hosc⟩ := hestimate a ha hprim hreg
  intro k hk
  let w := |2 * Real.pi * (k : ℝ) / L.val|
  have hw : 0 < w := lt_of_lt_of_le zero_lt_one (hW.trans hk)
  have hk0 : k ≠ 0 := by intro he; subst k; norm_num at hk; linarith
  let ω : ℂ := 2 * Real.pi * Complex.I * (k : ℂ) / L.val
  have hωn : ‖ω‖ = w := norm_circle_frequency L k
  have hω0 : ω ≠ 0 := norm_pos_iff.mp (hωn.symm ▸ hw)
  have hi0 : IntervalIntegrable (deriv (fun u : ℝ => ψ (u : Circle L))) volume 0 L.val :=
    (intervalIntegrable_iff' (by finiteness)).mpr (hi.integrableOn_isCompact isCompact_uIcc)
  have hJ := CircleFourier.integral_deriv_mul_fourier_shift hc
    (CircleSingularity.countable_marked_lifts (T := L.val) marks)
    (fun x hx => hd x (by simpa only [mem_ofPred_eq, not_exists] using hx))
    hi0 (-(L.val / 2)) k
  rw [show -(L.val / 2) + L.val = L.val / 2 by ring, ← neg_div] at hJ
  change _ = (L.val : ℂ) * ω *
    coeff L ⟨(fun x => (ψ x : ℂ)), complexL2Integrable L _ hψ⟩ k at hJ
  rw [hcoef, transportCoeffs, ite_eq_right hk0] at hJ
  have hJ' : (∫ t in (-L.val / 2)..(L.val / 2),
      ((deriv (fun u : ℝ => ψ (u : Circle L)) t : ℝ) : ℂ) * fourier (-k) (t : Circle L)) =
      (-(L.val : ℂ) * (w ^ (1 - P.val.2) : ℝ) / (A : ℂ)) *
        coeff L ⟨(fun x => (periodizedProfile p L x : ℂ)), complexL2Integrable L _ (periodizedProfileL2 p a)⟩ k := by
    rw [hJ]
    change (L.val : ℂ) * ω * (-(w ^ (1 - P.val.2) : ℝ) / ((A : ℂ) * ω) * _) = _
    field_simp
    rfl
  have hnorm := congrArg norm hJ'
  simp only [norm_mul, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos L.property, abs_of_pos hA,
    abs_of_nonneg (Real.rpow_nonneg hw.le (1 - P.val.2))] at hnorm
  have ho := hosc (fun t => fourier (-k) (t : Circle L)) (-ω)
    (by simpa only [norm_neg, hωn] using hk)
    (fun t => by simpa [ω, neg_div] using hasDerivAt_fourier_neg L.val k t)
    (fun _ => Circle.norm_coe _)
  rw [norm_neg, hωn, hnorm] at ho
  have hcancel : w ^ (-(1 - P.val.2)) * w ^ (1 - P.val.2) = 1 := by
    rw [← Real.rpow_add hw, neg_add_cancel, Real.rpow_zero]
  have hnormeq : ‖coeff L ⟨(fun x => (periodizedProfile p L x : ℂ)), complexL2Integrable L _ (periodizedProfileL2 p a)⟩ k‖ =
      (A / L.val) * w ^ (-(1 - P.val.2)) *
        (L.val * w ^ (1 - P.val.2) / A *
          ‖coeff L ⟨(fun x => (periodizedProfile p L x : ℂ)), complexL2Integrable L _ (periodizedProfileL2 p a)⟩ k‖) := by
    symm
    calc _ = (w ^ (-(1 - P.val.2)) * w ^ (1 - P.val.2)) *
        ‖coeff L ⟨(fun x => (periodizedProfile p L x : ℂ)), complexL2Integrable L _ (periodizedProfileL2 p a)⟩ k‖ := by
          field_simp [hA.ne', L.property.ne']
      _ = _ := by rw [hcancel, one_mul]
  calc _ = (A / L.val) * w ^ (-(1 - P.val.2)) *
      (L.val * w ^ (1 - P.val.2) / A *
        ‖coeff L ⟨(fun x => (periodizedProfile p L x : ℂ)), complexL2Integrable L _ (periodizedProfileL2 p a)⟩ k‖) := hnormeq
    _ ≤ (A / L.val) * w ^ (-(1 - P.val.2)) * (D * w ^ (α - P.val.2 + δ)) :=
      mul_le_mul_of_nonneg_left ho (mul_nonneg (div_nonneg hA.le L.property.le)
        (Real.rpow_nonneg hw.le _))
    _ = (A * D) * L.val⁻¹ * w ^ (α - 1 + δ) := by
      rw [show (A / L.val) * w ^ (-(1 - P.val.2)) * (D * w ^ (α - P.val.2 + δ)) =
        (A * D) * L.val⁻¹ * (w ^ (-(1 - P.val.2)) * w ^ (α - P.val.2 + δ)) by ring,
        ← Real.rpow_add hw]
      congr 2
      ring
    _ ≤ (A * D + 1) * L.val⁻¹ * w ^ (α - 1 + ε) := by
      have hp := Real.rpow_le_rpow_of_exponent_le (hW.trans hk) (by linarith : α - 1 + δ ≤ α - 1 + ε)
      nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg hA.le hD.le) (inv_nonneg.mpr L.property.le)),
        mul_nonneg (inv_nonneg.mpr L.property.le) (Real.rpow_nonneg hw.le (α - 1 + ε))]


end Riesz1
