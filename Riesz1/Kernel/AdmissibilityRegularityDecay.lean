/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityDerivative
public import Riesz1.ToMathlib.CircleSingularityEnvelope

/-!
# Oscillatory decay for the derivative of the admissible transport

The exponent may be increased by any sufficiently small positive amount. This covers
the logarithmic endpoint while retaining the exponent needed for Sobolev summability.
The constants in this module may depend on the fixed circle length.
-/

public section

open MeasureTheory Set

namespace Riesz1
namespace Internal

/-- The (A2)–(A3) bound gives a full-period oscillatory estimate, after an arbitrary
small exponent increase. This is an analytic helper. -/
theorem oscillatory_bound_of_transport_bound (P : Parameters) (L : Length)
    {ι : Type*} [Fintype ι] (marks : ι → ℝ) (α C δ : ℝ)
    (hα : P.val.2 - 1 ≤ α) (hδ : 0 < δ) (hδ1 : δ < P.val.2 - α) (hC : 0 ≤ C)
    (ψ : ℝ → ℝ)
    (hreg : ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
      ContDiffAt ℝ 2 ψ x ∧
      |deriv (deriv ψ) x| ≤ C *
        ((if dist (x : Circle L) 0 ≤ 1 then
            ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α)
          else 0) +
         (if 1 ≤ dist (x : Circle L) 0 then
            dist (x : Circle L) 0 ^ (-3 + P.val.2) else 0))) :
    IntervalIntegrable (deriv ψ) volume 0 L.val ∧
      ∃ K W : ℝ, 0 ≤ K ∧ 1 ≤ W ∧
        ∀ (χ : ℝ → ℂ) (c : ℂ), W ≤ ‖c‖ →
          (∀ t : ℝ, HasDerivAt χ (c * χ t) t) → (∀ t : ℝ, ‖χ t‖ = 1) →
          ‖∫ t in (0 : ℝ)..L.val, ((deriv ψ t : ℝ) : ℂ) * χ t‖ ≤
            K * ‖c‖ ^ (α - P.val.2 + δ) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  let b := 1 - P.val.2 + α + δ
  have hb : 0 < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith
  let M := (max 1 (L.val / 2)) ^ δ
  have hM : 1 ≤ M := Real.one_le_rpow (le_max_left _ _) hδ.le
  have hdmax (x : Circle L) (j : ι) : dist x (marks j : Circle L) ≤ max 1 (L.val / 2) := by
    rw [dist_eq_norm]
    exact (AddCircle.norm_le_half_period L.val L.property.ne').trans
      (by rw [abs_of_pos L.property]; exact le_max_right _ _)
  have hp (x : Circle L) (j : ι) (hx : x ≠ (marks j : Circle L)) :
      dist x (marks j : Circle L) ^ (-2 + P.val.2 - α) ≤
        M * dist x (marks j : Circle L) ^ (-1 - b) := by
    have hd : 0 < dist x (marks j : Circle L) := dist_pos.mpr hx
    have he : -2 + P.val.2 - α = δ + (-1 - b) := by dsimp [b]; ring
    rw [he, Real.rpow_add hd]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hd.le (hdmax x j) hδ.le) (by positivity)
  have hres := CircleSingularity.oscillatory_bound_of_deriv_bound L.property hb hb1
    (mul_nonneg hC (by linarith : 0 ≤ M)) (fun j => (marks j : Circle L))
    (q := deriv ψ)
    (fun x _ hx => ((hreg x hx).1.derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)) (fun x _ hx => by
      have hs := Finset.sum_le_sum (s := Finset.univ) fun j _ => hp (x : Circle L) j (hx j)
      rw [← Finset.mul_sum] at hs
      have htail : (if 1 ≤ dist (x : Circle L) 0 then
          dist (x : Circle L) 0 ^ (-3 + P.val.2) else 0) ≤ 1 := by
        split_ifs with hd
        · exact Real.rpow_le_one_of_one_le_of_nonpos hd (by linarith [P.property.2.2])
        · norm_num
      have hsum : (if dist (x : Circle L) 0 ≤ 1 then
          ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α) else 0) ≤
          M * ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-1 - b) := by
        split_ifs
        · exact hs
        · positivity
      have hh := (hreg x hx).2
      nlinarith [mul_le_mul_of_nonneg_left htail hC,
        mul_le_mul_of_nonneg_left hsum hC, mul_le_mul_of_nonneg_left hM hC])
  simpa only [show b - 1 = α - P.val.2 + δ by dsimp [b]; ring] using hres

end Internal

/-- The norm of the angular Fourier frequency, with the arclength normalization. -/
theorem norm_circle_frequency (L : Length) (k : ℤ) :
    ‖(2 * Real.pi * Complex.I * (k : ℂ) / (L.val : ℂ))‖ =
      |2 * Real.pi * (k : ℝ) / L.val| := by
  simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, Complex.norm_intCast, abs_div, abs_mul]
  norm_num

/-- Fourier decay on a fixed circle follows from (A1)–(A3), with no Sobolev or
derivative-integrability premise. Uniformity in varying circle lengths is separate. -/
theorem coeff_decay_of_primitive_transportRegularity (P : Parameters) (L : Length)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (p : ℕ+) (marks : Fin (p : ℕ) → ℝ) (α C : ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hC : 0 ≤ C)
    (hprim : PrimitiveRegularity L η P.val.2 B f)
    (hreg : TransportRegularity P L f p marks α C) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ k : ℤ, 1 ≤ |2 * Real.pi * (k : ℝ) / L.val| →
      ‖coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k‖ ≤
        K * L.val⁻¹ * |2 * Real.pi * (k : ℝ) / L.val| ^ (α - 1 + ε) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  let δ := min ε (P.val.2 - α) / 2
  have hδ : 0 < δ := by dsimp [δ]; exact half_pos (lt_min hε (by linarith [P.property.2.1]))
  have hδε : δ ≤ ε := by dsimp [δ]; linarith [min_le_left ε (P.val.2 - α)]
  have hδ1 : δ < P.val.2 - α := by
    dsimp [δ]; linarith [min_le_right ε (P.val.2 - α), P.property.2.1]
  obtain ⟨ψ, hc, hψ, hcoef, hpoint⟩ :=
    exists_continuous_transport_with_regularity P L η B hη hB f p marks α C hprim hreg
  obtain ⟨hi, K, W, hK, hW, hosc⟩ := Internal.oscillatory_bound_of_transport_bound P L
    marks α C δ hα0 hδ hδ1 hC (fun t : ℝ => ψ (t : Circle L)) hpoint
  obtain ⟨D, hD, hosc⟩ := PuncturedDerivative.oscillatory_bound_extend_to_one L.property.le
    hi (by linarith : α - P.val.2 + δ ≤ 0) hK hW hosc
  let A := 2 * P.val.1 * rieszConstant (parametersExponent P)
  have hA : 0 < A := mul_pos (mul_pos (by norm_num) P.property.1) (rieszConstant_pos _)
  refine ⟨A * D + 1, by positivity, fun k hk => ?_⟩
  let w := |2 * Real.pi * (k : ℝ) / L.val|
  have hw : 0 < w := lt_of_lt_of_le zero_lt_one hk
  have hk0 : k ≠ 0 := by intro he; subst k; norm_num at hk
  let ω : ℂ := 2 * Real.pi * Complex.I * (k : ℂ) / L.val
  have hωn : ‖ω‖ = w := norm_circle_frequency L k
  have hω0 : ω ≠ 0 := norm_pos_iff.mp (hωn.symm ▸ hw)
  have hJ := CircleFourier.integral_deriv_mul_fourier hc
    (CircleSingularity.countable_marked_lifts (T := L.val) marks)
    (fun x hx => (hpoint x (by simpa only [mem_ofPred_eq, not_exists] using hx)).1.differentiableAt
      (by norm_num)) hi k
  change _ = (L.val : ℂ) * ω *
    coeff L ⟨(fun x => (ψ x : ℂ)), complexL2Integrable L _ hψ⟩ k at hJ
  rw [hcoef, transportCoeffs, ite_eq_right hk0] at hJ
  have hJ' : (∫ t in (0 : ℝ)..L.val,
      ((deriv (fun u : ℝ => ψ (u : Circle L)) t : ℝ) : ℂ) * fourier (-k) (t : Circle L)) =
      (-(L.val : ℂ) * (w ^ (1 - P.val.2) : ℝ) / (A : ℂ)) *
        coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k := by
    rw [hJ]
    change (L.val : ℂ) * ω * (-(w ^ (1 - P.val.2) : ℝ) / ((A : ℂ) * ω) * _) = _
    field_simp
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
  have hnormeq : ‖coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k‖ =
      (A / L.val) * w ^ (-(1 - P.val.2)) *
        (L.val * w ^ (1 - P.val.2) / A *
          ‖coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k‖) := by
    symm
    calc _ = (w ^ (-(1 - P.val.2)) * w ^ (1 - P.val.2)) *
        ‖coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k‖ := by
          field_simp [hA.ne', L.property.ne']
      _ = _ := by rw [hcancel, one_mul]
  calc _ = (A / L.val) * w ^ (-(1 - P.val.2)) *
      (L.val * w ^ (1 - P.val.2) / A *
        ‖coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k‖) := hnormeq
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
      have hp := Real.rpow_le_rpow_of_exponent_le hk (by linarith : α - 1 + δ ≤ α - 1 + ε)
      nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg hA.le hD) (inv_nonneg.mpr L.property.le)),
        mul_nonneg (inv_nonneg.mpr L.property.le) (Real.rpow_nonneg hw.le (α - 1 + ε))]

end Riesz1
