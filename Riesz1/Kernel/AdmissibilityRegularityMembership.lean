/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityDecay
public import Riesz1.Kernel.AdmissibilityRegularitySobolev
public import Riesz1.Kernel.AdmissibilityRegularityExtension
public import Riesz1.ToMathlib.CircleFourierDilation
public import Riesz1.Frozen.Admissible

/-!
# Sobolev membership supplied by admissibility

Fourier decay on one relevant circle gives Sobolev membership of its unit-circle
pullback. For compact profiles this discharges the membership input in the
circle/line equivalence and variance comparison.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1
namespace Internal

/-- Conversion of a frequency bound on a fixed circle to the integer-frequency bound
used in the summability theorem. The conditional Fourier input stays internal. -/
theorem circleSobolev_of_circle_frequency_decay (L : Length) {s α ε K : ℝ}
    (hαε : α + ε < s / 2) {f : UnitAddCircle → ℂ} (hf : MemLp f 2 volume)
    (F : ℤ → ℂ) (hcoeff : ∀ k, fourierCoeff f k = F k)
    (hdecay : ∀ k : ℤ, 1 ≤ |2 * Real.pi * (k : ℝ) / L.val| →
      ‖F k‖ ≤ K * L.val⁻¹ * |2 * Real.pi * (k : ℝ) / L.val| ^ (α - 1 + ε)) :
    CircleSobolev ((1 - s) / 2) f := by
  let c := 2 * Real.pi / L.val
  have hc : 0 < c := div_pos (mul_pos (by norm_num) Real.pi_pos) L.property
  obtain ⟨k₀, hk₀⟩ := exists_int_gt (max 1 (1 / c))
  have hk₀1 : (1 : ℤ) ≤ k₀ := by
    have he : (1 : ℝ) < k₀ := (le_max_left _ _).trans_lt hk₀
    exact_mod_cast he.le
  have hk₀c : 1 ≤ c * (k₀ : ℝ) := by
    have he : 1 / c ≤ (k₀ : ℝ) := (le_max_right _ _).trans hk₀.le
    have hh := (div_le_iff₀ hc).mp he
    nlinarith
  apply circleSobolev_of_coeff_decay (g := α - 1 + ε)
    (K := K * L.val⁻¹ * c ^ (α - 1 + ε)) (by linarith) hf hk₀1
  intro k hk
  have hkR : (k₀ : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast hk
  have hfreq : |2 * Real.pi * (k : ℝ) / L.val| = c * |(k : ℝ)| := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos L.property,
      abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    dsimp [c]
    ring
  have hlarge : 1 ≤ |2 * Real.pi * (k : ℝ) / L.val| := by
    rw [hfreq]
    exact hk₀c.trans (mul_le_mul_of_nonneg_left hkR hc.le)
  rw [hcoeff]
  have hd := hdecay k hlarge
  rw [hfreq, Real.mul_rpow hc.le (abs_nonneg _)] at hd
  simpa only [mul_assoc] using hd

end Internal

/-- (A1)–(A3) on the unit circle imply the profile's Sobolev membership. -/
theorem circleSobolev_of_unit_primitive_transportRegularity (P : Parameters)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B) (p : Profile)
    (m : ℕ+) (marks : Fin (m : ℕ) → ℝ) (α C : ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hC : 0 ≤ C)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ m marks α C) :
    CircleSobolev ((1 - P.val.2) / 2) (fun x => (p.val x : ℂ)) := by
  let ε := (P.val.2 / 2 - α) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨K, _, hdecay⟩ := coeff_decay_of_primitive_transportRegularity P unitLength
    η B hη hB ⟨p.val, p.property⟩ m marks α C hα0 hα1 hC hprim hreg ε hε
  exact Internal.circleSobolev_of_circle_frequency_decay unitLength
    (by dsimp [ε]; linarith) p.property
    (fun k => coeff unitLength ⟨(fun x => (p.val x : ℂ)),
      complexL2Integrable unitLength _ p.property⟩ k) (fun _ => rfl) hdecay

/-- On a circle of length at least one, only the central translate of the zero
extension contributes. This elementary fact uses no transport-kernel module. -/
theorem admissibility_periodizedProfile_eq_zeroExtension (p : Profile) (L : Length)
    (hL : 1 ≤ L.val) (x : Circle L) :
    periodizedProfile p L x = zeroExtension p (centralRep L x) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  unfold periodizedProfile
  rw [tsum_eq_single (0 : ℤ)]
  · simp only [Int.cast_zero, zero_mul, add_zero]
  · intro n hn
    have hu := (AddCircle.equivIco L.val (-L.val / 2) x).property
    change -L.val / 2 ≤ centralRep L x ∧ centralRep L x < -L.val / 2 + L.val at hu
    have hdist : (1 / 2 : ℝ) ≤ |centralRep L x + (n : ℝ) * L.val| := by
      rcases lt_or_gt_of_ne hn with hn | hn
      · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
        have hmul := mul_le_mul_of_nonneg_right hn' L.property.le
        exact le_trans (by linarith [hu.2]) (neg_le_abs _)
      · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        have hmul := mul_le_mul_of_nonneg_right hn' L.property.le
        exact le_trans (by linarith [hu.1]) (le_abs_self _)
    simp only [zeroExtension, ite_eq_right (not_lt.mpr hdist)]

/-- The normalized coefficients of the actual scaled test agree with those of the
profile on the observation circle, with the endpoint conventions. -/
theorem testAtScale_coeff_eq_periodized (p : Profile) (a : Scale) (k : ℤ) :
    fourierCoeff (fun x => (testAtScale p a x : ℂ)) k =
      coeff (observationLength a) ⟨(fun x => (periodizedProfile p (observationLength a) x : ℂ)),
        complexL2Integrable _ _ (periodizedProfileL2 p a)⟩ k := by
  have : Fact (0 < (observationLength a).val) := ⟨(observationLength a).property⟩
  change fourierCoeff (fun x => (testAtScale p a x : ℂ)) k =
    fourierCoeff (fun x : Circle (observationLength a) =>
      (periodizedProfile p (observationLength a) x : ℂ)) k
  apply CircleFourier.coeff_eq_of_scaled_lifts
  intro t ht
  have htAbs : |t| < 1 / 2 := abs_lt.mpr ⟨ht.1, ht.2⟩
  have hL := (observationLength a).property
  have hcell : (observationLength a).val * t ∈
      Ico (-(observationLength a).val / 2)
        (-(observationLength a).val / 2 + (observationLength a).val) := by
    constructor <;> nlinarith [mul_lt_mul_of_pos_left ht.1 hL,
      mul_lt_mul_of_pos_left ht.2 hL]
  have hc : centralRep (observationLength a)
      (((observationLength a).val * t : ℝ) : Circle (observationLength a)) =
        (observationLength a).val * t := by
    unfold centralRep
    exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hcell)
  rw [testAtScale_coe_of_abs_lt p htAbs, admissibility_periodizedProfile_eq_zeroExtension,
    hc]
  · change (zeroExtension p (t / a.val) : ℂ) =
      (zeroExtension p ((observationLength a).val * t) : ℂ)
    congr 2
    change t / a.val = a.val⁻¹ * t
    ring
  · exact (one_le_inv₀ a.property.1).mpr a.property.2

/-- Regularity on an observation circle implies Sobolev membership of its actual
unit-circle pullback. No compact support premise is needed for this step. -/
theorem testAtScale_sobolev_of_periodized_regularity (P : Parameters) (p : Profile) (a : Scale)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (m : ℕ+) (marks : Fin (m : ℕ) → ℝ) (α C : ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hC : 0 ≤ C)
    (hprim : PrimitiveRegularity (observationLength a) η P.val.2 B
      ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩)
    (hreg : TransportRegularity P (observationLength a)
      ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ m marks α C) :
    CircleSobolev ((1 - P.val.2) / 2) (fun x => (testAtScale p a x : ℂ)) := by
  let ε := (P.val.2 / 2 - α) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨K, _, hdecay⟩ := coeff_decay_of_primitive_transportRegularity P (observationLength a)
    η B hη hB ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩
    m marks α C hα0 hα1 hC hprim hreg ε hε
  exact Internal.circleSobolev_of_circle_frequency_decay (observationLength a)
    (by dsimp [ε]; linarith) (testAtScaleL2 p a) _
    (testAtScale_coeff_eq_periodized p a) hdecay

/-- Every relevant scaled test of an admissible profile has finite Sobolev seminorm.
This discharges the circle-membership premise of the circle/line equivalence and the
variance comparison. -/
theorem admissible_circleSobolev (P : Parameters) (p : Profile)
    (ell : Scales) (α : ℝ) (d : TestData) (h : Admissible P p ell α d) (N : ℕ+) :
    CircleSobolev ((1 - P.val.2) / 2) (fun x => (testAtScale p (ell N) x : ℂ)) := by
  obtain ⟨hα0, hα1, hη, _, hB, hC, hcases⟩ := h
  rcases hcases with ⟨hell, hprim, hreg⟩ | ⟨_, _, hreg⟩
  · have hm := circleSobolev_of_unit_primitive_transportRegularity P d.1 d.2.1 hη hB.le p
      d.2.2.2.1 d.2.2.2.2 α d.2.2.1 hα0 hα1 hC.le hprim hreg
    simpa only [testAtScale, hell N, ite_true] using hm
  · exact testAtScale_sobolev_of_periodized_regularity P p (ell N) d.1 d.2.1 hη hB.le
      d.2.2.2.1 d.2.2.2.2 α d.2.2.1 hα0 hα1 hC.le (hreg N).1 (hreg N).2

end Riesz1
