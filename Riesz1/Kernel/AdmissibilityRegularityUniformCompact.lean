/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityUniformDecay
public import Riesz1.Kernel.AdmissibilityRegularityProfileFourier
public import Riesz1.ToMathlib.FourierGridLimit

/-!
# Fourier decay uniform over every enlarged circle

The large-circle estimate passes through a shrinking-grid limit to the continuous
Fourier integral of the fixed zero extension. Restricting that integral to any circle's
grid gives the estimate for every scale. The constant precedes the original scale sequence.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace Riesz1

/-- The compact-profile Fourier clause. The fixed data determine
one constant before the shrinking sequence. Its conclusion covers every observation circle,
including scales not selected by that sequence. -/
theorem uniform_compact_profile_coeff_decay (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (m : ℕ+) (marks : Fin (m : ℕ) → ℝ) (α C : ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hC : 0 ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ ell : Scales,
      Tendsto (fun n : ℕ => (ell ⟨n + 1, Nat.succ_pos n⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            m marks α C) →
      ∀ (a : Scale) (k : ℤ), 1 ≤ |2 * Real.pi * (k : ℝ) / (observationLength a).val| →
        ‖coeff (observationLength a)
          ⟨(fun x => (periodizedProfile p (observationLength a) x : ℂ)),
            complexL2Integrable _ _ (periodizedProfileL2 p a)⟩ k‖ ≤
          K * (observationLength a).val⁻¹ *
            |2 * Real.pi * (k : ℝ) / (observationLength a).val| ^ (α - 1 + ε) := by
  obtain ⟨D, W, L0, hD, hW, hL0, hlarge⟩ := uniform_large_circle_coeff_decay
    P p hp η B hη hB m marks α C hα0 hα1 hC ε hε
  let F := fun w : ℝ => ∫ x : ℝ, (zeroExtension p x : ℂ) *
    Complex.exp (((-w * x : ℝ) : ℂ) * Complex.I)
  let Z := ∫ x : ℝ, |zeroExtension p x|
  let g := α - 1 + ε
  let Q := Z * (W + 1) ^ |g|
  have hZ : 0 ≤ Z := integral_nonneg fun _ => abs_nonneg _
  have hQ : 0 ≤ Q := mul_nonneg hZ (Real.rpow_nonneg (by linarith) _)
  refine ⟨D + Q + 1, by linarith, fun ell hell hreg => ?_⟩
  let aN : ℕ → Scale := fun n => ell ⟨n + 1, Nat.succ_pos n⟩
  let h : ℕ → ℝ := fun n => 2 * Real.pi * (aN n).val
  have hh : ∀ n, 0 < h n := fun n => mul_pos (by positivity) (aN n).property.1
  have hlim : Tendsto h atTop (𝓝 0) := by
    simpa only [mul_zero] using hell.const_mul (2 * Real.pi)
  have hL0p : 0 < L0 := by linarith
  have hlength : ∀ᶠ n in atTop, L0 ≤ (observationLength (aN n)).val := by
    filter_upwards [hell.eventually (eventually_lt_nhds (inv_pos.mpr hL0p))] with n hn
    change L0 ≤ (aN n).val⁻¹
    exact (le_inv_comm₀ hL0p (aN n).property.1).mpr hn.le
  have hgrid : ∀ᶠ n in atTop, ∀ k : ℤ, W ≤ |h n * (k : ℝ)| →
      ‖F (h n * (k : ℝ))‖ ≤ D * |h n * (k : ℝ)| ^ g := by
    filter_upwards [hlength] with n hn
    intro k hk
    have hw : h n * (k : ℝ) = 2 * Real.pi * (k : ℝ) / (observationLength (aN n)).val := by
      dsimp [h, observationLength]
      simp only [inv_inv, div_eq_mul_inv]
      ring
    rw [hw] at hk ⊢
    rw [show F (2 * Real.pi * (k : ℝ) / (observationLength (aN n)).val) =
      ((observationLength (aN n)).val : ℂ) * coeff (observationLength (aN n))
        ⟨(fun x => (periodizedProfile p (observationLength (aN n)) x : ℂ)),
          complexL2Integrable _ _ (periodizedProfileL2 p (aN n))⟩ k from
        (length_mul_periodizedProfile_coeff p (aN n) k).symm]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (observationLength (aN n)).property]
    have hd := hlarge (aN n) hn (hreg ⟨n + 1, Nat.succ_pos n⟩).1
      (hreg ⟨n + 1, Nat.succ_pos n⟩).2 k hk
    have hm := mul_le_mul_of_nonneg_left hd (observationLength (aN n)).property.le
    convert hm using 1
    dsimp [g]
    field_simp [(observationLength (aN n)).property.ne']
  have hall (w : ℝ) (hw : 1 ≤ |w|) : ‖F w‖ ≤ (D + Q + 1) * |w| ^ g := by
    have hw0 : w ≠ 0 := abs_pos.mp (lt_of_lt_of_le zero_lt_one hw)
    have hpw : 0 ≤ |w| ^ g := Real.rpow_nonneg (abs_nonneg _) _
    by_cases hwW : W < |w|
    · exact (FourierGrid.norm_le_rpow_of_grid_bound
        (continuous_zeroExtension_fourierIntegral p) hh hlim hgrid hwW hw0).trans
          (mul_le_mul_of_nonneg_right (by linarith) hpw)
    · have hwW' : |w| ≤ W + 1 := by linarith
      have hpow : |w| ^ (-g) ≤ (W + 1) ^ |g| :=
        (Real.rpow_le_rpow_of_exponent_le hw (neg_le_abs g)).trans
          (Real.rpow_le_rpow (abs_nonneg _) hwW' (abs_nonneg g))
      have hcancel : |w| ^ (-g) * |w| ^ g = 1 := by
        rw [← Real.rpow_add (abs_pos.mpr hw0), neg_add_cancel, Real.rpow_zero]
      have hb := norm_zeroExtension_fourierIntegral_le p w
      change ‖F w‖ ≤ Z at hb
      have hmult := mul_le_mul_of_nonneg_left hpow hZ
      have hmult' := mul_le_mul_of_nonneg_right hmult hpw
      rw [mul_assoc, hcancel, mul_one] at hmult'
      exact (hb.trans hmult').trans (mul_le_mul_of_nonneg_right (by dsimp [Q]; linarith) hpw)
  intro a k hk
  have hb := hall (2 * Real.pi * (k : ℝ) / (observationLength a).val) hk
  rw [show F (2 * Real.pi * (k : ℝ) / (observationLength a).val) =
    ((observationLength a).val : ℂ) * coeff (observationLength a)
      ⟨(fun x => (periodizedProfile p (observationLength a) x : ℂ)),
        complexL2Integrable _ _ (periodizedProfileL2 p a)⟩ k from
      (length_mul_periodizedProfile_coeff p a k).symm,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (observationLength a).property] at hb
  have hm := mul_le_mul_of_nonneg_left hb (inv_pos.mpr (observationLength a).property).le
  simpa only [← mul_assoc, inv_mul_cancel₀ (observationLength a).property.ne', one_mul,
    mul_comm (observationLength a).val⁻¹ (D + Q + 1)] using hm

end Riesz1
