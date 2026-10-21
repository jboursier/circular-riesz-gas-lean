/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.CompactDecompositionPartition
public import Riesz1.Variance.CompactDecompositionCorrection
public import Riesz1.Variance.CompactDecompositionMass

/-!
# Periodic compact transport pieces without separated marks

The analytic reduction for Proposition 5.9. A normalized
partition splits the derivative, one common bump corrects its period
integrals, and periodic primitives give the transport pieces. The
coefficient precedes the circumference and both smoothing scales.
-/

public section

open MeasureTheory
open scoped ContDiff BigOperators

namespace Riesz1.Internal

/-- Smooth compact transports admit a fixed number of periodic pieces
with both translated transport envelopes, uniformly over all periods
and even coincident marked points. Only the stated analytic envelopes
are used. The transport's value and its higher derivatives are unrestricted. -/
theorem compactDecomposition (n : ℕ) (marks : Fin n → ℝ)
    (s b : ℝ) (hs : s < 1) (hb : 0 ≤ b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L h : {r : ℝ // 0 < r}) (K A : ℝ),
      1 ≤ L.val → 1 ≤ K → K⁻¹ ≤ h.val → 0 ≤ A →
      ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → Function.Periodic F L.val →
      (∀ x, |deriv F x| ≤ A * (1 + ∑ j,
        max (circDist L.val (x - marks j)) h.val ^ (-b))) →
      (∀ x, |deriv (deriv F) x| ≤ A * (1 + ∑ j,
        max (circDist L.val (x - marks j)) h.val ^ (-1 - b))) →
      (∀ x, 4 ≤ circDist L.val x →
        |deriv F x| ≤ A * circDist L.val x ^ (s - 2) ∧
          |deriv (deriv F) x| ≤ A * circDist L.val x ^ (s - 3)) →
      ∃ φ : Fin (n + 1) → ℝ → ℝ,
        (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) L.val) ∧
        (∀ x, F x = ∑ j, φ j x) ∧
        (∀ j x,
          |deriv (φ j) x| ≤ C * A * gradWeightOne s b K L.val
            (x - Fin.lastCases 0 marks j) ∧
          |deriv (deriv (φ j)) x| ≤ C * A * gradWeightTwo s b K L.val
            (x - Fin.lastCases 0 marks j)) := by
  obtain ⟨V, hV, hpartition⟩ := compactDecomposition_partition n marks s b hs hb
  obtain ⟨U, hU, hcorrection⟩ := compactDecomposition_correction n marks hs hb
  let D := 2 * (1 + 1 / (1 - b)) + 2 / (1 - s)
  have hD : 0 < D := by dsimp [D]; positivity
  let C := V + 4 * V * D * U
  refine ⟨C, by dsimp [C]; positivity, fun L h K A hL hK hh hA F hF hp h₁ h₂ ht => ?_⟩
  obtain ⟨q, hq, hsumq, henvq, _⟩ := hpartition L h K A hK hh hA (deriv F)
    (contDiff_infty_iff_deriv.mp hF).2 (varAlPieces_periodic_deriv_of hp) h₁ h₂ ht
  obtain ⟨u, hu, hup, hum, _, henvu⟩ := hcorrection L.val K hL hK
  have humpos : 0 < ∫ t in (0 : ℝ)..L.val, u t := by linarith
  obtain ⟨c, φ, hc, _, hφ, hsum, hd₁, hd₂⟩ := periodic_derivative_reconstruction
    (Fin.last n) hF hp hu hup humpos.ne' hq hsumq
  have hcm (j : Fin (n + 1)) : |c j| ≤ 4 * V * A * D := by
    have hmass := compactDecomposition_envelope_mass L.property hK hs hb1
      (mul_nonneg hV.le hA) (Fin.lastCases 0 marks j) (hq j).1.continuous
      (hq j).2 (fun y => (henvq j y).1)
    rw [hc, abs_div, abs_of_pos humpos]
    apply (div_le_iff₀ humpos).mpr
    have hab := intervalIntegral.abs_integral_le_integral_abs L.property.le (f := q j) (μ := volume)
    have hmass' : |∫ t in (0 : ℝ)..L.val, q j t| ≤ V * A * D := hab.trans hmass
    nlinarith [mul_le_mul_of_nonneg_left hum (by positivity : 0 ≤ 4 * V * A * D)]
  refine ⟨φ, hφ, fun x => (hsum x).symm, fun j x => ⟨?_, ?_⟩⟩
  · rw [hd₁]
    have hcub : |c j * u x| ≤ (4 * V * A * D) *
        (U * gradWeightOne s b K L.val (x - Fin.lastCases 0 marks j)) := by
      rw [abs_mul]
      exact mul_le_mul (hcm j) (henvu j x).1 (abs_nonneg _) (by positivity)
    calc
      _ ≤ |q j x| + |c j * u x| := abs_sub _ _
      _ ≤ V * A * gradWeightOne s b K L.val (x - Fin.lastCases 0 marks j) +
          (4 * V * A * D) * (U * gradWeightOne s b K L.val (x - Fin.lastCases 0 marks j)) :=
        add_le_add (henvq j x).1 hcub
      _ = _ := by dsimp [C]; ring
  · rw [hd₂]
    have hcub : |c j * deriv u x| ≤ (4 * V * A * D) *
        (U * gradWeightTwo s b K L.val (x - Fin.lastCases 0 marks j)) := by
      rw [abs_mul]
      exact mul_le_mul (hcm j) (henvu j x).2 (abs_nonneg _) (by positivity)
    calc
      _ ≤ |deriv (q j) x| + |c j * deriv u x| := abs_sub _ _
      _ ≤ V * A * gradWeightTwo s b K L.val (x - Fin.lastCases 0 marks j) +
          (4 * V * A * D) * (U * gradWeightTwo s b K L.val (x - Fin.lastCases 0 marks j)) :=
        add_le_add (henvq j x).2 hcub
      _ = _ := by dsimp [C]; ring

end Riesz1.Internal
