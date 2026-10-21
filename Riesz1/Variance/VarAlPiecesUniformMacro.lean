/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlPiecesEnvelopeMacro
public import Riesz1.Variance.VarAlPiecesCompleteMacro

/-!
# A common macroscopic decomposition for bounded transport families

Proposition 5.9. The cutoffs and coefficient are fixed before
the smooth function, so the same decomposition estimates apply to the
original profile and both of its convolution families.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1.Internal

/-- On the unit circle, the analytic finite-piece reduction is uniform
over all smooth functions with the stated supremum and derivative bounds. -/
theorem varAlPiecesUniform_macro (n : ℕ) (marks : Fin n → ℝ)
    (hinj : Function.Injective (fun j => (marks j : Circle unitLength)))
    {s b S A : ℝ} (hb : 0 < b) (hS : 0 ≤ S) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K h : ℝ), 1 ≤ K → K⁻¹ ≤ h →
      ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → Function.Periodic F 1 →
      (∀ x, |F x| ≤ S) →
      (∀ x, |deriv F x| ≤ A * (1 + ∑ j,
        max (circDist 1 (x - marks j)) h ^ (-b))) →
      (∀ x, |deriv (deriv F) x| ≤ A * (1 + ∑ j,
        max (circDist 1 (x - marks j)) h ^ (-1 - b))) →
      ∃ φ : Fin (n + 1) → ℝ → ℝ,
        (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) 1) ∧
        (∀ x, F x = ∑ j, φ j x) ∧
        (∀ j, ∃ a : ℝ,
          (∀ x, |deriv (fun t => φ j (t + a)) x| ≤ C * gradWeightOne s b K 1 x) ∧
          (∀ x, |deriv (deriv (fun t => φ j (t + a))) x| ≤
            C * gradWeightTwo s b K 1 x)) := by
  classical
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_dist_of_injective hinj
  let r := min (δ / 6) (1 / 16)
  have hr : 0 < r := lt_min (by linarith) (by norm_num)
  have hr16 : r ≤ 1 / 16 := min_le_right _ _
  have hδr : 6 * r ≤ δ := by linarith [min_le_left (δ / 6) (1 / 16)]
  obtain ⟨M₁, M₂, hM₁, hM₂⟩ := exists_bounds_deriv_bump (contDiff_cutoffBump r)
    (fun x hx => cutoffBump_eq_zero hr hx)
  let C := varAlConst M₁ M₂ S A r n b
  have hC : 0 < C := lt_of_lt_of_le one_pos
    (varAlConst_bounds ((abs_nonneg _).trans (hM₁ 0))
      ((abs_nonneg _).trans (hM₂ 0)) hS hA hr b).2.2.2.2
  refine ⟨C, hC, fun K h hK hh F hF hp hsup h1 h2 => ?_⟩
  have hsepc : ∀ i k, i ≠ k → δ ≤ circDist unitLength.val (marks i - marks k) := by
    intro i k hik
    simpa only [dist_coe_eq_circDist_sub unitLength.property] using hsep i k hik
  obtain ⟨φ, hφ, hsum, henv⟩ := pieces_envelope_of_data hr hr16 hδr hM₁ hM₂ marks
    hsepc hF hp hsup hA hb hK hh h1 h2
  refine ⟨φ, fun j => ⟨(hφ j).1, (hφ j).2.1⟩, hsum, fun j => ?_⟩
  obtain ⟨a, ha1, ha2⟩ := henv j
  change (∀ x, |deriv (fun t => φ j (t + a)) x| ≤ C *
    (if circDist 1 x < 1 then max (circDist 1 x) K⁻¹ ^ (-b) else 0)) at ha1
  refine ⟨a, fun x => ?_, fun x => ?_⟩
  · exact (ha1 x).trans (mul_le_mul_of_nonneg_left (by
      unfold gradWeightOne
      split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (circDist_nonneg _ _) _) hC.le)
  · convert (ha2 x).trans (mul_le_mul_of_nonneg_left (show
        (if circDist 1 x < 1 then max (circDist 1 x) K⁻¹ ^ (-1 - b) else 0) ≤
          gradWeightTwo s b K 1 x by
        unfold gradWeightTwo
        split_ifs
        · rw [show -(1 + b) = -1 - b by ring]
        · exact Real.rpow_nonneg (circDist_nonneg _ _) _) hC.le) using 1

end Riesz1.Internal
