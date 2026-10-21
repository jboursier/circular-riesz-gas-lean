/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingZDifferences

/-!
# Three-point divided differences, including lattice crossings

The two-point remainder bounds already proved in `GradientSplittingZBounds` imply
the finite-difference bound without any restriction on the three-point hull.
Subtract the derivative at the middle point, and use the secant identity to
transfer the estimate to either of the other choices of common endpoint.
-/

public section

open Set
open scoped ContDiff

namespace Riesz1

/-- The fundamental theorem of calculus, including coincident endpoints. -/
lemma gradZavg_mul_sub {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (p q : ℝ) :
    gradZavg ψ p q * (q - p) = ψ q - ψ p := by
  rcases eq_or_ne p q with rfl | hpq
  · simp
  · rw [gradZavg_eq_div hψ hpq, div_mul_cancel₀ _ (sub_ne_zero.mpr hpq.symm)]

/-- The algebraic three-point secant identity. No distinctness is required. -/
lemma gradZavg_three_point_identity {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (p P Q : ℝ) :
    (Q - p) * (gradZavg ψ p Q - gradZavg ψ p P) =
      (Q - P) * (gradZavg ψ P Q - gradZavg ψ p P) := by
  have h₁ := gradZavg_mul_sub hψ p Q
  have h₂ := gradZavg_mul_sub hψ p P
  have h₃ := gradZavg_mul_sub hψ P Q
  linear_combination h₁ - h₂ - h₃

/-- Distances add when the middle point belongs to the closed interval. -/
lemma gradSplit_abs_add_of_between {p P Q : ℝ} (h : P ∈ uIcc p Q) :
    |Q - P| + |P - p| = |Q - p| := by
  rcases Set.mem_uIcc.mp h with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h.2), abs_of_nonneg (sub_nonneg.mpr h.1),
      abs_of_nonneg (sub_nonneg.mpr (h.1.trans h.2))]
    ring
  · rw [abs_of_nonpos (sub_nonpos.mpr h.1), abs_of_nonpos (sub_nonpos.mpr h.2),
      abs_of_nonpos (sub_nonpos.mpr (h.1.trans h.2))]
    ring

/-- Internal transfer lemma: two-point remainder bounds control a three-point
finite difference when the changing endpoint is the middle point. -/
lemma gradZavg_sub_le_of_endpoint_between {ψ w : ℝ → ℝ} {A p P Q : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hA : 0 ≤ A) (hw : ∀ t, 0 ≤ w t)
    (hrem : ∀ u v, |gradZavg ψ u v - deriv ψ u| ≤ A * |v - u| * (w u + w v))
    (hmid : P ∈ uIcc p Q) :
    |gradZavg ψ p Q - gradZavg ψ p P| ≤ A * |Q - P| * (w p + w P + w Q) := by
  rcases eq_or_ne p Q with rfl | hpQ
  · have : P = p := by simpa using hmid
    subst P
    simp
  have hlen : 0 < |Q - p| := abs_pos.mpr (sub_ne_zero.mpr hpQ.symm)
  have h₁ := hrem P Q
  have h₂ := hrem P p
  rw [gradZavg_symm ψ P p] at h₂
  have hinner : |gradZavg ψ P Q - gradZavg ψ p P| ≤
      A * |Q - p| * (w p + w P + w Q) := by
    calc
      |gradZavg ψ P Q - gradZavg ψ p P| ≤
          |gradZavg ψ P Q - deriv ψ P| + |gradZavg ψ p P - deriv ψ P| :=
        by simpa only [abs_sub_comm (deriv ψ P)] using
          (abs_sub_le (gradZavg ψ P Q) (deriv ψ P) (gradZavg ψ p P))
      _ ≤ A * |Q - P| * (w P + w Q) + A * |p - P| * (w P + w p) := add_le_add h₁ h₂
      _ ≤ A * |Q - P| * (w p + w P + w Q) +
          A * |P - p| * (w p + w P + w Q) := by
        rw [abs_sub_comm p P]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (by linarith [hw p]) (mul_nonneg hA (abs_nonneg _)))
          (mul_le_mul_of_nonneg_left (by linarith [hw Q]) (mul_nonneg hA (abs_nonneg _)))
      _ = A * |Q - p| * (w p + w P + w Q) := by
        rw [← gradSplit_abs_add_of_between hmid]
        ring
  have hid := congrArg abs (gradZavg_three_point_identity hψ p P Q)
  simp only [abs_mul] at hid
  apply (mul_le_mul_iff_right₀ hlen).mp
  calc
    |Q - p| * |gradZavg ψ p Q - gradZavg ψ p P| =
        |Q - P| * |gradZavg ψ P Q - gradZavg ψ p P| := hid
    _ ≤ |Q - P| * (A * |Q - p| * (w p + w P + w Q)) :=
      mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
    _ = |Q - p| * (A * |Q - P| * (w p + w P + w Q)) := by ring

/-- Internal transfer lemma: a symmetric secant with weighted two-point
remainders satisfies the corresponding three-point finite-difference bound. -/
lemma gradZavg_sub_le_of_remainders {ψ w : ℝ → ℝ} {A : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hA : 0 ≤ A) (hw : ∀ t, 0 ≤ w t)
    (hrem : ∀ u v, |gradZavg ψ u v - deriv ψ u| ≤ A * |v - u| * (w u + w v))
    (p P Q : ℝ) :
    |gradZavg ψ p Q - gradZavg ψ p P| ≤ A * |Q - P| * (w p + w P + w Q) := by
  have hcases : p ∈ uIcc P Q ∨ P ∈ uIcc p Q ∨ Q ∈ uIcc p P := by
    simp only [Set.mem_uIcc]
    rcases le_total p P with h₁ | h₁ <;> rcases le_total P Q with h₂ | h₂ <;>
      rcases le_total p Q with h₃ | h₃ <;> tauto
  rcases hcases with hmid | hmid | hmid
  · have h₁ := hrem p Q
    have h₂ := hrem p P
    calc
      |gradZavg ψ p Q - gradZavg ψ p P| ≤
          |gradZavg ψ p Q - deriv ψ p| + |gradZavg ψ p P - deriv ψ p| := by
        simpa only [abs_sub_comm (deriv ψ p)] using
          (abs_sub_le (gradZavg ψ p Q) (deriv ψ p) (gradZavg ψ p P))
      _ ≤ A * |Q - p| * (w p + w Q) + A * |P - p| * (w p + w P) := add_le_add h₁ h₂
      _ ≤ A * |Q - p| * (w p + w P + w Q) +
          A * |p - P| * (w p + w P + w Q) := by
        rw [abs_sub_comm p P]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (by linarith [hw P]) (mul_nonneg hA (abs_nonneg _)))
          (mul_le_mul_of_nonneg_left (by linarith [hw Q]) (mul_nonneg hA (abs_nonneg _)))
      _ = A * |Q - P| * (w p + w P + w Q) := by
        rw [← gradSplit_abs_add_of_between hmid]
        ring
  · exact gradZavg_sub_le_of_endpoint_between hψ hA hw hrem hmid
  · have h := gradZavg_sub_le_of_endpoint_between hψ hA hw hrem hmid
    rw [abs_sub_comm (gradZavg ψ p P), abs_sub_comm P Q] at h
    convert h using 1
    ring

/-- Claim (iv), in rescaled coordinates, including every lattice-crossing case.
The hull length is unrestricted. -/
theorem gradZavg_sub_gradZavg_le {s a K L C0 : ℝ} {ψ : ℝ → ℝ}
    (hL : 0 < L) (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hK : 1 ≤ K) (hC0 : 0 ≤ C0) (hψ : ContDiff ℝ ∞ ψ) (hper : Function.Periodic ψ L)
    (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K L t)
    (hbd2 : ∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s a K L t)
    (p P Q : ℝ) :
    |gradZavg ψ p Q - gradZavg ψ p P| ≤ (gradZConst a s + 1) * C0 * |Q - P| *
      (gradWeightTwo s a K L p + gradWeightTwo s a K L P + gradWeightTwo s a K L Q) := by
  apply gradZavg_sub_le_of_remainders hψ
    (mul_nonneg (by linarith [gradZConst_nonneg ha1 hs1]) hC0)
    (fun _ => gradWeightTwo_nonneg hK)
  exact gradZavg_sub_deriv_le hL hs0 hs1 ha0 ha1 hK hC0 hψ hper hbd hbd2

end Riesz1

end
