/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingConvolutionParticle
public import Riesz1.ToMathlib.Calculus.IntegerPowerTail

/-!
# Power tails on one microscopic lattice period

Signed representatives give an injective map to the integers, including the
single antipodal point when the period is even. This supplies the cell-tail
step in the localization part of Lemma 5.8.
-/

public section

noncomputable section

open Finset

namespace Riesz1

/-- The two-sided power-tail bound for any subset of a single circle lattice.
The radius is real, so this includes fractional cutoff boundaries. -/
theorem loopLocalization_lattice_tail (N : ℕ+) {a R : ℝ}
    (ha : 1 < a) (hR : 1 ≤ R) (S : Finset ℕ) (hS : S ⊆ range (N : ℕ))
    (hfar : ∀ m ∈ S, R ≤ circDist (N : ℝ) (m : ℝ)) :
    ∑ m ∈ S, circDist (N : ℝ) (m : ℝ) ^ (-a) ≤
      (2 * (1 + 1 / (a - 1))) * R ^ (1 - a) := by
  classical
  let r := fun m : ℕ => if 2 * m ≤ (N : ℕ) then (m : ℤ) else (m : ℤ) - (N : ℤ)
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hrep (m : ℕ) (hm : m ∈ range (N : ℕ)) :
      |((r m : ℤ) : ℝ)| = circDist (N : ℝ) (m : ℝ) := by
    have hmN : (m : ℝ) < N := by exact_mod_cast mem_range.mp hm
    rw [circDist_of_range hN (Nat.cast_nonneg m) hmN]
    dsimp [r]
    split_ifs with h
    · have h' : 2 * (m : ℝ) ≤ N := by exact_mod_cast h
      rw [min_eq_left (by linarith)]
      push_cast
      exact abs_of_nonneg (Nat.cast_nonneg m)
    · have h' : (N : ℝ) < 2 * m := by exact_mod_cast not_le.mp h
      rw [min_eq_right (by linarith)]
      push_cast
      rw [abs_of_nonpos (by linarith)]
      ring
  have hmod (m : ℕ) (hm : m ∈ range (N : ℕ)) : r m % (N : ℤ) = m := by
    have hmN : (m : ℤ) < N := by exact_mod_cast mem_range.mp hm
    have hm0 : (0 : ℤ) ≤ m := by positivity
    dsimp [r]
    split_ifs
    · exact Int.emod_eq_of_lt hm0 hmN
    · rw [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod,
        Int.emod_eq_of_lt hm0 hmN]
  have hinj : Set.InjOn r S := by
    intro i hi j hj he
    have h := congrArg (fun k : ℤ => k % (N : ℤ)) he
    rw [hmod i (hS hi), hmod j (hS hj)] at h
    exact_mod_cast h
  have ht := sum_int_abs_rpow_tail ha hR (S.image r) (by
    intro j hj
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hj
    rw [hrep m (hS hm)]
    exact hfar m hm)
  rw [sum_image hinj] at ht
  convert ht using 1
  apply sum_congr rfl
  intro m hm
  rw [hrep m (hS hm)]

end Riesz1

end
