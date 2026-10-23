/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopMomentsDiscrepancy
public import Riesz1.Auxiliary.LoopArcsLambda

/-!
# Lattice facts for the cell estimate of the arc-crossing representation

Preparation for the `L^p` bound of the arcs part of Lemma B.2.
The particle positions are lifted to the line by `z_i + nN`, `n ∈ ℤ`, and the arcs of length at
most `2` used in the cell estimate meet at most one lift of each particle. This file proves

* `lift_eq_of_mem_window`: two lifts of one point lying in an open window of length `2` agree,
  when `N ≥ 2`.
* `loopPos_mem_microArc_iff`: membership of a particle in a microscopic arc, in lift form.
* `dist_loopPos_eq_of_forward`: two particles whose lifts differ by `d ∈ (0, 1)` (modulo `N`)
  are at circular distance `d`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set

namespace Riesz1

/-- Two lifts `x + nN` and `x + n'N` in an open window `(c, c + 2)` of length `2 ≤ N` coincide:
their difference `(n - n')N` has absolute value below `2 ≤ N`, so `|n - n'| < 1`. -/
theorem lift_eq_of_mem_window {N : ℕ+} (hN : (2 : ℝ) ≤ N) {x c : ℝ} {n n' : ℤ}
    (h1 : c < x + n * N) (h2 : x + n * N < c + 2) (h3 : c < x + n' * N)
    (h4 : x + n' * N < c + 2) : n = n' := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hA : ((n : ℝ) - n') * N < 2 := by nlinarith
  have hB : -2 < ((n : ℝ) - n') * N := by nlinarith
  have hC : ((n : ℝ) - n') < 1 := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith
  have hD : -1 < ((n : ℝ) - n') := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith
  have hE : n - n' < 1 := by exact_mod_cast hC
  have hF : -1 < n - n' := by exact_mod_cast hD
  omega

/-- A particle lies in the microscopic arc `microArc N a r` exactly when one of its lifts
`N x_i + nN` lies in the interval `(a, a + r)`. -/
theorem loopPos_mem_microArc_iff {N : ℕ+} (X : Configuration N) (i : Fin (N : ℕ)) (a r : ℝ) :
    loopPos X i ∈ microArc N a r ↔
      ∃ n : ℤ, a < (N : ℝ) * X.val i + n * N ∧ (N : ℝ) * X.val i + n * N < a + r := by
  unfold loopPos
  exact coe_mem_microArc_iff a r _

/-- Two particles whose real lifts differ by `d ∈ (0, 1)` modulo `N` are at circular distance
exactly `d`, when `N ≥ 2`. -/
theorem dist_loopPos_eq_of_forward {N : ℕ+} (hN : (2 : ℝ) ≤ N) (X : Configuration N)
    (i j : Fin (N : ℕ)) {d : ℝ} (hd0 : 0 < d) (hd1 : d < 1) {k : ℤ}
    (hk : (N : ℝ) * X.val j = (N : ℝ) * X.val i + d + k * N) :
    dist (loopPos X i) (loopPos X j) = d := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hdN : d < N := by linarith
  have hsub : loopPos X i - loopPos X j = -((d : ℝ) : AddCircle (N : ℝ)) := by
    unfold loopPos
    rw [← QuotientAddGroup.mk_sub, ← QuotientAddGroup.mk_neg]
    refine (coe_eq_coe_iff_int _ _).mpr ⟨-k, ?_⟩
    push_cast
    linarith
  rw [dist_eq_norm, hsub, norm_neg, norm_coe_block hd0 hdN]
  exact min_eq_left (by linarith)

end Riesz1

end
end
