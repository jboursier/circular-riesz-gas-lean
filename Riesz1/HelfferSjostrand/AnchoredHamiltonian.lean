/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SettingHamiltonian
public import Riesz1.Gibbs.AnchoredCoordinates

/-!
# The anchored Hamiltonian `H*(y) = H(0, y)`

For `N = n + 1` particles, `H*(y)` is the pair expression of the anchored
lift `(0, y_1, …, y_n)`, with `y` in the anchored domain `D_N^* = anchoredDomain n`.

The pair potentials are regular only on `(0, 1)`. On `D_N^*` every pair separation lies in
`(0, 1)`, so `H*` is continuous there, and the Hamiltonian of the fundamental region factors through
the anchored coordinates `(X_0, (X_{j+1} - X_0)_j)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The anchored Hamiltonian `H*(y) = H(0, y)`: the pair expression at the lift with first
coordinate zero and remaining coordinates `y`. -/
def hsAnchoredHamiltonian (χ : HsPairPotentials n.succPNat c) (y : Fin n → ℝ) : ℝ :=
  hsPairExpression χ (WithLp.toLp 2 (anchorVector y))

/-- The anchored lift is strictly increasing on the anchored domain. -/
theorem anchorVector_strictMono {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n) :
    StrictMono (anchorVector y) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact absurd hij (lt_irrefl _)
    | succ l =>
      show anchorVector y 0 < anchorVector y l.succ
      rw [anchorVector_zero, anchorVector_succ]
      exact (hy.1 l).1
  | succ k =>
    induction j using Fin.cases with
    | zero => exact (Fin.not_lt_zero _ hij).elim
    | succ l =>
      rw [anchorVector_succ, anchorVector_succ]
      exact hy.2 (Fin.succ_lt_succ_iff.mp hij)

/-- Every pair separation of the anchored lift lies in `(0, 1)`. -/
theorem anchorVector_sub_mem_Ioo {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n)
    {i j : Fin (n.succPNat : ℕ)} (hij : i < j) :
    anchorVector y j - anchorVector y i ∈ Ioo (0 : ℝ) 1 := by
  have hi := anchorVector_mem_Ico hy i
  have hj := anchorVector_mem_Ico hy j
  exact ⟨sub_pos.mpr (anchorVector_strictMono hy hij), by linarith [hi.1, hj.2]⟩

/-- Each coordinate of the anchored lift depends continuously on `y`. -/
theorem continuous_anchorVector_apply (k : Fin (n.succPNat : ℕ)) :
    Continuous (fun y : Fin n → ℝ => anchorVector y k) := by
  induction k using Fin.cases with
  | zero =>
    show Continuous fun y : Fin n → ℝ => anchorVector y 0
    simp only [anchorVector_zero]
    exact continuous_const
  | succ l =>
    simp only [anchorVector_succ]
    exact continuous_apply l

/-- The anchored Hamiltonian is continuous on the anchored domain. The pair potentials are
continuous on `(0, 1)`, and the pair separations stay in `(0, 1)` there. -/
theorem continuousOn_hsAnchoredHamiltonian (χ : HsPairPotentials n.succPNat c) :
    ContinuousOn (hsAnchoredHamiltonian χ) (anchoredDomain n) := by
  unfold hsAnchoredHamiltonian hsPairExpression
  apply ContinuousOn.mul continuousOn_const
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j hj
  have hij : i < j := (Finset.mem_filter.mp hj).2
  have hcont : Continuous (fun y : Fin n → ℝ => anchorVector y j - anchorVector y i) :=
    (continuous_anchorVector_apply j).sub (continuous_anchorVector_apply i)
  exact (χ.smooth i j hij).continuousOn.comp hcont.continuousOn
    (fun y hy => anchorVector_sub_mem_Ioo hy hij)

/-- The Hamiltonian of the fundamental region depends only on the anchored gap vector: the
configuration is a common translate of the anchored lift, and the pair expression is translation
invariant. -/
theorem hsFundamentalHamiltonian_eq_anchored (χ : HsPairPotentials n.succPNat c)
    (X : Configuration n.succPNat) :
    hsFundamentalHamiltonian χ X = hsAnchoredHamiltonian χ (anchorCoords n X.val).2 := by
  unfold hsFundamentalHamiltonian hsAnchoredHamiltonian
  have hX : WithLp.toLp 2 X.val =
      hsTranslate (X.val 0) (WithLp.toLp 2 (anchorVector (anchorCoords n X.val).2)) := by
    ext i
    change X.val i = anchorVector (anchorCoords n X.val).2 i + X.val 0
    rw [apply_eq_anchor_add n X.val i]
    ring
  rw [hX, hsPairExpression_translate]

end Riesz1

end
end
