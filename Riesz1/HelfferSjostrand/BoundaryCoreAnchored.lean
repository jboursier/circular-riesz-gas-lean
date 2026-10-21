/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreAnchoredCriterion
public import Riesz1.HelfferSjostrand.BoundaryCoreAnchoredShift

/-!
# The real anchored scalar boundary core

The anchored assertions of the scalar boundary core, on the test
submodule, Sobolev completion, and variational Neumann operator.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- For every admissible anchored Hamiltonian, the scalar operator on the
test functions is essentially self-adjoint, its closure is the actual Neumann operator,
and its test functions are both an operator core and a form core.
This is the real anchored component of the scalar boundary core. -/
theorem scalar_boundary_core_L3219_anchored_real {n : ℕ} {c C_N : ℝ}
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) (hadm : HsAdmissible χ C_N) :
    (anchoredTestL2Operator χ hc).closure = anchoredNeumannL2Operator χ hc ∧
      IsSelfAdjoint (anchoredTestL2Operator χ hc).closure ∧
      (anchoredNeumannL2Operator χ hc).HasCore (anchoredTestL2Domain χ hc) ∧
      Dense (anchoredSourceTestSobolev χ hc : Set (PoissonAnchoredSpace χ hc)) := by
  have hC : 0 ≤ C_N := hadm.choose_spec.2.1
  exact Internal.anchored_boundary_core_of_shift_kernel χ hc (lam := C_N + 1) (by linarith)
    (fun u hu => Internal.anchored_boundary_shift_kernel χ hc hadm (by linarith) u hu)

end Riesz1
