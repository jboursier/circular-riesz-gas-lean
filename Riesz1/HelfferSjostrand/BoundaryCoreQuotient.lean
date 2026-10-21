/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreShift

/-!
# Scalar boundary core on the cyclic quotient

The real quotient assertions of the scalar boundary core theorem, on the actual
source domain and the variational Neumann operator. The anchored
assertions are separate and are not claimed in this module.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- For an admissible Hamiltonian, the scalar source operator on `𝒟_N`
is essentially self-adjoint, its closure is the variational Neumann
operator, and the source tests form both an operator core and a form core.
This is the real quotient component of the scalar boundary core theorem. -/
theorem scalar_boundary_core_L3219_quotient_real {N : ℕ+} {c C_N : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) (hadm : HsAdmissible χ C_N) :
    (hsTestL2Operator χ hc).closure = hsNeumannL2Operator χ hc ∧
      IsSelfAdjoint (hsTestL2Operator χ hc).closure ∧
      (hsNeumannL2Operator χ hc).HasCore
        (hsTestL2Domain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) ∧
      Dense (hsSourceTestSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) :
        Set (HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))) := by
  have hC : 0 ≤ C_N := hadm.choose_spec.2.1
  exact Internal.scalar_boundary_core_of_shift_kernel hadm.choose χ hc
    (lam := C_N + 1) (by linarith)
    (fun u hu => Internal.scalar_boundary_shift_kernel χ hc hadm (by linarith) u hu)

end Riesz1
