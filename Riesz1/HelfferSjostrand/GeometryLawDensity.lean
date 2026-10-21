/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GeometryHessian

/-!
# The Gibbs density depends only on the orthogonal projection `z`

Part of the proof of Lemma 3.6 (product law of `(z, ω)`): with
`e = N^{-1/2} (1, …, 1)` and `z = x - ⟪x, e⟫ e`, the pair Hamiltonian satisfies `H(x) = H(z)`.
Indeed `⟪x, e⟫ e` is a real multiple of the common-translation vector `(1, …, 1)`, and the
pair Hamiltonian is invariant under such translations. This file proves that identity, which is
the first step of the product law. The measure-theoretic factorization is not formalized here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Finset

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

/-- The orthogonal projection `z = x - ⟪x, e⟫ e` onto the complement of `e`. -/
def hsOrthProj (N : ℕ+) (x : HsEuclidean N) : HsEuclidean N :=
  x - (inner ℝ x (hsUnitVector N)) • hsUnitVector N

/-- The orthogonal projection is a common real translation of `x`, by `-⟪x, e⟫ / √N`. -/
theorem hsOrthProj_eq_translate (N : ℕ+) (x : HsEuclidean N) :
    hsOrthProj N x = hsTranslate (-(inner ℝ x (hsUnitVector N) / Real.sqrt (N : ℕ))) x := by
  ext i
  simp only [hsOrthProj, hsUnitVector, hsRotationVector, hsTranslate_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

/-- The pair Hamiltonian is unchanged by the orthogonal projection: `H(x) = H(z)`. -/
theorem hsPairExpression_orthProj (χ : HsPairPotentials N c) (x : HsEuclidean N) :
    hsPairExpression χ (hsOrthProj N x) = hsPairExpression χ x := by
  rw [hsOrthProj_eq_translate, hsPairExpression_translate]

end Riesz1

end
