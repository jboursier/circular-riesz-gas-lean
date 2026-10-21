/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorOneMain
public import Riesz1.Variance.APrioriComplete

/-!
# The first Stein error

The first error bound in the proof of Theorem 3, every assertion, with only the Bakry–Émery
criterion `External.BakryEmery` and the Prékopa–Leindler inequality `External.PrekopaLeindler` as
hypotheses: the conditional `Riesz1.Internal.clt_error1_of_apriori` with its a priori input
discharged by `Riesz1.Internal.aPrioriConclusion_of_externals`.
-/

public section

namespace Riesz1

/-- **First error bound in the proof of Theorem 3.** For every positive loss `τ` there are
`C, K₀ > 0`, chosen after the fixed profile and before the scale sequence and `N`, such that
every admissible scale sequence and every `N` with `Nℓ_N ≥ K₀` satisfy
`Riesz1.Internal.ErrorOneConclusion`: both sup bounds, the variance bound for every lift of `q_N`,
and the `Error¹` bound for every bounded `C¹` test. -/
theorem clt_error1 (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ C K₀ : ℝ, 0 < C ∧ 0 < K₀ ∧
      ∀ ell : Scales, Admissible P p ell α d → ∀ N : ℕ+, K₀ ≤ (N : ℝ) * (ell N).val →
        Internal.ErrorOneConclusion hρ P p α τ C ell N :=
  Internal.clt_error1_of_apriori (Internal.aPrioriConclusion_of_externals hBE hPL) P p α d hρ τ hτ

end Riesz1
