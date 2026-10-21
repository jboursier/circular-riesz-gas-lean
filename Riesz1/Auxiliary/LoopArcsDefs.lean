/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopMomentsDefs
public import Riesz1.Auxiliary.GradientSplittingKernel

/-!
# Microscopic loop functional and arc-crossing representation

It covers the microscopic kernel, discrepancy and loop, and the arc-crossing representation.
Let `0 < s < 1`, let `N ≥ 1` be an integer and let `X` be a configuration.
The lifts `z_i = N x_i ∈ [0, N)` of the microscopic positions are `loopArcPos`, and
`ν = ∑ᵢ δ_{z_i} - dz` on `N𝕋` is encoded by the lifts and the Lebesgue integral over `[0, N]`.
This file defines

* the kernel `g_N(r) = N^{-s} g(r / N)` (`loopArcG`) and the pair kernel
  `(b(z) - b(u)) g_N'(z - u)` (`loopArcKernel`),
* the loop functional `L(b)` (`loopArcL`), expanded into its empirical and background terms,
  with the atomic diagonal omitted,
* the cutoff `Q` (`loopArcQ`) and the function `Λ` (`loopArcLambda`), where the arc
  discrepancies `A_t(u) = ν((t - u, t))` and `B_t(v) = ν((t, t + v))` are the
  `loopDiscrepancy`.

The definitions are total. `Λ(t)` is the formula of the paper at every real `t`, and
the carrier (the complement of the particle positions) is recorded in the
lemmas that use it, since the particle positions form a finite set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set

namespace Riesz1

/-- The microscopic kernel `g_N(r) = N^{-s} g(r / N)`, for the kernel
`g = hurwitzKernel s`. -/
noncomputable def loopArcG (s : ℝ) (N : ℕ+) (r : ℝ) : ℝ :=
  (N : ℝ) ^ (-s) * hurwitzKernel s (r / N)

/-- The microscopic pair kernel `(b(z) - b(u)) g_N'(z - u)`, for a
real function `b` on the lifted circle. -/
noncomputable def loopArcKernel (s : ℝ) (N : ℕ+) (b : ℝ → ℝ) (z u : ℝ) : ℝ :=
  (b z - b u) * deriv (loopArcG s N) (z - u)

/-- The real lift `z_i = N x_i ∈ [0, N)` of the microscopic position of particle `i`. -/
noncomputable def loopArcPos (N : ℕ+) (X : Configuration N) (i : Fin (N : ℕ)) : ℝ :=
  (N : ℝ) * X.val i

/-- The loop functional `L(b)`, that is the double integral of the pair
kernel against `ν ⊗ ν` with `ν = ∑ᵢ δ_{z_i} - dz` on `[0, N)`. The integral is written as its
empirical and background terms: the particle-particle sum over `j ≠ i`, the two
particle-background integrals and the background-background integral. -/
noncomputable def loopArcL (s : ℝ) (N : ℕ+) (b : ℝ → ℝ) (X : Configuration N) : ℝ :=
  (∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
      if j = i then 0 else loopArcKernel s N b (loopArcPos N X i) (loopArcPos N X j))
    - (∑ i : Fin (N : ℕ), ∫ u in (0 : ℝ)..(N : ℝ), loopArcKernel s N b (loopArcPos N X i) u)
    - (∑ j : Fin (N : ℕ), ∫ z in (0 : ℝ)..(N : ℝ), loopArcKernel s N b z (loopArcPos N X j))
    + ∫ z in (0 : ℝ)..(N : ℝ), ∫ u in (0 : ℝ)..(N : ℝ), loopArcKernel s N b z u

/-- The cutoff `Q`: `Q(r) = -g_N'(r)` for `r < N / 2` and `Q(r) = 0` for
`r ≥ N / 2`. The paper defines `Q` on `(0, ∞)`. Its values at `r ≤ 0` are never used. -/
noncomputable def loopArcQ (s : ℝ) (N : ℕ+) (r : ℝ) : ℝ :=
  if r < (N : ℝ) / 2 then -deriv (loopArcG s N) r else 0

/-- The function `Λ`, at a real point `t`:
`Λ(t) = ∬_{u,v > 0, u + v < N/2} -g_N'''(u + v) A_t(u) B_t(v) + g_N''(N/2) ∫₀^{N/2} A_t(u) B_t(N/2 - u)`,
where `A_t(u) = ν((t - u, t))` and `B_t(v) = ν((t, t + v))` are the arc discrepancies
`loopDiscrepancy`. The double integral is iterated: `v` runs over `(0, N/2 - u)`. -/
noncomputable def loopArcLambda (s : ℝ) (N : ℕ+) (X : Configuration N) (t : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..((N : ℝ) / 2), ∫ v in (0 : ℝ)..((N : ℝ) / 2 - u),
      -iteratedDeriv 3 (loopArcG s N) (u + v) * loopDiscrepancy (t - u) u X
        * loopDiscrepancy t v X)
    + iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)
      * ∫ u in (0 : ℝ)..((N : ℝ) / 2),
          loopDiscrepancy (t - u) u X * loopDiscrepancy t ((N : ℝ) / 2 - u) X

end Riesz1

end
end
