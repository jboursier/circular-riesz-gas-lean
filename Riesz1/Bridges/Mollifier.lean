/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.Basic
public import Riesz1.ToMathlib.Mollifier.Multiplier

/-!
# Bridge: the two mollifier predicates

The hypothesis `ρ ∈ C_c^∞((-1/2, 1/2))` is `IsMollifier` (with `tsupport`). The predicate
`IsCircleMollifier` (with `Function.support`) is weaker. This file proves that `IsMollifier` implies
`IsCircleMollifier`, so that a lemma assuming only `IsCircleMollifier` applies to every
mollifier. The converse fails, for example for `exp(-1/(1 - 4x²))` on `(-1/2, 1/2)` extended by
zero, whose support is the open interval. This remark is not formalized here.

Main result: `IsMollifier.isCircleMollifier`.
-/

public section

namespace Riesz1

/-- A mollifier `ρ` (`IsMollifier`) is a circle mollifier (`IsCircleMollifier`). The
support of `ρ` lies in its topological support, which lies in `(-1/2, 1/2)`. The other four
conditions are the same. -/
theorem IsMollifier.isCircleMollifier {ρ : ℝ → ℝ} (h : IsMollifier ρ) : IsCircleMollifier ρ :=
  ⟨h.1, h.2.2.1, h.2.1, (subset_tsupport ρ).trans h.2.2.2.1, h.2.2.2.2⟩

end Riesz1

end
