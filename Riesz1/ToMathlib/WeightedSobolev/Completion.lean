/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Weighted Sobolev membership on a set

For a measure `μ` on a real inner product space `E` and a set `U ⊆ E`, the space `H¹(μ)` is
the completion of the smooth functions on a neighborhood of `closure U` for the
norm `‖f‖² = ∫ (f² + ‖∇f‖²) dμ`. This file encodes the completion as the closure of the graph
`{(f, ∇f)}` in `L²(μ) × L²(μ; E)`: a pair `(F, G)` is a point of the completion exactly when
`F ∈ L²(μ)`, `G ∈ L²(μ; E)`, and there are approximating smooth functions whose values and
gradients converge to `F` and `G` in `L²(μ)`. The vector field `G` is then the weak gradient of `F`.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace Riesz1.WeightedSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E]

/-- The function `f` is smooth on some open set containing `closure U`. -/
@[expose]
def SmoothNearClosure (U : Set E) (f : E → ℝ) : Prop :=
  ∃ W : Set E, IsOpen W ∧ closure U ⊆ W ∧ ContDiffOn ℝ ∞ f W

/-- The pair `(F, G)` lies in the completion `H¹(μ)` of the smooth functions on a neighborhood
of `closure U`, with `G` the weak gradient of `F`. This is the closure of the graph of the
gradient in `L²(μ) × L²(μ; E)`: there is a sequence of smooth functions `φ k` whose values and
gradients converge to `F` and `G` in `L²(μ)`. -/
@[expose]
def IsWeightedH1 (μ : Measure E) (U : Set E) (F : E → ℝ) (G : E → E) : Prop :=
  MemLp F 2 μ ∧ MemLp G 2 μ ∧
    ∃ φ : ℕ → E → ℝ, (∀ k, SmoothNearClosure U (φ k)) ∧
      Tendsto (fun k => ∫⁻ x, ‖φ k x - F x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫⁻ x, ‖gradient (φ k) x - G x‖ₑ ^ 2 ∂μ) atTop (𝓝 0)

namespace IsWeightedH1

variable {μ : Measure E} {U : Set E} {F : E → ℝ} {G : E → E}

/-- The function component of a point of `H¹(μ)` lies in `L²(μ)`. -/
theorem memLp_fun (h : IsWeightedH1 μ U F G) : MemLp F 2 μ :=
  h.1

/-- The gradient component of a point of `H¹(μ)` lies in `L²(μ; E)`. -/
theorem memLp_grad (h : IsWeightedH1 μ U F G) : MemLp G 2 μ :=
  h.2.1

end IsWeightedH1

end Riesz1.WeightedSobolev

end
