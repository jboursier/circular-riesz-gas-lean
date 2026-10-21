/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Nonnegative coordinates give a nonnegative `L²` pairing

For two `L²` fields with values in `ℝ^n`, the pairing `⟪f, g⟫ = ∫ ⟪f, g⟫ dμ` is nonnegative when
every coordinate of `f` and of `g` is nonnegative almost everywhere. This is the pointwise
positivity used in the monotonicity argument of Lemma 3.4.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

variable {α : Type*} [MeasurableSpace α] {n : ℕ} {μ : Measure α}

/-- Two `L²` fields with almost everywhere nonnegative coordinates have a nonnegative inner
product. The pointwise inner product is the sum of the products of the coordinates. -/
theorem lp_euclidean_inner_nonneg_of_coords (f g : Lp (EuclideanSpace ℝ (Fin n)) 2 μ)
    (hf : ∀ i : Fin n, ∀ᵐ y ∂μ, 0 ≤ f y i) (hg : ∀ i : Fin n, ∀ᵐ y ∂μ, 0 ≤ g y i) :
    0 ≤ inner ℝ f g := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  rw [← ae_all_iff] at hf hg
  filter_upwards [hf, hg] with y h1 h2
  rw [PiLp.inner_apply]
  exact Finset.sum_nonneg fun i _ => by
    simpa using mul_nonneg (h2 i) (h1 i)

end Riesz1

end
