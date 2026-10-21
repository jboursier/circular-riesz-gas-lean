/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# A local dominated criterion for a continuously differentiable integral

The parameter domain is open. The derivative is dominated by one integrable
function on that domain and is continuous there almost everywhere in the
integration variable. This gives `C¹` regularity, including
continuity of the derivative.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

theorem contDiffOn_integral_one_of_dominated {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {U : Set ℝ} (hU : IsOpen U) {F F' : ℝ → Ω → ℝ}
    {b : Ω → ℝ}
    (hi : ∀ x ∈ U, Integrable (F x) μ)
    (hm : ∀ x ∈ U, AEStronglyMeasurable (F' x) μ)
    (hb : ∀ᵐ a ∂μ, ∀ x ∈ U, ‖F' x a‖ ≤ b a)
    (hbi : Integrable b μ)
    (hd : ∀ᵐ a ∂μ, ∀ x ∈ U, HasDerivAt (fun t => F t a) (F' x a) x)
    (hc : ∀ᵐ a ∂μ, ContinuousOn (fun x => F' x a) U) :
    ContDiffOn ℝ 1 (fun x => ∫ a, F x a ∂μ) U := by
  have hder (x : ℝ) (hx : x ∈ U) :
      HasDerivAt (fun t => ∫ a, F t a ∂μ) (∫ a, F' x a ∂μ) x := by
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (hU.mem_nhds hx)
      (by filter_upwards [hU.mem_nhds hx] with t ht; exact (hi t ht).aestronglyMeasurable)
      (hi x hx) (hm x hx) hb hbi hd).2
  rw [show (1 : ℕ∞ω) = 0+1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hU]
  refine ⟨fun x hx => (hder x hx).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  apply (continuousOn_of_dominated hm ?_ hbi hc).congr
  · intro x hx
    exact (hder x hx).deriv
  · intro x hx
    exact hb.mono (fun a ha => ha x hx)

end Riesz1
