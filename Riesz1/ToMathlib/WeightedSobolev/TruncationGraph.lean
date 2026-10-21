/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.CompositionLimits
public import Riesz1.ToMathlib.WeightedSobolev.ClipApproximation
public import Riesz1.ToMathlib.WeightedSobolev.TruncationConvergence

/-!
# Truncations in a closed first order graph

Smooth clipping and vanishing of the gradient on the two threshold
levels give graph membership with the strict-sublevel gradient formula.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Riesz1.WeightedSobolev.Internal

variable {Ω J E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure Ω} {P : J → Prop} {value : J → Ω → ℝ} {grad : J → Ω → E}

/-- Smooth composition and locality at the two thresholds imply exact truncation membership. -/
theorem graph_clip (hv : ∀ t, P t → MemLp (value t) 2 μ)
    (hg : ∀ t, P t → MemLp (grad t) 2 μ)
    {F : Ω → ℝ} {G : Ω → E} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (hcomp : ∀ (S : ℝ → ℝ), ContDiff ℝ ∞ S → S 0 = 0 →
      ∀ (K : ℝ≥0), (∀ r, ‖deriv S r‖₊ ≤ K) →
      IsGraphH1 μ P value grad (fun x => S (F x)) (fun x => deriv S (F x) • G x))
    {R : ℝ} (hR : 0 ≤ R)
    (hlevel1 : ∀ᵐ x ∂μ, F x = -R → G x = 0)
    (hlevel2 : ∀ᵐ x ∂μ, F x = R → G x = 0) :
    IsGraphH1 μ P value grad (fun x => clipReal R (F x)) ({x | |F x| < R}.indicator G) := by
  let S : ℕ → ℝ → ℝ := fun k => smoothClip R (1 / (k + 1))
  have hS k : ContDiff ℝ ∞ (S k) := contDiff_smoothClip R (by positivity)
  have hS0 k : S k 0 = 0 := smoothClip_zero _ _
  have hSb k r : ‖deriv (S k) r‖₊ ≤ 1 := norm_deriv_smoothClip_le R (by positivity) r
  apply graph_comp_approx hv hg hF hG (lipschitzWith_clipReal R)
    (clipReal_eq_of_abs_le (by simpa only [abs_zero] using hR)) hS hS0 hSb
    (fun k => hcomp (S k) (hS k) (hS0 k) 1 (hSb k))
    (tendsto_smoothClip hR) (memLp_truncatedGradient hF hG R)
  · exact Eventually.of_forall fun x => by
      simp only [NNReal.coe_one, one_mul]
      exact norm_indicator_le_norm_self _ _
  · filter_upwards [hlevel1, hlevel2] with x hx1 hx2
    by_cases hGx : G x = 0
    · simpa only [hGx, smul_zero, indicator_apply, ite_self] using
        (tendsto_const_nhds (x := (0 : E)) : Tendsto (fun _ : ℕ => (0 : E)) atTop (𝓝 0))
    · have ht := (tendsto_deriv_smoothClip hR (fun h => hGx (hx1 h))
        (fun h => hGx (hx2 h))).smul (tendsto_const_nhds (x := G x))
      simpa only [S, indicator_apply, mem_ofPred_eq, ite_smul, one_smul, zero_smul] using ht

end Riesz1.WeightedSobolev.Internal

end
