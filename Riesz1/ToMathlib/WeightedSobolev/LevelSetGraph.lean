/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.CompositionLimits
public import Riesz1.ToMathlib.WeightedSobolev.LevelMaps
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Level sets in a closed first order graph

Smooth flattening maps show that the jet with zero value and gradient
restricted to an individual level belongs to the graph. Closability
then forces that restricted gradient to vanish.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Riesz1.WeightedSobolev.Internal

variable {Ω J E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure Ω} {P : J → Prop} {value : J → Ω → ℝ} {grad : J → Ω → E}

/-- Level-set gradients give vertical jets in any graph stable under smooth scalar composition. -/
theorem graph_levelSet (hv : ∀ t, P t → MemLp (value t) 2 μ)
    (hg : ∀ t, P t → MemLp (grad t) 2 μ)
    {F : Ω → ℝ} {G : Ω → E} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (hcomp : ∀ (S : ℝ → ℝ), ContDiff ℝ ∞ S → S 0 = 0 →
      ∀ (K : ℝ≥0), (∀ r, ‖deriv S r‖₊ ≤ K) →
      IsGraphH1 μ P value grad (fun x => S (F x)) (fun x => deriv S (F x) • G x))
    (a : ℝ) : IsGraphH1 μ P value grad (fun _ => 0) ({x | F x = a}.indicator G) := by
  let S : ℕ → ℝ → ℝ := fun k => levelMap a (1 / (k + 1)) (by positivity)
  have hS k : ContDiff ℝ ∞ (S k) := contDiff_levelMap _ (by positivity)
  have hS0 k : S k 0 = 0 := levelMap_zero _ (by positivity)
  have hSb k r : ‖deriv (S k) r‖₊ ≤ 1 := norm_deriv_levelMap_le a (by positivity) r
  have hD : MemLp ({x | F x = a}.indicator G) 2 μ :=
    hG.indicator (nullMeasurableSet_eq_fun hF.aestronglyMeasurable.aemeasurable aemeasurable_const)
  apply graph_comp_approx hv hg hF hG
    (LipschitzWith.const' (K := 1) (0 : ℝ)) rfl hS hS0 hSb
    (fun k => hcomp (S k) (hS k) (hS0 k) 1 (hSb k))
    (tendsto_levelMap a) hD
  · exact Eventually.of_forall fun x => by
      simp only [NNReal.coe_one, one_mul]
      exact norm_indicator_le_norm_self _ _
  · exact Eventually.of_forall fun x => by
      have ht := (tendsto_deriv_levelMap a (F x)).smul (tendsto_const_nhds (x := G x))
      simpa only [S, indicator_apply, mem_ofPred_eq, ite_smul, one_smul, zero_smul] using ht

end Riesz1.WeightedSobolev.Internal

end
