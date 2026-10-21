/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.CompositionLimits
public import Riesz1.ToMathlib.WeightedSobolev.PiecewiseScalarApproximation

/-!
# Finitely piecewise C¹ composition in a closed graph

The exceptional scalar values are handled by level-set vanishing. The
derivative approximation is needed only away from these values.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Riesz1.WeightedSobolev.Internal

variable {Ω J E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure Ω} {P : J → Prop} {value : J → Ω → ℝ} {grad : J → Ω → E}

/-- The finitely piecewise `C¹` Lipschitz chain rule, from smooth composition and level locality. -/
theorem graph_comp_piecewise (hv : ∀ t, P t → MemLp (value t) 2 μ)
    (hg : ∀ t, P t → MemLp (grad t) 2 μ)
    {F : Ω → ℝ} {G : Ω → E} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (hcomp : ∀ (S : ℝ → ℝ), ContDiff ℝ ∞ S → S 0 = 0 →
      ∀ (K : ℝ≥0), (∀ r, ‖deriv S r‖₊ ≤ K) →
      IsGraphH1 μ P value grad (fun x => S (F x)) (fun x => deriv S (F x) • G x))
    {T : ℝ → ℝ} {C : ℝ≥0} (hT : LipschitzWith C T) (h0 : T 0 = 0)
    {B : Set ℝ} (hB : B.Finite) (hTC : ContDiffOn ℝ 1 T Bᶜ)
    (hlevel : ∀ a ∈ B, ∀ᵐ x ∂μ, F x = a → G x = 0) :
    IsGraphH1 μ P value grad (fun x => T (F x)) (fun x => deriv T (F x) • G x) := by
  obtain ⟨S, hS, hS0, hSb, hSv, hSd⟩ := exists_smooth_approximation_piecewise hT h0 hB hTC
  have hSb' k r : ‖deriv (S k) r‖₊ ≤ 3 * C := hSb k r
  have hLip : LipschitzWith (3 * C) T := hT.weaken
    (le_mul_of_one_le_left (show (0 : ℝ≥0) ≤ C from zero_le) (by norm_num))
  have hd : AEStronglyMeasurable (fun x => deriv T (F x)) μ :=
    ((measurable_deriv T).comp_aemeasurable hF.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hb r : ‖deriv T r‖ ≤ (C : ℝ) := norm_deriv_le_of_lipschitz hT
  have hD : MemLp (fun x => deriv T (F x) • G x) 2 μ :=
    hG.of_le_mul (hd.smul hG.aestronglyMeasurable) (Eventually.of_forall fun x => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))
  apply graph_comp_approx hv hg hF hG hLip h0 hS hS0 hSb'
    (fun k => hcomp (S k) (hS k) (hS0 k) (3 * C) (hSb' k)) hSv hD
  · exact Eventually.of_forall fun x => by
      rw [norm_smul]
      have hh := mul_le_mul_of_nonneg_right (hb (F x)) (norm_nonneg (G x))
      change _ ≤ (3 * (C : ℝ)) * ‖G x‖
      have hn : 0 ≤ (C : ℝ) * ‖G x‖ := by positivity
      nlinarith
  · filter_upwards [(ae_ball_iff hB.countable).mpr hlevel] with x hx
    by_cases hFx : F x ∈ B
    · have hGx := hx (F x) hFx rfl
      simp only [hGx, smul_zero]
      exact tendsto_const_nhds
    · exact (hSd (F x) hFx).smul tendsto_const_nhds

end Riesz1.WeightedSobolev.Internal

end
