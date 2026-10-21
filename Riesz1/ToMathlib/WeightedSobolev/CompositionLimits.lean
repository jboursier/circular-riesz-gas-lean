/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.GraphLimits
public import Riesz1.ToMathlib.WeightedSobolev.ScalarApproximation
public import Riesz1.ToMathlib.WeightedSobolev.SmoothComposition

/-!
# Passage from smooth scalar composition to strong graph limits

The internal limit theorem keeps the approximation hypotheses separate
from the chain rules.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff NNReal

namespace Riesz1.WeightedSobolev.Internal

variable {Ω J E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure Ω} {P : J → Prop} {value : J → Ω → ℝ} {grad : J → Ω → E}

/-- Strong graph limit of scalar compositions with a common derivative bound. -/
theorem graph_comp_approx (hv : ∀ t, P t → MemLp (value t) 2 μ)
    (hg : ∀ t, P t → MemLp (grad t) 2 μ)
    {F : Ω → ℝ} {G D : Ω → E} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    {T : ℝ → ℝ} {C : ℝ≥0} (hT : LipschitzWith C T) (h0 : T 0 = 0)
    {S : ℕ → ℝ → ℝ} (hS : ∀ k, ContDiff ℝ ∞ (S k)) (hS0 : ∀ k, S k 0 = 0)
    (hb : ∀ k r, ‖deriv (S k) r‖₊ ≤ C)
    (hm : ∀ k, IsGraphH1 μ P value grad (fun x => S k (F x))
      (fun x => deriv (S k) (F x) • G x))
    (hvl : ∀ r, Tendsto (fun k => S k r) atTop (𝓝 (T r)))
    (hD : MemLp D 2 μ) (hDb : ∀ᵐ x ∂μ, ‖D x‖ ≤ (C : ℝ) * ‖G x‖)
    (hdl : ∀ᵐ x ∂μ, Tendsto (fun k => deriv (S k) (F x) • G x) atTop (𝓝 (D x))) :
    IsGraphH1 μ P value grad (fun x => T (F x)) D := by
  have hTF := hT.comp_memLp h0 hF
  apply graph_closed_limit hv hg hm hTF hD
  · apply tendsto_toLp_of_dominated (fun k => (hm k).1) hTF
      (hF.norm.const_smul (C : ℝ))
    · intro k
      exact Eventually.of_forall fun x => by
        simpa only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, hS0 k, sub_zero, dist_zero_right] using
          (lipschitzWith_of_nnnorm_deriv_le ((hS k).differentiable (by norm_num))
            (hb k)).dist_le_mul (F x) 0
    · exact Eventually.of_forall fun x => by
        simpa only [Function.comp_def, Pi.smul_apply, smul_eq_mul, h0, sub_zero, dist_zero_right, Real.norm_eq_abs] using hT.dist_le_mul (F x) 0
    · exact Eventually.of_forall fun x => hvl (F x)
  · apply tendsto_toLp_of_dominated (fun k => (hm k).2.1) hD
      (hG.norm.const_smul (C : ℝ))
    · intro k
      exact Eventually.of_forall fun x => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hb k (F x) : ‖deriv (S k) (F x)‖ ≤ (C : ℝ))
          (norm_nonneg _)
    · exact hDb
    · exact hdl

/-- The `C¹` chain rule follows from stability under smooth composition. -/
theorem graph_comp_C1 (hv : ∀ t, P t → MemLp (value t) 2 μ)
    (hg : ∀ t, P t → MemLp (grad t) 2 μ)
    {F : Ω → ℝ} {G : Ω → E} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (hcomp : ∀ (S : ℝ → ℝ), ContDiff ℝ ∞ S → S 0 = 0 →
      ∀ (K : ℝ≥0), (∀ r, ‖deriv S r‖₊ ≤ K) →
      IsGraphH1 μ P value grad (fun x => S (F x)) (fun x => deriv S (F x) • G x))
    {T : ℝ → ℝ} (hT : ContDiff ℝ 1 T) (h0 : T 0 = 0) {C : ℝ≥0}
    (hb : ∀ r, ‖deriv T r‖₊ ≤ C) :
    IsGraphH1 μ P value grad (fun x => T (F x)) (fun x => deriv T (F x) • G x) := by
  obtain ⟨S, hS, hS0, hSb, hSv, hSd⟩ := exists_smooth_approximation_C1 hT h0
    (fun r => (hb r : ‖deriv T r‖ ≤ (C : ℝ)))
  have hSb' k r : ‖deriv (S k) r‖₊ ≤ 3 * C := hSb k r
  have hLip0 : LipschitzWith C T :=
    lipschitzWith_of_nnnorm_deriv_le (hT.differentiable (by norm_num)) hb
  have hLip : LipschitzWith (3 * C) T := hLip0.weaken
    (le_mul_of_one_le_left (show (0 : ℝ≥0) ≤ C from zero_le) (by norm_num))
  apply graph_comp_approx hv hg hF hG hLip h0 hS hS0 hSb'
    (fun k => hcomp (S k) (hS k) (hS0 k) (3 * C) (hSb' k)) hSv
    (memLp_bounded_comp_smul hT.continuous_deriv_one
      (fun r => (hb r : ‖deriv T r‖ ≤ (C : ℝ))) hF.aestronglyMeasurable hG)
  · exact Eventually.of_forall fun x => by
      rw [norm_smul]
      have hbr : ‖deriv T (F x)‖ ≤ (C : ℝ) := hb (F x)
      have hh := mul_le_mul_of_nonneg_right hbr (norm_nonneg (G x))
      have hn : 0 ≤ (C : ℝ) * ‖G x‖ := by positivity
      change _ ≤ (3 * (C : ℝ)) * ‖G x‖
      nlinarith
  · exact Eventually.of_forall fun x => (hSd (F x)).smul tendsto_const_nhds

end Riesz1.WeightedSobolev.Internal

end
