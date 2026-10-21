/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.BoundedMultiplier

/-!
# Strong limits in a completed first order graph

Dominated pointwise convergence gives strong `L²` convergence, and the
closure of the finite-norm smooth jets is stable under strong limits.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set

namespace Riesz1.WeightedSobolev

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  {μ : Measure Ω}

/-- A common `L²` majorant turns almost everywhere convergence into strong `L²` convergence. -/
theorem tendsto_toLp_of_dominated {f : ℕ → Ω → E} {F : Ω → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hF : MemLp F 2 μ)
    {b : Ω → ℝ} (hb : MemLp b 2 μ)
    (hfb : ∀ k, ∀ᵐ x ∂μ, ‖f k x‖ ≤ b x) (hFb : ∀ᵐ x ∂μ, ‖F x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (F x))) :
    Tendsto (fun k => (hf k).toLp (f k)) atTop (𝓝 (hF.toLp F)) := by
  apply (tendsto_toLp_iff_lintegral_sq f hf F hF).mpr
  have hi : Integrable (fun x => 4 * ‖b x‖ ^ 2) μ := hb.norm.integrable_sq.const_mul 4
  have hl : ∀ᵐ x ∂μ, Tendsto (fun k => ‖f k x - F x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (hx.sub (tendsto_const_nhds (x := F x))).norm.pow 2
  have ht := tendsto_integral_of_dominated_convergence (fun x => 4 * ‖b x‖ ^ 2)
    (fun k => ((hf k).sub hF).aestronglyMeasurable.norm.pow 2) hi
    (fun k => ?_) hl
  · have he k : (∫⁻ x, ‖f k x - F x‖ₑ ^ 2 ∂μ) =
        ENNReal.ofReal (∫ x, ‖f k x - F x‖ ^ 2 ∂μ) := by
      change (∫⁻ x, ‖(f k - F) x‖ₑ ^ 2 ∂μ) =
        ENNReal.ofReal (∫ x, ‖(f k - F) x‖ ^ 2 ∂μ)
      rw [ofReal_integral_eq_lintegral_ofReal ((hf k).sub hF).norm.integrable_sq
        (Eventually.of_forall fun x => sq_nonneg _)]
      exact lintegral_congr fun x => enorm_sq_eq_ofReal_norm_sq _
    simp only [he]
    simpa only [Pi.pow_apply, Pi.sub_apply, integral_zero, Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  · filter_upwards [hfb k, hFb] with x hx hy
    have hbn : 0 ≤ b x := (norm_nonneg _).trans hy
    have he : ‖f k x - F x‖ ≤ 2 * b x := (norm_sub_le _ _).trans (by linarith)
    change ‖‖f k x - F x‖ ^ 2‖ ≤ 4 * ‖b x‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg hbn]
    nlinarith [mul_self_le_mul_self (norm_nonneg (f k x - F x)) he]

namespace Internal

variable {J : Type*} {P : J → Prop} {value : J → Ω → ℝ} {grad : J → Ω → E}

/-- Closedness of the completed graph under strong convergence of both components. -/
theorem graph_closed_limit (hv : ∀ t, P t → MemLp (value t) 2 μ)
    (hg : ∀ t, P t → MemLp (grad t) 2 μ)
    {f : ℕ → Ω → ℝ} {g : ℕ → Ω → E} {F : Ω → ℝ} {G : Ω → E}
    (hfg : ∀ k, IsGraphH1 μ P value grad (f k) (g k))
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (hf : Tendsto (fun k => (hfg k).1.toLp (f k)) atTop (𝓝 (hF.toLp F)))
    (hgl : Tendsto (fun k => (hfg k).2.1.toLp (g k)) atTop (𝓝 (hG.toLp G))) :
    IsGraphH1 μ P value grad F G := by
  apply (isGraphH1_iff_mem_closure hv hg F G hF hG).mpr
  apply isClosed_closure.mem_of_tendsto
    ((WithLp.prod_continuous_toLp 2 (Lp ℝ 2 μ) (Lp E 2 μ)).tendsto
      (hF.toLp F, hG.toLp G) |>.comp (hf.prodMk_nhds hgl))
  exact Eventually.of_forall fun k =>
    (isGraphH1_iff_mem_closure hv hg (f k) (g k) (hfg k).1 (hfg k).2.1).mp (hfg k)

end Internal

end Riesz1.WeightedSobolev

end
