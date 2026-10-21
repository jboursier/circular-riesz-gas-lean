/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.Graph
public import Riesz1.ToMathlib.WeightedSobolev.L2Facts
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded continuous multipliers on convergent Sobolev jets

The nonlinear gradient limit needed for smooth composition: a bounded
continuous scalar coefficient converging pointwise can multiply a strongly
convergent sequence of square integrable vector fields.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace Riesz1.WeightedSobolev

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure Ω} {d : ℝ → ℝ} {C : ℝ}

/-- A bounded measurable scalar coefficient preserves square integrability. -/
theorem memLp_bounded_comp_smul (hd : Continuous d) (hb : ∀ r, ‖d r‖ ≤ C)
    {F : Ω → ℝ} (hF : AEStronglyMeasurable F μ) {G : Ω → E} (hG : MemLp G 2 μ) :
    MemLp (fun x => d (F x) • G x) 2 μ := by
  apply hG.of_le_mul (c := C) ((hd.comp_aestronglyMeasurable hF).smul hG.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖d (F x) • G x‖ ≤ C * ‖G x‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)

/-- For a fixed `L²` field, bounded pointwise multiplier convergence gives `L²` convergence. -/
theorem tendsto_bounded_comp_smul_fixed (hd : Continuous d) (hb : ∀ r, ‖d r‖ ≤ C)
    {F : Ω → ℝ} {f : ℕ → Ω → ℝ}
    (hF : AEStronglyMeasurable F μ) (hf : ∀ k, AEStronglyMeasurable (f k) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (F x)))
    {G : Ω → E} (hG : MemLp G 2 μ) :
    Tendsto (fun k => ∫⁻ x, ‖d (f k x) • G x - d (F x) • G x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
  let err := fun k x => d (f k x) • G x - d (F x) • G x
  have hm k : MemLp (err k) 2 μ :=
    (memLp_bounded_comp_smul hd hb (hf k) hG).sub
      (memLp_bounded_comp_smul hd hb hF hG)
  have hC : 0 ≤ C := (norm_nonneg (d 0)).trans (hb 0)
  have hbnd k x : ‖err k x‖ ≤ 2 * C * ‖G x‖ := by
    calc
      _ ≤ ‖d (f k x) • G x‖ + ‖d (F x) • G x‖ := norm_sub_le _ _
      _ ≤ C * ‖G x‖ + C * ‖G x‖ := by
        simp only [norm_smul]
        exact add_le_add (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))
      _ = _ := by ring
  have hreal : Tendsto (fun k => ∫ x, ‖err k x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have hl : ∀ᵐ x ∂μ, Tendsto (fun k => ‖err k x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      filter_upwards [hlim] with x hx
      have hh := ((hd.continuousAt.tendsto.comp hx).smul
        (tendsto_const_nhds (x := G x))).sub
        (tendsto_const_nhds (x := d (F x) • G x))
      simpa only [err, Function.comp_def, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hh.norm.pow 2
    have hi : Integrable (fun x => (2 * C) ^ 2 * ‖G x‖ ^ 2) μ :=
      hG.norm.integrable_sq.const_mul _
    have ht := tendsto_integral_of_dominated_convergence
      (fun x => (2 * C) ^ 2 * ‖G x‖ ^ 2)
      (fun k => (hm k).aestronglyMeasurable.norm.pow 2) hi
      (fun k => Eventually.of_forall fun x => by
        simp only [Pi.pow_apply]
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        simpa only [← pow_two, mul_pow] using
          (mul_self_le_mul_self (norm_nonneg (err k x)) (hbnd k x))) hl
    simpa only [Pi.pow_apply, integral_zero] using ht
  have he k : ∫⁻ x, ‖err k x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖err k x‖ ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hm k).norm.integrable_sq
      (Eventually.of_forall fun x => sq_nonneg _)]
    exact lintegral_congr fun x => enorm_sq_eq_ofReal_norm_sq _
  change Tendsto (fun k => ∫⁻ x, ‖err k x‖ₑ ^ 2 ∂μ) atTop (𝓝 0)
  simp only [he]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal

/-- Bounded pointwise multipliers preserve strong convergence of varying `L²` fields. -/
theorem tendsto_bounded_comp_smul (hd : Continuous d) (hb : ∀ r, ‖d r‖ ≤ C)
    {F : Ω → ℝ} {f : ℕ → Ω → ℝ}
    (hF : AEStronglyMeasurable F μ) (hf : ∀ k, AEStronglyMeasurable (f k) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (F x)))
    {G : Ω → E} {g : ℕ → Ω → E} (hG : MemLp G 2 μ) (hg : ∀ k, MemLp (g k) 2 μ)
    (hgLim : Tendsto (fun k => ∫⁻ x, ‖g k x - G x‖ₑ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ x, ‖d (f k x) • g k x - d (F x) • G x‖ₑ ^ 2 ∂μ)
      atTop (𝓝 0) := by
  let a := fun k x => d (f k x) • (g k x - G x)
  let b := fun k x => d (f k x) • G x - d (F x) • G x
  have ha k : MemLp (a k) 2 μ := memLp_bounded_comp_smul hd hb (hf k) ((hg k).sub hG)
  have hbMem k : MemLp (b k) 2 μ :=
    (memLp_bounded_comp_smul hd hb (hf k) hG).sub (memLp_bounded_comp_smul hd hb hF hG)
  have hgl := (tendsto_toLp_iff_lintegral_sq g hg G hG).mpr hgLim
  have han : Tendsto (fun k => ‖(ha k).toLp (a k)‖) atTop (𝓝 0) := by
    have hbound k : ‖(ha k).toLp (a k)‖ ≤ C * ‖(hg k).toLp (g k) - hG.toLp G‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(ha k).coeFn_toLp, Lp.coeFn_sub ((hg k).toLp (g k)) (hG.toLp G),
        (hg k).coeFn_toLp, hG.coeFn_toLp] with x hx hs hgx hGx
      rw [hx, hs]
      simp only [Pi.sub_apply]
      rw [hgx, hGx]
      change ‖d (f k x) • (g k x - G x)‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)
    apply squeeze_zero (fun _ => norm_nonneg _) hbound
    simpa only [sub_self, norm_zero, mul_zero] using
      (hgl.sub (tendsto_const_nhds (x := hG.toLp G))).norm.const_mul C
  have hbl := tendsto_bounded_comp_smul_fixed hd hb hF hf hlim hG
  have hbzero : Tendsto (fun k => (hbMem k).toLp (b k)) atTop (𝓝 0) := by
    have hh := (tendsto_toLp_iff_lintegral_sq b hbMem (fun _ => (0 : E)) (MemLp.zero : MemLp (fun _ : Ω => (0 : E)) 2 μ)).mpr
      (by simpa only [sub_zero] using hbl)
    change Tendsto (fun k => (hbMem k).toLp (b k)) atTop
      (𝓝 ((MemLp.zero : MemLp (0 : Ω → E) 2 μ).toLp 0)) at hh
    simpa only [MemLp.toLp_zero] using hh
  have hazero : Tendsto (fun k => (ha k).toLp (a k)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr han
  have hprod k := memLp_bounded_comp_smul hd hb (hf k) (hg k)
  have hprodLim := memLp_bounded_comp_smul hd hb hF hG
  apply (tendsto_toLp_iff_lintegral_sq (fun k x => d (f k x) • g k x) hprod
    (fun x => d (F x) • G x) hprodLim).mp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he k : (hprod k).toLp (fun x => d (f k x) • g k x) -
      hprodLim.toLp (fun x => d (F x) • G x) = (ha k).toLp (a k) + (hbMem k).toLp (b k) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub ((hprod k).toLp _) (hprodLim.toLp _),
      Lp.coeFn_add ((ha k).toLp _) ((hbMem k).toLp _), (hprod k).coeFn_toLp,
      hprodLim.coeFn_toLp, (ha k).coeFn_toLp, (hbMem k).coeFn_toLp] with x hs ha hx hy hx' hy'
    rw [hs, ha]
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [hx, hy, hx', hy']
    dsimp [a, b]
    rw [smul_sub]
    abel
  have ht := ((hazero.add hbzero).congr fun k => (he k).symm).norm
  simpa only [add_zero, norm_zero] using ht

end Riesz1.WeightedSobolev

end
