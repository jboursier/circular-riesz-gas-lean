/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The limiting inverse-square boundary estimate

Positive-part distance cutoffs have gradient bounded by one. This lemma
extracts the vanishing conclusion from their integral estimates, without
requiring convergence of their gradients.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Riesz1.Internal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem boundary_barrier_cutoff_bound {d ε q R f : ℝ}
    (hd : 0 < d) (hdR : d ≤ R) (hε : 0 ≤ ε) (hq : 0 ≤ q) (hf : 0 ≤ f) :
    0 ≤ ((max (d - ε) 0 / d) ^ 2 + q * max (d - ε) 0 ^ 2) * f ∧
      ((max (d - ε) 0 / d) ^ 2 + q * max (d - ε) 0 ^ 2) * f ≤
        (1 + q * R ^ 2) * f := by
  have hb : 0 ≤ max (d - ε) 0 := le_max_right _ _
  have hbd : max (d - ε) 0 ≤ d := max_le (by linarith) hd.le
  have hratio : 0 ≤ max (d - ε) 0 / d := div_nonneg hb hd.le
  have hratio1 : max (d - ε) 0 / d ≤ 1 := (div_le_one hd).mpr hbd
  have hs1 : (max (d - ε) 0 / d) ^ 2 ≤ 1 := by nlinarith
  have hsR : max (d - ε) 0 ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ hb (hbd.trans hdR) 2
  constructor
  · positivity
  · exact mul_le_mul_of_nonneg_right (add_le_add hs1 (mul_le_mul_of_nonneg_left hsR hq)) hf

/-- The final limiting step of the scalar boundary argument. This is an
internal estimate criterion, not a boundary-core theorem of the paper. -/
theorem eq_zero_of_boundary_barrier_estimates {d f : α → ℝ} {q R : ℝ}
    (hdm : Measurable d) (hd : ∀ᵐ x ∂μ, 0 < d x ∧ d x ≤ R)
    (hf : Integrable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hq : 0 < q)
    (hest : ∀ ε : ℝ, 0 < ε →
      (∫ x, ((max (d x - ε) 0 / d x) ^ 2 + q * max (d x - ε) 0 ^ 2) * f x ∂μ) ≤
        ∫ x, f x ∂μ) : f =ᵐ[μ] 0 := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let A : ℕ → α → ℝ := fun n x =>
    ((max (d x - ε n) 0 / d x) ^ 2 + q * max (d x - ε n) 0 ^ 2) * f x
  let F : α → ℝ := fun x => (1 + q * d x ^ 2) * f x
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hAbound (n : ℕ) : ∀ᵐ x ∂μ, ‖A n x‖ ≤ (1 + q * R ^ 2) * f x := by
    filter_upwards [hd, hf0] with x hx hfx
    have hb := boundary_barrier_cutoff_bound hx.1 hx.2 (hεpos n).le hq.le hfx
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => A n x) atTop (𝓝 (F x)) := by
    filter_upwards [hd] with x hx
    have hb : Tendsto (fun n => max (d x - ε n) 0) atTop (𝓝 (d x)) := by
      simpa only [sub_zero, max_eq_left hx.1.le] using
        (((tendsto_const_nhds (x := d x)).sub hεlim).max (tendsto_const_nhds (x := (0 : ℝ))))
    have hh := (((hb.div_const (d x)).pow 2).add
      ((tendsto_const_nhds (x := q)).mul (hb.pow 2))).mul (tendsto_const_nhds (x := f x))
    simpa only [div_self hx.1.ne', one_pow, A, F] using hh
  have hAm (n : ℕ) : AEStronglyMeasurable (A n) μ := by
    exact ((((hdm.sub_const (ε n)).max measurable_const).div hdm).aestronglyMeasurable.pow 2 |>.add
      (aestronglyMeasurable_const.mul
        (((hdm.sub_const (ε n)).max measurable_const).aestronglyMeasurable.pow 2))).mul
          hf.aestronglyMeasurable
  have hconv := tendsto_integral_of_dominated_convergence
    (fun x => (1 + q * R ^ 2) * f x) hAm (hf.const_mul _) hAbound hlim
  have hle : (∫ x, F x ∂μ) ≤ ∫ x, f x ∂μ :=
    le_of_tendsto hconv (Filter.Eventually.of_forall fun n => hest (ε n) (hεpos n))
  have hdf : Integrable (fun x => d x ^ 2 * f x) μ := by
    apply Integrable.mono' (hf.const_mul (R ^ 2))
      ((hdm.pow_const 2).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    filter_upwards [hd, hf0] with x hx hfx
    change ‖d x ^ 2 * f x‖ ≤ R ^ 2 * f x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hfx)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.1.le hx.2 2) hfx
  have heq : (∫ x, F x ∂μ) = (∫ x, f x ∂μ) + q * ∫ x, d x ^ 2 * f x ∂μ := by
    have he : F = fun x => f x + q * (d x ^ 2 * f x) := by funext x; dsimp [F]; ring
    rw [he, integral_add hf (hdf.const_mul q), integral_const_mul]
  have hnonneg : 0 ≤ ∫ x, d x ^ 2 * f x ∂μ :=
    integral_nonneg_of_ae (hf0.mono fun x hx => mul_nonneg (sq_nonneg _) hx)
  have hzero : (∫ x, d x ^ 2 * f x ∂μ) = 0 := by nlinarith
  have haz := (integral_eq_zero_iff_of_nonneg_ae
    (hf0.mono fun x hx => mul_nonneg (sq_nonneg _) hx) hdf).mp hzero
  filter_upwards [haz, hd] with x hx hdx
  exact (mul_eq_zero.mp hx).resolve_left (pow_ne_zero 2 hdx.1.ne')

end Riesz1.Internal
