/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Instances.Int
public import Mathlib.Tactic

/-!
# Extending estimates from shrinking frequency grids

A continuous function inherits a uniform power bound from grids whose mesh tends to
zero. This avoids any separation assumptions on finitely many discarded circle lengths.
-/

public section

open Filter
open scoped Topology

namespace Riesz1.FourierGrid

/-- Rounding down on a shrinking real grid converges to the specified real point. -/
theorem tendsto_mul_floor_div {h : ℕ → ℝ} (hh : ∀ n, 0 < h n)
    (hlim : Tendsto h atTop (𝓝 0)) (w : ℝ) :
    Tendsto (fun n => h n * (⌊w / h n⌋ : ℝ)) atTop (𝓝 w) := by
  have hlo (n : ℕ) : w - h n ≤ h n * (⌊w / h n⌋ : ℝ) := by
    have ht := (div_lt_iff₀ (hh n)).mp (Int.lt_floor_add_one (w / h n))
    nlinarith
  have hhi (n : ℕ) : h n * (⌊w / h n⌋ : ℝ) ≤ w := by
    have ht := (le_div_iff₀ (hh n)).mp (Int.floor_le (w / h n))
    nlinarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using tendsto_const_nhds.sub hlim) tendsto_const_nhds hlo hhi

/-- A power bound on successively finer grids extends to every frequency strictly
above its threshold. The bound and threshold are unchanged. -/
theorem norm_le_rpow_of_grid_bound {F : ℝ → ℂ} (hF : Continuous F)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hlim : Tendsto h atTop (𝓝 0))
    {D W g : ℝ}
    (hbound : ∀ᶠ n in atTop, ∀ k : ℤ, W ≤ |h n * (k : ℝ)| →
      ‖F (h n * (k : ℝ))‖ ≤ D * |h n * (k : ℝ)| ^ g)
    {w : ℝ} (hw : W < |w|) (hw0 : w ≠ 0) :
    ‖F w‖ ≤ D * |w| ^ g := by
  let v := fun n => h n * (⌊w / h n⌋ : ℝ)
  have hv : Tendsto v atTop (𝓝 w) := tendsto_mul_floor_div hh hlim w
  have hav : Tendsto (fun n => |v n|) atTop (𝓝 |w|) := hv.abs
  have hevent : ∀ᶠ n in atTop, W ≤ |v n| := (hav.eventually (eventually_ge_nhds hw)).mono
    (fun _ hx => hx)
  have hnorm : Tendsto (fun n => ‖F (v n)‖) atTop (𝓝 ‖F w‖) :=
    (hF.continuousAt.tendsto.comp hv).norm
  have hpow : Tendsto (fun n => D * |v n| ^ g) atTop (𝓝 (D * |w| ^ g)) :=
    tendsto_const_nhds.mul (hav.rpow_const (Or.inl (abs_ne_zero.mpr hw0)))
  apply le_of_tendsto_of_tendsto hnorm hpow
  filter_upwards [hbound, hevent] with n hn hvn
  exact hn ⌊w / h n⌋ hvn

end Riesz1.FourierGrid
