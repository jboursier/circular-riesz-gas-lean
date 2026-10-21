/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Triangle change of variables for iterated interval integrals

For a bounded measurable kernel `G` on the triangle `0 < y < x ≤ R`, the iterated integral over
the triangle `{0 < y < x ≤ R}` in the variables `(x, y)` equals the iterated integral over the
triangle `{u, v > 0, u + v ≤ R}` in the variables `(u, v) = (y, x - y)`:

`∫₀^R (∫₀^x G(x, y) dy) dx = ∫₀^R (∫₀^{R-u} G(u + v, u) dv) du`.

This is the substitution `x = u + v`, `y = u` in the inner integral, combined with the exchange of
the two integrations on the triangle. It is used to pass from the `(x, y)` form of the arc
cutoff `Q` to the `(u, v)` form of the arc function `Λ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- **Triangle change of variables.** Let `G` be measurable on `ℝ²` and bounded by `K` on the
triangle `0 < y < x ≤ R`. Then the iterated integral of `G` over `0 < y < x ≤ R`, with the
inner integral in `y`, equals the iterated integral over `u, v > 0`, `u + v ≤ R` of `G(u+v, u)`. -/
theorem integral_triangle_interval_eq {R K : ℝ} (hR : 0 ≤ R) (G : ℝ → ℝ → ℝ)
    (hm : Measurable (fun p : ℝ × ℝ => G p.1 p.2))
    (hK : ∀ x y : ℝ, 0 < y → y < x → x ≤ R → |G x y| ≤ K) :
    ∫ x in (0 : ℝ)..R, ∫ y in (0 : ℝ)..x, G x y
      = ∫ u in (0 : ℝ)..R, ∫ v in (0 : ℝ)..(R - u), G (u + v) u := by
  -- The indicator form `f x y = 1[y < x] G(x, y)`, bounded on the rectangle `[0, R] × (0, R]`.
  set f : ℝ → ℝ → ℝ := fun x y => if y < x then G x y else 0 with hf
  have hfm : Measurable (fun p : ℝ × ℝ => f p.1 p.2) := by
    simp only [hf]
    exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst) hm measurable_const
  have hfK : ∀ x y : ℝ, x ∈ Icc (0 : ℝ) R → y ∈ Ioc (0 : ℝ) R → |f x y| ≤ max K 0 := by
    intro x y hx hy
    simp only [hf]
    split_ifs with hxy
    · exact (hK x y hy.1 hxy hx.2).trans (le_max_left K 0)
    · simp
  have hint : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict (uIoc (0 : ℝ) R)).prod (volume.restrict (Ioc (0 : ℝ) R))) := by
    rw [uIoc_of_le hR]
    refine Integrable.of_bound hfm.aestronglyMeasurable (max K 0) ?_
    rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)]
    refine ae_of_all _ fun p hp => ?_
    rw [Real.norm_eq_abs]
    exact hfK p.1 p.2 ⟨hp.1.1.le, hp.1.2⟩ hp.2
  -- Exchange the two integrations on the triangle.
  have hswap := intervalIntegral_integral_swap (f := f) hint
  -- Inner integral in `y` for fixed `x ∈ [0, R]`: the indicator restricts `y` to `(0, x)`.
  have hL : ∫ x in (0 : ℝ)..R, ∫ y in (0 : ℝ)..x, G x y
      = ∫ x in (0 : ℝ)..R, ∫ y, f x y ∂(volume.restrict (Ioc (0 : ℝ) R)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hR] at hx
    have hfx : (fun y => f x y) = Set.indicator (Iio x) (G x) := by
      ext y
      simp only [hf, Set.indicator, mem_Iio]
    have hset : Iio x ∩ Ioc (0 : ℝ) R = Ioo 0 x := by
      ext y
      simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
      constructor
      · rintro ⟨h1, h2, _⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, by linarith [hx.2]⟩
    rw [hfx, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      hset, intervalIntegral.integral_of_le hx.1, integral_Ioc_eq_integral_Ioo]
  -- Inner integral in `x` for fixed `y ∈ (0, R]`: the indicator restricts `x` to `(y, R]`.
  have hR' : ∀ y ∈ Ioc (0 : ℝ) R, ∫ x in (0 : ℝ)..R, f x y = ∫ x in y..R, G x y := by
    intro y hy
    have hfy : (fun x => f x y) = Set.indicator (Ioi y) (fun x => G x y) := by
      ext x
      simp only [hf, Set.indicator, mem_Ioi]
    have hset : Ioi y ∩ Ioc (0 : ℝ) R = Ioc y R := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨h1, _, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨h1, by linarith [hy.1, h1], h3⟩
    rw [intervalIntegral.integral_of_le hR, hfy, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, hset, intervalIntegral.integral_of_le hy.2]
  -- Assemble the chain of equalities.
  rw [hL, hswap]
  have hmid : ∫ y, (∫ x in (0 : ℝ)..R, f x y) ∂(volume.restrict (Ioc (0 : ℝ) R))
      = ∫ y in (0 : ℝ)..R, ∫ x in y..R, G x y := by
    rw [intervalIntegral.integral_of_le hR]
    exact setIntegral_congr_fun measurableSet_Ioc fun y hy => hR' y hy
  rw [hmid]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hR] at hu
  have hc := intervalIntegral.integral_comp_add_left (fun x => G x u) u (a := 0) (b := R - u)
  rw [add_zero, add_sub_cancel] at hc
  exact hc.symm

end Riesz1

end
end
