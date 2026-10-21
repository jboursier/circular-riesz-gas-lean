/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifyPowerTail
public import Riesz1.ToMathlib.MollifierPointwise.Derivative

/-!
# Power tails after a further convolution

Local convolution with radius at most one preserves a negative power
tail outside radius four if the input tail holds outside radius two.
The same estimate applies to every classical derivative of a smooth
periodic function.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace Riesz1

/-- A second smoothing step only enlarges a fixed tail neighborhood. -/
theorem mollifyLine_power_tail_from_two {ρ f δ : ℝ → ℝ} (hρ : IsMollifier ρ)
    {C e h x : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hC : 0 ≤ C) (he : e ≤ 0)
    (hm : AEStronglyMeasurable f volume)
    (hδ : ∀ y z, δ y ≤ δ z + |y - z|)
    (hf : ∀ y, 2 ≤ δ y → |f y| ≤ C * δ y ^ e) (hx : 4 ≤ δ x) :
    |mollifyLine ρ h f x| ≤ C * 2 ^ (-e) * δ x ^ e := by
  apply (mollifyLine_abs_le_of_local hρ hh (by positivity) hm ?_).2
  intro y hy
  have hxy := hδ x y
  rw [abs_sub_comm x y] at hxy
  have hy2 : 2 ≤ δ y := by linarith
  have hhalf : δ x / 2 ≤ δ y := by linarith
  have hp := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < δ x / 2) hhalf he
  have heq : (δ x / 2) ^ e = δ x ^ e * 2 ^ (-e) := by
    simpa only [neg_neg] using div_two_rpow_neg (by linarith : 0 ≤ δ x) (p := -e)
  rw [heq] at hp
  exact (hf y hy2).trans (by nlinarith [mul_le_mul_of_nonneg_left hp hC])

/-- Any smooth periodic derivative with a tail from radius two retains
that tail after smoothing, uniformly in the smoothing radius. -/
theorem circleMollify_iterated_power_tail_from_two {ρ f δ : ℝ → ℝ}
    (hρ : IsMollifier ρ) {L C e h x : ℝ} (hL : 0 < L)
    (hh : 0 < h) (hh1 : h ≤ 1) (hC : 0 ≤ C) (he : e ≤ 0)
    (m : ℕ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f L)
    (hδ : ∀ y z, δ y ≤ δ z + |y - z|)
    (ht : ∀ y, 2 ≤ δ y → |iteratedDeriv m f y| ≤ C * δ y ^ e)
    (hx : 4 ≤ δ x) :
    |iteratedDeriv m (circleMollify ρ L h f) x| ≤ C * 2 ^ (-e) * δ x ^ e := by
  have hi : LocallyIntegrable (iteratedDeriv m f) volume :=
    (contDiff_iteratedDeriv_inf hf m).continuous.locallyIntegrable
  rw [iteratedDeriv_circleMollify_eq_deriv hρ hL hh m (hf.of_le (by simp)) hp]
  change |circleMollify ρ L h (iteratedDeriv m f) x| ≤ _
  rw [circleMollify_eq_mollifyLine hρ hL hh hi (periodic_iteratedDeriv hp m)]
  exact mollifyLine_power_tail_from_two hρ hh hh1 hC he hi.aestronglyMeasurable hδ ht hx

end Riesz1
