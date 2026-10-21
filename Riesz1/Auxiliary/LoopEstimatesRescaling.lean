/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopAnchoringRescaling
public import Riesz1.Variance.LoopScale
import all Riesz1.Variance.LoopForce

/-!
# The microscopic loop is the loop functional

The rescaling identity in Lemma 5.8. It is an exact
change of variables in all four terms of the fluctuation expansion. No
smoothness assumption or new encoding of either loop is needed.
-/

public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- Rescaling the pair kernel, including its value on the diagonal. -/
theorem loopEstimates_pair_rescale (s : ℝ) (N : ℕ+) (f : ℝ → ℝ) (x y : ℝ) :
    loopArcKernel s N (loopScaleField (N : ℝ) f) ((N : ℝ) * x) ((N : ℝ) * y) =
      (N : ℝ) ^ (-s) * loopKernel s f x y := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  unfold loopArcKernel loopScaleField loopKernel
  rw [loopAnchoring_deriv_scaled_kernel, mul_div_cancel_left₀ _ hN, mul_div_cancel_left₀ _ hN,
    show ((N : ℝ) * x - (N : ℝ) * y) / N = x - y by field_simp]
  field_simp

private theorem rescale_integral (N : ℕ+) (f : ℝ → ℝ) :
    (∫ u in (0 : ℝ)..(N : ℝ), f u) =
      (N : ℝ) * ∫ u in (0 : ℝ)..1, f ((N : ℝ) * u) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  have hh := intervalIntegral.integral_comp_mul_left (f := f) (a := (0 : ℝ)) (b := 1) hN
  simp only [mul_zero, mul_one, smul_eq_mul] at hh
  rw [hh]
  field_simp

/-- The complete microscopic loop equals the loop functional defined earlier.
The assertion holds for arbitrary real fields on their whole carriers. -/
theorem loopEstimates_loopArcL_eq_loopFunctional (s : ℝ) (N : ℕ+)
    (f : ℝ → ℝ) (X : Configuration N) :
    loopArcL s N (loopScaleField (N : ℝ) f) X =
      loopFunctional s (N : ℕ) f X.val := by
  classical
  have hpair := loopEstimates_pair_rescale s N f
  have hleft (x : ℝ) :
      (∫ u in (0 : ℝ)..(N : ℝ),
        loopArcKernel s N (loopScaleField (N : ℝ) f) ((N : ℝ) * x) u) =
          (N : ℝ) * ((N : ℝ) ^ (-s) * ∫ u in (0 : ℝ)..1, loopKernel s f x u) := by
    rw [rescale_integral N]
    simp only [hpair, intervalIntegral.integral_const_mul]
  have hright (x : ℝ) :
      (∫ u in (0 : ℝ)..(N : ℝ),
        loopArcKernel s N (loopScaleField (N : ℝ) f) u ((N : ℝ) * x)) =
          (N : ℝ) * ((N : ℝ) ^ (-s) * ∫ u in (0 : ℝ)..1, loopKernel s f u x) := by
    rw [rescale_integral N]
    simp only [hpair, intervalIntegral.integral_const_mul]
  have hdouble :
      (∫ z in (0 : ℝ)..(N : ℝ), ∫ u in (0 : ℝ)..(N : ℝ),
        loopArcKernel s N (loopScaleField (N : ℝ) f) z u) =
          (N : ℝ) ^ 2 * (N : ℝ) ^ (-s) *
            ∫ z in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, loopKernel s f z u := by
    rw [rescale_integral N]
    simp only [hleft, intervalIntegral.integral_const_mul]
    ring
  unfold loopArcL loopArcPos loopFunctional
  simp only [hpair, hleft, hright, hdouble, ← Finset.mul_sum]
  have hite (i j : Fin (N : ℕ)) :
      (if j = i then 0 else (N : ℝ) ^ (-s) * loopKernel s f (X.val i) (X.val j)) =
        (N : ℝ) ^ (-s) * (if j = i then 0 else loopKernel s f (X.val i) (X.val j)) := by
    split <;> simp_all
  simp only [hite, ← Finset.mul_sum]
  ring

/-- The microscopic scale `K = Nℓ` yields the original scale-`ℓ` loop. -/
theorem loopEstimates_loopArcL_scale (s : ℝ) (N : ℕ+) (ℓ : ℝ) (ψ : ℝ → ℝ)
    (X : Configuration N) :
    loopArcL s N (loopScaleField ((N : ℝ) * ℓ) ψ) X =
      loopFunctional s (N : ℕ) (loopScaleField ℓ ψ) X.val := by
  have he : loopScaleField ((N : ℝ) * ℓ) ψ =
      loopScaleField (N : ℝ) (loopScaleField ℓ ψ) := by
    funext z
    unfold loopScaleField
    rw [div_div]
    ring
  rw [he, loopEstimates_loopArcL_eq_loopFunctional]

end Riesz1

end
