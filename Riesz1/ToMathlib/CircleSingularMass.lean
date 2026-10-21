/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.AbsRpowRadius
public import Riesz1.ToMathlib.CircleSingularityLocalization
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Singular powers on sets of bounded arclength

The bounds are uniform in the circumference and singularity location.
They apply to unbounded measurable representatives in the positive-exponent
near step of Lemma 5.3.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- A distance power integrated over a circle ball is bounded by the
corresponding integral on the line, even when the ball fills the circle. -/
theorem lintegral_circle_ball_rpow_le {L p R : ℝ} [hL : Fact (0 < L)]
    (hp : p < 1) (hR : 0 ≤ R) (a : AddCircle L) :
    (∫⁻ x in Metric.closedBall a R, ENNReal.ofReal (dist x a ^ (-p))) ≤
      ENNReal.ofReal (2 * R ^ (1-p) / (1-p)) := by
  classical
  let F : AddCircle L → ℝ≥0∞ := (Metric.closedBall 0 R).indicator
    (fun x => ENNReal.ofReal (dist x 0 ^ (-p)))
  have he : (Metric.closedBall a R).indicator
      (fun x => ENNReal.ofReal (dist x a ^ (-p))) = fun x => F (x-a) := by
    funext x
    simp [F, Set.indicator, Metric.mem_closedBall, dist_eq_norm]
  rw [← lintegral_indicator measurableSet_closedBall, he, lintegral_sub_right_eq_self]
  rw [← AddCircle.lintegral_preimage L (-(L/2)) F,
    show -(L/2)+L = L/2 by ring]
  have hdom : (∫⁻ x in Ioc (-(L/2)) (L/2), F (x : AddCircle L)) ≤
      ∫⁻ x in Icc (-R) R, ENNReal.ofReal (|x| ^ (-p)) := by
    rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Icc]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ Ioc (-(L/2)) (L/2)
    · have hd : dist (x : AddCircle L) 0 = |x| := by
        simpa using CircleSingularity.dist_coe_eq_abs_sub hL.out
          (x := x) (y := 0) (by simpa using abs_le.mpr ⟨hx.1.le, hx.2⟩)
      rw [Set.indicator_of_mem hx]
      by_cases hr : |x| ≤ R
      · have hxR : x ∈ Icc (-R) R := abs_le.mp hr
        simp only [F, Set.indicator, Metric.mem_closedBall, hd, hr, ↓reduceIte, hxR, le_refl]
      · simp only [F, Set.indicator, Metric.mem_closedBall, hd, hr, ↓reduceIte, zero_le]
    · simp only [Set.indicator_of_notMem hx, zero_le]
  apply hdom.trans_eq
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_abs_rpow (by linarith : -1 < -p) hR)
    (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg x) _)]
  congr 1
  exact integral_abs_rpow_symm (by linarith) hR

/-- Only the arclength bound on `S` is needed. In particular, `S` may
be a union of overlapping neighborhoods of other marked points. -/
theorem lintegral_circle_rpow_le_of_measure_le {L p h B : ℝ} [hL : Fact (0 < L)]
     (hp0 : 0 ≤ p) (hp1 : p < 1) (hh : 0 < h) (hB : 0 ≤ B)
    (a : AddCircle L) (S : Set (AddCircle L))
    (hS : volume S ≤ ENNReal.ofReal (B*h)) :
    (∫⁻ x in S, ENNReal.ofReal (dist x a ^ (-p))) ≤
      ENNReal.ofReal ((2/(1-p)+B) * h^(1-p)) := by
  classical
  let F : AddCircle L → ℝ≥0∞ := (Metric.closedBall a h).indicator
    (fun x => ENNReal.ofReal (dist x a ^ (-p)))
  have hF : Measurable F := by
    dsimp [F]
    exact ((by fun_prop : Measurable (fun x : AddCircle L => dist x a)).pow_const (-p)).ennreal_ofReal.indicator
      measurableSet_closedBall
  have hpt (x : AddCircle L) : ENNReal.ofReal (dist x a ^ (-p)) ≤ F x +
      ENNReal.ofReal (h^(-p)) := by
    by_cases hx : dist x a ≤ h
    · simp only [F, Set.indicator_of_mem (show x ∈ Metric.closedBall a h from hx)]
      exact le_add_right le_rfl
    · have hd : h ≤ dist x a := (lt_of_not_ge hx).le
      have hb := Real.rpow_le_rpow_of_nonpos hh hd (neg_nonpos.mpr hp0)
      exact (ENNReal.ofReal_le_ofReal hb).trans (le_add_left le_rfl)
  calc
    _ ≤ ∫⁻ x in S, F x + ENNReal.ofReal (h^(-p)) := lintegral_mono hpt
    _ = (∫⁻ x in S, F x) + ENNReal.ofReal (h^(-p)) * volume S := by
      rw [lintegral_add_left hF, lintegral_const, Measure.restrict_apply_univ]
    _ ≤ (∫⁻ x, F x) + ENNReal.ofReal (h^(-p)) * ENNReal.ofReal (B*h) :=
      add_le_add (setLIntegral_le_lintegral S F) (mul_le_mul_of_nonneg_left hS zero_le)
    _ ≤ ENNReal.ofReal (2*h^(1-p)/(1-p)) +
        ENNReal.ofReal (h^(-p)) * ENNReal.ofReal (B*h) := by
      apply add_le_add _ le_rfl
      rw [lintegral_indicator measurableSet_closedBall]
      exact lintegral_circle_ball_rpow_le hp1 hh.le a
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hh.le _), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
      congr 1
      have he : h^(-p)*h = h^(1-p) := by
        calc
          _ = h^(-p)*h^(1 : ℝ) := by rw [Real.rpow_one]
          _ = h^(-p+1) := (Real.rpow_add hh _ _).symm
          _ = _ := by congr 1; ring
      calc
        _ = 2/(1-p)*h^(1-p) + B*(h^(-p)*h) := by ring
        _ = _ := by rw [he]; ring

end Riesz1
