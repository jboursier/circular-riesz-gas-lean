/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalizationCentered
public import Riesz1.ToMathlib.PeriodicRectangleIntegral

/-!
# Absolute convergence on centered background rectangles

The localization part of Lemma 5.8. These certificates justify
partitioning and interchanging the global background integrals.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- The microscopic pair kernel is absolutely integrable on any translated
fundamental rectangle. No diagonal is removed from the background integral. -/
theorem loopLocalization_kernel_integrable_rectangle {N : ℕ+} {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) {b : ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    (hp : Function.Periodic b (N : ℝ)) (a c : ℝ) :
    Integrable (fun p : ℝ × ℝ => loopArcKernel s N b p.1 p.2)
      ((volume.restrict (Ioc a (a + N))).prod (volume.restrict (Ioc c (c + N)))) := by
  have hsq := integrable_arc_square s hs hs1 N hb hp
  have hi : Integrable (fun p : ℝ × ℝ => loopArcKernel s N b p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))) := by
    exact (hsq.add hsq.swap).neg.congr (Filter.Eventually.of_forall fun p =>
      (loopArcKernel_eq_integral_add s N b hb hp p.1 p.2).symm)
  exact integrable_periodic_rectangle (by exact_mod_cast N.pos)
    (measurable_loopLocalKernel hb.continuous s N)
    (fun u => loopLocalKernel_periodic_left hp s u)
    (fun z => loopLocalKernel_periodic_right hp s z)
    (fun z => loopLocalKernel_intervalIntegrable hs hs1 N hb hp z 0 N) hi a c

/-- Absolute convergence also holds on the closed centered fundamental square.
The endpoints have zero arclength measure. -/
theorem loopLocalization_kernel_integrable_centered {N : ℕ+} {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) {b : ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    (hp : Function.Periodic b (N : ℝ)) :
    Integrable (fun p : ℝ × ℝ => loopArcKernel s N b p.1 p.2)
      ((volume.restrict (Icc (-(N : ℝ) / 2) ((N : ℝ) / 2))).prod
        (volume.restrict (Icc (-(N : ℝ) / 2) ((N : ℝ) / 2)))) := by
  have he : (volume : Measure ℝ).restrict (Icc (-(N : ℝ) / 2) ((N : ℝ) / 2)) =
      volume.restrict (Ioc (-(N : ℝ) / 2) ((N : ℝ) / 2)) := by
    exact Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
  rw [he]
  simpa only [show -(N : ℝ) / 2 + N = (N : ℝ) / 2 by ring] using
    loopLocalization_kernel_integrable_rectangle hs hs1 hb hp
      (-(N : ℝ) / 2) (-(N : ℝ) / 2)

end Riesz1

end
