/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Integrability on translated periodic rectangles

Separate periodicity transports absolute integrability from one fundamental
rectangle to every translated fundamental rectangle.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Absolute integrability of a separately periodic measurable function on
translated fundamental rectangles. Slice integrability is required at every
first coordinate, so translation does not need to transport exceptional sets. -/
theorem integrable_periodic_rectangle {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {T : ℝ} (hT : 0 < T) {f : ℝ × ℝ → E} (hf : Measurable f)
    (hp : ∀ u, Function.Periodic (fun z => f (z, u)) T)
    (hq : ∀ z, Function.Periodic (fun u => f (z, u)) T)
    (hslice : ∀ z, IntervalIntegrable (fun u => f (z, u)) volume 0 T)
    (hi : Integrable f ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T))))
    (a b : ℝ) :
    Integrable f ((volume.restrict (Ioc a (a + T))).prod
      (volume.restrict (Ioc b (b + T)))) := by
  let g := fun z => ∫ u in (0 : ℝ)..T, ‖f (z, u)‖
  have hg : Function.Periodic g T := by
    intro z
    exact intervalIntegral.integral_congr (fun u _ => congrArg norm (hp u z))
  have hg0 : IntervalIntegrable g volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    change Integrable (fun z => ∫ u in (0 : ℝ)..T, ‖f (z, u)‖)
      (volume.restrict (Ioc 0 T))
    simpa only [intervalIntegral.integral_of_le hT.le] using hi.integral_norm_prod_left
  have hga : IntegrableOn g (Ioc a (a + T)) := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
      (hg.intervalIntegrable₀ hT.ne' hg0 _ _)
  refine (integrable_prod_iff hf.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun z =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
        ((hq z).intervalIntegrable₀ hT.ne' (hslice z) _ _)
  · have he (z : ℝ) : (∫ u in Ioc b (b + T), ‖f (z, u)‖) = g z := by
      rw [← intervalIntegral.integral_of_le (show b ≤ b + T by linarith)]
      have hn : Function.Periodic (fun u => ‖f (z, u)‖) T :=
        fun u => congrArg norm (hq z u)
      simpa only [g, zero_add] using hn.intervalIntegral_add_eq b 0
    simp_rw [he]
    exact hga

end Riesz1

end
