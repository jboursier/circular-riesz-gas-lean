/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Removing an exponential density from L² data

Multiplication by the square root of a positive exponential density
transports arbitrary weighted L² representatives to unweighted L².
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The square root of the density is the L² isometry multiplier.
No continuity of the input function is needed. -/
theorem memLp_two_exp_neg_half {μ : Measure α} {H : α → ℝ}
    (hH : Measurable H) {f : α → F}
    (hf : MemLp f 2 (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-H x))))) :
    MemLp (fun x => Real.exp (-H x / 2) • f x) 2 μ := by
  have hd : Measurable (fun x => ENNReal.ofReal (Real.exp (-H x))) := by fun_prop
  have hac : μ ≪ μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-H x))) :=
    withDensity_absolutelyContinuous' hd.aemeasurable
      (Filter.Eventually.of_forall (fun x => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'))
  have hfm : AEStronglyMeasurable f μ := hf.aestronglyMeasurable.mono_ac hac
  have hm : AEStronglyMeasurable (fun x => Real.exp (-H x / 2) • f x) μ :=
    (by fun_prop : Measurable (fun x => Real.exp (-H x / 2))).aestronglyMeasurable.smul hfm
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hi' := (integrable_withDensity_iff_integrable_smul' hd
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hi
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  convert hi' using 1
  funext x
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

end Riesz1
