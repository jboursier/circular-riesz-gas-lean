/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Local absolute continuity of positive log-concave functions

On a compact subinterval of an open convex set the logarithm is Lipschitz.
The exponential is Lipschitz on the compact image of that subinterval.
-/

public section

open Set

namespace Riesz1

/-- A positive log-concave function is absolutely continuous on every compact
interval contained in its open convex domain. -/
theorem absolutelyContinuousOnInterval_of_concaveOn_log {f : ℝ → ℝ} {D : Set ℝ}
    (hD : IsOpen D) (hf : ∀ x ∈ D, 0 < f x)
    (hlog : ConcaveOn ℝ D (fun x => Real.log (f x)))
    {a b : ℝ} (hab : uIcc a b ⊆ D) : AbsolutelyContinuousOnInterval f a b := by
  have hl := (hlog.locallyLipschitzOn hD).mono hab
  obtain ⟨K, hK⟩ := hl.exists_lipschitzOnWith_of_compact isCompact_uIcc
  have himage : IsCompact ((fun x => Real.log (f x)) '' uIcc a b) :=
    isCompact_uIcc.image_of_continuousOn hl.continuousOn
  have hexp : LocallyLipschitzOn ((fun x => Real.log (f x)) '' uIcc a b) Real.exp :=
    (Real.contDiff_exp (n := 1)).locallyLipschitz.locallyLipschitzOn
  obtain ⟨J, hJ⟩ := hexp.exists_lipschitzOnWith_of_compact himage
  have hc := hJ.comp_absolutelyContinuousOnInterval
    (fun x hx => mem_image_of_mem _ hx) hK.absolutelyContinuousOnInterval
  exact hc.congr (fun x hx => Real.exp_log (hf x (hab hx)))

end Riesz1

end
