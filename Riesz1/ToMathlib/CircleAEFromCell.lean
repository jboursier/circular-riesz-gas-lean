/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.Arclength
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Almost everywhere equality from a fundamental circle interval

The converse of pulling almost everywhere equality back to a fundamental
cell, for almost everywhere measurable representatives. This allows the
inverse representative in Lemma 5.3 to inherit the
original profile's `L²` membership.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- Equality on the fundamental cell gives equality on the circle.
Only almost everywhere measurability is required of either representative. -/
theorem ae_circle_of_ae_cell {L : Length} {f g : Circle L → ℝ}
    (hf : AEMeasurable f (arclength L)) (hg : AEMeasurable g (arclength L))
    (hfg : ∀ᵐ x : ℝ ∂volume.restrict (Ioc (-(L.val/2)) (L.val/2)),
      f (x : Circle L) = g (x : Circle L)) : f =ᵐ[arclength L] g := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hmp := AddCircle.measurePreserving_mk L.val (-(L.val/2))
  have hmap := hmp.map_eq
  rw [show -(L.val/2)+L.val = L.val/2 by ring] at hmap
  have hfc := hmp.quasiMeasurePreserving.ae_eq_comp hf.ae_eq_mk
  have hgc := hmp.quasiMeasurePreserving.ae_eq_comp hg.ae_eq_mk
  rw [show -(L.val/2)+L.val = L.val/2 by ring] at hfc hgc
  have hmk : hf.mk f =ᵐ[arclength L] hg.mk g := by
    change ∀ᵐ z : Circle L ∂volume, hf.mk f z = hg.mk g z
    rw [← hmap]
    apply (ae_map_iff hmp.measurable.aemeasurable
      (measurableSet_eq_fun hf.measurable_mk hg.measurable_mk)).mpr
    filter_upwards [hfc, hgc, hfg] with x hx hy hxy
    exact hx.symm.trans (hxy.trans hy)
  exact hf.ae_eq_mk.trans (hmk.trans hg.ae_eq_mk.symm)

end Riesz1
