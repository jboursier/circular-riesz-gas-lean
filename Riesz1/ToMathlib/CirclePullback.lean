/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopMasterScaling
public import Riesz1.ToMathlib.MicroLocal.CircleScale
public import Riesz1.Frozen.Profile

/-!
# Pullback of square integrable functions along the dilation of circles

For a length `L > 0`, the dilation `UnitAddCircle → Circle L` underlying `loopMasterPullback` pushes
the Haar probability measure forward to a multiple of the arclength measure
(`map_circleScale_volume`). Hence the pullback of an `L²` function on `Circle L` is an `L²`
function on the unit circle. This lets the variance `σ_ℓ²` be evaluated on a general
`L²` function on `ℓ⁻¹𝕋`.

The file also records the difference of two real `L²` functions on `Circle L`, which is the
profile `ξ - ξ_h` of Proposition 5.6.

The main results are `Riesz1.memLp_comp_dilation`, `Riesz1.loopMasterPullback_memLp`,
`Riesz1.pullbackProfile` and `Riesz1.subCircleL2`.
-/

@[expose] public section

open MeasureTheory

namespace Riesz1

/-- The pullback of a complex `L²` function on `Circle L` along the dilation is `L²` on the unit
circle. -/
theorem memLp_comp_dilation (L : Length) (f : Circle L → ℂ) (hf : MemLp f 2 (arclength L)) :
    MemLp (fun z : UnitAddCircle =>
      f (AddCircle.equivAddCircle 1 L.val one_ne_zero L.property.ne' z)) 2 volume := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hf' : MemLp f 2 (volume : Measure (Circle L)) := hf
  have hmap := map_circleScale_volume L.val
  have hpos : (ENNReal.ofReal L.val)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr L.property).ne'
  have hmemap : MemLp f 2 ((volume : Measure UnitAddCircle).map
      (AddCircle.equivAddCircle 1 L.val one_ne_zero L.property.ne')) := by
    rw [hmap]
    exact hf'.smul_measure hpos
  exact hmemap.comp_of_map (AddCircle.continuous_equivAddCircle _ _ _ _).measurable.aemeasurable

/-- The pullback of a real `L²` function on `Circle L` to the unit circle is `L²` (as a complex
valued function). -/
theorem loopMasterPullback_memLp (L : Length)
    (f : {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)}) :
    MemLp (fun z : UnitAddCircle => (loopMasterPullback L f.val z : ℂ)) 2 volume :=
  memLp_comp_dilation L (fun z => (f.val z : ℂ)) f.property

/-- The pullback of a real `L²` function on `Circle L` as an element of the profile
carrier `Profile` (Assumption 1.1). -/
noncomputable def pullbackProfile (L : Length)
    (f : {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)}) : Profile :=
  ⟨loopMasterPullback L f.val, by
    have h := loopMasterPullback_memLp L f
    exact h⟩

/-- The difference of two real `L²` functions on `Circle L`, in the same carrier. -/
def subCircleL2 {L : Length}
    (f g : {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)}) :
    {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)} :=
  ⟨fun z => f.val z - g.val z, by
    refine MemLp.ae_eq (Filter.Eventually.of_forall fun z => ?_) (f.property.sub g.property)
    simp [Complex.ofReal_sub]⟩

/-- The pullback of a difference is the difference of the pullbacks. -/
lemma loopMasterPullback_subCircleL2 {L : Length}
    (f g : {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)}) (z : UnitAddCircle) :
    loopMasterPullback L (subCircleL2 f g).val z =
      loopMasterPullback L f.val z - loopMasterPullback L g.val z := rfl

end Riesz1

end
