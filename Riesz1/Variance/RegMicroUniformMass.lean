/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CirclePullback
public import Riesz1.Variance.RegMicroKernelSupport

/-!
# Square mass on enlarged circles

Circle dilation contributes the reciprocal circumference. Periodization
of a profile on a circle of length at least one has exactly the
square mass of its zero extension, independently of that circumference.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1.Internal

/-- The precise arclength factor for the square mass of a pullback. -/
theorem integral_sq_loopMasterPullback (L : Length)
    (f : {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)}) :
    (∫ z : UnitAddCircle, (loopMasterPullback L f.val z)^2) =
      L.val⁻¹ * ∫ z : Circle L, f.val z^2 ∂arclength L := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hf : MemLp f.val 2 (arclength L) := f.property.re
  have hA : AEStronglyMeasurable (fun z => f.val z^2)
      ((volume : Measure UnitAddCircle).map
        (AddCircle.equivAddCircle 1 L.val one_ne_zero L.property.ne')) := by
    rw [map_circleScale_volume]
    exact hf.integrable_sq.aestronglyMeasurable.smul_measure _
  change (∫ z : UnitAddCircle,
    f.val (AddCircle.equivAddCircle 1 L.val one_ne_zero L.property.ne' z)^2) = _
  rw [← integral_map (AddCircle.continuous_equivAddCircle ..).measurable.aemeasurable hA,
    map_circleScale_volume, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal L.property.le]
  rfl

/-- No periodic copies overlap on an enlarged circle. The identity
includes the unit circle and arbitrary endpoint values of the profile. -/
theorem integral_sq_periodizedProfile (p : Profile) (L : Length) (hL : 1 ≤ L.val) :
    (∫ z : Circle L, (periodizedProfile p L z)^2 ∂arclength L) =
      ∫ x : ℝ, (zeroExtension p x)^2 := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  change (∫ z : Circle L, (periodizedProfile p L z)^2) = _
  rw [← AddCircle.integral_preimage L.val (-(L.val/2))]
  rw [show -(L.val/2)+L.val = L.val/2 by ring]
  calc
    _ = ∫ x in Ioc (-(L.val/2)) (L.val/2), (zeroExtension p x)^2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (show ∀ᵐ x : ℝ, x ≠ L.val/2 by rw [ae_iff]; simp)] with x hx hxend
      rw [regMicroKernel_periodized_coe_eq p L hL
        ⟨by linarith [hx.1], lt_of_le_of_ne hx.2 hxend⟩]
    _ = _ := by
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      refine Eventually.of_forall fun x hx => ?_
      have habs : ¬ |x| < 1/2 := by
        intro h
        obtain ⟨h0, h1⟩ := abs_lt.mp h
        exact hx ⟨by linarith, by linarith⟩
      simp only [zeroExtension, habs, ite_false, zero_pow (by norm_num : 2 ≠ 0)]

end Riesz1.Internal
