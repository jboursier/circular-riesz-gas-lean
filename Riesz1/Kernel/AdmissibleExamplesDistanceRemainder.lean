/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibleExamplesDistancePrimitive
public import Riesz1.ToMathlib.FourierMatchedCell

/-!
# Removing the antipodal corner of a distance power

Subtracting a multiple of the squared central coordinate matches the first
endpoint derivatives of the smooth cell remainder. The residual periodic function
has cubic Fourier decay. This isolates the only corner of the distance power.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1
namespace Internal

/-- The square of the central coordinate on the unit circle. Its only corner in
its first derivative lies at the antipode. -/
@[expose] noncomputable def quadraticCell : UnitAddCircle → ℝ :=
  AddCircle.liftIco 1 (-(1 / 2 : ℝ)) (fun x : ℝ => x ^ 2)

lemma continuous_quadraticCell : Continuous quadraticCell := by
  apply AddCircle.liftIco_continuous
  · norm_num
  · exact (continuous_pow 2).continuousOn

/-- Removing the derivative jump of a smooth cell by a quadratic polynomial gives
matching values and first derivatives. -/
lemma exists_matched_quadratic_remainder {H : ℝ → ℝ}
    (hH : ∀ x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), ContDiffAt ℝ ∞ H x)
    (he : H (-(1 / 2)) = H (1 / 2)) :
    ∃ A : ℝ, ∃ R : ℝ → ℝ,
      (∀ x, H x = A * x ^ 2 + R x) ∧
      (∀ x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), ContDiffAt ℝ ∞ R x) ∧
      R (-(1 / 2)) = R (1 / 2) ∧
      deriv R (-(1 / 2)) = deriv R (1 / 2) := by
  let A := (deriv H (1 / 2) - deriv H (-(1 / 2))) / 2
  let R : ℝ → ℝ := fun x => H x - A * x ^ 2
  have hR (x : ℝ) (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
      ContDiffAt ℝ ∞ R x := (hH x hx).sub (contDiffAt_const.mul (contDiffAt_id.pow 2))
  have hd (x : ℝ) (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
      deriv R x = deriv H x - A * (2 * x) := by
    exact (((hH x hx).differentiableAt (by simp)).hasDerivAt.sub
      (((hasDerivAt_id x).pow 2).const_mul A)).deriv.trans (by simp)
  refine ⟨A, R, fun x => by dsimp [R]; ring, hR, ?_, ?_⟩
  · dsimp [R]
    rw [he]
    ring
  · rw [hd _ (by constructor <;> norm_num), hd _ (by constructor <;> norm_num)]
    dsimp [A]
    ring

/-- A distance power is the sum, almost everywhere, of its Riesz singularity,
one quadratic corner, and a continuous real remainder with cubic coefficient decay. -/
lemma exists_distance_power_matched_remainder (a : RieszExponent) :
    ∃ A : ℝ, ∃ h : UnitAddCircle → ℝ, Continuous h ∧
      ((fun x : UnitAddCircle => ((dist x 0 ^ (-a.val) : ℝ) : ℂ)) =ᵐ[volume]
        fun x => (rieszRepresentative a x : ℂ) + (A : ℂ) * (quadraticCell x : ℂ) + (h x : ℂ)) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ k : ℤ, k ≠ 0 →
        ‖fourierCoeff (fun x => (h x : ℂ)) k‖ ≤ K * |(k : ℝ)| ^ (-3 : ℝ) := by
  obtain ⟨H, hH, he, hform⟩ := exists_smooth_power_remainder_cell a
  obtain ⟨A, R, hRform, hR, hRe, hRd⟩ := exists_matched_quadratic_remainder hH he
  let h : UnitAddCircle → ℝ := AddCircle.liftIco 1 (-(1 / 2 : ℝ)) R
  have hc : Continuous h := by
    apply AddCircle.liftIco_continuous
    · simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using hRe
    · intro x hx
      exact (hR x (by simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using hx)).continuousAt.continuousWithinAt
  have hd (x : ℝ) (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
      deriv (fun t => (R t : ℂ)) x = ((deriv R x : ℝ) : ℂ) :=
    (((hR x hx).differentiableAt (by simp)).hasDerivAt.ofReal_comp).deriv
  obtain ⟨K, hK, hb⟩ := exists_fourierCoeff_liftIco_bound_three
    (f := fun x => (R x : ℂ)) (a := -(1 / 2 : ℝ))
    (fun x hx => (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (hR x (by simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using hx))).of_le (by simp))
    (by simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using congrArg Complex.ofReal hRe)
    (by rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring, hd _ (by constructor <;> norm_num),
          hd _ (by constructor <;> norm_num), hRd])
  refine ⟨A, h, hc, ?_, K, hK, hb⟩
  have hae : ∀ᵐ x : UnitAddCircle ∂volume, x ≠ 0 := by
    simp only [ae_iff, not_not]
    change volume ({(0 : UnitAddCircle)} : Set UnitAddCircle) = 0
    have hmp := AddCircle.measurePreserving_mk 1 (-(1 / 2 : ℝ))
    rw [← hmp.measure_preimage (measurableSet_singleton _).nullMeasurableSet,
      Measure.restrict_apply' measurableSet_Ioc]
    refine measure_mono_null (t := {(0 : ℝ)}) ?_ (measure_singleton _)
    rintro y ⟨hy1, hy2⟩
    have hz : (0 : ℝ) ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by norm_num
    have heq : (y : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := hy1
    rw [AddCircle.coe_eq_coe_iff_of_mem_Ioc hy2 hz] at heq
    exact heq
  filter_upwards [hae] with x hx0
  let z := (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) x).val
  have hz : z ∈ Ico (-(1 / 2 : ℝ)) (1 / 2) := by
    simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using
      (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) x).property
  have hzx : (z : UnitAddCircle) = x := AddCircle.coe_equivIco
  have hz0 : z ≠ 0 := by intro h0; apply hx0; rw [← hzx, h0, AddCircle.coe_zero]
  have hd : dist x 0 = |z| := by
    rw [dist_zero_right, ← hzx]
    exact (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).mpr (by
      rw [abs_one, abs_le]
      exact ⟨hz.1, hz.2.le⟩)
  have hz' : z ∈ Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using hz
  have hhz : h x = R z := by rw [← hzx]; exact AddCircle.liftIco_coe_apply hz'
  have hqz : quadraticCell x = z ^ 2 := by rw [← hzx]; exact AddCircle.liftIco_coe_apply hz'
  have heq := hform z ⟨hz.1, hz.2.le⟩ hz0
  rw [hzx, hRform] at heq
  rw [hd, hhz, hqz]
  exact_mod_cast (show |z| ^ (-a.val) = rieszRepresentative a x + A * z ^ 2 + R z by linarith)

end Internal
end Riesz1
