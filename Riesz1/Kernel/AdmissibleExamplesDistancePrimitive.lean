/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibleExamplesDistance
public import Riesz1.Kernel.AdmissibleExamplesPrimitive

/-!
# Hölder primitives of the subcritical distance powers

The (A1) assertion for the distance-power branch of the admissible examples. The smooth
cell remainder has inverse-frequency decay. Adding the explicit Riesz coefficients
gives the same power bound as the singular part, hence an actual Hölder primitive.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1
namespace Internal

/-- The smooth cell remainder has inverse-frequency decay, independently of any
Sobolev certificate. The singular point is removed only in the almost everywhere identity. -/
lemma exists_distance_power_fourier_remainder (a : RieszExponent) :
    ∃ h : UnitAddCircle → ℂ, Continuous h ∧
      ((fun x : UnitAddCircle => ((dist x 0 ^ (-a.val) : ℝ) : ℂ)) =ᵐ[volume]
        fun x => (rieszRepresentative a x : ℂ) + h x) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ k : ℤ, k ≠ 0 →
        ‖fourierCoeff h k‖ ≤ K * |(k : ℝ)| ^ (-1 : ℝ) := by
  obtain ⟨H, hcd, he, hform⟩ := exists_smooth_power_remainder_cell a
  let h : UnitAddCircle → ℂ := AddCircle.liftIco 1 (-(1 / 2 : ℝ)) (fun x => (H x : ℂ))
  have hc : Continuous h := by
    apply AddCircle.liftIco_continuous
    · norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring]
      exact congrArg Complex.ofReal he
    · intro x hx
      exact (Complex.continuous_ofReal.continuousAt.comp
        (hcd x (by simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using hx)).continuousAt).continuousWithinAt
  obtain ⟨K, hK, hdec⟩ := exists_fourierCoeff_liftIco_bound
    (f := fun x => (H x : ℂ)) (a := -(1 / 2 : ℝ))
    (fun x hx => (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (hcd x (by simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using hx))).of_le (by exact_mod_cast le_top))
    (by simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using congrArg Complex.ofReal he)
  refine ⟨h, hc, ?_, K, hK, hdec⟩
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
  have hhz : h x = (H z : ℂ) := by
    rw [← hzx]
    exact AddCircle.liftIco_coe_apply (by
      simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using hz)
  rw [hd, hhz, hform z ⟨hz.1, hz.2.le⟩ hz0, hzx]
  push_cast
  ring

/-- A distance power has the same upper coefficient power as its Riesz singularity. -/
lemma exists_distance_power_coeff_bound (a : RieszExponent) :
    ∃ K : ℝ, 0 < K ∧ ∀ k : ℤ, k ≠ 0 →
      ‖fourierCoeff (fun x : UnitAddCircle => ((dist x 0 ^ (-a.val) : ℝ) : ℂ)) k‖ ≤
        K * |(k : ℝ)| ^ (a.val - 1) := by
  obtain ⟨h, hc, he, K, hK, hdec⟩ := exists_distance_power_fourier_remainder a
  let A := rieszConstant a * (2 * Real.pi) ^ (a.val - 1)
  have hA : 0 < A := mul_pos (rieszConstant_pos a) (by positivity)
  refine ⟨A + K, by positivity, fun k hk => ?_⟩
  have hkg : 1 ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hkp : 0 < |(k : ℝ)| := lt_of_lt_of_le zero_lt_one hkg
  have hg : ‖fourierCoeff (fun x => (rieszRepresentative a x : ℂ)) k‖ =
      A * |(k : ℝ)| ^ (a.val - 1) := by
    rw [fourierCoeff_rieszRepresentative]
    simp only [hk, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (mul_pos (rieszConstant_pos a) (by positivity)),
      Real.mul_rpow (by positivity) (abs_nonneg _)]
    dsimp only [A]
    ring
  have hec := fourierCoeff_congr_ae he k
  have hgi : Integrable (fun x : UnitAddCircle => (rieszRepresentative a x : ℂ))
      AddCircle.haarAddCircle := by
    rw [← volume_eq_haar_circle]
    exact Complex.ofRealCLM.integrable_comp (integrable_rieszRepresentative a)
  have hsum : fourierCoeff (fun x => (rieszRepresentative a x : ℂ) + h x) k =
      fourierCoeff (fun x => (rieszRepresentative a x : ℂ)) k + fourierCoeff h k :=
    congrFun (fourierCoeff.add hgi (integrable_of_continuous_circle hc)) k
  rw [hec, hsum]
  calc
    ‖fourierCoeff (fun x => (rieszRepresentative a x : ℂ)) k + fourierCoeff h k‖
      ≤ ‖fourierCoeff (fun x => (rieszRepresentative a x : ℂ)) k‖ + ‖fourierCoeff h k‖ := norm_add_le _ _
    _ ≤ A * |(k : ℝ)| ^ (a.val - 1) + K * |(k : ℝ)| ^ (-1 : ℝ) := add_le_add hg.le (hdec k hk)
    _ ≤ (A + K) * |(k : ℝ)| ^ (a.val - 1) := by
      have hp := Real.rpow_le_rpow_of_exponent_le hkg (show (-1 : ℝ) ≤ a.val - 1 by linarith [a.2.1])
      nlinarith

end Internal

/-- Subcritical distance powers satisfy (A1) with explicit exponent
`η = (s-a)/2`. Both the L² certificate and the bound are concluded. -/
theorem primitiveRegularity_distance_power (s : RieszExponent) {a : ℝ}
    (ha0 : 0 < a) (ha : a < s.val / 2) :
    ∃ hf : MemLp (fun x : UnitAddCircle => ((dist x 0 ^ (-a) : ℝ) : ℂ)) 2 volume,
      ∃ B : ℝ, 0 < B ∧ PrimitiveRegularity unitLength ((s.val - a) / 2) s.val B
        ⟨fun x => dist x 0 ^ (-a), hf⟩ := by
  let ae : RieszExponent := ⟨a, ha0, by linarith [s.2.2]⟩
  have hf := ((circleSobolev_distance_power_real_iff s ha0).mpr ha).1
  obtain ⟨K, hK, hb⟩ := Internal.exists_distance_power_coeff_bound ae
  refine ⟨hf, ?_⟩
  exact Internal.exists_primitiveRegularity_of_fourier_decay hf hK.le
    (by linarith [s.2.2]) (by linarith [s.2.1]) (by linarith) hb

end Riesz1
