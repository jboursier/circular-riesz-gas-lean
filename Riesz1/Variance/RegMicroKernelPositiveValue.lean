/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelProfileDerivative
public import Riesz1.ToMathlib.CircleIntegrablePowerEnvelope

/-!
# Positive-exponent values of the inverse representative

Estimate the inverse convolution directly, without choosing reference values
on the separate punctured components. Its constant is uniform in the circle
length. This is the value analysis in Lemma 5.3.
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1.Internal

/-- The inverse convolution has the finite-mark value envelope. The density
envelope and `L¹` bound are internal analytic inputs, supplied by the
transport bounds when this result is applied. -/
theorem inverseConv_positive_value_bound (P : Parameters) {α : ℝ}
    (hα : 0 < α) (hα1 : α < P.val.2) (ι : Type*) [Fintype ι] [Nonempty ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℝ) [Fact (0 < L)] (marks : ι → ℝ)
      (q : ℝ → ℝ) (A : ℝ), 0 ≤ A → Measurable q →
      IntegrableOn q (Ioc (-(L/2)) (L/2)) →
      (∫ y in Ioc (-(L/2)) (L/2), |q y|) ≤ A →
      (∀ y : ℝ, (∀ j, (y : AddCircle L) ≠ (marks j : AddCircle L)) →
        |q y| ≤ A * cappedMarkDistance (fun j => (marks j : AddCircle L))
          (y : AddCircle L) ^ (-1 + P.val.2 - α)) →
      ∀ x : ℝ, (∀ j, (x : AddCircle L) ≠ (marks j : AddCircle L)) →
        IntegrableOn (fun y => q y * inverseKernel P L (x-y)) (Ioc (-(L/2)) (L/2)) ∧
        |inverseConv P L q x| ≤ K * A *
          (1 + ∑ j, dist (x : AddCircle L) (marks j : AddCircle L) ^ (-α)) := by
  classical
  let b := 1 - P.val.2 + α
  have hb : 0 < b := by dsimp [b]; linarith [P.property.2.2]
  have hb1 : b < 1 := by dsimp [b]; linarith
  obtain ⟨D, hD, hkernel⟩ := inverseKernel_iteratedDeriv_bound P 0
  obtain ⟨C, hC, hpower⟩ := CirclePowerConvolution.integral_power_envelope_le
    P.property.2.1 P.property.2.2 hb hb1 (by dsimp [b]; linarith) ι
  refine ⟨D*C, mul_pos hD hC, fun L hL marks q A hA hqm hqi hnorm hq x hx => ?_⟩
  have hd (y z : ℝ) : circDist L (y-z) = dist (y : AddCircle L) (z : AddCircle L) := by
    simp only [← dist_coe_zero_eq_circDist, AddCircle.coe_sub, dist_eq_norm, sub_zero]
  have henv : ∀ᵐ y : ℝ ∂(volume.restrict (Ioc (-(L/2)) (L/2))),
      |q y| ≤ A * (1 + ∑ j, circDist L (y-marks j) ^ (-b)) := by
    filter_upwards [ae_restrict_of_ae
      ((CircleSingularity.countable_marked_lifts (T := L) marks).ae_notMem volume)] with y hy
    have hym : ∀ j, (y : AddCircle L) ≠ (marks j : AddCircle L) := by
      simpa only [mem_ofPred_eq, not_exists] using hy
    have hh := (hq y hym).trans (mul_le_mul_of_nonneg_left
      (cappedMarkDistance_rpow_le_one_add_sum _ _ _) hA)
    simpa only [hd, b, show -(1-P.val.2+α) = -1+P.val.2-α by ring] using hh
  obtain ⟨hi, hbound⟩ := hpower L hL.out marks x
    (fun j => by rw [hd]; exact dist_pos.mpr (hx j)) q A hA hqm hqi hnorm henv
  have hker : ∀ᵐ y : ℝ ∂(volume.restrict (Ioc (-(L/2)) (L/2))),
      |q y * inverseKernel P L (x-y)| ≤ D * (circDist L (y-x) ^ (-P.val.2) * |q y|) := by
    filter_upwards [ae_restrict_of_ae
      ((CircleSingularity.countable_marked_lifts (T := L) (fun _ : Unit => x)).ae_notMem volume)] with y hy
    have hyx : (y : AddCircle L) ≠ (x : AddCircle L) := by
      simpa only [mem_ofPred_eq, exists_const, not_false_eq_true] using hy
    have ht : ∀ k : ℤ, x-y ≠ k*L := by
      intro k hk
      have hz : ((x-y : ℝ) : AddCircle L) = 0 :=
        (AddCircle.coe_eq_zero_iff L).mpr ⟨k, by simpa only [zsmul_eq_mul] using hk.symm⟩
      rw [AddCircle.coe_sub] at hz
      exact hyx (sub_eq_zero.mp hz).symm
    have hh := hkernel L (x-y) hL.out ht
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at hh
    have he : latticeDist L (x-y) = circDist L (y-x) := by
      change circDist L (x-y) = circDist L (y-x)
      rw [hd, hd, dist_comm]
    rw [he] at hh
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hh (abs_nonneg _)).trans_eq (by ring)
  have hMi := hi.const_mul D
  have hprod : IntegrableOn (fun y => q y * inverseKernel P L (x-y)) (Ioc (-(L/2)) (L/2)) := by
    refine hMi.mono'
      ((hqm.mul ((measurable_inverseKernel P hL.out).comp (measurable_const.sub measurable_id))).aestronglyMeasurable) ?_
    simpa only [Real.norm_eq_abs] using hker
  refine ⟨hprod, ?_⟩
  have hn := norm_integral_le_of_norm_le
    (f := fun y => q y * inverseKernel P L (x-y)) hMi
    (by simpa only [Real.norm_eq_abs] using hker)
  rw [integral_const_mul] at hn
  change |∫ y in Ioc (-(L/2)) (L/2), q y * inverseKernel P L (x-y)| ≤ _
  rw [← Real.norm_eq_abs]
  apply hn.trans
  have he : 1-P.val.2-b = -α := by dsimp [b]; ring
  simpa only [he, hd, mul_assoc] using mul_le_mul_of_nonneg_left hbound hD.le

end Riesz1.Internal
