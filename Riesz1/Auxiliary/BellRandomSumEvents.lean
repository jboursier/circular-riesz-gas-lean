/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellRandomSumWeights

/-!
# Splitting a kernel comparison into good and bad events

The good event has a uniform pointwise bound. Cauchy--Schwarz on the bad event
uses the second moment of the inverse-power bound and the event probability.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- Integrate a good-event bound and use a second moment on the bad event. -/
lemma bell_integral_good_bad {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f W : Ω → ℝ}
    (hi : Integrable f μ) (hW : AEStronglyMeasurable W μ)
    (hW0 : ∀ x, 0 ≤ W x) (hiW : Integrable (fun x => W x ^ 2) μ)
    {E : Set Ω} (hE : MeasurableSet E) {A G M T : ℝ}
    (hA : 0 ≤ A) (hG : 0 ≤ G)
    (hgood : ∀ x ∈ Eᶜ, |f x| ≤ G) (hpoint : ∀ x, |f x| ≤ A * W x)
    (hmom : (∫ x, W x ^ 2 ∂μ) ≤ M) (hprob : μ.real E ≤ T) :
    |∫ x, f x ∂μ| ≤ G + A * (Real.sqrt M * Real.sqrt T) := by
  have hiW' := ((memLp_two_iff_integrable_sq hW).mpr hiW).integrable (by norm_num)
  have hg : (∫ x in Eᶜ, |f x| ∂μ) ≤ G := by
    calc _ ≤ ∫ _x in Eᶜ, G ∂μ :=
          setIntegral_mono_on hi.abs.integrableOn (integrable_const _) hE.compl hgood
      _ = μ.real Eᶜ * G := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ G := (mul_le_mul_of_nonneg_right measureReal_le_one hG).trans_eq (one_mul _)
  have hb : (∫ x in E, |f x| ∂μ) ≤ A * (Real.sqrt M * Real.sqrt T) := by
    have hcs := integral_on_event_le_second_moment hW hW0 hiW hE
    simp only [← Real.sqrt_eq_rpow] at hcs
    calc _ ≤ ∫ x in E, A * W x ∂μ :=
          setIntegral_mono_on hi.abs.integrableOn (hiW'.const_mul A).integrableOn hE
            (fun x _ => hpoint x)
      _ = A * ∫ x in E, W x ∂μ := integral_const_mul _ _
      _ ≤ A * (Real.sqrt M * Real.sqrt T) :=
          mul_le_mul_of_nonneg_left (hcs.trans (mul_le_mul
            (Real.sqrt_le_sqrt hmom) (Real.sqrt_le_sqrt hprob)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) hA
  calc _ ≤ ∫ x, |f x| ∂μ := abs_integral_le_integral_abs
    _ = (∫ x in E, |f x| ∂μ) + ∫ x in Eᶜ, |f x| ∂μ :=
      (integral_add_compl hE hi.abs).symm
    _ ≤ _ := by linarith

/-- The two kernel values are bounded by inverse powers of the block and its complement. -/
lemma bell_kernel_value_weight {s C : ℝ} {N : ℕ+} {ℓ : ℝ} {ψ : ℝ → ℝ}
    (hℓ : 0 < ℓ) (hC : 0 ≤ C)
    (hq : ∀ y ∈ Ioo (0 : ℝ) N,
      |bellKernel s N ℓ ψ y| ≤ C * bellConstant ℓ ψ * min y ((N : ℝ) - y) ^ (-s))
    (j : ℤ) {k : ℕ} (hk : 0 < k) (hkN : k < (N : ℕ)) (X : Configuration N) :
    |bellKernel s N ℓ ψ (blockLength X j k) - bellKernel s N ℓ ψ (k : ℝ)| ≤
      C * bellConstant ℓ ψ * bellValueWeight s j k X := by
  have hx := bell_block_mem X j hk hkN
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hkR : (k : ℝ) < N := by exact_mod_cast hkN
  have hA : 0 ≤ C * bellConstant ℓ ψ :=
    mul_nonneg hC (mul_nonneg hℓ.le (bellEnergy_nonneg hℓ))
  have h1 := (hq _ hx).trans (mul_le_mul_of_nonneg_left
    (rpow_min_le_add _ _ _ hx.1 (sub_pos.mpr hx.2)) hA)
  have h2 := (hq _ ⟨hk0, hkR⟩).trans (mul_le_mul_of_nonneg_left
    (rpow_min_le_add _ _ _ hk0 (sub_pos.mpr hkR)) hA)
  rw [← bell_block_complement X j hkN.le] at h1
  rw [← Nat.cast_sub hkN.le] at h2
  exact (abs_sub _ _).trans ((add_le_add h1 h2).trans_eq (by unfold bellValueWeight; ring))

end Riesz1

end
