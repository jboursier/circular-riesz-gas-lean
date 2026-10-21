/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopAnchoringRegularity
public import Riesz1.Auxiliary.LoopLocalMomentsRegularity

/-!
# Microscopic rescaling for the anchoring path

Identities connecting the localized microscopic loop to the
gradient loop, for the anchoring part of Lemma 5.8.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- The chain-rule rescaling of the microscopic kernel, on the whole real
line with the usual derivative convention at singular points. -/
theorem loopAnchoring_deriv_scaled_kernel (s : ℝ) (N : ℕ+) (r : ℝ) :
    deriv (loopArcG s N) r =
      (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * deriv (hurwitzKernel s) (r / N)) := by
  unfold loopArcG
  rw [deriv_const_mul_field]
  have he : (fun x : ℝ => hurwitzKernel s (x / N)) =
      (fun x : ℝ => hurwitzKernel s ((N : ℝ)⁻¹ * x)) := by
    funext x
    rw [div_eq_mul_inv, mul_comm]
  rw [he, deriv_comp_mul_left]
  simp only [smul_eq_mul]
  congr 2
  rw [div_eq_mul_inv, mul_comm]

/-- A microscopic pair term rescales to the gradient pair kernel. -/
theorem loopAnchoring_pair_rescale (s ℓ : ℝ) (N : ℕ+) (ψ : ℝ → ℝ)
    (x y : ℝ) :
    loopArcKernel s N (loopScaleField ((N : ℝ) * ℓ) ψ) ((N : ℝ) * x) ((N : ℝ) * y) =
      (N : ℝ) ^ (-s) * gradPairKernel s ψ ℓ x y := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  have hx : (N : ℝ) * x / ((N : ℝ) * ℓ) = x / ℓ := mul_div_mul_left _ _ hN
  have hy : (N : ℝ) * y / ((N : ℝ) * ℓ) = y / ℓ := mul_div_mul_left _ _ hN
  have hr : ((N : ℝ) * x - (N : ℝ) * y) / N = x - y := by field_simp
  unfold loopArcKernel loopScaleField gradPairKernel
  rw [loopAnchoring_deriv_scaled_kernel, hx, hy, hr,
    show x - y = -(y - x) by ring, deriv_hurwitzKernel_neg']
  field_simp
  ring

/-- Cyclic lifts of the preceding anchor retain exactly the original real
lift minus the preceding particle. -/
theorem loopAnchoring_lift_preceding {N : ℕ+} (X : LoopPrecedingConfiguration N) (i : ℤ) :
    gradLift N (loopPrecedingY X) i =
      cyclicLift X.val (loopPrecedingLabel X + i) - cyclicLift X.val (loopPrecedingLabel X) := by
  have hN : (0 : ℤ) < N := by exact_mod_cast N.pos
  have hmod : (((gradIndex N i).val : ℕ) : ℤ) = i % (N : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg i hN.ne')
  have hi : loopPrecedingLabel X + i =
      (loopPrecedingLabel X + i % (N : ℤ)) + (N : ℤ) * (i / (N : ℤ)) := by
    have := Int.emod_add_mul_ediv i (N : ℤ)
    omega
  rw [hi, boundary_cyclicLift_add_mul]
  simp only [gradLift, loopPrecedingY, hmod]
  ring

/-- Every point of the physical path has microscopic lift `z_i + v`. -/
theorem loopAnchoring_path_lift {N : ℕ+} (X : LoopPrecedingConfiguration N) (v : ℝ) (i : ℤ) :
    (N : ℝ) * gradLift N
      (fun k => loopPrecedingY X k + (v - loopPrecedingD X) / N) i =
      loopPrecedingLift X i + v := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  rw [gradLift_add_const, loopAnchoring_lift_preceding]
  unfold loopPrecedingLift loopPrecedingD
  field_simp
  ring

/-- The preceding anchor belongs to the ordered chart for every particle
number, including one. -/
theorem loopAnchoring_preceding_mem {N : ℕ+} (X : LoopPrecedingConfiguration N) :
    loopPrecedingY X ∈ orderedDomain N := by
  have hmono := cyclicLift_strictMono X.val
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    dsimp [loopPrecedingY]
    apply sub_lt_sub_right
    apply hmono
    have hij' : (i.val : ℤ) < j.val := by exact_mod_cast hij
    omega
  · rw [loopPrecedingY_zero]
  · rw [loopPrecedingY_zero]
    norm_num
  · intro i
    rw [loopPrecedingY_zero]
    have hi : (i.val : ℤ) < N := by exact_mod_cast i.isLt
    have h := hmono (show loopPrecedingLabel X + (i.val : ℤ) < loopPrecedingLabel X + N by omega)
    rw [cyclicLift_add_N] at h
    dsimp [loopPrecedingY]
    linarith

/-- Common translations of the preceding anchor have no circular collisions,
including the negative-anchor interior of the anchoring path. -/
theorem loopAnchoring_path_nonInt {N : ℕ+} {ℓ γ : ℝ} (hℓ : 0 ≤ ℓ)
    (X : LoopPrecedingConfiguration N) (c : ℝ) :
    ∀ i ∈ gradLabels N ℓ γ, ∀ j ∈ gradLabels N ℓ γ, i ≠ j →
      ((gradLift N (fun k => loopPrecedingY X k + c) j -
        gradLift N (fun k => loopPrecedingY X k + c) i : ℝ) : UnitAddCircle) ≠ 0 := by
  intro i hi j hj hij
  simp only [gradLift_add_const, add_sub_add_right_eq_sub]
  exact nonInt_of_mem_orderedDomain hℓ (loopAnchoring_preceding_mem X) i hi j hj hij

/-- The background interval rescales to the fixed physical window. In a
full window, periodicity identifies the fixed and particle-centered periods. -/
theorem loopAnchoring_background_rescale {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {ℓ γ : ℝ} (hℓ : 0 < ℓ) (hp : Function.Periodic ψ ℓ⁻¹)
    (s : ℝ) (N : ℕ+) (x : ℝ) :
    (∫ u in loopLocalLo N ℓ γ..loopLocalHi N ℓ γ,
      loopArcKernel s N (loopScaleField ((N : ℝ) * ℓ) ψ) ((N : ℝ) * x) u) =
        (N : ℝ) ^ (1 - s) * gradBackground s ψ N ℓ γ x := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hpair (y : ℝ) := loopAnchoring_pair_rescale s ℓ N ψ x y
  let lo := loopLocalLo N ℓ γ / (N : ℝ)
  let hi := loopLocalHi N ℓ γ / (N : ℝ)
  have hc := intervalIntegral.integral_comp_mul_left
    (f := fun u => loopArcKernel s N (loopScaleField ((N : ℝ) * ℓ) ψ) ((N : ℝ) * x) u)
    (a := lo) (b := hi) hN.ne'
  simp only [hpair, intervalIntegral.integral_const_mul, smul_eq_mul] at hc
  have helo : (N : ℝ) * lo = loopLocalLo N ℓ γ := mul_div_cancel₀ _ hN.ne'
  have hehi : (N : ℝ) * hi = loopLocalHi N ℓ γ := mul_div_cancel₀ _ hN.ne'
  rw [helo, hehi] at hc
  have hbg : (∫ y in lo..hi, gradPairKernel s ψ ℓ x y) = gradBackground s ψ N ℓ γ x := by
    unfold gradBackground
    simp_rw [gradZ_mul_kernelH hψ hℓ.ne']
    change (∫ y in lo..hi, gradPairKernel s ψ ℓ x y) =
      ∫ y in gradBLo N ℓ γ x..gradBHi N ℓ γ x, gradPairKernel s ψ ℓ x y
    by_cases hP : GradPartial N ℓ γ
    · simp only [lo, hi, loopLocalLo, loopLocalHi, gradBLo, gradBHi, gradT,
        hP, ite_true, neg_div]
    · have hf : Function.Periodic (gradPairKernel s ψ ℓ x) 1 :=
        fun y => gradPairKernel_add_one_right (by simpa only [one_div] using hp) s x y
      simpa only [lo, hi, loopLocalLo, loopLocalHi, gradBLo, gradBHi,
        hP, ite_false, zero_div, div_self hN.ne', zero_add,
        show x - 1 / 2 + 1 = x + 1 / 2 by ring] using hf.intervalIntegral_add_eq 0 (x - 1 / 2)
  rw [hbg] at hc
  have hpow : (N : ℝ) * (N : ℝ) ^ (-s) = (N : ℝ) ^ (1 - s) := by
    calc
      _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-s) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hN]; congr 1
  calc
    _ = (N : ℝ) * ((N : ℝ) ^ (-s) * gradBackground s ψ N ℓ γ x) := by
      rw [hc]
      field_simp
    _ = _ := by rw [← mul_assoc, hpow]

/-- At the start of the physical path, the actual local loop is the actual
gradient loop, with the same transport and fixed background. -/
theorem loopAnchoring_localLoop_eq_gradLoop {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {ℓ γ : ℝ} (hℓ : 0 < ℓ) (hp : Function.Periodic ψ ℓ⁻¹)
    (s : ℝ) (N : ℕ+) (X : LoopPrecedingConfiguration N) :
    loopLocalLoop s N ℓ γ (loopScaleField ((N : ℝ) * ℓ) ψ) X =
      gradLoop s ψ N ℓ γ
        (fun k => loopPrecedingY X k + (0 - loopPrecedingD X) / N) := by
  classical
  let q := fun k => loopPrecedingY X k + (0 - loopPrecedingD X) / N
  have hl (i : ℤ) : loopPrecedingLift X i = (N : ℝ) * gradLift N q i := by
    simpa only [add_zero] using (loopAnchoring_path_lift X 0 i).symm
  change loopLocalLoop s N ℓ γ (loopScaleField ((N : ℝ) * ℓ) ψ) X = gradLoop s ψ N ℓ γ q
  rw [gradLoop_eq_pairs_background hψ hℓ.ne' (by simpa only [one_div] using hp)]
  unfold loopLocalLoop
  simp_rw [hl, loopAnchoring_pair_rescale, loopAnchoring_background_rescale hψ hℓ hp]
  simp only [Finset.mul_sum]
  ring_nf

end Riesz1

end
