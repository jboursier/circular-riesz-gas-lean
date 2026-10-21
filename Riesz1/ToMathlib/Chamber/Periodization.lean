/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Instances.Int

/-!
# Smooth periodization along a nonzero vector

Compactly supported smooth functions can be periodized along an integer
translation. The sum is locally finite, so this construction introduces
no convergence convention. It agrees with the original function on a
fundamental strip when the original support lies in that strip.
-/

@[expose] public section

noncomputable section

open Set Function Filter Metric Topology
open scoped ContDiff Manifold

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem locallyFinite_vector_translates {v : E} (hv : v ≠ 0) {f : E → ℝ}
    (hf : HasCompactSupport f) :
    LocallyFinite (fun k : ℤ => support (fun x => f (x + (k : ℝ) • v))) := by
  obtain ⟨C, hC⟩ := hf.isCompact.isBounded.exists_norm_le
  intro x
  let R := (C + ‖x‖ + 1) / ‖v‖
  have hfin : {k : ℤ | ‖k‖ ≤ R}.Finite := by
    simpa only [closedBall, dist_zero_right] using
      (isCompact_closedBall (0 : ℤ) R).finite_of_discrete
  refine ⟨ball x 1, ball_mem_nhds x zero_lt_one, hfin.subset ?_⟩
  rintro k ⟨y, hy, hyx⟩
  have hsum : ‖y + (k : ℝ) • v‖ ≤ C := hC _ (subset_closure hy)
  have hybound : ‖y‖ < ‖x‖ + 1 := by
    have := norm_sub_norm_le y x
    rw [← dist_eq_norm] at this
    linarith [mem_ball.mp hyx]
  have hk : ‖(k : ℝ) • v‖ ≤ ‖y + (k : ℝ) • v‖ + ‖y‖ := by
    simpa only [add_sub_cancel_left] using norm_sub_le (y + (k : ℝ) • v) y
  have hk' : |(k : ℝ)| ≤ R := by
    apply (le_div_iff₀ (norm_pos_iff.mpr hv)).mpr
    rw [norm_smul, Real.norm_eq_abs] at hk
    linarith
  simpa only [mem_ofPred_eq, Int.norm_eq_abs, Int.cast_abs] using hk'

/-- Integer periodization along a nonzero vector. Compact support guarantees
that the defining sum has finite support at every point. -/
def vectorPeriodize (v : E) (_hv : v ≠ 0) (f : E → ℝ) (_hs : HasCompactSupport f)
    (x : E) : ℝ := ∑ᶠ k : ℤ, f (x + (k : ℝ) • v)

theorem vectorPeriodize_finite_support {v : E} (hv : v ≠ 0) {f : E → ℝ}
    (hs : HasCompactSupport f) (x : E) :
    HasFiniteSupport (fun k : ℤ => f (x + (k : ℝ) • v)) :=
  (locallyFinite_vector_translates hv hs).point_finite x

theorem vectorPeriodize_periodic (v : E) (hv : v ≠ 0) (f : E → ℝ)
    (hs : HasCompactSupport f) (k : ℤ) (x : E) :
    vectorPeriodize v hv f hs (x + (k : ℝ) • v) = vectorPeriodize v hv f hs x := by
  unfold vectorPeriodize
  convert finsum_comp_equiv (Equiv.addRight k) (f := fun n : ℤ => f (x + (n : ℝ) • v)) using 1
  congr 1
  funext n
  simp only [Equiv.coe_addRight, Int.cast_add, add_smul]
  congr 1
  abel

theorem contDiff_vectorPeriodize {v : E} (hv : v ≠ 0) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ContDiff ℝ ∞ (vectorPeriodize v hv f hs) := by
  rw [← contMDiff_iff_contDiff]
  exact contMDiff_finsum (fun k =>
    (contMDiff_iff_contDiff.mpr (hf.comp (contDiff_id.add contDiff_const))))
    (locallyFinite_vector_translates hv hs)

/-- Periodization does not change a test on a fundamental strip containing its support. -/
theorem vectorPeriodize_eq_on_strip {v : E} (hv : v ≠ 0)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1)
    {f : E → ℝ} (hs : HasCompactSupport f) (hf : support f ⊆ ℓ ⁻¹' Ioo (0 : ℝ) 1)
    {x : E} (hx : ℓ x ∈ Ico (0 : ℝ) 1) : vectorPeriodize v hv f hs x = f x := by
  unfold vectorPeriodize
  rw [finsum_eq_single _ 0]
  · simp
  · intro k hk
    by_contra hne
    have h := hf hne
    simp only [mem_preimage, map_add, map_smul, hℓ, smul_eq_mul, mul_one, mem_Ioo] at h
    have hklo : (-1 : ℝ) < (k : ℝ) := by linarith [hx.2]
    have hkhi : (k : ℝ) < 1 := by linarith [hx.1]
    have hklo' : (-1 : ℤ) < k := by exact_mod_cast hklo
    have hkhi' : k < 1 := by exact_mod_cast hkhi
    omega

end Riesz1

end
