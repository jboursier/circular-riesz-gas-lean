/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.BoundedGradientCutoff

/-!
# Smooth cutoffs with uniform bounds

Compactly supported cutoffs of a bounded smooth function with bounded derivative have
uniform value and derivative bounds and eventually agree locally with the original function.
These approximation tools support the proof of the Bakry–Émery criterion.
-/

public section

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Compactly supported smooth approximation, with uniform bounds and eventual local equality. -/
theorem exists_smooth_compact_cutoffs {g : E → ℝ} (hg : ContDiff ℝ ∞ g)
    {K D : ℝ} (hK : ∀ x, |g x| ≤ K) (hD : ∀ x, ‖fderiv ℝ g x‖ ≤ D) :
    ∃ (gn : ℕ → E → ℝ) (B : ℝ),
      (∀ n, ContDiff ℝ ∞ (gn n)) ∧ (∀ n, HasCompactSupport (gn n)) ∧
      (∀ n x, |gn n x| ≤ K) ∧ (∀ n x, ‖fderiv ℝ (gn n) x‖ ≤ B) ∧
      ∀ x, ∀ᶠ n in atTop, gn n =ᶠ[𝓝 x] g := by
  obtain ⟨θ, hθ, hθcs, h01, h1, h2, M, hM⟩ := WeightedSobolev.exists_unit_cutoff (E := E)
  let R (n : ℕ) : ℝ := (n : ℝ) + 1
  have hR (n) : 0 < R n := by dsimp [R]; positivity
  have hR1 (n) : 1 ≤ R n := by dsimp [R]; linarith [Nat.cast_nonneg (α := ℝ) n]
  let a (n : ℕ) (x : E) := θ ((R n)⁻¹ • x)
  have ha (n) : ContDiff ℝ ∞ (a n) := hθ.comp (contDiff_const.smul contDiff_id)
  let gn (n : ℕ) (x : E) := a n x * g x
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  refine ⟨gn, D + K * M, fun n => (ha n).mul hg, ?_, ?_, ?_, ?_⟩
  · intro n
    apply HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * R n))
    intro x hx
    have hx' : 2 * R n < ‖x‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hx
    have hscaled : 2 ≤ ‖(R n)⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hR n).le)]
      apply (le_inv_mul_iff₀ (hR n)).mpr
      linarith
    simp only [gn, a, h2 _ hscaled, zero_mul]
  · intro n x
    change |a n x * g x| ≤ K
    rw [abs_mul, abs_of_nonneg (h01 _).1]
    exact (mul_le_mul_of_nonneg_left (hK x) (h01 _).1).trans
      (mul_le_of_le_one_left hK0 (h01 _).2)
  · intro n x
    have hda : ‖fderiv ℝ (a n) x‖ ≤ M := by
      apply (WeightedSobolev.norm_fderiv_scaled_le (hθ.differentiable (by simp)) hM (hR n) x).trans
      exact div_le_self hM0 (hR1 n)
    rw [show gn n = fun y => a n y * g y from rfl,
      show fderiv ℝ (fun y => a n y * g y) x =
          a n x • fderiv ℝ g x + g x • fderiv ℝ (a n) x from
        fderiv_mul ((ha n).differentiable (by simp) x) (hg.differentiable (by simp) x)]
    apply (norm_add_le _ _).trans
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (h01 _).1]
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_left (hD x) (h01 _).1).trans
        (mul_le_of_le_one_left hD0 (h01 _).2)
    · exact mul_le_mul (hK x) hda (norm_nonneg _) hK0
  · intro x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hx : x ∈ ball (0 : E) (R n) := by
      rw [mem_ball, dist_zero_right]
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      dsimp [R]
      linarith
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    have hymem : (R n)⁻¹ • y ∈ closedBall (0 : E) 1 := by
      rw [mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (hR n).le), inv_mul_le_iff₀ (hR n), mul_one]
      exact (by simpa only [mem_ball, dist_zero_right] using hy : ‖y‖ < R n).le
    simp only [gn, a, h1 _ hymem, one_mul]

omit [FiniteDimensional ℝ E] in
/-- Continuity of the norm of a smooth function's Hessian. -/
theorem continuous_norm_hessian {g : E → ℝ} (hg : ContDiff ℝ ∞ g) :
    Continuous (fun x => ‖fderiv ℝ (fderiv ℝ g) x‖) := by
  have hc : Continuous (fderiv ℝ (fderiv ℝ g)) :=
    ((hg.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp))
  exact @Continuous.norm E (E →L[ℝ] E →L[ℝ] ℝ) inferInstance inferInstance _ hc

/-- A compactly supported smooth function has bounded Hessian norm. -/
theorem exists_norm_hessian_bound {d : ℕ} {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hcs : HasCompactSupport g) : ∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M := by
  have hcs1 : HasCompactSupport (fderiv ℝ g) := hcs.fderiv (𝕜 := ℝ)
  have hcs2 : HasCompactSupport (fderiv ℝ (fderiv ℝ g)) := hcs1.fderiv (𝕜 := ℝ)
  have hcsn : HasCompactSupport (fun x => ‖fderiv ℝ (fderiv ℝ g) x‖) :=
    @HasCompactSupport.norm _ ((EuclideanSpace ℝ (Fin d)) →L[ℝ]
      (EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ) inferInstance inferInstance _ hcs2
  obtain ⟨M, hM⟩ := (continuous_norm_hessian hg).bounded_above_of_compact_support hcsn
  refine ⟨M, fun x => ?_⟩
  have hx := hM x
  change |‖fderiv ℝ (fderiv ℝ g) x‖| ≤ M at hx
  rw [abs_of_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ g) x))] at hx
  exact hx

/-- Compact support gives a global quadratic upper bound on the Hessian of a smooth test. -/
theorem exists_hessian_upper_of_hasCompactSupport {d : ℕ} {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hcs : HasCompactSupport g) :
    ∃ M : ℝ, ∀ x h, (fderiv ℝ (fderiv ℝ g) x h) h ≤ M * ‖h‖ ^ 2 := by
  obtain ⟨M, hM⟩ := exists_norm_hessian_bound hg hcs
  refine ⟨M, fun x h => ?_⟩
  calc (fderiv ℝ (fderiv ℝ g) x h) h
      ≤ ‖(fderiv ℝ (fderiv ℝ g) x h) h‖ := le_abs_self _
    _ ≤ ‖fderiv ℝ (fderiv ℝ g) x h‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖fderiv ℝ (fderiv ℝ g) x‖ * ‖h‖) * ‖h‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ (M * ‖h‖) * ‖h‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)) (norm_nonneg _)
    _ = M * ‖h‖ ^ 2 := by ring

end Riesz1

end
