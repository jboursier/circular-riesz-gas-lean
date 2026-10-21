/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-! # Linear variational inverses on a normalization kernel

The construction is made for an abstract Hilbert space, so that applications
to completions need only provide their norm estimate and existing form.
-/

public section

noncomputable section

open InnerProductSpace

namespace Riesz1.Internal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (M : V →L[ℝ] ℝ) (B : V →L[ℝ] V →L[ℝ] ℝ) (C : ℝ) (hC : 0 < C)
  (hP : ∀ u : V, M u = 0 → ‖u‖ ^ 2 ≤ C * B u u)

def normalizedInverseBilinear : M.ker →L[ℝ] M.ker →L[ℝ] ℝ :=
  B.bilinearComp M.ker.subtypeL M.ker.subtypeL

omit [CompleteSpace V] in
include C hC hP in
theorem normalizedInverse_coercive : IsCoercive (normalizedInverseBilinear M B) := by
  refine ⟨C⁻¹, inv_pos.mpr hC, fun u => ?_⟩
  have hp := hP u.val u.property
  change C⁻¹ * ‖u.val‖ * ‖u.val‖ ≤ B u.val u.val
  nlinarith [mul_le_mul_of_nonneg_left hp (inv_pos.mpr hC).le, inv_mul_cancel₀ hC.ne']

/-- Invert the coercive restriction, retaining the original normalization carrier. -/
def normalizedVariationalInverse : StrongDual ℝ V →ₗ[ℝ] M.ker := by
  have : CompleteSpace M.ker := M.isClosed_ker.completeSpace_coe
  let e := (normalizedInverse_coercive M B C hC hP).continuousLinearEquivOfBilin.symm.toLinearMap
  let d := (toDual ℝ M.ker).symm.toLinearMap
  let r : StrongDual ℝ V →ₗ[ℝ] StrongDual ℝ M.ker :=
    ((ContinuousLinearMap.compL ℝ M.ker V ℝ).flip M.ker.subtypeL).toLinearMap
  exact e.comp (d.comp r)

theorem normalizedVariationalInverse_solves (f : StrongDual ℝ V) (w : M.ker) :
    B (normalizedVariationalInverse M B C hC hP f).val w.val = f w.val := by
  have : CompleteSpace M.ker := M.isClosed_ker.completeSpace_coe
  let hB := normalizedInverse_coercive M B C hC hP
  change normalizedInverseBilinear M B
    (hB.continuousLinearEquivOfBilin.symm ((toDual ℝ M.ker).symm (f.comp M.ker.subtypeL))) w = _
  rw [← hB.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact congrArg (fun g : StrongDual ℝ M.ker => g w)
    ((toDual ℝ M.ker).apply_symm_apply (f.comp M.ker.subtypeL))

theorem normalizedVariationalInverse_unique (f : StrongDual ℝ V) (u : M.ker)
    (hu : ∀ w : M.ker, B u.val w.val = f w.val) :
    u = normalizedVariationalInverse M B C hC hP f := by
  have : CompleteSpace M.ker := M.isClosed_ker.completeSpace_coe
  let hB := normalizedInverse_coercive M B C hC hP
  apply hB.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro w
  rw [hB.continuousLinearEquivOfBilin_apply, hB.continuousLinearEquivOfBilin_apply]
  change B u.val w.val = B (normalizedVariationalInverse M B C hC hP f).val w.val
  rw [hu, normalizedVariationalInverse_solves]

theorem normalizedVariationalInverse_complete_square
    (hs : ∀ u w, B u w = B w u) (f : StrongDual ℝ V) (w : M.ker) :
    B w.val w.val - 2 * f w.val =
      -f (normalizedVariationalInverse M B C hC hP f).val +
        B (w - normalizedVariationalInverse M B C hC hP f).val
          (w - normalizedVariationalInverse M B C hC hP f).val := by
  let u := normalizedVariationalInverse M B C hC hP f
  have hu := normalizedVariationalInverse_solves M B C hC hP f
  change B w.val w.val - 2 * f w.val = -f u.val + B (w.val - u.val) (w.val - u.val)
  simp only [map_sub, sub_apply]
  rw [hs w.val u.val, hu w, hu u]
  ring

theorem normalizedVariationalInverse_minimizer_iff
    (hs : ∀ u w, B u w = B w u) (f : StrongDual ℝ V) (u : M.ker) :
    (∀ w : M.ker, B u.val u.val - 2 * f u.val ≤ B w.val w.val - 2 * f w.val) ↔
      u = normalizedVariationalInverse M B C hC hP f := by
  let v := normalizedVariationalInverse M B C hC hP f
  have he := normalizedVariationalInverse_complete_square M B C hC hP hs f
  have hv : B v.val v.val - 2 * f v.val = -f v.val := by
    have hv := normalizedVariationalInverse_solves M B C hC hP f v
    change B v.val v.val = f v.val at hv
    linarith only [hv]
  constructor
  · intro hmin
    have hm := hmin v
    rw [he u, hv] at hm
    have hq : B (u - v).val (u - v).val ≤ 0 := by linarith only [hm]
    have hb := hP (u - v).val (u - v).property
    have hn : ‖(u - v).val‖ = 0 := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hC.le hq, norm_nonneg (u - v).val]
    apply sub_eq_zero.mp
    exact Subtype.ext (norm_eq_zero.mp hn)
  · rintro rfl w
    rw [hv, he w]
    have hb := hP (w - v).val (w - v).property
    have hq : 0 ≤ B (w - v).val (w - v).val := by
      nlinarith [sq_nonneg ‖(w - v).val‖]
    exact le_add_of_nonneg_right hq

end Riesz1.Internal
