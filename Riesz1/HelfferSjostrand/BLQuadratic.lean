/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The quadratic optimization in the Brascamp–Lieb second variation

For a symmetric coercive continuous bilinear form, the variational expression
`sup_h (2 ⟪g, h⟫ - B h h)` equals the inverse quadratic form. The inverse is
the inverse of the Lax–Milgram equivalence. It is defined only with a coercivity
certificate, so no singular inverse is used.

This is an algebraic ingredient of the proof of Lemma 3.6,
not the variance inequality.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {B : E →L[ℝ] E →L[ℝ] ℝ}

omit [CompleteSpace E] in
/-- A coercive form has a nonnegative diagonal. -/
theorem bl_bilin_self_nonneg (hB : IsCoercive B) (h : E) : 0 ≤ B h h := by
  obtain ⟨c, hc, hbound⟩ := hB
  exact (by positivity : 0 ≤ c * ‖h‖ * ‖h‖).trans (hbound h)

/-- Completing the square, with the inverse defined by Lax–Milgram. -/
theorem bl_quadratic_complete_square (hB : IsCoercive B)
    (hs : ∀ v w, B v w = B w v) (g h : E) :
    2 * ⟪g, h⟫_ℝ - B h h =
      ⟪g, hB.continuousLinearEquivOfBilin.symm g⟫_ℝ -
        B (h - hB.continuousLinearEquivOfBilin.symm g)
          (h - hB.continuousLinearEquivOfBilin.symm g) := by
  let u := hB.continuousLinearEquivOfBilin.symm g
  have hu (w : E) : B u w = ⟪g, w⟫_ℝ := by
    rw [← hB.continuousLinearEquivOfBilin_apply u w]
    simp [u]
  change 2 * ⟪g, h⟫_ℝ - B h h = ⟪g, u⟫_ℝ - B (h - u) (h - u)
  simp only [map_sub, sub_apply, hs h u, hu]
  ring

/-- The inverse quadratic form bounds every value of the variational expression. -/
theorem bl_quadratic_le_inverse (hB : IsCoercive B)
    (hs : ∀ v w, B v w = B w v) (g h : E) :
    2 * ⟪g, h⟫_ℝ - B h h ≤ ⟪g, hB.continuousLinearEquivOfBilin.symm g⟫_ℝ := by
  rw [bl_quadratic_complete_square hB hs]
  exact sub_le_self _ (bl_bilin_self_nonneg hB _)

/-- The inverse quadratic form is attained and is the supremum, not a default value
of a conditionally complete supremum. -/
theorem bl_quadratic_isGreatest (hB : IsCoercive B)
    (hs : ∀ v w, B v w = B w v) (g : E) :
    IsGreatest (Set.range (fun h : E => 2 * ⟪g, h⟫_ℝ - B h h))
      ⟪g, hB.continuousLinearEquivOfBilin.symm g⟫_ℝ := by
  refine ⟨⟨hB.continuousLinearEquivOfBilin.symm g, ?_⟩, ?_⟩
  · dsimp only
    rw [bl_quadratic_complete_square hB hs]
    simp
  · rintro _ ⟨h, rfl⟩
    exact bl_quadratic_le_inverse hB hs g h

/-- Identification of the variational energy with the explicit inverse energy. -/
theorem bl_quadratic_sSup_eq_inverse (hB : IsCoercive B)
    (hs : ∀ v w, B v w = B w v) (g : E) :
    sSup (Set.range (fun h : E => 2 * ⟪g, h⟫_ℝ - B h h)) =
      ⟪g, hB.continuousLinearEquivOfBilin.symm g⟫_ℝ :=
  (bl_quadratic_isGreatest hB hs g).csSup_eq

/-- Nonnegativity of the inverse energy. -/
theorem bl_inverse_energy_nonneg (hB : IsCoercive B) (g : E) :
    0 ≤ ⟪g, hB.continuousLinearEquivOfBilin.symm g⟫_ℝ := by
  have h := bl_bilin_self_nonneg hB (hB.continuousLinearEquivOfBilin.symm g)
  rwa [← hB.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply]
    at h

omit [CompleteSpace E] in
/-- The sharp scalar bound on the variational energy from a uniform coercivity bound. -/
theorem bl_quadratic_le_norm_sq_div {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ h, κ * ‖h‖ ^ 2 ≤ B h h) (g h : E) :
    2 * ⟪g, h⟫_ℝ - B h h ≤ ‖g‖ ^ 2 / κ := by
  have hinner := real_inner_le_norm g h
  have hsq : 0 ≤ (‖g‖ - κ * ‖h‖) ^ 2 := sq_nonneg _
  apply (le_div_iff₀ hκ).2
  nlinarith [hb h]

/-- The inverse energy is finite and bounded by `‖g‖² / κ`. -/
theorem bl_inverse_energy_le_norm_sq_div (hB : IsCoercive B)
    (hs : ∀ v w, B v w = B w v) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ h, κ * ‖h‖ ^ 2 ≤ B h h) (g : E) :
    ⟪g, hB.continuousLinearEquivOfBilin.symm g⟫_ℝ ≤ ‖g‖ ^ 2 / κ := by
  have h := bl_quadratic_le_norm_sq_div hκ hb g (hB.continuousLinearEquivOfBilin.symm g)
  rw [bl_quadratic_complete_square hB hs] at h
  simpa using h

end Riesz1

end
