/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BLQuadratic
public import Riesz1.HelfferSjostrand.BLNormalization
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Finiteness of the variational Brascamp–Lieb energy

The supremum of the quadratic objective is measurable on the domain by
lower semicontinuity and is bounded by the squared norm of the linear term
divided by the coercivity parameter. This proves integrability without any
assumption of integrability of the desired right side.
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace Riesz1

variable {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
variable {V : EuclideanSpace ℝ (Fin d) → ℝ}

/-- Bounds on the variational quadratic expression, including existence of finite
upper bounds needed for the conditionally complete supremum. -/
theorem bl_variational_energy_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (g : E) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ h, κ * ‖h‖ ^ 2 ≤ B h h) :
    0 ≤ sSup (Set.range (fun h : E => 2 * ⟪g, h⟫_ℝ - B h h)) ∧
      sSup (Set.range (fun h : E => 2 * ⟪g, h⟫_ℝ - B h h)) ≤ ‖g‖ ^ 2 / κ := by
  have hbdd : BddAbove (Set.range (fun h : E => 2 * ⟪g, h⟫_ℝ - B h h)) := by
    refine ⟨‖g‖ ^ 2 / κ, ?_⟩
    rintro _ ⟨h, rfl⟩
    exact bl_quadratic_le_norm_sq_div hκ hb g h
  constructor
  · have hz : (0 : ℝ) ∈ Set.range (fun h : E => 2 * ⟪g, h⟫_ℝ - B h h) :=
      ⟨0, by simp⟩
    exact le_csSup hbdd hz
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨h, rfl⟩
    exact bl_quadratic_le_norm_sq_div hκ hb g h

/-- Finiteness of the variational energy under the Gibbs law, for continuous
fields and a uniformly coercive form on the domain. -/
theorem bl_variational_energy_integrable
    (hU : Bornology.IsBounded U) (ho : IsOpen U) (hne : U.Nonempty)
    (hV : ContinuousOn V (closure U))
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (B : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hg : ContinuousOn g (closure U)) (hB : ContinuousOn B (closure U))
    {κ : ℝ} (hκ : 0 < κ) (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ B x h h) :
    Integrable (fun x => sSup (Set.range
      (fun h : EuclideanSpace ℝ (Fin d) => 2 * ⟪g x, h⟫_ℝ - B x h h)))
      ((volume.restrict U).tilted (fun x => -V x)) := by
  let Q (x : EuclideanSpace ℝ (Fin d)) := sSup (Set.range
    (fun h : EuclideanSpace ℝ (Fin d) => 2 * ⟪g x, h⟫_ℝ - B x h h))
  have hQ : LowerSemicontinuousOn Q U := by
    apply lowerSemicontinuousOn_ciSup
    · intro x hx
      refine ⟨‖g x‖ ^ 2 / κ, ?_⟩
      rintro _ ⟨h, rfl⟩
      exact bl_quadratic_le_norm_sq_div hκ (hb x hx) (g x) h
    · intro h
      apply ContinuousOn.lowerSemicontinuousOn
      exact (continuousOn_const.mul ((hg.mono subset_closure).inner continuousOn_const)).sub
        (((hB.mono subset_closure).clm_apply continuousOn_const).clm_apply continuousOn_const)
  have hmeas : AEMeasurable Q (volume.restrict U) :=
    aemeasurable_restrict_of_measurable_subtype ho.measurableSet
      (lowerSemicontinuous_restrict_iff.mpr hQ).measurable
  have hν := tilted_absolutelyContinuous (volume.restrict U) (fun x => -V x)
  have hQmeas : AEStronglyMeasurable Q ((volume.restrict U).tilted (fun x => -V x)) :=
    (hmeas.mono_ac hν).aestronglyMeasurable
  have hmem : ∀ᵐ x ∂((volume.restrict U).tilted (fun x => -V x)), x ∈ U :=
    hν.ae_le (ae_restrict_mem ho.measurableSet)
  have := bl_isProbabilityMeasure hU ho hne hV
  obtain ⟨M, hM⟩ := (hU.isCompact_closure.image_of_continuousOn hg).isBounded.exists_norm_le
  apply (integrable_const (M ^ 2 / κ)).mono' hQmeas
  filter_upwards [hmem] with x hx
  obtain ⟨hpos, hbound⟩ := bl_variational_energy_bounds (B x) (g x) hκ (hb x hx)
  rw [Real.norm_eq_abs, abs_of_nonneg hpos]
  exact hbound.trans (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (hM _ (Set.mem_image_of_mem g (subset_closure hx))) 2) hκ.le)

/-- The variational right side is integrable under precisely the regularity and
coercivity assumptions in the smooth bounded-domain checkpoint. -/
theorem bl_hessian_energy_integrable {W : Set (EuclideanSpace ℝ (Fin d))}
    {F : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : Bornology.IsBounded U) (ho : IsOpen U) (hne : U.Nonempty)
    (hW : IsOpen W) (hUW : closure U ⊆ W)
    (hV : ContDiffOn ℝ 2 V W) (hF : ContDiffOn ℝ 2 F W)
    {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h) :
    Integrable (fun x => sSup (Set.range (fun h : EuclideanSpace ℝ (Fin d) =>
      2 * fderiv ℝ F x h - fderiv ℝ (fderiv ℝ V) x h h)))
      ((volume.restrict U).tilted (fun x => -V x)) := by
  have hFc : ContinuousOn (fderiv ℝ F) (closure U) :=
    (hF.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hUW
  have hV1 : ContDiffOn ℝ 1 (fderiv ℝ V) W := hV.fderiv_of_isOpen hW (by norm_num)
  have hVc : ContinuousOn (fderiv ℝ (fderiv ℝ V)) (closure U) :=
    (hV1.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hUW
  have hi := bl_variational_energy_integrable hU ho hne (hV.continuousOn.mono hUW)
    (fun x => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ F x))
    (fderiv ℝ (fderiv ℝ V))
    ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.comp_continuousOn hFc)
    hVc hκ hb
  simpa only [InnerProductSpace.toDual_symm_apply] using hi

/-- At every point of the domain, the variational Hessian energy equals the
gradient paired with its image under the actual inverse Hessian. The coercivity
certificate defining that inverse is a conclusion. -/
theorem bl_hessian_variational_eq_inverse {W : Set (EuclideanSpace ℝ (Fin d))}
    {F : EuclideanSpace ℝ (Fin d) → ℝ} (hW : IsOpen W) (hUW : U ⊆ W)
    (hV : ContDiffOn ℝ 2 V W) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U) :
    ∃ hB : IsCoercive (fderiv ℝ (fderiv ℝ V) x),
      sSup (Set.range (fun h : EuclideanSpace ℝ (Fin d) =>
        2 * fderiv ℝ F x h - fderiv ℝ (fderiv ℝ V) x h h)) =
        ⟪(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ F x),
          hB.continuousLinearEquivOfBilin.symm
            ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ F x))⟫_ℝ := by
  have hB : IsCoercive (fderiv ℝ (fderiv ℝ V) x) :=
    ⟨κ, hκ, fun h => by simpa only [pow_two, mul_assoc] using hb x hx h⟩
  refine ⟨hB, ?_⟩
  have hs : ∀ v w, fderiv ℝ (fderiv ℝ V) x v w = fderiv ℝ (fderiv ℝ V) x w v :=
    (hV.contDiffAt (hW.mem_nhds (hUW hx))).isSymmSndFDerivAt (by simp)
  simpa only [InnerProductSpace.toDual_symm_apply] using
    bl_quadratic_sSup_eq_inverse hB hs
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ F x))

/-- Finiteness of the nonnegative extended real Hessian energy integral. -/
theorem bl_hessian_energy_lintegral_lt_top {W : Set (EuclideanSpace ℝ (Fin d))}
    {F : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : Bornology.IsBounded U) (ho : IsOpen U) (hne : U.Nonempty)
    (hW : IsOpen W) (hUW : closure U ⊆ W)
    (hV : ContDiffOn ℝ 2 V W) (hF : ContDiffOn ℝ 2 F W)
    {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h) :
    (∫⁻ x, ENNReal.ofReal (sSup (Set.range (fun h : EuclideanSpace ℝ (Fin d) =>
      2 * fderiv ℝ F x h - fderiv ℝ (fderiv ℝ V) x h h)))
      ∂((volume.restrict U).tilted (fun x => -V x))) < ∞ := by
  have hi := bl_hessian_energy_integrable hU ho hne hW hUW hV hF hκ hb
  have hmem : ∀ᵐ x ∂((volume.restrict U).tilted (fun x => -V x)), x ∈ U :=
    (tilted_absolutelyContinuous (volume.restrict U) (fun x => -V x)).ae_le
      (ae_restrict_mem ho.measurableSet)
  have hn : ∀ᵐ x ∂((volume.restrict U).tilted (fun x => -V x)),
      0 ≤ sSup (Set.range (fun h : EuclideanSpace ℝ (Fin d) =>
        2 * fderiv ℝ F x h - fderiv ℝ (fderiv ℝ V) x h h)) := by
    filter_upwards [hmem] with x hx
    have h := (bl_variational_energy_bounds (fderiv ℝ (fderiv ℝ V) x)
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ F x))
      hκ (hb x hx)).1
    simpa only [InnerProductSpace.toDual_symm_apply] using h
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  exact ENNReal.ofReal_lt_top

end Riesz1

end
