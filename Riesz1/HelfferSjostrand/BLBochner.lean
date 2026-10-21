/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BLComparison
public import Riesz1.HelfferSjostrand.BLSecondVariation
public import Mathlib.Probability.Moments.Variance

/-!
# Brascamp–Lieb on bounded open convex domains

This proves Lemma 3.6 by midpoint
second variation, using only the explicit Prékopa–Leindler hypothesis `External.PrekopaLeindler`.
The variational energy equals the inverse-Hessian energy by
`bl_hessian_variational_eq_inverse`. Normalization, integrability, and the
finiteness of both nonnegative integrals are included in the final theorem.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace Riesz1

variable {d : ℕ} {U W : Set (EuclideanSpace ℝ (Fin d))}
variable {V F : EuclideanSpace ℝ (Fin d) → ℝ}

/-- Smooth bounded-domain Brascamp–Lieb, as an inequality of real integrals.
Integrability used by this proof is derived from the stated geometric data. -/
theorem bl_variance_integral_le (hPL : Riesz1.External.PrekopaLeindler) (hd : 0 < d)
    (hU : Bornology.IsBounded U) (ho : IsOpen U) (hne : U.Nonempty) (hc : Convex ℝ U)
    (hW : IsOpen W) (hUW : closure U ⊆ W)
    (hV : ContDiffOn ℝ 2 V W) (hF : ContDiffOn ℝ 2 F W)
    {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h) :
    (∫ x, (F x - ∫ y, F y ∂((volume.restrict U).tilted (fun y => -V y))) ^ 2
        ∂((volume.restrict U).tilted (fun x => -V x))) ≤
      ∫ x, sSup (Set.range (fun h : EuclideanSpace ℝ (Fin d) =>
        2 * fderiv ℝ F x h - fderiv ℝ (fderiv ℝ V) x h h))
        ∂((volume.restrict U).tilted (fun x => -V x)) := by
  let ν := (volume.restrict U).tilted (fun x => -V x)
  let Q (x : EuclideanSpace ℝ (Fin d)) := sSup (Set.range
    (fun h : EuclideanSpace ℝ (Fin d) =>
      2 * fderiv ℝ F x h - fderiv ℝ (fderiv ℝ V) x h h))
  have hVc := hV.continuousOn.mono hUW
  have hFc := hF.continuousOn.mono hUW
  have : IsProbabilityMeasure ν := bl_isProbabilityMeasure hU ho hne hVc
  have hQ : ContinuousOn Q (closure U) :=
    bl_hessian_energy_continuousOn hU hW hUW hV hF hκ hb
  have hQi : Integrable Q ν := bl_hessian_energy_integrable hU ho hne hW hUW hV hF hκ hb
  have hExpF (t : ℝ) : Integrable (fun x => Real.exp (t * F x)) ν :=
    bl_integrable_tilted_of_continuousOn_closure hU ho hVc
      (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hFc))
  have hIF : integrableExpSet F ν = univ := Set.eq_univ_of_forall hExpF
  have hMem : MemLp F 2 ν :=
    memLp_of_mem_interior_integrableExpSet (by simp [hIF]) 2
  have heq : (∫ x, (F x - ∫ y, F y ∂ν) ^ 2 ∂ν) =
      (∫ x, F x ^ 2 ∂ν) - (∫ x, F x ∂ν) ^ 2 := by
    rw [← variance_eq_integral hMem.aemeasurable, variance_eq_sub hMem]
    rfl
  change (∫ x, (F x - ∫ y, F y ∂ν) ^ 2 ∂ν) ≤ ∫ x, Q x ∂ν
  rw [heq]
  apply le_of_forall_pos_le_add
  intro b hbpos
  have hExpQ (t : ℝ) : Integrable (fun x => Real.exp (t * (Q x / 2 + b / 2))) ν :=
    bl_integrable_tilted_of_continuousOn_closure hU ho hVc
      (Real.continuous_exp.comp_continuousOn
        (continuousOn_const.mul ((hQ.div_const 2).add continuousOn_const)))
  have hi := bl_second_variation_mgf hExpF hExpQ
    (bl_mgf_comparison hPL hd hU ho hc hW hUW hV hF hκ hb
      (by positivity : (0 : ℝ) < b / 2))
  rw [integral_add (hQi.div_const 2) (integrable_const (b / 2)), integral_div] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  linarith

/-- Brascamp–Lieb with positive finite normalization, probability of the Gibbs
law, integrability of every displayed observable, finite nonnegative variance
and energy integrals, and their comparison. The variational expression on the
right is identified with the inverse Hessian in `bl_hessian_variational_eq_inverse`. -/
theorem brascamp_lieb_inequality_bochner
    (hPL : Riesz1.External.PrekopaLeindler) (hd : 0 < d)
    (hU : Bornology.IsBounded U) (ho : IsOpen U) (hne : U.Nonempty) (hc : Convex ℝ U)
    (hW : IsOpen W) (hUW : closure U ⊆ W)
    (hV : ContDiffOn ℝ 2 V W) (hF : ContDiffOn ℝ 2 F W)
    {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h) :
    let ν := (volume.restrict U).tilted (fun x => -V x)
    let Q := fun x => sSup (Set.range (fun h : EuclideanSpace ℝ (Fin d) =>
      2 * fderiv ℝ F x h - fderiv ℝ (fderiv ℝ V) x h h))
    let S := fun x => (F x - ∫ y, F y ∂ν) ^ 2
    (0 < ∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x))) ∧
      (∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x))) < ∞ ∧
      IsProbabilityMeasure ν ∧ Integrable F ν ∧ Integrable S ν ∧ Integrable Q ν ∧
      (∫⁻ x, ENNReal.ofReal (S x) ∂ν) < ∞ ∧
      (∫⁻ x, ENNReal.ofReal (Q x) ∂ν) < ∞ ∧
      (∫⁻ x, ENNReal.ofReal (S x) ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (Q x) ∂ν := by
  dsimp only
  have hVc := hV.continuousOn.mono hUW
  have hFc := hF.continuousOn.mono hUW
  obtain ⟨hZpos, hZfin⟩ := bl_normalization_lintegral_bounds hU ho hne hVc
  have hSi := bl_centered_sq_integrable hU ho hVc hFc
  have hQi := bl_hessian_energy_integrable hU ho hne hW hUW hV hF hκ hb
  refine ⟨hZpos, hZfin, bl_isProbabilityMeasure hU ho hne hVc,
    bl_integrable_tilted_of_continuousOn_closure hU ho hVc hFc, hSi, hQi,
    bl_centered_sq_lintegral_lt_top hU ho hVc hFc,
    bl_hessian_energy_lintegral_lt_top hU ho hne hW hUW hV hF hκ hb, ?_⟩
  have hνU : ∀ᵐ x ∂((volume.restrict U).tilted (fun x => -V x)), x ∈ U :=
    (tilted_absolutelyContinuous (volume.restrict U) (fun x => -V x)).ae_le
      (ae_restrict_mem ho.measurableSet)
  have hQpos : ∀ᵐ x ∂((volume.restrict U).tilted (fun x => -V x)),
      0 ≤ sSup (Set.range (fun h : EuclideanSpace ℝ (Fin d) =>
        2 * fderiv ℝ F x h - fderiv ℝ (fderiv ℝ V) x h h)) := by
    filter_upwards [hνU] with x hx
    have hi := (bl_variational_energy_bounds (fderiv ℝ (fderiv ℝ V) x)
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ F x))
      hκ (hb x hx)).1
    simpa only [InnerProductSpace.toDual_symm_apply] using hi
  rw [← ofReal_integral_eq_lintegral_ofReal hSi (Eventually.of_forall (fun x => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hQi hQpos]
  exact ENNReal.ofReal_le_ofReal
    (bl_variance_integral_le hPL hd hU ho hne hc hW hUW hV hF hκ hb)

end Riesz1

end
