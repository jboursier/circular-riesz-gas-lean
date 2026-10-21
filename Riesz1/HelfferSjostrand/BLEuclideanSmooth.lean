/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BLBochner
public import Riesz1.HelfferSjostrand.BLEuclideanNormalization
public import Riesz1.HelfferSjostrand.BLEuclideanVariational
public import Riesz1.HelfferSjostrand.BLEuclideanShrink
public import Riesz1.ToMathlib.WeightedSobolev.Completion
public import Riesz1.ToMathlib.WeightedSobolev.L2Facts

/-!
# The Euclidean Brascamp–Lieb inequality for smooth observables

For a function `F` that is smooth on a neighborhood of `closure U`, the Euclidean
Brascamp–Lieb inequality `Var_ν F ≤ ∫ ∇F · (D²V)⁻¹ ∇F dν` holds with `ν ∝ e^{-V} 1_U dx`.
The proof applies the smooth bounded-domain inequality `bl_variance_integral_le` to the shrunken
domains `U_r`, where `V` is `C²` on a neighborhood of the closure, and lets `r ↑ 1`. The variance
and the variational energy both converge under the tilted measures, because `F` and `∇F` are
bounded on `U` and the energy is bounded by `‖∇F‖² / κ`.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff InnerProductSpace

namespace Riesz1

variable {d : ℕ}

/-- A function that is continuous on `U` is in `L²` of the tilted measure, when it is bounded
there. The tilted measure is concentrated on `U`. -/
theorem memLp_tilted_of_bounded {U : Set (EuclideanSpace ℝ (Fin d))}
    {V F : EuclideanSpace ℝ (Fin d) → ℝ} (ho : IsOpen U) (hF : ContinuousOn F U) {C : ℝ}
    (hC : ∀ x ∈ U, ‖F x‖ ≤ C) [IsFiniteMeasure ((volume.restrict U).tilted (fun x => -V x))] :
    MemLp F 2 ((volume.restrict U).tilted (fun x => -V x)) := by
  refine MemLp.of_bound ?_ C ?_
  · exact (hF.aestronglyMeasurable ho.measurableSet).mono_ac
      (tilted_absolutelyContinuous _ _)
  · filter_upwards [(tilted_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem ho.measurableSet)] with x hx
    exact hC x hx

/-- The gradient of a differentiable function is a measurable vector field. -/
theorem measurable_gradient_euclidean (F : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measurable (gradient F) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
    (measurable_fderiv ℝ F)

/-- The Euclidean Brascamp–Lieb inequality for a function smooth near the closure of `U`: the
variance under `ν` is at most the energy `∫ sup_h (2⟪∇F, h⟫ - D²V(h, h)) dν`. -/
theorem bl_euclidean_smooth (hPL : Riesz1.External.PrekopaLeindler) (hd : 0 < d)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : Bornology.IsBounded U) (ho : IsOpen U)
    (hne : U.Nonempty) (hc : Convex ℝ U)
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiffOn ℝ 2 V U) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    {F : EuclideanSpace ℝ (Fin d) → ℝ} (hF : WeightedSobolev.SmoothNearClosure U F) :
    (∫ x, (F x - ∫ y, F y ∂((volume.restrict U).tilted (fun x => -V x))) ^ 2
        ∂((volume.restrict U).tilted (fun x => -V x))) ≤
      ∫ x, sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
        2 * ⟪gradient F x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h)
        ∂((volume.restrict U).tilted (fun x => -V x)) := by
  obtain ⟨W, hW, hUW, hFs⟩ := hF
  obtain ⟨x0, hx0⟩ := hne
  have hF2 : ContDiffOn ℝ 2 F W := hFs.of_le (by norm_num)
  have hF2U : ContDiffOn ℝ 2 F U := hF2.mono (subset_closure.trans hUW)
  -- Continuity and boundedness on the compact closure of `U`.
  have hFc : ContinuousOn F U := (hFs.continuousOn.mono hUW).mono subset_closure
  have hFdc : ContinuousOn (fderiv ℝ F) (closure U) :=
    (hFs.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hUW
  have hgc : ContinuousOn (gradient F) (closure U) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.comp_continuousOn
      hFdc
  obtain ⟨CF, hCF⟩ := hU.isCompact_closure.exists_bound_of_continuousOn
    (hFs.continuousOn.mono hUW)
  obtain ⟨CG, hCG⟩ := hU.isCompact_closure.exists_bound_of_continuousOn hgc
  have hCGu : ∀ x ∈ U, ‖gradient F x‖ ≤ CG := fun x hx => hCG x (subset_closure hx)
  have hCFu : ∀ x ∈ U, ‖F x‖ ≤ CF := fun x hx => hCF x (subset_closure hx)
  -- The energy is bounded on `U` and measurable under the tilted measures.
  have hint := bl_convex_exp_integrableOn hU hc ho ⟨x0, hx0⟩ hV hκ hb
  have hpos := bl_convex_normalization_pos hU hc ho ⟨x0, hx0⟩ hV hκ hb
  have := bl_convex_isProbabilityMeasure hU hc ho ⟨x0, hx0⟩ hV hκ hb
  have hQbound : ∀ x ∈ U, ‖sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
      2 * ⟪gradient F x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h)‖ ≤ CG ^ 2 / κ := by
    intro x hx
    obtain ⟨h0, h1⟩ := bl_variational_energy_bounds (fderiv ℝ (fderiv ℝ V) x)
      (gradient F x) hκ (hb x hx)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    refine h1.trans ?_
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hCGu x hx) 2) hκ.le
  have hQmeas : AEStronglyMeasurable (fun x => sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
      2 * ⟪gradient F x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h))
      (volume.restrict U) :=
    (aemeasurable_sSup_hessian (measurable_gradient_euclidean F)
      (ae_restrict_mem ho.measurableSet) hb hκ).aestronglyMeasurable
  -- Passing to the limit `r ↑ 1` in the three terms.
  have hFsq : AEStronglyMeasurable (fun x => F x ^ 2) (volume.restrict U) :=
    (hFc.aestronglyMeasurable ho.measurableSet).pow 2
  have hL1 := tendsto_integral_tilted_shrinkSet hc ho hx0 hint hpos
    (g := fun x => F x ^ 2) hFsq
    (C := CF ^ 2) (fun x hx => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hCFu x hx) 2)
  have hL2 := tendsto_integral_tilted_shrinkSet hc ho hx0 hint hpos
    (g := F) (hFc.aestronglyMeasurable ho.measurableSet) (C := CF) hCFu
  have hL3 := tendsto_integral_tilted_shrinkSet hc ho hx0 hint hpos
    (g := fun x => sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
      2 * ⟪gradient F x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h))
    hQmeas (C := CG ^ 2 / κ) hQbound
  -- The inequality on each shrunken domain, with the variance written as `∫F² - (∫F)²`.
  have hiQ : ∀ x : EuclideanSpace ℝ (Fin d),
      sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
        2 * fderiv ℝ F x h - fderiv ℝ (fderiv ℝ V) x h h) =
      sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
        2 * ⟪gradient F x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) := by
    intro x
    simp only [inner_gradient_eq_fderiv]
  have hineq : ∀ r ∈ Ioo (0 : ℝ) 1,
      (∫ x, F x ^ 2 ∂((volume.restrict (shrinkSet x0 r U)).tilted (fun x => -V x))) -
        (∫ x, F x ∂((volume.restrict (shrinkSet x0 r U)).tilted (fun x => -V x))) ^ 2 ≤
      ∫ x, sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
        2 * ⟪gradient F x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h)
        ∂((volume.restrict (shrinkSet x0 r U)).tilted (fun x => -V x)) := by
    intro r hr
    have hSo : IsOpen (shrinkSet x0 r U) := isOpen_shrinkSet ho x0 r
    have hSsub : shrinkSet x0 r U ⊆ U := shrinkSet_subset hc hx0 hr.1 hr.2.le
    have hSU : closure (shrinkSet x0 r U) ⊆ U := closure_shrinkSet_subset hc ho hx0 hr.1 hr.2
    have hSne : (shrinkSet x0 r U).Nonempty := ⟨x0, by simpa [shrinkSet] using hx0⟩
    have hSc : Convex ℝ (shrinkSet x0 r U) := convex_shrinkSet hc x0 r
    have hSb : Bornology.IsBounded (shrinkSet x0 r U) :=
      isBounded_shrinkSet hU x0 hr.1 hr.2.le
    have hbS : ∀ x ∈ shrinkSet x0 r U, ∀ h,
        κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h :=
      fun x hx => hb x (hSsub hx)
    have hVS : ContDiffOn ℝ 2 V (shrinkSet x0 r U) := hV.mono hSsub
    have := bl_convex_isProbabilityMeasure hSb hSc hSo hSne hVS hκ hbS
    have hFmem : MemLp F 2 ((volume.restrict (shrinkSet x0 r U)).tilted (fun x => -V x)) :=
      memLp_tilted_of_bounded hSo (hFc.mono hSsub) (C := CF) (fun x hx => hCFu x (hSsub hx))
    have hL := bl_variance_integral_le hPL hd hSb hSo hSne hSc ho hSU hV hF2U hκ hbS
    simp only [hiQ] at hL
    rw [WeightedSobolev.integral_sub_mean_sq hFmem] at hL
    exact hL
  -- The limit of the three terms.
  have hFmem : MemLp F 2 ((volume.restrict U).tilted (fun x => -V x)) :=
    memLp_tilted_of_bounded ho hFc (C := CF) hCFu
  rw [WeightedSobolev.integral_sub_mean_sq hFmem]
  exact le_of_tendsto_of_tendsto ((hL1.sub (hL2.pow 2)))
    hL3 (eventually_of_mem (Ioo_mem_nhdsLT zero_lt_one) fun r hr => hineq r hr)

end Riesz1

end

end
