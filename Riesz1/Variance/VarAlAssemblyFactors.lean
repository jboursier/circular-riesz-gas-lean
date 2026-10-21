/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlAssemblyScalar

/-!
# The good-event factors are anchored Sobolev functions

The reciprocal factor is treated on positive gaps by a positive-clamped
inverse. Equality on that open set identifies both the value and gradient
with the cutoff formula, including its nonsmooth corners.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ContDiff

namespace Riesz1.Internal

variable {n : ℕ} {c : ℝ} (Q : HsPairPotentials n.succPNat c) (hc : 0 < c)

include hc

theorem varAlAssembly_smooth_classical {F : AnchoredEuclidean n → ℝ}
    (hF : ContDiff ℝ ∞ F) : IsAnchoredH1 Q F (gradient F) := by
  have := isProbabilityMeasure_anchoredMeasureE Q hc
  exact WeightedSobolev.isWeightedH1_of_smoothNearClosure
    (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex Q)
    ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩

theorem varAlAssembly_pair_factor {F : AnchoredEuclidean n → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (hlevel : ∀ t : ℝ, ∀ᵐ x ∂anchoredMeasureE Q, F x ≠ t)
    {M : ℝ} (hM : 0 < M) :
    IsAnchoredH1 Q (fun x => scalarCutoff (2 * |F x| / M))
      (gradient (fun x => scalarCutoff (2 * |F x| / M))) ∧
    ∀ᵐ x ∂anchoredMeasureE Q,
      DifferentiableAt ℝ (fun x => scalarCutoff (2 * |F x| / M)) x := by
  have hS := varAlAssembly_smooth_classical Q hc hF
  have hdF : ∀ᵐ x ∂anchoredMeasureE Q, DifferentiableAt ℝ F x :=
    Eventually.of_forall fun x => hF.differentiable (by simp) x
  have hAbs := varAlAssembly_abs_classical Q hc hS hdF (hlevel 0)
  have hdAbs : ∀ᵐ x ∂anchoredMeasureE Q, DifferentiableAt ℝ (fun x => |F x|) x := by
    filter_upwards [hdF, hlevel 0] with x hx hy
    exact hx.norm ℝ hy
  have hScale := varAlAssembly_scale_classical Q hc hAbs hdAbs (2 / M)
  have hdScale : ∀ᵐ x ∂anchoredMeasureE Q,
      DifferentiableAt ℝ (fun x => (2 / M) * |F x|) x :=
    hdAbs.mono fun x hx => hx.const_mul _
  have hcond : ∀ᵐ x ∂anchoredMeasureE Q,
      F x ≠ 0 ∧ 2 * |F x| / M ≠ 1 ∧ 2 * |F x| / M ≠ 2 := by
    filter_upwards [hlevel 0, hlevel (M / 2), hlevel (-(M / 2)), hlevel M, hlevel (-M)]
      with x h0 h1 h2 h3 h4
    exact pair_conditions_of_ne hM h0 h1 h2 h3 h4
  have hmem := varAlAssembly_scalarCutoff_classical Q hc hScale hdScale
    (hcond.mono fun x hx => by simpa only [div_mul_eq_mul_div] using hx.2.1)
    (hcond.mono fun x hx => by simpa only [div_mul_eq_mul_div] using hx.2.2)
  refine ⟨by simpa only [div_mul_eq_mul_div] using hmem, ?_⟩
  filter_upwards [hdF, hcond] with x hx hy
  obtain ⟨d, _, hd⟩ := pair_scalarCutoff_hasDerivAt hM hy.1 hy.2.1 hy.2.2
  exact (hd.comp_hasFDerivAt x hx.hasFDerivAt).differentiableAt

/-- The nearest-neighbour factor, with all its actual corners included
in the Sobolev completion. The positivity premise concerns the input gap. -/
theorem varAlAssembly_nearest_factor {F : AnchoredEuclidean n → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (hpos : ∀ᵐ x ∂anchoredMeasureE Q, 0 < F x)
    (hlevel : ∀ t : ℝ, ∀ᵐ x ∂anchoredMeasureE Q, F x ≠ t)
    {κ : ℝ} (hκ : 1 ≤ κ) :
    IsAnchoredH1 Q (fun x => scalarCutoff (2 * F x / κ) * scalarCutoff (2 / (κ * F x)))
      (gradient (fun x => scalarCutoff (2 * F x / κ) * scalarCutoff (2 / (κ * F x)))) ∧
    ∀ᵐ x ∂anchoredMeasureE Q,
      DifferentiableAt ℝ
        (fun x => scalarCutoff (2 * F x / κ) * scalarCutoff (2 / (κ * F x))) x := by
  have hκ0 : 0 < κ := by linarith
  let a := 1 / (4 * κ)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 / κ := by dsimp [a]; field_simp; linarith
  have ha2 : a < 2 / κ := by dsimp [a]; field_simp; linarith
  have hdF : ∀ᵐ x ∂anchoredMeasureE Q, DifferentiableAt ℝ F x :=
    Eventually.of_forall fun x => hF.differentiable (by simp) x
  have hS := varAlAssembly_smooth_classical Q hc hF
  have hscale := varAlAssembly_scale_classical Q hc hS hdF (2 / κ)
  have hdscale : ∀ᵐ x ∂anchoredMeasureE Q,
      DifferentiableAt ℝ (fun x => (2 / κ) * F x) x :=
    hdF.mono fun x hx => hx.const_mul _
  have hcond : ∀ᵐ x ∂anchoredMeasureE Q,
      2 * F x / κ ≠ 1 ∧ 2 * F x / κ ≠ 2 ∧
      2 / (κ * F x) ≠ 1 ∧ 2 / (κ * F x) ≠ 2 := by
    filter_upwards [hlevel 0, hlevel (κ / 2), hlevel κ, hlevel (2 * κ⁻¹), hlevel κ⁻¹]
      with x h0 h1 h2 h3 h4
    exact near_conditions_of_ne hκ0 (mul_inv_cancel₀ hκ0.ne') h0 h1 h2 h3 h4
  have hA := varAlAssembly_scalarCutoff_classical Q hc hscale hdscale
    (hcond.mono fun x hx => by simpa only [div_mul_eq_mul_div] using hx.1)
    (hcond.mono fun x hx => by simpa only [div_mul_eq_mul_div] using hx.2.1)
  have hdA : ∀ᵐ x ∂anchoredMeasureE Q,
      DifferentiableAt ℝ (fun x => scalarCutoff ((2 / κ) * F x)) x := by
    filter_upwards [hdscale, hcond] with x hx hy
    apply (varAlAssembly_contDiffAt_scalarCutoff
      (by simpa only [div_mul_eq_mul_div] using hy.1)
      (by simpa only [div_mul_eq_mul_div] using hy.2.1)).differentiableAt (by simp) |>.comp x hx
  have hI := varAlAssembly_inv_max_classical Q hc hS hdF ha (hlevel a)
  have hdI : ∀ᵐ x ∂anchoredMeasureE Q,
      DifferentiableAt ℝ (fun x => (max a (F x))⁻¹) x := by
    filter_upwards [hdF, hlevel a] with x hx hy
    exact (((contDiffOn_inv_max ha).contDiffAt
      (isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hy))).differentiableAt
        (by simp)).comp x hx
  have hR := varAlAssembly_scale_classical Q hc hI hdI (2 / κ)
  have hdR : ∀ᵐ x ∂anchoredMeasureE Q,
      DifferentiableAt ℝ (fun x => (2 / κ) * (max a (F x))⁻¹) x :=
    hdI.mono fun x hx => hx.const_mul _
  have havoid (v : ℝ) (hv : v = 1 ∨ v = 2) :
      ∀ᵐ x ∂anchoredMeasureE Q, (2 / κ) * (max a (F x))⁻¹ ≠ v := by
    filter_upwards [hlevel (2 / κ), hlevel (1 / κ)] with x hx hy he
    have hm : 0 < max a (F x) := ha.trans_le (le_max_left _ _)
    rcases hv with rfl | rfl
    · have hmax : max a (F x) = 2 / κ := by
        field_simp [hκ0.ne', hm.ne'] at he ⊢
        linarith
      rcases max_choice a (F x) with h | h
      · linarith
      · exact hx (h.symm.trans hmax)
    · have hmax : max a (F x) = 1 / κ := by
        field_simp [hκ0.ne', hm.ne'] at he ⊢
        linarith
      rcases max_choice a (F x) with h | h
      · linarith
      · exact hy (h.symm.trans hmax)
  have hB := varAlAssembly_scalarCutoff_classical Q hc hR hdR
    (havoid 1 (Or.inl rfl)) (havoid 2 (Or.inr rfl))
  have hdB : ∀ᵐ x ∂anchoredMeasureE Q,
      DifferentiableAt ℝ (fun x => scalarCutoff ((2 / κ) * (max a (F x))⁻¹)) x := by
    filter_upwards [hdR, havoid 1 (Or.inl rfl), havoid 2 (Or.inr rfl)] with x hx hy hz
    exact DifferentiableAt.comp (f := fun x => (2 / κ) * (max a (F x))⁻¹)
      (g := scalarCutoff) x
      ((varAlAssembly_contDiffAt_scalarCutoff hy hz).differentiableAt (by simp)) hx
  have hprod := varAlAssembly_mul_classical Q hc hA hB hdA hdB zero_le_one zero_le_one
    (Eventually.of_forall fun x => by
      rw [abs_of_nonneg (scalarCutoff_nonneg _)]
      exact scalarCutoff_le_one _)
    (Eventually.of_forall fun x => by
      rw [abs_of_nonneg (scalarCutoff_nonneg _)]
      exact scalarCutoff_le_one _)
  have heq (r : ℝ) (hr : 0 < r) :
      scalarCutoff ((2 / κ) * r) * scalarCutoff ((2 / κ) * (max a r)⁻¹) =
        scalarCutoff (2 * r / κ) * scalarCutoff (2 / (κ * r)) := by
    rw [div_mul_eq_mul_div]
    by_cases har : a ≤ r
    · rw [max_eq_right har]
      congr 2
      field_simp
    · have hra : r < a := lt_of_not_ge har
      have hsmall : κ * r ≤ 1 := by
        have hmul := mul_le_mul_of_nonneg_left hra.le hκ0.le
        have hka : κ * a = 1 / 4 := by dsimp [a]; field_simp
        rw [hka] at hmul
        linarith
      have hright : 2 ≤ 2 / (κ * r) :=
        (le_div_iff₀ (mul_pos hκ0 hr)).mpr (by linarith)
      have hleft : 2 ≤ (2 / κ) * (max a r)⁻¹ := by
        rw [max_eq_left hra.le]
        have he : (2 / κ) * a⁻¹ = 8 := by dsimp [a]; field_simp; ring
        rw [he]
        norm_num
      rw [scalarCutoff_eq_zero_of_two_le hleft, scalarCutoff_eq_zero_of_two_le hright,
        mul_zero]
  have hlocal (x : AnchoredEuclidean n) (hx : 0 < F x) :
      (fun y => scalarCutoff ((2 / κ) * F y) *
          scalarCutoff ((2 / κ) * (max a (F y))⁻¹)) =ᶠ[𝓝 x]
        (fun y => scalarCutoff (2 * F y / κ) * scalarCutoff (2 / (κ * F y))) := by
    filter_upwards [hF.continuous.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx)] with y hy
    exact heq _ hy
  refine ⟨hprod.congr (hpos.mono fun x hx => heq _ hx) ?_, ?_⟩
  · filter_upwards [hpos] with x hx
    exact congrArg (InnerProductSpace.toDual ℝ (AnchoredEuclidean n)).symm (hlocal x hx).fderiv_eq
  · filter_upwards [hdF, hlevel 0, hcond] with x hx h0 hy
    obtain ⟨d, _, hd⟩ := nearest_scalarCutoff_hasDerivAt hκ h0 hy.1 hy.2.1 hy.2.2.1 hy.2.2.2
    exact (hd.comp_hasFDerivAt x hx.hasFDerivAt).differentiableAt

end Riesz1.Internal

end
