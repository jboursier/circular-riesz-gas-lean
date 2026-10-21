/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Normalization of the Euclidean Brascamp–Lieb measure without continuity on the closure

The Euclidean part of Lemma 3.6 assumes only `V ∈ C²(U)`, not continuity of
`V` on the closure of `U`. Here the positive definite Hessian makes `V` convex on `U`, so `V`
lies above its tangent planes. The tangent inequality is proved along segments, by monotonicity of
the derivative. A tangent plane is bounded on the bounded set `U`, which gives a lower bound
for `V`, and hence the finiteness and positivity of `∫_U e^{-V}`.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Tangent inequality for a function with positive semidefinite Hessian on a convex open set:
`V y ≥ V x0 + DV(x0)(y - x0)` for `x0, y ∈ U`. -/
theorem bl_tangent_le {U : Set E} {V : E → ℝ} (hc : Convex ℝ U) (ho : IsOpen U)
    (hV : ContDiffOn ℝ 2 V U) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    {x0 y : E} (hx0 : x0 ∈ U) (hy : y ∈ U) :
    V x0 + fderiv ℝ V x0 (y - x0) ≤ V y := by
  set v : E := y - x0 with hv
  let γ : ℝ → E := fun t => x0 + t • v
  have hγ (t : ℝ) : HasDerivAt γ v t := by
    have h : HasDerivAt (fun s : ℝ => x0 + s • v) ((1 : ℝ) • v) t :=
      ((hasDerivAt_id t).smul_const v).const_add x0
    simpa only [one_smul] using h
  -- The segment lies in `U` on an open set containing `[0, 1]`.
  have hsub : Icc (0 : ℝ) 1 ⊆ γ ⁻¹' U := by
    intro t ht
    show x0 + t • v ∈ U
    have heq : x0 + t • v = (1 - t) • x0 + t • y := by
      simp only [v]
      module
    rw [heq]
    exact hc hx0 hy (by linarith [ht.2]) ht.1 (by ring)
  have hdiff (t : ℝ) (ht : γ t ∈ U) : DifferentiableAt ℝ V (γ t) :=
    (hV.contDiffAt (ho.mem_nhds ht)).differentiableAt (by norm_num)
  -- First derivative of the restriction `t ↦ V (γ t)`.
  have hd1 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => V (γ t)) (fderiv ℝ V (γ t) v) t :=
    HasFDerivAt.comp_hasDerivAt t (hdiff t (hsub ht)).hasFDerivAt (hγ t)
  -- Second derivative of the restriction, which is the Hessian in the direction `v`.
  have hd2 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => fderiv ℝ V (γ t) v) (fderiv ℝ (fderiv ℝ V) (γ t) v v) t := by
    have hV2 : ContDiffAt ℝ 2 V (γ t) := hV.contDiffAt (ho.mem_nhds (hsub ht))
    have hV1 : ContDiffAt ℝ 1 (fderiv ℝ V) (γ t) :=
      ContDiffAt.fderiv_right (m := 1) hV2 (by norm_num)
    have hF : HasFDerivAt (fderiv ℝ V) (fderiv ℝ (fderiv ℝ V) (γ t)) (γ t) :=
      (hV1.differentiableAt (by norm_num)).hasFDerivAt
    have hc' := HasFDerivAt.comp_hasDerivAt t hF (hγ t)
    have h2 := hc'.clm_apply (hasDerivAt_const t v)
    simp only [map_zero, add_zero] at h2
    exact h2
  -- The derivative of the restriction is nondecreasing on `[0, 1]`.
  have hmono : MonotoneOn (fun t => fderiv ℝ V (γ t) v) (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun t ht => (hd2 t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hd2 t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd2 t (interior_subset ht)).deriv]
      exact (mul_nonneg hκ.le (sq_nonneg _)).trans (hb _ (hsub (interior_subset ht)) v)
  -- The mean value estimate: the derivative at `0` bounds the increment from below.
  have hcont : ContinuousOn (fun t => V (γ t)) (Icc 0 1) :=
    fun t ht => (hd1 t ht).continuousAt.continuousWithinAt
  have hdiffOn : DifferentiableOn ℝ (fun t => V (γ t)) (interior (Icc 0 1)) :=
    fun t ht => (hd1 t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hge : ∀ t ∈ interior (Icc (0 : ℝ) 1), fderiv ℝ V x0 v ≤ deriv (fun t => V (γ t)) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
    rw [(hd1 t ht').deriv]
    have h0 : fderiv ℝ V (γ 0) v = fderiv ℝ V x0 v := by simp [γ]
    rw [← h0]
    exact hmono ⟨le_rfl, zero_le_one⟩ ht' ht'.1
  have key := (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv hcont hdiffOn hge
    0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [γ, zero_smul, add_zero, one_smul, mul_one, sub_zero] at key
  have hyv : x0 + v = y := by simp [v]
  rw [hyv] at key
  linarith

/-- A convex function with positive semidefinite Hessian is bounded below on a bounded convex
open set, by a tangent plane at a point. -/
theorem bl_exists_lower_bound {U : Set E} {V : E → ℝ} (hU : Bornology.IsBounded U)
    (hc : Convex ℝ U) (ho : IsOpen U) (hne : U.Nonempty) (hV : ContDiffOn ℝ 2 V U)
    {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h) :
    ∃ c : ℝ, ∀ y ∈ U, c ≤ V y := by
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨R, hR⟩ := hU.subset_closedBall x0
  refine ⟨V x0 - ‖fderiv ℝ V x0‖ * R, fun y hy => ?_⟩
  have hyR : ‖y - x0‖ ≤ R := by
    have := hR hy
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hlin : |fderiv ℝ V x0 (y - x0)| ≤ ‖fderiv ℝ V x0‖ * R :=
    calc |fderiv ℝ V x0 (y - x0)| = ‖fderiv ℝ V x0 (y - x0)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ V x0‖ * ‖y - x0‖ := (fderiv ℝ V x0).le_opNorm (y - x0)
      _ ≤ ‖fderiv ℝ V x0‖ * R := mul_le_mul_of_nonneg_left hyR (norm_nonneg _)
  have htan := bl_tangent_le hc ho hV hκ hb hx0 hy
  have := (abs_le.1 hlin).1
  linarith

/-- Finiteness of the unnormalized Euclidean density on a bounded convex open set, when only
`V ∈ C²(U)` with a positive Hessian lower bound is known. -/
theorem bl_convex_exp_integrableOn {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
    {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : Bornology.IsBounded U) (hc : Convex ℝ U) (ho : IsOpen U) (hne : U.Nonempty)
    (hV : ContDiffOn ℝ 2 V U) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h) :
    IntegrableOn (fun x => Real.exp (-V x)) U := by
  obtain ⟨c, hcV⟩ := bl_exists_lower_bound hU hc ho hne hV hκ hb
  have hcont : ContinuousOn (fun x => Real.exp (-V x)) U :=
    Real.continuous_exp.comp_continuousOn hV.continuousOn.neg
  have hmeas : AEStronglyMeasurable (fun x => Real.exp (-V x)) (volume.restrict U) :=
    hcont.aestronglyMeasurable ho.measurableSet
  refine Integrable.mono' (g := fun _ => Real.exp (-c))
    (integrableOn_const hU.measure_lt_top.ne) hmeas ?_
  filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.2 (by linarith [hcV x hx])

/-- The Euclidean normalizing integral `∫_U e^{-V}` is positive, on a bounded convex open set. -/
theorem bl_convex_normalization_pos {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
    {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : Bornology.IsBounded U) (hc : Convex ℝ U) (ho : IsOpen U) (hne : U.Nonempty)
    (hV : ContDiffOn ℝ 2 V U) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h) :
    0 < ∫ x in U, Real.exp (-V x) := by
  have : NeZero (volume.restrict U) :=
    ⟨fun hz => (ho.measure_pos volume hne).ne' (Measure.restrict_eq_zero.mp hz)⟩
  exact integral_exp_pos (bl_convex_exp_integrableOn hU hc ho hne hV hκ hb)

/-- The Euclidean normalizing constant is finite and positive, in the extended-real form used
by the Brascamp–Lieb statement. -/
theorem bl_convex_lintegral_bounds {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
    {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : Bornology.IsBounded U) (hc : Convex ℝ U) (ho : IsOpen U) (hne : U.Nonempty)
    (hV : ContDiffOn ℝ 2 V U) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h) :
    0 < ∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x)) ∧
      (∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x))) < ⊤ := by
  have hi := bl_convex_exp_integrableOn hU hc ho hne hV hκ hb
  have heq := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun x => (Real.exp_pos (-V x)).le)
  rw [← heq]
  exact ⟨ENNReal.ofReal_pos.2 (bl_convex_normalization_pos hU hc ho hne hV hκ hb),
    ENNReal.ofReal_lt_top⟩

/-- The tilted Euclidean measure `e^{-V} dx / Z` on a bounded convex open set is a probability
measure. -/
theorem bl_convex_isProbabilityMeasure {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
    {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : Bornology.IsBounded U) (hc : Convex ℝ U) (ho : IsOpen U) (hne : U.Nonempty)
    (hV : ContDiffOn ℝ 2 V U) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h) :
    IsProbabilityMeasure ((volume.restrict U).tilted (fun x => -V x)) := by
  have : NeZero (volume.restrict U) :=
    ⟨fun hz => (ho.measure_pos volume hne).ne' (Measure.restrict_eq_zero.mp hz)⟩
  exact isProbabilityMeasure_tilted (bl_convex_exp_integrableOn hU hc ho hne hV hκ hb)

end Riesz1

end
