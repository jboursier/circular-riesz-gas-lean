/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BLEuclideanNormalization
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Order.OrderClosed

/-!
# Shrinking a convex domain towards an interior point

The Euclidean part of the proof of Lemma 3.6 approximates `U` from inside by the
homothetic copies `U_r = x0 + r (U - x0)`, `0 < r < 1`, which are open, convex, bounded and have
closure inside `U`. Each `U_r` is an admissible domain for the smooth Brascamp–Lieb inequality
(the Bochner part of the proof of Lemma 3.6), so the inequality for `U` follows by letting
`r ↑ 1`. This file proves the geometry of the shrunken sets, and the convergence of the integrals of a fixed
integrable function, and of the tilted expectations, as `r ↑ 1`.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The homothetic copy of `U` with centre `x0` and ratio `r`, written as the preimage under the
inverse homothety: `x ∈ shrinkSet x0 r U` exactly when `x0 + r⁻¹ • (x - x0) ∈ U`. -/
@[expose]
def shrinkSet (x0 : E) (r : ℝ) (U : Set E) : Set E :=
  {x | x0 + r⁻¹ • (x - x0) ∈ U}

theorem isOpen_shrinkSet {U : Set E} (ho : IsOpen U) (x0 : E) (r : ℝ) :
    IsOpen (shrinkSet x0 r U) :=
  ho.preimage (by fun_prop)

theorem convex_shrinkSet {U : Set E} (hc : Convex ℝ U) (x0 : E) (r : ℝ) :
    Convex ℝ (shrinkSet x0 r U) := by
  intro x hx y hy a b ha hb hab
  have hx' : x0 + r⁻¹ • (x - x0) ∈ U := hx
  have hy' : x0 + r⁻¹ • (y - x0) ∈ U := hy
  show x0 + r⁻¹ • (a • x + b • y - x0) ∈ U
  have heq : x0 + r⁻¹ • (a • x + b • y - x0) =
      a • (x0 + r⁻¹ • (x - x0)) + b • (x0 + r⁻¹ • (y - x0)) := by
    obtain rfl : b = 1 - a := by linarith
    module
  rw [heq]
  exact hc hx' hy' ha hb hab

/-- The shrunken set lies in `U` for ratios in `(0, 1]`. -/
theorem shrinkSet_subset {U : Set E} (hc : Convex ℝ U) {x0 : E} (hx0 : x0 ∈ U)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : shrinkSet x0 r U ⊆ U := by
  intro x hx
  have hT : x0 + r⁻¹ • (x - x0) ∈ U := hx
  have key : r • (r⁻¹ • (x - x0)) = x - x0 := smul_inv_smul₀ hr.ne' _
  have hconv := hc hx0 hT (sub_nonneg.2 hr1) hr.le (by ring : (1 - r) + r = 1)
  rwa [show (1 - r) • x0 + r • (x0 + r⁻¹ • (x - x0)) = x from by
    rw [smul_add, key]
    module] at hconv

/-- The closure of the shrunken set lies in `U`, when `x0` is an interior point and the ratio is
in `(0, 1)`. -/
theorem closure_shrinkSet_subset {U : Set E} (hc : Convex ℝ U) (ho : IsOpen U) {x0 : E}
    (hx0 : x0 ∈ U) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    closure (shrinkSet x0 r U) ⊆ U := by
  have hcont : Continuous fun x : E => x0 + r⁻¹ • (x - x0) := by fun_prop
  have hcl : closure (shrinkSet x0 r U) ⊆ (fun x : E => x0 + r⁻¹ • (x - x0)) ⁻¹' closure U := by
    apply closure_minimal
    · intro x hx
      exact subset_closure hx
    · exact IsClosed.preimage hcont isClosed_closure
  intro z hz
  have hw : x0 + r⁻¹ • (z - x0) ∈ closure U := hcl hz
  have hx0' : x0 ∈ interior U := by rwa [ho.interior_eq]
  have hz_eq : (1 - r) • x0 + r • (x0 + r⁻¹ • (z - x0)) = z := by
    have key : r • (r⁻¹ • (z - x0)) = z - x0 := smul_inv_smul₀ hr.ne' _
    rw [smul_add, key]
    module
  have hmem := hc.openSegment_interior_closure_subset_interior hx0' hw
    ⟨1 - r, r, by linarith, hr, by ring, hz_eq⟩
  rwa [ho.interior_eq] at hmem

/-- The shrunken set is bounded, for ratios in `(0, 1]`. -/
theorem isBounded_shrinkSet {U : Set E} (hU : Bornology.IsBounded U) (x0 : E) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) : Bornology.IsBounded (shrinkSet x0 r U) := by
  obtain ⟨R, hR⟩ := hU.subset_closedBall x0
  refine (Metric.isBounded_closedBall (x := x0) (r := R)).subset ?_
  intro x hx
  have hT : x0 + r⁻¹ • (x - x0) ∈ U := hx
  have hTR := hR hT
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 hr.le)] at hTR
  have hR0 : 0 ≤ R := (mul_nonneg (inv_nonneg.2 hr.le) (norm_nonneg _)).trans hTR
  have hinv : 1 ≤ r⁻¹ := (one_le_inv₀ hr).2 hr1
  rw [Metric.mem_closedBall, dist_eq_norm]
  nlinarith [norm_nonneg (x - x0)]

/-- Every point of `U` eventually, as the ratio increases to `1`, lies in the shrunken set. -/
theorem eventually_mem_shrinkSet {U : Set E} (ho : IsOpen U) {x0 x : E} (hx : x ∈ U) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), x ∈ shrinkSet x0 r U := by
  have hc1 : ContinuousAt (fun r : ℝ => x0 + r⁻¹ • (x - x0)) 1 :=
    ContinuousAt.add continuousAt_const (ContinuousAt.smul (continuousAt_inv₀ one_ne_zero)
      continuousAt_const)
  have hlim : Tendsto (fun r : ℝ => x0 + r⁻¹ • (x - x0)) (𝓝 1) (𝓝 x) := by
    simpa using hc1.tendsto
  exact (hlim.eventually (ho.mem_nhds hx)).filter_mono nhdsWithin_le_nhds

/-- The integral of a fixed integrable function over the shrunken sets converges to its integral
over `U`, as the ratio increases to `1`. -/
theorem tendsto_setIntegral_shrinkSet [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    {U : Set E} (hc : Convex ℝ U) (ho : IsOpen U) {x0 : E} (hx0 : x0 ∈ U) {h : E → ℝ}
    (hint : IntegrableOn h U μ) :
    Tendsto (fun r => ∫ x in shrinkSet x0 r U, h x ∂μ) (𝓝[<] (1 : ℝ))
      (𝓝 (∫ x in U, h x ∂μ)) := by
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := μ.restrict U)
    (l := 𝓝[<] (1 : ℝ)) (F := fun r => (shrinkSet x0 r U).indicator h) (f := h)
    (fun x => ‖h x‖)
    (Eventually.of_forall fun r =>
      hint.aestronglyMeasurable.indicator (isOpen_shrinkSet ho x0 r).measurableSet)
    (Eventually.of_forall fun r => Eventually.of_forall fun x =>
      norm_indicator_le_norm_self _ _)
    hint.norm
    (by
      filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
      exact (tendsto_const_nhds (x := h x)).congr' ((eventually_mem_shrinkSet ho hx).mono
        fun r hr => (indicator_of_mem hr h).symm))
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with r hr
  rw [integral_indicator (isOpen_shrinkSet ho x0 r).measurableSet,
    Measure.restrict_restrict (isOpen_shrinkSet ho x0 r).measurableSet,
    Set.inter_eq_left.2 (shrinkSet_subset hc hx0 hr.1 hr.2.le)]

/-- Mean of a tilted measure as a quotient of unnormalized integrals. -/
theorem integral_tilted_eq_div {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) :
    ∫ x, g x ∂(μ.tilted f) = (∫ x, Real.exp (f x) * g x ∂μ) / ∫ x, Real.exp (f x) ∂μ := by
  rw [integral_tilted, ← integral_div]
  congr 1
  funext x
  simp only [smul_eq_mul]
  ring

section Tilted

variable {d : ℕ}

/-- The tilted expectation of a function bounded on `U` converges to its value on `U`, as the
domain shrinks to `U`. The integrability of the density `e^{-V}` on `U` is an assumption, and is
established for `V ∈ C²(U)` with positive Hessian in `bl_convex_exp_integrableOn`. -/
theorem tendsto_integral_tilted_shrinkSet {U : Set (EuclideanSpace ℝ (Fin d))}
    {x0 : EuclideanSpace ℝ (Fin d)} {V : EuclideanSpace ℝ (Fin d) → ℝ} (hc : Convex ℝ U)
    (ho : IsOpen U) (hx0 : x0 ∈ U) (hint : IntegrableOn (fun x => Real.exp (-V x)) U)
    (hpos : 0 < ∫ x in U, Real.exp (-V x)) {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict U)) {C : ℝ} (hgC : ∀ x ∈ U, ‖g x‖ ≤ C) :
    Tendsto (fun r => ∫ x, g x ∂((volume.restrict (shrinkSet x0 r U)).tilted (fun x => -V x)))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ x, g x ∂((volume.restrict U).tilted (fun x => -V x)))) := by
  have hEg : IntegrableOn (fun x => Real.exp (-V x) * g x) U := by
    refine Integrable.mono' (hint.const_mul C) (hint.aestronglyMeasurable.mul hg) ?_
    filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hgC x hx) (Real.exp_pos _).le
  have hN := tendsto_setIntegral_shrinkSet volume hc ho hx0 hEg
  have hD := tendsto_setIntegral_shrinkSet volume hc ho hx0 hint
  simp only [integral_tilted_eq_div]
  exact hN.div hD hpos.ne'

end Tilted

end Riesz1

end
