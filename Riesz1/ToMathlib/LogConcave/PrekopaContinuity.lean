/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LogConcave.PrekopaBounds
public import Riesz1.ToMathlib.LogConcave.PrekopaFrontier
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Continuity of fiber integrals of `e^{-V}` on bounded open convex sets

Let `Q` be a bounded open convex set in `E × EuclideanSpace ℝ (Fin n)`, and let `V` be convex on
`Q`. The function `F` equal to `exp (-V)` on `Q` and to zero outside `Q` is measurable and
bounded, and its fiber integral `z ↦ ∫ y, F (z, y)` is continuous on the projection of `Q`.
The proof is dominated convergence. For a fixed `z`, the exceptional `y` lie on the frontier of
the fiber, which is null by `Riesz1.volume_section_frontier_eq_zero`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology Filter

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The indicator of an open set, of a function continuous on that set, is measurable. -/
theorem measurable_indicator_of_continuousOn {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] {Q : Set α} (hQo : IsOpen Q) {g : α → ℝ}
    (hg : ContinuousOn g Q) : Measurable (Q.indicator g) := by
  refine measurable_of_isOpen fun U hU => ?_
  have hpre : Q.indicator g ⁻¹' U = (Q ∩ g ⁻¹' U) ∪ (Qᶜ ∩ {_p | (0 : ℝ) ∈ U}) := by
    ext p
    by_cases hp : p ∈ Q
    · simp [hp]
    · simp [hp]
  rw [hpre]
  exact MeasurableSet.union (hg.isOpen_inter_preimage hQo hU).measurableSet
    (MeasurableSet.inter hQo.isClosed_compl.measurableSet (MeasurableSet.const _))

variable {n : ℕ}

/-- The integrand `F` equal to `exp (-V)` on `Q` and to zero outside `Q` is measurable. -/
theorem measurable_exp_indicator {Q : Set (E × EuclideanSpace ℝ (Fin n))}
    {V : E × EuclideanSpace ℝ (Fin n) → ℝ} (hQo : IsOpen Q) (hV : ConvexOn ℝ Q V) :
    Measurable (Q.indicator fun p => Real.exp (-V p)) := by
  have hcont : ContinuousOn V Q := by
    have h := hV.continuousOn_interior
    rwa [hQo.interior_eq] at h
  apply measurable_indicator_of_continuousOn hQo
  exact Real.continuous_exp.comp_continuousOn hcont.neg

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For a bounded set `Q`, the constant `exp (-c)` on the closure of its exterior projection is
integrable. This bounds the density `F` when `V ≥ c` on `Q`. -/
theorem bound_exp_indicator_integrable {Q : Set (E × EuclideanSpace ℝ (Fin n))}
    (hQb : Bornology.IsBounded Q) {c : ℝ} :
    Integrable ((closure (Prod.snd '' Q)).indicator (fun _ => Real.exp (-c)))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall
    (0 : E × EuclideanSpace ℝ (Fin n))).mp hQb
  have hsub : Prod.snd '' Q ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    rintro _ ⟨p, hp, rfl⟩
    have h := hR hp
    rw [mem_closedBall_zero_iff] at h ⊢
    exact (norm_snd_le p).trans h
  have hcpt : IsCompact (closure (Prod.snd '' Q)) :=
    IsCompact.of_isClosed_subset (isCompact_closedBall _ R) isClosed_closure
      (closure_minimal hsub Metric.isClosed_closedBall)
  exact (integrable_indicator_iff hcpt.isClosed.measurableSet).2
    (integrableOn_const hcpt.measure_lt_top.ne)

/-- Bounded open convex sets with convex potential have integrable fiber densities. -/
theorem integrable_fiber_exp_indicator {Q : Set (E × EuclideanSpace ℝ (Fin n))}
    {V : E × EuclideanSpace ℝ (Fin n) → ℝ} (hQo : IsOpen Q) (hQb : Bornology.IsBounded Q)
    (hV : ConvexOn ℝ Q V) (z : E) :
    Integrable (fun y => Q.indicator (fun p => Real.exp (-V p)) (z, y))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨c, hc⟩ := exists_lower_bound_of_convexOn hQo hQb hV
  have hF := measurable_exp_indicator (E := E) hQo hV
  refine Integrable.mono' (bound_exp_indicator_integrable (E := E) hQb (c := c)) ?_ ?_
  · exact (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · refine ae_of_all _ fun y => ?_
    rw [Real.norm_of_nonneg (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)]
    by_cases hin : (z, y) ∈ Q
    · rw [indicator_of_mem hin]
      have hyc : y ∈ closure (Prod.snd '' Q) := subset_closure ⟨(z, y), hin, rfl⟩
      rw [indicator_of_mem hyc]
      exact Real.exp_le_exp.2 (neg_le_neg (hc _ hin))
    · rw [indicator_of_notMem hin]
      exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _

omit [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise continuity of the density: if `(z0, y)` is not on the frontier of `Q`, then the
density `z ↦ F (z, y)` is continuous at `z0`. -/
theorem tendsto_indicator_exp_of_notMem_frontier {Q : Set (E × EuclideanSpace ℝ (Fin n))}
    {V : E × EuclideanSpace ℝ (Fin n) → ℝ} (hQo : IsOpen Q) (hV : ConvexOn ℝ Q V)
    {z0 : E} {y : EuclideanSpace ℝ (Fin n)} (hy : (z0, y) ∉ frontier Q) :
    Tendsto (fun z => Q.indicator (fun p => Real.exp (-V p)) (z, y)) (𝓝 z0)
      (𝓝 (Q.indicator (fun p => Real.exp (-V p)) (z0, y))) := by
  have hcont_y : Continuous fun z : E => (z, y) := by fun_prop
  by_cases hin : (z0, y) ∈ Q
  · have hcont : ContinuousOn V Q := by
      have h := hV.continuousOn_interior
      rwa [hQo.interior_eq] at h
    have hVt : Tendsto (fun z => V (z, y)) (𝓝 z0) (𝓝 (V (z0, y))) :=
      (hcont.continuousAt (hQo.mem_nhds hin)).tendsto.comp hcont_y.continuousAt.tendsto
    have h1 : Tendsto (fun z => Real.exp (-V (z, y))) (𝓝 z0)
        (𝓝 (Real.exp (-V (z0, y)))) :=
      (Real.continuous_exp.tendsto _).comp hVt.neg
    have heq : (fun z => Q.indicator (fun p => Real.exp (-V p)) (z, y)) =ᶠ[𝓝 z0]
        fun z => Real.exp (-V (z, y)) := by
      filter_upwards [(hQo.preimage hcont_y).mem_nhds hin] with z hz
      rw [indicator_of_mem (show (z, y) ∈ Q from hz)]
    rw [indicator_of_mem hin]
    exact h1.congr' heq.symm
  · have hncl : (z0, y) ∉ closure Q := fun hcl =>
      hy ⟨hcl, fun hi => hin (by rw [← hQo.interior_eq]; exact hi)⟩
    have hopen : IsOpen (closure Q)ᶜ := isClosed_closure.isOpen_compl
    have hev : ∀ᶠ z in 𝓝 z0, (z, y) ∈ (closure Q)ᶜ :=
      (hopen.preimage hcont_y).mem_nhds hncl
    have hzero : (fun z => Q.indicator (fun p => Real.exp (-V p)) (z, y)) =ᶠ[𝓝 z0]
        fun _ => 0 := by
      filter_upwards [hev] with z hz
      exact indicator_of_notMem (fun h => hz (subset_closure h)) _
    rw [indicator_of_notMem hin]
    exact tendsto_const_nhds.congr' hzero.symm

/-- Dominated convergence: the fiber integral of `F` is continuous at every point of the
projection of a bounded open convex set. -/
theorem tendsto_marginal_exp_indicator {Q : Set (E × EuclideanSpace ℝ (Fin n))}
    {V : E × EuclideanSpace ℝ (Fin n) → ℝ} (hQo : IsOpen Q) (hQc : Convex ℝ Q)
    (hQb : Bornology.IsBounded Q) (hV : ConvexOn ℝ Q V) {z0 : E}
    (hz0 : ∃ y, (z0, y) ∈ Q) :
    Tendsto (fun z => ∫ y, Q.indicator (fun p => Real.exp (-V p)) (z, y)) (𝓝 z0)
      (𝓝 (∫ y, Q.indicator (fun p => Real.exp (-V p)) (z0, y))) := by
  obtain ⟨c, hc⟩ := exists_lower_bound_of_convexOn hQo hQb hV
  have hF := measurable_exp_indicator (E := E) hQo hV
  have hnull := volume_section_frontier_eq_zero (E := E) hQo hQc hz0
  have hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (z0, y) ∉ frontier Q := by
    rw [ae_iff]
    simpa using hnull
  refine tendsto_integral_filter_of_dominated_convergence
    (bound := (closure (Prod.snd '' Q)).indicator (fun _ => Real.exp (-c))) ?_ ?_
    (bound_exp_indicator_integrable (E := E) hQb (c := c)) ?_
  · exact Filter.Eventually.of_forall fun z =>
      (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ae_of_all _ fun y => ?_
    rw [Real.norm_of_nonneg (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)]
    by_cases hin : (z, y) ∈ Q
    · rw [indicator_of_mem hin]
      have hyc : y ∈ closure (Prod.snd '' Q) := subset_closure ⟨(z, y), hin, rfl⟩
      rw [indicator_of_mem hyc]
      exact Real.exp_le_exp.2 (neg_le_neg (hc _ hin))
    · rw [indicator_of_notMem hin]
      exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  · filter_upwards [hae] with y hy
    exact tendsto_indicator_exp_of_notMem_frontier hQo hV hy

/-- The fiber integral of `F` is continuous on the projection of a bounded open convex set. -/
theorem continuousOn_marginal_exp_indicator {Q : Set (E × EuclideanSpace ℝ (Fin n))}
    {V : E × EuclideanSpace ℝ (Fin n) → ℝ} (hQo : IsOpen Q) (hQc : Convex ℝ Q)
    (hQb : Bornology.IsBounded Q) (hV : ConvexOn ℝ Q V) :
    ContinuousOn (fun z => ∫ y, Q.indicator (fun p => Real.exp (-V p)) (z, y))
      (Prod.fst '' Q) := by
  intro z0 hz0
  obtain ⟨p, hp, hpz⟩ := hz0
  have hyz : ∃ y, (z0, y) ∈ Q := ⟨p.2, by rw [← hpz]; simpa using hp⟩
  exact ContinuousAt.continuousWithinAt (tendsto_marginal_exp_indicator hQo hQc hQb hV hyz)

/-- The fiber integral of `F` is positive over every point of the projection of `Q`. -/
theorem marginal_exp_indicator_pos {Q : Set (E × EuclideanSpace ℝ (Fin n))}
    {V : E × EuclideanSpace ℝ (Fin n) → ℝ} (hQo : IsOpen Q) (hQb : Bornology.IsBounded Q)
    (hV : ConvexOn ℝ Q V) {z : E} (hz : ∃ y, (z, y) ∈ Q) :
    0 < ∫ y, Q.indicator (fun p => Real.exp (-V p)) (z, y) := by
  obtain ⟨y0, hy0⟩ := hz
  rw [integral_pos_iff_support_of_nonneg
    (fun y => indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)
    (integrable_fiber_exp_indicator hQo hQb hV z)]
  have hsupp : Function.support (fun y => Q.indicator (fun p => Real.exp (-V p)) (z, y)) =
      {y : EuclideanSpace ℝ (Fin n) | (z, y) ∈ Q} := by
    ext y
    by_cases h : (z, y) ∈ Q
    · simp [Function.mem_support, h]
    · simp [Function.mem_support, h]
  rw [hsupp]
  have hopen : IsOpen {y : EuclideanSpace ℝ (Fin n) | (z, y) ∈ Q} :=
    hQo.preimage (by fun_prop)
  exact hopen.measure_pos volume ⟨y0, hy0⟩

end Riesz1

end
end
