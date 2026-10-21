/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.ConvergesInLaw
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Probability.CDF
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Convergence in law through distribution functions

For Borel probability measures `μ_n` and `ν` on `ℝ`, the laws `μ_n` converge in law to `ν`
exactly when `μ_n (Iic t) → ν (Iic t)` for every `t` with `ν {t} = 0`. These are the points where
the distribution function of `ν` is continuous. This is the second sentence of
the test-convergence statement in the proof of Theorem 3.

The forward implication is the portmanteau theorem, because the frontier of `Iic t` lies in
`{t}`. For the converse, the intervals `Ioc a b` whose endpoints carry no mass under `ν` form a
`π`-system. Its finite unions approximate every open set, so Mathlib's convergence criterion for
`π`-systems applies. A probability measure on `ℝ` has countably many atoms, so the atom-free
points are dense, and they supply the required neighborhoods.
-/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Riesz1

/-- The atoms of a finite measure on `ℝ` form a countable set. -/
lemma countable_atoms (ν : Measure ℝ) [IsFiniteMeasure ν] : {t : ℝ | ν {t} ≠ 0}.Countable := by
  have h := Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top ν
    (As := fun t : ℝ => ({t} : Set ℝ)) (fun t => measurableSet_singleton t)
    (fun _ _ hxy => Set.disjoint_singleton.mpr hxy) (measure_ne_top ν _)
  simpa [pos_iff_ne_zero] using h

/-- The points carrying no mass under a finite measure on `ℝ` are dense. -/
lemma dense_no_atom (ν : Measure ℝ) [IsFiniteMeasure ν] : Dense {t : ℝ | ν {t} = 0} := by
  have h : {t : ℝ | ν {t} = 0} = {t : ℝ | ν {t} ≠ 0}ᶜ := by
    ext t
    simp
  rw [h]
  exact (countable_atoms ν).dense_compl ℝ

/-- Convergence in law gives convergence of `μ_n (Iic t)` at every `t` with `ν {t} = 0`. -/
lemma tendsto_measure_Iic_of_convergesInLaw {laws : ℕ → Measure ℝ} {limit : Measure ℝ}
    (h : ConvergesInLaw laws limit) {t : ℝ} (ht : limit {t} = 0) :
    Tendsto (fun n => laws n (Iic t)) atTop (𝓝 (limit (Iic t))) := by
  obtain ⟨hlaws, hlimit, hf⟩ := h
  let μs : ℕ → ProbabilityMeasure ℝ := fun n => ⟨laws n, hlaws n⟩
  let μ : ProbabilityMeasure ℝ := ⟨limit, hlimit⟩
  have hweak : Tendsto μs atTop (𝓝 μ) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hf
  -- The frontier of `Iic t` is contained in `{t}`, which has no mass under the limit.
  have hnull : (μ : Measure ℝ) (frontier (Iic t)) = 0 :=
    measure_mono_null (frontier_Iic_subset t) ht
  exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak hnull

/-- If `μ_n (Iic t) → ν (Iic t)` at every `t` with `ν {t} = 0`, then the laws `μ_n` converge in
law to `ν`. The proof applies Mathlib's convergence criterion along the `π`-system of intervals
`Ioc a b` with `ν {a} = 0` and `ν {b} = 0`. -/
lemma convergesInLaw_of_tendsto_measure_Iic {laws : ℕ → Measure ℝ} {limit : Measure ℝ}
    (hlaws : ∀ n, IsProbabilityMeasure (laws n)) (hlimit : IsProbabilityMeasure limit)
    (h : ∀ t : ℝ, limit {t} = 0 → Tendsto (fun n => laws n (Iic t)) atTop (𝓝 (limit (Iic t)))) :
    ConvergesInLaw laws limit := by
  let μs : ℕ → ProbabilityMeasure ℝ := fun n => ⟨laws n, hlaws n⟩
  let μ : ProbabilityMeasure ℝ := ⟨limit, hlimit⟩
  -- The `π`-system of intervals with endpoints carrying no mass under `limit`.
  let S : Set (Set ℝ) := {s | ∃ a b : ℝ, a < b ∧ limit {a} = 0 ∧ limit {b} = 0 ∧ s = Ioc a b}
  have hS : IsPiSystem S := by
    rintro _ ⟨a, b, -, ha, hb, rfl⟩ _ ⟨c, d, -, hc, hd, rfl⟩ ⟨x, ⟨hax, hxb⟩, ⟨hcx, hxd⟩⟩
    have hlt : max a c < min b d := lt_of_lt_of_le (max_lt hax hcx) (le_min hxb hxd)
    refine ⟨max a c, min b d, hlt, ?_, ?_, Set.Ioc_inter_Ioc⟩
    · rcases max_choice a c with h' | h' <;> rw [h'] <;> assumption
    · rcases min_choice b d with h' | h' <;> rw [h'] <;> assumption
  have hmeas : ∀ s ∈ S, MeasurableSet s := by
    rintro _ ⟨a, b, -, -, -, rfl⟩
    exact measurableSet_Ioc
  -- Every open neighborhood contains an interval of `S` around each of its points.
  have hnhds : ∀ u : Set ℝ, IsOpen u → ∀ x ∈ u, ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u := by
    intro u hu x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu x hx
    obtain ⟨a, ha, hla, hax⟩ := (dense_no_atom limit).exists_between (show x - ε < x by linarith)
    obtain ⟨b, hb, hxb, hbε⟩ :=
      (dense_no_atom limit).exists_between (show x < x + ε by linarith)
    refine ⟨Ioc a b, ⟨a, b, by linarith, ha, hb, rfl⟩, ?_, ?_⟩
    · exact Filter.mem_of_superset (Ioo_mem_nhds hax hxb) Ioo_subset_Ioc_self
    · refine fun y hy => hball ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [hy.1, hy.2]
  -- On an interval `Ioc a b` with null endpoints, the mass is a difference of two tail masses.
  have hint : ∀ s ∈ S, Tendsto (fun n => μs n s) atTop (𝓝 (μ s)) := by
    rintro _ ⟨a, b, hab, ha, hb, rfl⟩
    have hIoc : Iic b \ Iic a = Ioc a b := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_Iic, Set.mem_Ioc, not_le]
      tauto
    have hsub : Iic a ⊆ Iic b := Iic_subset_Iic.mpr hab.le
    have e1 : ∀ n, laws n (Ioc a b) = laws n (Iic b) - laws n (Iic a) := fun n => by
      rw [← hIoc, measure_sdiff hsub measurableSet_Iic.nullMeasurableSet (measure_ne_top _ _)]
    have e2 : limit (Ioc a b) = limit (Iic b) - limit (Iic a) := by
      rw [← hIoc, measure_sdiff hsub measurableSet_Iic.nullMeasurableSet (measure_ne_top _ _)]
    apply ENNReal.tendsto_coe.mp
    simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    show Tendsto (fun n => laws n (Ioc a b)) atTop (𝓝 (limit (Ioc a b)))
    simp_rw [e1]
    rw [e2]
    exact ENNReal.Tendsto.sub (h b hb) (h a ha) (Or.inl (measure_ne_top _ _))
  have hweak : Tendsto μs atTop (𝓝 μ) :=
    IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem hS hmeas hnhds hint
  exact ⟨hlaws, hlimit, fun f =>
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak f⟩

/-- Convergence in law of probability measures on `ℝ` is equivalent to convergence of the
distribution functions `t ↦ μ_n (Iic t)` at every `t` with `ν {t} = 0`. -/
theorem convergesInLaw_iff_tendsto_measure_Iic (laws : ℕ → Measure ℝ) (limit : Measure ℝ)
    (hlaws : ∀ n, IsProbabilityMeasure (laws n)) (hlimit : IsProbabilityMeasure limit) :
    ConvergesInLaw laws limit ↔
      ∀ t : ℝ, limit {t} = 0 → Tendsto (fun n => laws n (Iic t)) atTop (𝓝 (limit (Iic t))) :=
  ⟨fun h _ ht => tendsto_measure_Iic_of_convergesInLaw h ht,
    convergesInLaw_of_tendsto_measure_Iic hlaws hlimit⟩

/-- A point carries no mass under a probability measure on `ℝ` exactly when the distribution
function of the measure is continuous there. -/
lemma measure_singleton_eq_zero_iff_continuousAt_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (t : ℝ) : μ {t} = 0 ↔ ContinuousAt (ProbabilityTheory.cdf μ) t := by
  have hmono : Monotone (ProbabilityTheory.cdf μ) := ProbabilityTheory.monotone_cdf μ
  -- The mass of `{t}` is the jump of the distribution function at `t`.
  have hjump : μ {t} = ENNReal.ofReal
      (ProbabilityTheory.cdf μ t - Function.leftLim (ProbabilityTheory.cdf μ) t) := by
    have h := StieltjesFunction.measure_singleton (ProbabilityTheory.cdf μ) t
    rwa [ProbabilityTheory.measure_cdf] at h
  rw [hjump, ENNReal.ofReal_eq_zero, sub_nonpos, hmono.continuousAt_iff_leftLim_eq_rightLim,
    StieltjesFunction.rightLim_eq]
  exact ⟨fun h => le_antisymm (hmono.leftLim_le le_rfl) h, fun h => h.symm.le⟩

/-- Convergence in law of probability measures on `ℝ` is equivalent to convergence of the
distribution functions `t ↦ μ_n (Iic t)` at every continuity point `t` of the distribution
function of the limit. -/
theorem convergesInLaw_iff_tendsto_cdf (laws : ℕ → Measure ℝ) (limit : Measure ℝ)
    (hlaws : ∀ n, IsProbabilityMeasure (laws n)) (hlimit : IsProbabilityMeasure limit) :
    ConvergesInLaw laws limit ↔
      ∀ t : ℝ, ContinuousAt (ProbabilityTheory.cdf limit) t →
        Tendsto (fun n => laws n (Iic t)) atTop (𝓝 (limit (Iic t))) := by
  have := hlimit
  rw [convergesInLaw_iff_tendsto_measure_Iic laws limit hlaws hlimit]
  simp only [measure_singleton_eq_zero_iff_continuousAt_cdf limit]

end Riesz1
