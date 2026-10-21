/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsLpPairSum
public import Riesz1.Auxiliary.LoopArcsLpMeasure

/-!
# The small region of the cell estimate

The arcs part of Lemma 5.8, small region `u + v < 1`. The integrand of the cell
representation over `u, v > 0`, `u + v < 1`, after the bound `|g_N'''(r)| ≤ C r^{-s-3}` and the
replacement of the arc discrepancies by `count ± arclength`, is controlled by the rooted energies
of the particles in the windows of the cell. This file proves the bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set
open scoped ENNReal

namespace Riesz1

attribute [local instance] Classical.propDecidable

/-- A triple iterated lower integral of a measurable function is the integral over the product measure. -/
theorem smallRegion_lintegral_flatten {μ ν ρ : Measure ℝ} [SFinite μ] [SFinite ν] [SFinite ρ]
    {f : ℝ × ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ t, ∫⁻ u, ∫⁻ v, f (t, u, v) ∂ρ ∂ν ∂μ = ∫⁻ p, f p ∂(μ.prod (ν.prod ρ)) := by
  rw [lintegral_prod _ hf.aemeasurable]
  refine lintegral_congr fun t => ?_
  exact (lintegral_prod (fun y : ℝ × ℝ => f (t, y))
    (hf.comp measurable_prodMk_left).aemeasurable).symm

/-- The count of an arc, as an extended nonnegative real, is a finite sum of indicators. -/
theorem smallRegion_ofReal_loopCount {N : ℕ+} (a r : ℝ) (X : Configuration N) :
    ENNReal.ofReal (loopCount a r X) =
      ∑ i : Fin (N : ℕ), if loopPos X i ∈ microArc N a r then 1 else 0 := by
  unfold loopCount
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs <;> norm_num)]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- The count of the arc `(a, a + r)` is at most the sum over the lifts `z_i + nN` of the indicators of the lifts lying in `(a, a + r)`. -/
theorem smallRegion_ofReal_loopCount_le {N : ℕ+} (a r : ℝ) (X : Configuration N) :
    ENNReal.ofReal (loopCount a r X) ≤ ∑ i : Fin (N : ℕ), ∑' n : ℤ,
      if a < loopArcPos N X i + n * N ∧ loopArcPos N X i + n * N < a + r then (1 : ℝ≥0∞)
        else 0 := by
  rw [smallRegion_ofReal_loopCount]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : loopPos X i ∈ microArc N a r
  · rw [ite_eq_left h]
    obtain ⟨n, hn1, hn2⟩ := (loopPos_mem_microArc_iff X i a r).mp h
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum n)
    rw [ite_eq_left ⟨hn1, hn2⟩]
  · rw [ite_eq_right h]
    exact zero_le

/-- Since an open window of length `2 ≤ N` contains at most one lift of each particle, the sum over lifts in the window is at most the indicator that the particle lies in the window. -/
theorem smallRegion_tsum_window {N : ℕ+} (hN : (2 : ℝ) ≤ N) (X : Configuration N)
    (i : Fin (N : ℕ)) (c : ℝ) (d : ℝ≥0∞) :
    ∑' n : ℤ, (if c < loopArcPos N X i + n * N ∧ loopArcPos N X i + n * N < c + 2 then d
        else 0) ≤ if loopPos X i ∈ microArc N c 2 then d else 0 := by
  by_cases h : loopPos X i ∈ microArc N c 2
  · rw [ite_eq_left h]
    obtain ⟨n0, h1, h2⟩ := (loopPos_mem_microArc_iff X i c 2).mp h
    rw [tsum_eq_single n0]
    · rw [ite_eq_left ⟨h1, h2⟩]
    · intro n hn
      rw [ite_eq_right]
      rintro ⟨h3, h4⟩
      exact hn (lift_eq_of_mem_window (c := c) (x := (N : ℝ) * X.val i) hN h3 h4 h1 h2)
  · rw [ite_eq_right h]
    refine nonpos_iff_eq_zero.mpr (ENNReal.tsum_eq_zero.mpr fun n => ?_)
    rw [ite_eq_right]
    rintro ⟨h3, h4⟩
    exact h ((loopPos_mem_microArc_iff X i c 2).mpr ⟨n, h3, h4⟩)

/-- Distributing a product of two sums over finite sets and lifts into a four-fold sum. -/
theorem smallRegion_sum_mul_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ℤ → ℝ≥0∞) (g : κ → ℤ → ℝ≥0∞) (w : ℝ≥0∞) :
    w * ((∑ i, ∑' n, f i n) * (∑ j, ∑' n', g j n')) =
      ∑ i, ∑' n, ∑ j, ∑' n', w * (f i n * g j n') := by
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]

/-- The `t`-integral over the cell `(m, m + 1]` of the indicator that a fixed lift `ℓ` lies in `(t - u, t)` is at most `u`, and vanishes unless `ℓ ∈ (m - 1, m + 1)`, when `u ≤ 1`. -/
theorem smallRegion_lintegral_cell_left (m u ℓ : ℝ) (hu : u ≤ 1) :
    ∫⁻ t in Ioc m (m + 1), (if t - u < ℓ ∧ ℓ < t - u + u then (1 : ℝ≥0∞) else 0)
      ≤ if m - 1 < ℓ ∧ ℓ < m - 1 + 2 then ENNReal.ofReal u else 0 := by
  by_cases hw : m - 1 < ℓ ∧ ℓ < m - 1 + 2
  · rw [ite_eq_left hw]
    calc ∫⁻ t in Ioc m (m + 1), (if t - u < ℓ ∧ ℓ < t - u + u then (1 : ℝ≥0∞) else 0)
        ≤ ∫⁻ t in Ioc m (m + 1), (Ioo ℓ (ℓ + u)).indicator 1 t := by
          refine lintegral_mono fun t => ?_
          by_cases h : t - u < ℓ ∧ ℓ < t - u + u
          · rw [ite_eq_left h, Set.indicator_of_mem (show t ∈ Ioo ℓ (ℓ + u) from
              ⟨by linarith [h.2], by linarith [h.1]⟩)]
            rfl
          · rw [ite_eq_right h]
            exact zero_le
      _ ≤ ∫⁻ t, (Ioo ℓ (ℓ + u)).indicator 1 t := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal u := by
          rw [lintegral_indicator_one measurableSet_Ioo, Real.volume_Ioo]
          congr 1
          ring
  · rw [ite_eq_right hw]
    refine nonpos_iff_eq_zero.mpr ?_
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℝ≥0∞)) (fun t ht => ?_)]
    · simp
    · rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      exact hw ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- The `t`-integral over the cell `(m, m + 1]` of the indicator that a fixed lift `ℓ` lies in `(t, t + v)` is at most `v`, and vanishes unless `ℓ ∈ (m, m + 2)`, when `v ≤ 1`. -/
theorem smallRegion_lintegral_cell_right (m v ℓ : ℝ) (hv : v ≤ 1) :
    ∫⁻ t in Ioc m (m + 1), (if t < ℓ ∧ ℓ < t + v then (1 : ℝ≥0∞) else 0)
      ≤ if m < ℓ ∧ ℓ < m + 2 then ENNReal.ofReal v else 0 := by
  by_cases hw : m < ℓ ∧ ℓ < m + 2
  · rw [ite_eq_left hw]
    calc ∫⁻ t in Ioc m (m + 1), (if t < ℓ ∧ ℓ < t + v then (1 : ℝ≥0∞) else 0)
        ≤ ∫⁻ t in Ioc m (m + 1), (Ioo (ℓ - v) ℓ).indicator 1 t := by
          refine lintegral_mono fun t => ?_
          by_cases h : t < ℓ ∧ ℓ < t + v
          · rw [ite_eq_left h, Set.indicator_of_mem (show t ∈ Ioo (ℓ - v) ℓ from
              ⟨by linarith [h.2], h.1⟩)]
            rfl
          · rw [ite_eq_right h]
            exact zero_le
      _ ≤ ∫⁻ t, (Ioo (ℓ - v) ℓ).indicator 1 t := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal v := by
          rw [lintegral_indicator_one measurableSet_Ioo, Real.volume_Ioo]
          congr 1
          ring
  · rw [ite_eq_right hw]
    refine nonpos_iff_eq_zero.mpr ?_
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℝ≥0∞)) (fun t ht => ?_)]
    · simp
    · rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      exact hw ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- The `t`-integral over a unit cell of the left count `n₋(t, u)` is at most `u n(m - 1, 2)`. -/
theorem smallRegion_lintegral_left_count {N : ℕ+} (hN : 2 ≤ (N : ℕ)) (X : Configuration N)
    (m u : ℝ) (hu : u ≤ 1) :
    ∫⁻ t in Ioc m (m + 1), ENNReal.ofReal (loopCount (t - u) u X)
      ≤ ENNReal.ofReal u * ENNReal.ofReal (loopCount (m - 1) 2 X) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  calc ∫⁻ t in Ioc m (m + 1), ENNReal.ofReal (loopCount (t - u) u X)
      ≤ ∫⁻ t in Ioc m (m + 1), ∑ i : Fin (N : ℕ), ∑' n : ℤ,
          (if t - u < loopArcPos N X i + n * N ∧ loopArcPos N X i + n * N < t - u + u then
            (1 : ℝ≥0∞) else 0) :=
        lintegral_mono fun t => smallRegion_ofReal_loopCount_le (t - u) u X
    _ = ∑ i : Fin (N : ℕ), ∑' n : ℤ, ∫⁻ t in Ioc m (m + 1),
          (if t - u < loopArcPos N X i + n * N ∧ loopArcPos N X i + n * N < t - u + u then
            (1 : ℝ≥0∞) else 0) := by
        rw [lintegral_finsetSum']
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [lintegral_tsum]
          intro n
          refine Measurable.aemeasurable (Measurable.ite ?_ measurable_const measurable_const)
          exact (measurableSet_lt (measurable_id.sub_const u) measurable_const).inter
            (measurableSet_lt measurable_const ((measurable_id.sub_const u).add_const u))
        · intro i _
          refine Measurable.aemeasurable (Measurable.tsum fun n => ?_)
          refine Measurable.ite ?_ measurable_const measurable_const
          exact (measurableSet_lt (measurable_id.sub_const u) measurable_const).inter
            (measurableSet_lt measurable_const ((measurable_id.sub_const u).add_const u))
    _ ≤ ∑ i : Fin (N : ℕ), ∑' n : ℤ,
          (if m - 1 < loopArcPos N X i + n * N ∧ loopArcPos N X i + n * N < m - 1 + 2 then
            ENNReal.ofReal u else 0) :=
        Finset.sum_le_sum fun i _ => ENNReal.tsum_le_tsum fun n =>
          smallRegion_lintegral_cell_left m u _ hu
    _ ≤ ∑ i : Fin (N : ℕ), (if loopPos X i ∈ microArc N (m - 1) 2 then ENNReal.ofReal u else 0) :=
        Finset.sum_le_sum fun i _ => smallRegion_tsum_window hN2 X i (m - 1) _
    _ = ENNReal.ofReal u * ENNReal.ofReal (loopCount (m - 1) 2 X) := by
        rw [smallRegion_ofReal_loopCount, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : loopPos X i ∈ microArc N (m - 1) 2
        · rw [ite_eq_left h, ite_eq_left h, mul_one]
        · rw [ite_eq_right h, ite_eq_right h, mul_zero]

/-- The `t`-integral over a unit cell of the right count `n₊(t, v)` is at most `v n(m, 2)`. -/
theorem smallRegion_lintegral_right_count {N : ℕ+} (hN : 2 ≤ (N : ℕ)) (X : Configuration N)
    (m v : ℝ) (hv : v ≤ 1) :
    ∫⁻ t in Ioc m (m + 1), ENNReal.ofReal (loopCount t v X)
      ≤ ENNReal.ofReal v * ENNReal.ofReal (loopCount m 2 X) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hmeas : ∀ ℓ : ℝ, Measurable (fun t : ℝ =>
      (if t < ℓ ∧ ℓ < t + v then (1 : ℝ≥0∞) else 0)) := fun ℓ =>
    Measurable.ite ((measurableSet_lt measurable_id measurable_const).inter
      (measurableSet_lt measurable_const (measurable_id.add_const v))) measurable_const
      measurable_const
  calc ∫⁻ t in Ioc m (m + 1), ENNReal.ofReal (loopCount t v X)
      ≤ ∫⁻ t in Ioc m (m + 1), ∑ i : Fin (N : ℕ), ∑' n : ℤ,
          (if t < loopArcPos N X i + n * N ∧ loopArcPos N X i + n * N < t + v then
            (1 : ℝ≥0∞) else 0) :=
        lintegral_mono fun t => smallRegion_ofReal_loopCount_le t v X
    _ = ∑ i : Fin (N : ℕ), ∑' n : ℤ, ∫⁻ t in Ioc m (m + 1),
          (if t < loopArcPos N X i + n * N ∧ loopArcPos N X i + n * N < t + v then
            (1 : ℝ≥0∞) else 0) := by
        rw [lintegral_finsetSum']
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [lintegral_tsum]
          intro n
          exact (hmeas _).aemeasurable
        · intro i _
          exact (Measurable.tsum fun n => hmeas _).aemeasurable
    _ ≤ ∑ i : Fin (N : ℕ), ∑' n : ℤ,
          (if m < loopArcPos N X i + n * N ∧ loopArcPos N X i + n * N < m + 2 then
            ENNReal.ofReal v else 0) :=
        Finset.sum_le_sum fun i _ => ENNReal.tsum_le_tsum fun n =>
          smallRegion_lintegral_cell_right m v _ hv
    _ ≤ ∑ i : Fin (N : ℕ), (if loopPos X i ∈ microArc N m 2 then ENNReal.ofReal v else 0) :=
        Finset.sum_le_sum fun i _ => smallRegion_tsum_window hN2 X i m _
    _ = ENNReal.ofReal v * ENNReal.ofReal (loopCount m 2 X) := by
        rw [smallRegion_ofReal_loopCount, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : loopPos X i ∈ microArc N m 2
        · rw [ite_eq_left h, ite_eq_left h, mul_one]
        · rw [ite_eq_right h, ite_eq_right h, mul_zero]

/-- Elementary bound `(u + v)^{-s-3} u v ≤ u^{-(s+1)/2} v^{-(s+1)/2}` for `u, v > 0`. -/
theorem smallRegion_rpow_bound {s : ℝ} (hs0 : 0 < s) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (u + v) ^ (-s - 3) * (u * v) ≤ u ^ (-((s + 1) / 2)) * v ^ (-((s + 1) / 2)) := by
  have huv : 0 < u + v := by linarith
  have hq : (0 : ℝ) ≤ (s + 3) / 2 := by linarith
  have h1 : (u + v) ^ (-s - 3) = (u + v) ^ (-((s + 3) / 2)) * (u + v) ^ (-((s + 3) / 2)) := by
    rw [← Real.rpow_add huv]
    congr 1
    ring
  have h2 : (u + v) ^ (-((s + 3) / 2)) ≤ u ^ (-((s + 3) / 2)) :=
    Real.rpow_le_rpow_of_nonpos hu (by linarith) (by linarith)
  have h3 : (u + v) ^ (-((s + 3) / 2)) ≤ v ^ (-((s + 3) / 2)) :=
    Real.rpow_le_rpow_of_nonpos hv (by linarith) (by linarith)
  have h4 : (u + v) ^ (-s - 3) ≤ u ^ (-((s + 3) / 2)) * v ^ (-((s + 3) / 2)) := by
    rw [h1]
    exact mul_le_mul h2 h3 (Real.rpow_nonneg huv.le _) (Real.rpow_nonneg hu.le _)
  have h5 : u ^ (-((s + 1) / 2)) = u ^ (-((s + 3) / 2)) * u := by
    rw [← Real.rpow_add_one hu.ne']
    congr 1
    ring
  have h6 : v ^ (-((s + 1) / 2)) = v ^ (-((s + 3) / 2)) * v := by
    rw [← Real.rpow_add_one hv.ne']
    congr 1
    ring
  calc (u + v) ^ (-s - 3) * (u * v)
      ≤ (u ^ (-((s + 3) / 2)) * v ^ (-((s + 3) / 2))) * (u * v) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = u ^ (-((s + 1) / 2)) * v ^ (-((s + 1) / 2)) := by rw [h5, h6]; ring

/-- The weight integral `∫∫_{u + v < 1} C (u + v)^{-s-3} u v` is finite for `0 < s < 1`. -/
theorem smallRegion_weight_lt_top {s C : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hC : 0 ≤ C) :
    ∫⁻ u in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
        (if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3)) else 0)
          * (ENNReal.ofReal u * ENNReal.ofReal v) < ⊤ := by
  set a : ℝ := (s + 1) / 2 with ha
  set ι : ℝ → ℝ≥0∞ := (Ioc (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (x ^ (-a))) with hι
  have hιm : Measurable ι :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).indicator measurableSet_Ioc
  set J : ℝ≥0∞ := ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ (-a)) with hJ
  have hJtop : J < ⊤ := by
    have hint : IntegrableOn (fun x : ℝ => x ^ (-a)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by rw [ha]; linarith))
    exact hint.lintegral_lt_top
  have hιJ : ∫⁻ x in Ioi (0 : ℝ), ι x ≤ J := by
    calc ∫⁻ x in Ioi (0 : ℝ), ι x ≤ ∫⁻ x, ι x := setLIntegral_le_lintegral _ _
      _ = J := lintegral_indicator measurableSet_Ioc _
  have hpt : ∀ u ∈ Ioi (0 : ℝ), ∀ v ∈ Ioi (0 : ℝ),
      (if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3)) else 0)
          * (ENNReal.ofReal u * ENNReal.ofReal v) ≤ ENNReal.ofReal C * (ι u * ι v) := by
    intro u hu v hv
    have hu0 : 0 < u := hu
    have hv0 : 0 < v := hv
    by_cases h : u + v < 1
    · rw [ite_eq_left h]
      have hu1 : u ∈ Ioc (0 : ℝ) 1 := ⟨hu0, by linarith⟩
      have hv1 : v ∈ Ioc (0 : ℝ) 1 := ⟨hv0, by linarith⟩
      rw [hι]
      simp only [Set.indicator_of_mem hu1, Set.indicator_of_mem hv1]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hu0.le _), ← ENNReal.ofReal_mul hC,
        ← ENNReal.ofReal_mul hu0.le, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := smallRegion_rpow_bound hs0 hu0 hv0
      calc C * (u + v) ^ (-s - 3) * (u * v) = C * ((u + v) ^ (-s - 3) * (u * v)) := by ring
        _ ≤ C * (u ^ (-a) * v ^ (-a)) := mul_le_mul_of_nonneg_left this hC
    · rw [ite_eq_right h, zero_mul]
      exact zero_le
  calc ∫⁻ u in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
        (if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3)) else 0)
          * (ENNReal.ofReal u * ENNReal.ofReal v)
      ≤ ∫⁻ u in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal C * ι u * ι v :=
        setLIntegral_mono' measurableSet_Ioi fun u hu =>
          setLIntegral_mono' measurableSet_Ioi fun v hv => by
            rw [mul_assoc]
            exact hpt u hu v hv
    _ = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal C * ι u * ∫⁻ v in Ioi (0 : ℝ), ι v := by
        refine lintegral_congr fun u => ?_
        rw [lintegral_const_mul _ hιm]
    _ ≤ ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal C * ι u * J :=
        lintegral_mono fun u => by gcongr
    _ = ENNReal.ofReal C * (∫⁻ u in Ioi (0 : ℝ), ι u) * J := by
        rw [lintegral_mul_const _ (hιm.const_mul _), lintegral_const_mul _ hιm]
    _ ≤ ENNReal.ofReal C * J * J := by gcongr
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJtop) hJtop

/-- Pointwise comparison of the product of two lift indicators, weighted by the kernel, with the pair integrand. -/
theorem smallRegion_pair_pointwise {s C : ℝ} (hC : 0 ≤ C) (t u v ℓ₁ ℓ₂ : ℝ) :
    (if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3)) else 0) *
        ((if t - u < ℓ₁ ∧ ℓ₁ < t - u + u then (1 : ℝ≥0∞) else 0) *
          (if t < ℓ₂ ∧ ℓ₂ < t + v then (1 : ℝ≥0∞) else 0))
      ≤ ENNReal.ofReal C * pairIntegrand s ℓ₁ ℓ₂ t u v := by
  by_cases hP : ℓ₁ < t ∧ t < ℓ₂ ∧ t - ℓ₁ < u ∧ ℓ₂ - t < v ∧ u + v < 1
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hP
    have e1 : t - u < ℓ₁ ∧ ℓ₁ < t - u + u := ⟨by linarith, by linarith⟩
    have e2 : t < ℓ₂ ∧ ℓ₂ < t + v := ⟨h2, by linarith⟩
    unfold pairIntegrand
    rw [ite_eq_left h5, ite_eq_left e1, ite_eq_left e2, ite_eq_left ⟨h1, h2, h3, h4, h5⟩,
      mul_one, mul_one, ← ENNReal.ofReal_mul hC]
  · have hz : pairIntegrand s ℓ₁ ℓ₂ t u v = 0 := by
      unfold pairIntegrand
      rw [ite_eq_right hP]
    rw [hz, mul_zero]
    refine nonpos_iff_eq_zero.mpr ?_
    by_cases h5 : u + v < 1
    · by_cases e1 : t - u < ℓ₁ ∧ ℓ₁ < t - u + u
      · by_cases e2 : t < ℓ₂ ∧ ℓ₂ < t + v
        · exact absurd ⟨by linarith [e1.2], e2.1, by linarith [e1.1], by linarith [e2.2], h5⟩ hP
        · rw [ite_eq_right e2, mul_zero, mul_zero]
      · rw [ite_eq_right e1, zero_mul, mul_zero]
    · rw [ite_eq_right h5, zero_mul]

/-- A constant factors out of the four-fold sum. -/
theorem smallRegion_sum4_const_mul (c : ℝ≥0∞) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : ι → ℤ → κ → ℤ → ℝ≥0∞) :
    ∑ i, ∑' n, ∑ j, ∑' n', c * Q i n j n' = c * ∑ i, ∑' n, ∑ j, ∑' n', Q i n j n' := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← ENNReal.tsum_mul_left]

/-- The lower integral of a four-fold sum of measurable functions is the four-fold sum of the integrals. -/
theorem smallRegion_lintegral_sum4 {α ι κ : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]
    (μ : Measure α) (R : ι → ℤ → κ → ℤ → α → ℝ≥0∞) (hR : ∀ i n j n', Measurable (R i n j n')) :
    ∫⁻ x, ∑ i, ∑' n, ∑ j, ∑' n', R i n j n' x ∂μ =
      ∑ i, ∑' n, ∑ j, ∑' n', ∫⁻ x, R i n j n' x ∂μ := by
  rw [lintegral_finsetSum']
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_tsum]
    · refine tsum_congr fun n => ?_
      rw [lintegral_finsetSum']
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_tsum]
        intro n'
        exact (hR i n j n').aemeasurable
      · intro j _
        exact (Measurable.tsum fun n' => hR i n j n').aemeasurable
    · intro n
      exact (Finset.measurable_sum _ fun j _ => Measurable.tsum fun n' => hR i n j n').aemeasurable
  · intro i _
    exact (Measurable.tsum fun n => Finset.measurable_sum _ fun j _ =>
      Measurable.tsum fun n' => hR i n j n').aemeasurable

/-- The pair integrand is jointly measurable in `(t, u, v)`. -/
theorem smallRegion_measurable_pairIntegrand (s ℓ₁ ℓ₂ : ℝ) :
    Measurable (fun p : ℝ × ℝ × ℝ => pairIntegrand s ℓ₁ ℓ₂ p.1 p.2.1 p.2.2) := by
  unfold pairIntegrand
  have h1 : Measurable (fun p : ℝ × ℝ × ℝ => p.1) := measurable_fst
  have h2 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.1) := measurable_fst.comp measurable_snd
  have h3 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.2) := measurable_snd.comp measurable_snd
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_lt measurable_const h1).inter
      ((measurableSet_lt h1 measurable_const).inter
        ((measurableSet_lt (h1.sub_const ℓ₁) h2).inter
          ((measurableSet_lt (measurable_const.sub h1) h3).inter
            (measurableSet_lt (h2.add h3) measurable_const))))
  · exact ENNReal.measurable_ofReal.comp ((h2.add h3).pow_const _)

/-- The product-measure integral of the pair integrand is at most the iterated integral over the cell and the whole of `ℝ²`. -/
theorem smallRegion_pair_flat_le (s m ℓ₁ ℓ₂ : ℝ) :
    ∫⁻ p : ℝ × ℝ × ℝ, pairIntegrand s ℓ₁ ℓ₂ p.1 p.2.1 p.2.2
        ∂((volume.restrict (Ioc m (m + 1))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
      ≤ ∫⁻ t in Ioc m (m + 1), ∫⁻ u, ∫⁻ v, pairIntegrand s ℓ₁ ℓ₂ t u v := by
  rw [← smallRegion_lintegral_flatten
    (f := fun p : ℝ × ℝ × ℝ => pairIntegrand s ℓ₁ ℓ₂ p.1 p.2.1 p.2.2)
    (smallRegion_measurable_pairIntegrand s ℓ₁ ℓ₂)]
  exact lintegral_mono' le_rfl fun t => lintegral_mono' Measure.restrict_le_self fun u =>
    lintegral_mono' Measure.restrict_le_self fun v => le_rfl

/-- The pair term `n₋ n₊` is bounded by the rooted energies, with the constant `C / ((s+1)(s+2))`. -/
theorem smallRegion_term_pairs {s C : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hC : 0 ≤ C)
    (W : ℝ → ℝ → ℝ≥0∞)
    (hW : ∀ u v, W u v = if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3)) else 0)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (X : Configuration N) (m : ℝ) :
    ∫⁻ p : ℝ × ℝ × ℝ, W p.2.1 p.2.2 *
        (ENNReal.ofReal (loopCount (p.1 - p.2.1) p.2.1 X) *
          ENNReal.ofReal (loopCount p.1 p.2.2 X))
        ∂((volume.restrict (Ioc m (m + 1))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
      ≤ ENNReal.ofReal C * (ENNReal.ofReal (((s + 1) * (s + 2))⁻¹) *
          ∑ i : Fin (N : ℕ), (if loopPos X i ∈ microArc N (m - 1) 2 then
            ENNReal.ofReal (rootedEnergy s X i) else 0)) := by
  calc _ ≤ ∫⁻ p : ℝ × ℝ × ℝ, ∑ i : Fin (N : ℕ), ∑' n : ℤ, ∑ j : Fin (N : ℕ), ∑' n' : ℤ,
          ENNReal.ofReal C * pairIntegrand s (loopArcPos N X i + n * N)
            (loopArcPos N X j + n' * N) p.1 p.2.1 p.2.2
          ∂((volume.restrict (Ioc m (m + 1))).prod
            ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) := by
        refine lintegral_mono fun p => ?_
        obtain ⟨t, u, v⟩ := p
        have ha := smallRegion_ofReal_loopCount_le (t - u) u X
        have hb := smallRegion_ofReal_loopCount_le t v X
        calc W u v * (ENNReal.ofReal (loopCount (t - u) u X) * ENNReal.ofReal (loopCount t v X))
            ≤ W u v * ((∑ i : Fin (N : ℕ), ∑' n : ℤ,
                (if t - u < loopArcPos N X i + n * N ∧ loopArcPos N X i + n * N < t - u + u then
                  (1 : ℝ≥0∞) else 0)) *
              (∑ j : Fin (N : ℕ), ∑' n' : ℤ,
                (if t < loopArcPos N X j + n' * N ∧ loopArcPos N X j + n' * N < t + v then
                  (1 : ℝ≥0∞) else 0))) := by gcongr
          _ = _ := smallRegion_sum_mul_sum _ _ _
          _ ≤ _ := by
            refine Finset.sum_le_sum fun i _ => ENNReal.tsum_le_tsum fun n =>
              Finset.sum_le_sum fun j _ => ENNReal.tsum_le_tsum fun n' => ?_
            rw [hW]
            exact smallRegion_pair_pointwise hC t u v _ _
    _ = ∑ i : Fin (N : ℕ), ∑' n : ℤ, ∑ j : Fin (N : ℕ), ∑' n' : ℤ,
          ∫⁻ p : ℝ × ℝ × ℝ, ENNReal.ofReal C * pairIntegrand s (loopArcPos N X i + n * N)
            (loopArcPos N X j + n' * N) p.1 p.2.1 p.2.2
          ∂((volume.restrict (Ioc m (m + 1))).prod
            ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) :=
        smallRegion_lintegral_sum4 (ι := Fin (N : ℕ)) (κ := Fin (N : ℕ))
          ((volume.restrict (Ioc m (m + 1))).prod
            ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
          (fun i n j n' p => ENNReal.ofReal C * pairIntegrand s (loopArcPos N X i + n * N)
            (loopArcPos N X j + n' * N) p.1 p.2.1 p.2.2)
          (fun i n j n' => (smallRegion_measurable_pairIntegrand s _ _).const_mul _)
    _ ≤ ∑ i : Fin (N : ℕ), ∑' n : ℤ, ∑ j : Fin (N : ℕ), ∑' n' : ℤ,
          ENNReal.ofReal C * ∫⁻ t in Ioc m (m + 1), ∫⁻ u, ∫⁻ v,
            pairIntegrand s (loopArcPos N X i + n * N) (loopArcPos N X j + n' * N) t u v := by
        refine Finset.sum_le_sum fun i _ => ENNReal.tsum_le_tsum fun n =>
          Finset.sum_le_sum fun j _ => ENNReal.tsum_le_tsum fun n' => ?_
        rw [lintegral_const_mul _ (smallRegion_measurable_pairIntegrand s _ _)]
        exact mul_le_mul_right (smallRegion_pair_flat_le s m _ _) _
    _ = ENNReal.ofReal C * ∑ i : Fin (N : ℕ), ∑' n : ℤ, ∑ j : Fin (N : ℕ), ∑' n' : ℤ,
          ∫⁻ t in Ioc m (m + 1), ∫⁻ u, ∫⁻ v,
            pairIntegrand s (loopArcPos N X i + n * N) (loopArcPos N X j + n' * N) t u v :=
        smallRegion_sum4_const_mul _ _
    _ ≤ _ := by
        gcongr
        exact sum_pairIntegrand_le hs0 hs1 N hN X m

/-- The kernel weight is measurable in `(u, v)`. -/
theorem smallRegion_measurable_W2 {s C : ℝ} (W : ℝ → ℝ → ℝ≥0∞)
    (hW : ∀ u v, W u v = if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3)) else 0) :
    Measurable (fun q : ℝ × ℝ => W q.1 q.2) := by
  have : (fun q : ℝ × ℝ => W q.1 q.2) = fun q : ℝ × ℝ =>
      if q.1 + q.2 < 1 then ENNReal.ofReal (C * (q.1 + q.2) ^ (-s - 3)) else 0 :=
    funext fun q => hW _ _
  rw [this]
  exact Measurable.ite (measurableSet_lt (measurable_fst.add measurable_snd) measurable_const)
    (ENNReal.measurable_ofReal.comp
      (measurable_const.mul ((measurable_fst.add measurable_snd).pow_const _)))
    measurable_const

/-- The kernel weight is measurable in `(t, u, v)`. -/
theorem smallRegion_measurable_W {s C : ℝ} (W : ℝ → ℝ → ℝ≥0∞)
    (hW : ∀ u v, W u v = if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3)) else 0) :
    Measurable (fun p : ℝ × ℝ × ℝ => W p.2.1 p.2.2) :=
  (smallRegion_measurable_W2 W hW).comp measurable_snd

/-- The kernel weight times `u v` is measurable in `(u, v)`. -/
theorem smallRegion_measurable_Wuv {s C : ℝ} (W : ℝ → ℝ → ℝ≥0∞)
    (hW : ∀ u v, W u v = if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3)) else 0) :
    Measurable (fun q : ℝ × ℝ => W q.1 q.2 * (ENNReal.ofReal q.1 * ENNReal.ofReal q.2)) :=
  (smallRegion_measurable_W2 W hW).mul
    ((ENNReal.measurable_ofReal.comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp measurable_snd))

/-- The left count `n₋(t, u)` is measurable in `(t, u, v)`. -/
theorem smallRegion_measurable_left {N : ℕ+} (X : Configuration N) :
    Measurable (fun p : ℝ × ℝ × ℝ => ENNReal.ofReal (loopCount (p.1 - p.2.1) p.2.1 X)) := by
  have h2 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.1) := measurable_fst.comp measurable_snd
  exact ENNReal.measurable_ofReal.comp (measurable_loopCount_of (c := fun _ => X)
    (a := fun p : ℝ × ℝ × ℝ => p.1 - p.2.1) (r := fun p : ℝ × ℝ × ℝ => p.2.1)
    (measurable_fst.sub h2) h2 measurable_const)

/-- The right count `n₊(t, v)` is measurable in `(t, u, v)`. -/
theorem smallRegion_measurable_right {N : ℕ+} (X : Configuration N) :
    Measurable (fun p : ℝ × ℝ × ℝ => ENNReal.ofReal (loopCount p.1 p.2.2 X)) := by
  have h3 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.2) := measurable_snd.comp measurable_snd
  exact ENNReal.measurable_ofReal.comp (measurable_loopCount_of (c := fun _ => X)
    (a := fun p : ℝ × ℝ × ℝ => p.1) (r := fun p : ℝ × ℝ × ℝ => p.2.2)
    measurable_fst h3 measurable_const)

/-- Pointwise expansion of `(n₋ + u)(n₊ + v)` into four terms. -/
theorem smallRegion_integrand_le {s C : ℝ} (W : ℝ → ℝ → ℝ≥0∞)
    (hW : ∀ u v, W u v = if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3)) else 0)
    {N : ℕ+} (X : Configuration N) (t u v : ℝ) :
    (if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3))
          * ENNReal.ofReal (loopCount (t - u) u X + u)
          * ENNReal.ofReal (loopCount t v X + v) else 0)
      ≤ W u v * (ENNReal.ofReal (loopCount (t - u) u X) * ENNReal.ofReal (loopCount t v X))
        + W u v * (ENNReal.ofReal (loopCount (t - u) u X) * ENNReal.ofReal v)
        + W u v * (ENNReal.ofReal u * ENNReal.ofReal (loopCount t v X))
        + W u v * (ENNReal.ofReal u * ENNReal.ofReal v) := by
  rw [hW u v]
  by_cases h : u + v < 1
  · rw [ite_eq_left h, ite_eq_left h]
    calc ENNReal.ofReal (C * (u + v) ^ (-s - 3)) * ENNReal.ofReal (loopCount (t - u) u X + u)
          * ENNReal.ofReal (loopCount t v X + v)
        ≤ ENNReal.ofReal (C * (u + v) ^ (-s - 3)) *
            ((ENNReal.ofReal (loopCount (t - u) u X) + ENNReal.ofReal u) *
              (ENNReal.ofReal (loopCount t v X) + ENNReal.ofReal v)) := by
          rw [mul_assoc]
          gcongr <;> exact ENNReal.ofReal_add_le
      _ = _ := by ring
  · rw [ite_eq_right h]
    simp

/-- The term `v n₋` is bounded by `D n(m - 1, 2)`, where `D` is the weight integral. -/
theorem smallRegion_term_left {s C : ℝ} (W : ℝ → ℝ → ℝ≥0∞)
    (hW : ∀ u v, W u v = if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3)) else 0)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (X : Configuration N) (m : ℝ) (D : ℝ≥0∞)
    (hD : D = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
      W u v * (ENNReal.ofReal u * ENNReal.ofReal v)) :
    ∫⁻ p : ℝ × ℝ × ℝ, W p.2.1 p.2.2 *
        (ENNReal.ofReal (loopCount (p.1 - p.2.1) p.2.1 X) * ENNReal.ofReal p.2.2)
        ∂((volume.restrict (Ioc m (m + 1))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
      ≤ D * ENNReal.ofReal (loopCount (m - 1) 2 X) := by
  have hWm := smallRegion_measurable_W (s := s) (C := C) W hW
  have h3 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.2) := measurable_snd.comp measurable_snd
  have hmeas : Measurable (fun p : ℝ × ℝ × ℝ => W p.2.1 p.2.2 *
      (ENNReal.ofReal (loopCount (p.1 - p.2.1) p.2.1 X) * ENNReal.ofReal p.2.2)) :=
    hWm.mul ((smallRegion_measurable_left X).mul (ENNReal.measurable_ofReal.comp h3))
  have hWq := smallRegion_measurable_Wuv (s := s) (C := C) W hW
  rw [lintegral_prod_symm _ hmeas.aemeasurable]
  calc _ ≤ ∫⁻ q : ℝ × ℝ, W q.1 q.2 * (ENNReal.ofReal q.1 * ENNReal.ofReal q.2) *
          ENNReal.ofReal (loopCount (m - 1) 2 X)
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
        refine lintegral_mono fun q => ?_
        obtain ⟨u, v⟩ := q
        by_cases hz : W u v * ENNReal.ofReal v = 0
        · have : ∀ t : ℝ, W u v * (ENNReal.ofReal (loopCount (t - u) u X) * ENNReal.ofReal v)
              = 0 := fun t => by
            rw [show W u v * (ENNReal.ofReal (loopCount (t - u) u X) * ENNReal.ofReal v)
              = (W u v * ENNReal.ofReal v) * ENNReal.ofReal (loopCount (t - u) u X) by ring, hz,
              zero_mul]
          simp only [this, lintegral_zero]
          exact zero_le
        · have hW0 : W u v ≠ 0 := fun h => hz (by rw [h, zero_mul])
          have hv0 : ENNReal.ofReal v ≠ 0 := fun h => hz (by rw [h, mul_zero])
          have hv : 0 < v := ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hv0)
          have huv : u + v < 1 := by
            by_contra hcon
            apply hW0
            rw [hW u v, ite_eq_right hcon]
          have hu1 : u ≤ 1 := by linarith
          have hm : Measurable (fun t : ℝ => ENNReal.ofReal (loopCount (t - u) u X)) :=
            ENNReal.measurable_ofReal.comp (measurable_loopCount_of (c := fun _ => X)
              (a := fun t : ℝ => t - u) (r := fun _ => u) (measurable_id.sub_const u)
              measurable_const measurable_const)
          calc ∫⁻ t, W u v * (ENNReal.ofReal (loopCount (t - u) u X) * ENNReal.ofReal v)
                ∂(volume.restrict (Ioc m (m + 1)))
              = (W u v * ENNReal.ofReal v) * ∫⁻ t in Ioc m (m + 1),
                  ENNReal.ofReal (loopCount (t - u) u X) := by
                rw [← lintegral_const_mul _ hm]
                refine lintegral_congr fun t => ?_
                ring
            _ ≤ (W u v * ENNReal.ofReal v) * (ENNReal.ofReal u *
                  ENNReal.ofReal (loopCount (m - 1) 2 X)) := by
                gcongr
                exact smallRegion_lintegral_left_count hN X m u hu1
            _ = _ := by ring
    _ = D * ENNReal.ofReal (loopCount (m - 1) 2 X) := by
        rw [lintegral_mul_const _ hWq, hD, lintegral_prod _ hWq.aemeasurable]

/-- The term `u n₊` is bounded by `D n(m, 2)`, where `D` is the weight integral. -/
theorem smallRegion_term_right {s C : ℝ} (W : ℝ → ℝ → ℝ≥0∞)
    (hW : ∀ u v, W u v = if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3)) else 0)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (X : Configuration N) (m : ℝ) (D : ℝ≥0∞)
    (hD : D = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
      W u v * (ENNReal.ofReal u * ENNReal.ofReal v)) :
    ∫⁻ p : ℝ × ℝ × ℝ, W p.2.1 p.2.2 *
        (ENNReal.ofReal p.2.1 * ENNReal.ofReal (loopCount p.1 p.2.2 X))
        ∂((volume.restrict (Ioc m (m + 1))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
      ≤ D * ENNReal.ofReal (loopCount m 2 X) := by
  have hWm := smallRegion_measurable_W (s := s) (C := C) W hW
  have h2 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.1) := measurable_fst.comp measurable_snd
  have hmeas : Measurable (fun p : ℝ × ℝ × ℝ => W p.2.1 p.2.2 *
      (ENNReal.ofReal p.2.1 * ENNReal.ofReal (loopCount p.1 p.2.2 X))) :=
    hWm.mul ((ENNReal.measurable_ofReal.comp h2).mul (smallRegion_measurable_right X))
  have hWq := smallRegion_measurable_Wuv (s := s) (C := C) W hW
  rw [lintegral_prod_symm _ hmeas.aemeasurable]
  calc _ ≤ ∫⁻ q : ℝ × ℝ, W q.1 q.2 * (ENNReal.ofReal q.1 * ENNReal.ofReal q.2) *
          ENNReal.ofReal (loopCount m 2 X)
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
        refine lintegral_mono fun q => ?_
        obtain ⟨u, v⟩ := q
        by_cases hz : W u v * ENNReal.ofReal u = 0
        · have : ∀ t : ℝ, W u v * (ENNReal.ofReal u * ENNReal.ofReal (loopCount t v X))
              = 0 := fun t => by
            rw [show W u v * (ENNReal.ofReal u * ENNReal.ofReal (loopCount t v X))
              = (W u v * ENNReal.ofReal u) * ENNReal.ofReal (loopCount t v X) by ring, hz,
              zero_mul]
          simp only [this, lintegral_zero]
          exact zero_le
        · have hW0 : W u v ≠ 0 := fun h => hz (by rw [h, zero_mul])
          have hu0 : ENNReal.ofReal u ≠ 0 := fun h => hz (by rw [h, mul_zero])
          have hu : 0 < u := ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hu0)
          have huv : u + v < 1 := by
            by_contra hcon
            apply hW0
            rw [hW u v, ite_eq_right hcon]
          have hv1 : v ≤ 1 := by linarith
          have hm : Measurable (fun t : ℝ => ENNReal.ofReal (loopCount t v X)) :=
            ENNReal.measurable_ofReal.comp (measurable_loopCount_of (c := fun _ => X)
              (a := fun t : ℝ => t) (r := fun _ => v) measurable_id
              measurable_const measurable_const)
          calc ∫⁻ t, W u v * (ENNReal.ofReal u * ENNReal.ofReal (loopCount t v X))
                ∂(volume.restrict (Ioc m (m + 1)))
              = (W u v * ENNReal.ofReal u) * ∫⁻ t in Ioc m (m + 1),
                  ENNReal.ofReal (loopCount t v X) := by
                rw [← lintegral_const_mul _ hm]
                refine lintegral_congr fun t => ?_
                ring
            _ ≤ (W u v * ENNReal.ofReal u) * (ENNReal.ofReal v *
                  ENNReal.ofReal (loopCount m 2 X)) := by
                gcongr
                exact smallRegion_lintegral_right_count hN X m v hv1
            _ = _ := by ring
    _ = D * ENNReal.ofReal (loopCount m 2 X) := by
        rw [lintegral_mul_const _ hWq, hD, lintegral_prod _ hWq.aemeasurable]

/-- The term `u v` integrates over the unit cell to the weight integral `D`. -/
theorem smallRegion_term_const {s C : ℝ} (W : ℝ → ℝ → ℝ≥0∞)
    (hW : ∀ u v, W u v = if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3)) else 0)
    (m : ℝ) (D : ℝ≥0∞)
    (hD : D = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
      W u v * (ENNReal.ofReal u * ENNReal.ofReal v)) :
    ∫⁻ p : ℝ × ℝ × ℝ, W p.2.1 p.2.2 * (ENNReal.ofReal p.2.1 * ENNReal.ofReal p.2.2)
        ∂((volume.restrict (Ioc m (m + 1))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
      = D := by
  have hWm := smallRegion_measurable_W (s := s) (C := C) W hW
  have h2 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.1) := measurable_fst.comp measurable_snd
  have h3 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.2) := measurable_snd.comp measurable_snd
  have hmeas : Measurable (fun p : ℝ × ℝ × ℝ => W p.2.1 p.2.2 *
      (ENNReal.ofReal p.2.1 * ENNReal.ofReal p.2.2)) :=
    hWm.mul ((ENNReal.measurable_ofReal.comp h2).mul (ENNReal.measurable_ofReal.comp h3))
  have hWq := smallRegion_measurable_Wuv (s := s) (C := C) W hW
  have hconst : ∫⁻ q : ℝ × ℝ, W q.1 q.2 * (ENNReal.ofReal q.1 * ENNReal.ofReal q.2)
      ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) = D := by
    rw [hD, lintegral_prod _ hWq.aemeasurable]
  rw [lintegral_prod _ hmeas.aemeasurable]
  simp only [hconst, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc]
  rw [show m + 1 - m = 1 by ring, ENNReal.ofReal_one, mul_one]

/-- The iterated integral over the cell is at most the sum of the four term bounds. -/
theorem smallRegion_nested_le {s C : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hC : 0 ≤ C)
    (W : ℝ → ℝ → ℝ≥0∞)
    (hW : ∀ u v, W u v = if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3)) else 0)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (X : Configuration N) (m : ℝ) (D : ℝ≥0∞)
    (hD : D = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
      W u v * (ENNReal.ofReal u * ENNReal.ofReal v)) :
    ∫⁻ t in Ioc m (m + 1), ∫⁻ u in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
        (if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3))
            * ENNReal.ofReal (loopCount (t - u) u X + u)
            * ENNReal.ofReal (loopCount t v X + v) else 0)
      ≤ ENNReal.ofReal C * (ENNReal.ofReal (((s + 1) * (s + 2))⁻¹) *
          ∑ i : Fin (N : ℕ), (if loopPos X i ∈ microArc N (m - 1) 2 then
            ENNReal.ofReal (rootedEnergy s X i) else 0))
        + D * ENNReal.ofReal (loopCount (m - 1) 2 X) + D * ENNReal.ofReal (loopCount m 2 X)
        + D := by
  have hWm := smallRegion_measurable_W (s := s) (C := C) W hW
  have h2 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.1) := measurable_fst.comp measurable_snd
  have h3 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.2) := measurable_snd.comp measurable_snd
  have hL := smallRegion_measurable_left X
  have hR := smallRegion_measurable_right X
  have hU : Measurable (fun p : ℝ × ℝ × ℝ => ENNReal.ofReal p.2.1) :=
    ENNReal.measurable_ofReal.comp h2
  have hV : Measurable (fun p : ℝ × ℝ × ℝ => ENNReal.ofReal p.2.2) :=
    ENNReal.measurable_ofReal.comp h3
  have m1 : Measurable (fun p : ℝ × ℝ × ℝ => W p.2.1 p.2.2 *
      (ENNReal.ofReal (loopCount (p.1 - p.2.1) p.2.1 X) *
        ENNReal.ofReal (loopCount p.1 p.2.2 X))) := hWm.mul (hL.mul hR)
  have m2 : Measurable (fun p : ℝ × ℝ × ℝ => W p.2.1 p.2.2 *
      (ENNReal.ofReal (loopCount (p.1 - p.2.1) p.2.1 X) * ENNReal.ofReal p.2.2)) :=
    hWm.mul (hL.mul hV)
  have m3 : Measurable (fun p : ℝ × ℝ × ℝ => W p.2.1 p.2.2 *
      (ENNReal.ofReal p.2.1 * ENNReal.ofReal (loopCount p.1 p.2.2 X))) := hWm.mul (hU.mul hR)
  have m4 : Measurable (fun p : ℝ × ℝ × ℝ => W p.2.1 p.2.2 *
      (ENNReal.ofReal p.2.1 * ENNReal.ofReal p.2.2)) := hWm.mul (hU.mul hV)
  have m12 : Measurable (fun p : ℝ × ℝ × ℝ => W p.2.1 p.2.2 *
      (ENNReal.ofReal (loopCount (p.1 - p.2.1) p.2.1 X) * ENNReal.ofReal (loopCount p.1 p.2.2 X))
      + W p.2.1 p.2.2 * (ENNReal.ofReal (loopCount (p.1 - p.2.1) p.2.1 X) *
        ENNReal.ofReal p.2.2)) := m1.add m2
  have m123 : Measurable (fun p : ℝ × ℝ × ℝ => W p.2.1 p.2.2 *
      (ENNReal.ofReal (loopCount (p.1 - p.2.1) p.2.1 X) * ENNReal.ofReal (loopCount p.1 p.2.2 X))
      + W p.2.1 p.2.2 * (ENNReal.ofReal (loopCount (p.1 - p.2.1) p.2.1 X) *
        ENNReal.ofReal p.2.2)
      + W p.2.1 p.2.2 * (ENNReal.ofReal p.2.1 * ENNReal.ofReal (loopCount p.1 p.2.2 X))) :=
    m12.add m3
  calc _ ≤ ∫⁻ t in Ioc m (m + 1), ∫⁻ u in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
        (W u v * (ENNReal.ofReal (loopCount (t - u) u X) * ENNReal.ofReal (loopCount t v X))
        + W u v * (ENNReal.ofReal (loopCount (t - u) u X) * ENNReal.ofReal v)
        + W u v * (ENNReal.ofReal u * ENNReal.ofReal (loopCount t v X))
        + W u v * (ENNReal.ofReal u * ENNReal.ofReal v)) :=
        lintegral_mono fun t => lintegral_mono fun u => lintegral_mono fun v =>
          smallRegion_integrand_le W hW X t u v
    _ = ∫⁻ p : ℝ × ℝ × ℝ,
        (W p.2.1 p.2.2 * (ENNReal.ofReal (loopCount (p.1 - p.2.1) p.2.1 X) *
            ENNReal.ofReal (loopCount p.1 p.2.2 X))
        + W p.2.1 p.2.2 * (ENNReal.ofReal (loopCount (p.1 - p.2.1) p.2.1 X) *
            ENNReal.ofReal p.2.2)
        + W p.2.1 p.2.2 * (ENNReal.ofReal p.2.1 * ENNReal.ofReal (loopCount p.1 p.2.2 X))
        + W p.2.1 p.2.2 * (ENNReal.ofReal p.2.1 * ENNReal.ofReal p.2.2))
        ∂((volume.restrict (Ioc m (m + 1))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) :=
        smallRegion_lintegral_flatten (m123.add m4)
    _ = ∫⁻ p : ℝ × ℝ × ℝ, W p.2.1 p.2.2 * (ENNReal.ofReal (loopCount (p.1 - p.2.1) p.2.1 X) *
            ENNReal.ofReal (loopCount p.1 p.2.2 X))
          ∂((volume.restrict (Ioc m (m + 1))).prod
            ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
        + ∫⁻ p : ℝ × ℝ × ℝ, W p.2.1 p.2.2 * (ENNReal.ofReal (loopCount (p.1 - p.2.1) p.2.1 X) *
            ENNReal.ofReal p.2.2)
          ∂((volume.restrict (Ioc m (m + 1))).prod
            ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
        + ∫⁻ p : ℝ × ℝ × ℝ, W p.2.1 p.2.2 *
            (ENNReal.ofReal p.2.1 * ENNReal.ofReal (loopCount p.1 p.2.2 X))
          ∂((volume.restrict (Ioc m (m + 1))).prod
            ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
        + ∫⁻ p : ℝ × ℝ × ℝ, W p.2.1 p.2.2 * (ENNReal.ofReal p.2.1 * ENNReal.ofReal p.2.2)
          ∂((volume.restrict (Ioc m (m + 1))).prod
            ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) := by
        rw [lintegral_add_left m123, lintegral_add_left m12, lintegral_add_left m1]
    _ ≤ _ := by
        rw [smallRegion_term_const W hW m D hD]
        gcongr
        · exact smallRegion_term_pairs hs0 hs1 hC W hW N hN X m
        · exact smallRegion_term_left W hW N hN X m D hD
        · exact smallRegion_term_right W hW N hN X m D hD

/-- **Small-region bound.** For `0 < s < 1`, `C ≥ 0` there is a constant `K ≥ 0` such that for
every `N ≥ 2`, configuration `X` and cell origin `m`,
`∫_{(m, m+1]} ∫_{u>0} ∫_{v>0} 1[u+v<1] C (u+v)^{-s-3} (n₋(t,u)+u) (n₊(t,v)+v) ≤
K (1 + n(m,2) + n(m-1,2) + ∑_{i : z_i ∈ (m-1,m+1)} E_i)`,
where `n₋(t,u) = loopCount (t-u) u X`, `n₊(t,v) = loopCount t v X`, `n(a,2) = loopCount a 2 X`
and `E_i = rootedEnergy s X i`. -/
theorem smallRegion_lintegral_le {s C : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (X : Configuration N) (m : ℝ),
      ∫⁻ t in Ioc m (m + 1), ∫⁻ u in Ioi 0, ∫⁻ v in Ioi 0,
          (if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3))
              * ENNReal.ofReal (loopCount (t - u) u X + u)
              * ENNReal.ofReal (loopCount t v X + v) else 0)
        ≤ ENNReal.ofReal K * (1 + ENNReal.ofReal (loopCount m 2 X)
            + ENNReal.ofReal (loopCount (m - 1) 2 X)
            + ∑ i : Fin (N : ℕ), (if loopPos X i ∈ microArc N (m - 1) 2 then
                ENNReal.ofReal (rootedEnergy s X i) else 0)) := by
  obtain ⟨W, hW⟩ : ∃ W : ℝ → ℝ → ℝ≥0∞, ∀ u v, W u v =
      if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3)) else 0 :=
    ⟨fun u v => if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3)) else 0,
      fun _ _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ≥0∞, D = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
      W u v * (ENNReal.ofReal u * ENNReal.ofReal v) := ⟨_, rfl⟩
  have hDtop : D < ⊤ := by
    have h := smallRegion_weight_lt_top hs0 hs1 hC
    rw [hD]
    simpa only [hW] using h
  have hr : (0 : ℝ) ≤ ((s + 1) * (s + 2))⁻¹ := by positivity
  refine ⟨D.toReal + C * ((s + 1) * (s + 2))⁻¹, by positivity, ?_⟩
  intro N hN X m
  refine (smallRegion_nested_le hs0 hs1 hC W hW N hN X m D hD).trans ?_
  have hK : ENNReal.ofReal (D.toReal + C * ((s + 1) * (s + 2))⁻¹) =
      D + ENNReal.ofReal C * ENNReal.ofReal (((s + 1) * (s + 2))⁻¹) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (mul_nonneg hC hr),
      ENNReal.ofReal_toReal hDtop.ne, ENNReal.ofReal_mul hC]
  rw [hK]
  have key : ∀ (a b c d : ℝ≥0∞), a * d + b * c ≤ (a + b) * (d + c) := fun a b c d => by
    calc a * d + b * c ≤ (a * d + b * c) + (a * c + b * d) := le_self_add
      _ = (a + b) * (d + c) := by ring
  refine le_trans (le_of_eq ?_) (key D (ENNReal.ofReal C * ENNReal.ofReal (((s + 1) * (s + 2))⁻¹))
    (∑ i : Fin (N : ℕ), (if loopPos X i ∈ microArc N (m - 1) 2 then
      ENNReal.ofReal (rootedEnergy s X i) else 0))
    (1 + ENNReal.ofReal (loopCount m 2 X) + ENNReal.ofReal (loopCount (m - 1) 2 X)))
  ring

end Riesz1

end
end
