/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PuncturedTransportBounds
public import Riesz1.ToMathlib.FiniteMarkDistance
public import Riesz1.ToMathlib.CircleSingularityLocalization

/-!
# First derivative power bounds on a fixed circle

Local integration at each marked point and local boundedness elsewhere give one
power envelope on a compact interval. The resulting coefficient depends on the fixed
circle and function. This supports the macroscopic case of
Lemma 5.1.
-/

public section

open Set Filter
open scoped Topology

namespace Riesz1.CircleSingularity

/-- On a fixed circle, integrating the derivative envelope gives a capped-distance
bound for `q` on every compact real interval. This is an internal analytic helper:
the hypotheses describe `q` and its derivative rather than an admissible profile. -/
theorem exists_abs_le_cappedMarkDistance_on_compact {T b C : ℝ} (hT : 0 < T)
    (hb : 0 < b) (hC : 0 ≤ C) {ι : Type*} [Fintype ι] [Nonempty ι]
    (marks : ι → AddCircle T) (q : ℝ → ℝ)
    (hq : ∀ x : ℝ, (∀ j, (x : AddCircle T) ≠ marks j) → DifferentiableAt ℝ q x)
    (hbound : ∀ x : ℝ, (∀ j, (x : AddCircle T) ≠ marks j) →
      |deriv q x| ≤ C * (1 + ∑ j, dist (x : AddCircle T) (marks j) ^ (-1 - b)))
    (S : Set ℝ) (hS : IsCompact S) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ∈ S, (∀ j, (x : AddCircle T) ≠ marks j) →
      |q x| ≤ K * cappedMarkDistance marks (x : AddCircle T) ^ (-b) := by
  classical
  have : Fact (0 < T) := ⟨hT⟩
  have hlocal (a : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ᶠ t : ℝ in 𝓝 a,
      (∀ j, (t : AddCircle T) ≠ marks j) →
        |q t| ≤ K * cappedMarkDistance marks (t : AddCircle T) ^ (-b) := by
    by_cases ha : ∀ j, (a : AddCircle T) ≠ marks j
    · have hc := (hq a ha).continuousAt.abs
      refine ⟨|q a| + 1, by positivity, ?_⟩
      filter_upwards [hc.eventually (gt_mem_nhds (lt_add_one |q a|))] with t ht htm
      have hp : 1 ≤ cappedMarkDistance marks (t : AddCircle T) ^ (-b) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        (cappedMarkDistance_pos marks _ htm) (cappedMarkDistance_le_one marks _) (by linarith)
      exact ht.le.trans (le_mul_of_one_le_right (by positivity) hp)
    · push Not at ha
      obtain ⟨j, haj⟩ := ha
      obtain ⟨R, D, hR, hR1, hD, hloc⟩ := exists_punctured_power_bound hT marks
        (e := -1 - b) (by linarith) a
      let R' := min R (T / 2)
      have hR' : 0 < R' := lt_min hR (by linarith)
      have hloc' : ∀ t : ℝ, 0 < |t - a| → |t - a| ≤ R' →
          DifferentiableAt ℝ q t ∧ |deriv q t| ≤ (C * (1 + D)) * |t - a| ^ (-1 - b) := by
        intro t ht htR
        obtain ⟨hn, hs⟩ := hloc t ht (htR.trans (min_le_left _ _))
        refine ⟨hq t hn, (hbound t hn).trans ?_⟩
        have hone : 1 ≤ |t - a| ^ (-1 - b) :=
          Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht
            ((htR.trans (min_le_left _ _)).trans hR1) (by linarith)
        nlinarith [mul_le_mul_of_nonneg_left hs hC,
          mul_le_mul_of_nonneg_left hone hC]
      obtain ⟨K, hK, hbK⟩ := PuncturedDerivative.exists_abs_le_rpow_punctured hb
        (by positivity : 0 ≤ C * (1 + D)) hR'
        (fun t ht htR => (hloc' t ht htR).1) (fun t ht htR => (hloc' t ht htR).2)
      refine ⟨K, hK, ?_⟩
      filter_upwards [Metric.ball_mem_nhds a hR'] with t ht htm
      have htR : |t - a| ≤ R' := by
        exact (show |t - a| < R' from ht).le
      have hta : 0 < |t - a| := abs_pos.mpr (sub_ne_zero.mpr (fun he =>
        htm j (by simpa only [he] using haj)))
      have hd : dist (t : AddCircle T) (a : AddCircle T) = |t - a| :=
        dist_coe_eq_abs_sub hT (htR.trans (min_le_right _ _))
      have hr : cappedMarkDistance marks (t : AddCircle T) ≤ |t - a| := by
        rw [← hd, haj]
        exact cappedMarkDistance_le_dist marks _ j
      exact (hbK t hta htR).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (cappedMarkDistance_pos marks _ htm) hr (by linarith)) hK.le)
  choose K hK hlocalK using hlocal
  let U : ℝ → Set ℝ := fun a => {t | (∀ j, (t : AddCircle T) ≠ marks j) →
    |q t| ≤ K a * cappedMarkDistance marks (t : AddCircle T) ^ (-b)}
  obtain ⟨I, _, hcover⟩ := hS.elim_nhds_subcover U (fun a _ => hlocalK a)
  have hsum : 0 ≤ ∑ a ∈ I, K a := Finset.sum_nonneg fun a _ => (hK a).le
  refine ⟨(∑ a ∈ I, K a) + 1, by positivity, fun x hx hxm => ?_⟩
  obtain ⟨a, ha, hax⟩ := mem_iUnion₂.mp (hcover hx)
  have haK : K a ≤ (∑ a ∈ I, K a) + 1 :=
    (Finset.single_le_sum (fun a _ => (hK a).le) ha).trans (by linarith)
  exact (hax hxm).trans (mul_le_mul_of_nonneg_right haK
    (Real.rpow_nonneg (cappedMarkDistance_pos marks _ hxm).le _))

end Riesz1.CircleSingularity
