/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PositiveRadiusPartition
public import Riesz1.ToMathlib.SmoothCircleRadius

/-! # A separation-free decomposition for the loop error

This is the analytic splitting step in the proof of the second error bound in Theorem 3.
It splits the first transport derivative itself, rather than requiring
each piece to be a derivative of a periodic transport. The constant is
chosen before the period, smoothing scale and marked points. The first
derivative bound for the resulting pieces has no separation loss.
-/

public section

open scoped ContDiff BigOperators

namespace Riesz1.Internal

/-- Adjacent power envelopes for the clipped geodesic radius can be
replaced with smooth chord radii, at a uniform cost. -/
theorem errorTwo_radius_power_comparison (L h : {r : ℝ // 0 < r})
    {q : ℝ} (hq : 0 ≤ q) (x : ℝ) :
    max (circDist L.val x) h.val ^ (-q) ≤
        2 ^ q * smoothCircleRadius L h x ^ (-q) ∧
      smoothCircleRadius L h x ^ (-q) ≤
        (Real.pi / 2) ^ q * max (circDist L.val x) h.val ^ (-q) := by
  have hpos : 0 < max (circDist L.val x) h.val := lt_max_of_lt_right h.property
  obtain ⟨hl, hu⟩ := smoothCircleRadius_comparison L h x
  constructor
  · have hh := Real.rpow_le_rpow_of_nonpos (smoothCircleRadius_pos L h x) hu
      (neg_nonpos.mpr hq)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hpos.le] at hh
    have he : (2 : ℝ) ^ q * 2 ^ (-q) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero]
    have hh' := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q)
    rw [← mul_assoc, he, one_mul] at hh'
    exact hh'
  · have hh := Real.rpow_le_rpow_of_nonpos
      (mul_pos (div_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hpos) hl
        (neg_nonpos.mpr hq)
    rw [Real.mul_rpow (by positivity : 0 ≤ 2 / Real.pi) hpos.le] at hh
    have he : (2 / Real.pi : ℝ) ^ (-q) = (Real.pi / 2) ^ q := by
      rw [Real.rpow_neg_eq_inv_rpow, inv_div]
    rwa [he] at hh

/-- Smooth pieces for finitely many possibly coincident marks. The
singular pieces are centered at the original marks. The last piece is
the background. The estimate is uniform in every period and radius.
Tail estimates are supplied separately by the normalized-weight lemma. -/
theorem errorTwo_decomposition_radii (n : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L h : {r : ℝ // 0 < r}) (marks : Fin n → ℝ)
      (A : ℝ), 0 ≤ A → ∀ F : ℝ → ℝ,
        ContDiff ℝ ∞ F → Function.Periodic F L.val →
        (∀ x, |F x| ≤ A * (1 + ∑ j,
          max (circDist L.val (x - marks j)) h.val ^ (-b))) →
        (∀ x, |deriv F x| ≤ A * (1 + ∑ j,
          max (circDist L.val (x - marks j)) h.val ^ (-1 - b))) →
        ∃ φ : Fin (n + 1) → ℝ → ℝ,
          (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) L.val) ∧
          (∀ x, ∑ j, φ j x = F x) ∧
          (∀ j : Fin n, ∀ x, |deriv (φ j.castSucc) x| ≤
            C * A * max (circDist L.val (x - marks j)) h.val ^ (-1 - b)) ∧
          (∀ x, |deriv (φ (Fin.last n)) x| ≤ C * A) ∧
          (∀ j x, φ j x = F x *
            (Fin.lastCases 1 (fun i => smoothCircleRadius L h (x - marks i)) j) ^ (-1 - b) /
            (1 + ∑ i, smoothCircleRadius L h (x - marks i) ^ (-1 - b))) := by
  classical
  let B := (2 : ℝ) ^ (1 + b)
  let D := 1 + 2 * ((n + 1 : ℕ) : ℝ) * (1 + b)
  let E := (Real.pi / 2) ^ (1 + b)
  have hB : 0 < B := Real.rpow_pos_of_pos (by norm_num) _
  have hB1 : 1 ≤ B := Real.one_le_rpow (by norm_num) (by linarith)
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 < E := Real.rpow_pos_of_pos (by positivity) _
  have hE1 : 1 ≤ E := Real.one_le_rpow (by nlinarith [Real.two_le_pi]) (by linarith)
  refine ⟨B * D * E, by positivity, fun L h marks A hA F hF hp hval hder => ?_⟩
  let d : Fin (n + 1) → ℝ → ℝ :=
    Fin.lastCases (fun _ => 1) (fun j x => smoothCircleRadius L h (x - marks j))
  have dlast : d (Fin.last n) = fun _ => 1 := by simp [d]
  have dcast (i : Fin n) : d i.castSucc = fun x => smoothCircleRadius L h (x - marks i) := by
    simp [d]
  have hd (j : Fin (n + 1)) : ContDiff ℝ ∞ (d j) := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [dlast]; exact contDiff_const
    · rw [dcast]; exact (contDiff_smoothCircleRadius L h).comp (contDiff_id.sub contDiff_const)
  have hdp (j : Fin (n + 1)) : Function.Periodic (d j) L.val := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [dlast]; exact fun _ => rfl
    · rw [dcast]
      intro x
      dsimp only
      rw [show x + L.val - marks i = (x - marks i) + L.val by ring]
      exact periodic_smoothCircleRadius L h (x - marks i)
  have hpos (j : Fin (n + 1)) (x : ℝ) : 0 < d j x := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [dlast]; exact one_pos
    · rw [dcast]; exact smoothCircleRadius_pos L h _
  have hdv (j : Fin (n + 1)) (x : ℝ) : |deriv (d j) x| ≤ 1 := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [d]
    · rw [dcast]
      rw [show deriv (fun y => smoothCircleRadius L h (y - marks i)) x =
        deriv (smoothCircleRadius L h) (x - marks i) from
        ((contDiff_smoothCircleRadius L h).differentiable (by simp) _).hasDerivAt.comp_sub_const
          x (marks i) |>.deriv]
      exact abs_deriv_smoothCircleRadius_le_one L h _
  have hsum (q : ℝ) (hq : 0 ≤ q) (hqB : 2 ^ q ≤ B) (x : ℝ) :
      1 + ∑ j, max (circDist L.val (x - marks j)) h.val ^ (-q) ≤
        B * (∑ j, d j x ^ (-q)) := by
    rw [Fin.sum_univ_castSucc, dlast, Real.one_rpow,
      mul_add, mul_one]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      ((errorTwo_radius_power_comparison L h hq (x - marks j)).1).trans
        (mul_le_mul_of_nonneg_right hqB
          (Real.rpow_nonneg (smoothCircleRadius_pos L h _).le _)))
    rw [← Finset.mul_sum] at hh
    simp only [dcast] at hh ⊢
    simpa only [add_comm] using add_le_add hB1 hh
  have hval' (x : ℝ) : |F x| ≤ (A * B) * (∑ j, d j x ^ (-b)) := by
    have hh := (hval x).trans (mul_le_mul_of_nonneg_left
      (hsum b hb (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)) x) hA)
    simpa only [mul_assoc] using hh
  have hder' (x : ℝ) : |deriv F x| ≤ (A * B) * (∑ j, d j x ^ (-1 - b)) := by
    have hh := (hder x).trans (mul_le_mul_of_nonneg_left
      (by simpa only [show -(1 + b) = -1 - b by ring] using
        hsum (1 + b) (by linarith) le_rfl x) hA)
    simpa only [mul_assoc] using hh
  obtain ⟨φ, hφeq, hφ, hsumφ, hbound⟩ := positive_radii_partition hF hp hd hdp hpos hdv
    (mul_nonneg hA hB.le) hb hval' hder'
  have hbound' (j : Fin (n + 1)) (x : ℝ) :
      |deriv (φ j) x| ≤ A * B * D * d j x ^ (-1 - b) := by
    simpa only [Fintype.card_fin] using hbound j x
  refine ⟨φ, hφ, hsumφ, ?_, ?_, ?_⟩
  · intro j x
    have hh := (hbound' j.castSucc x).trans (mul_le_mul_of_nonneg_left
      (by simpa only [dcast, show -(1 + b) = -1 - b by ring] using
        (errorTwo_radius_power_comparison L h (q := 1 + b)
          (by linarith) (x - marks j)).2)
      (mul_nonneg (mul_nonneg hA hB.le) hD.le))
    change |deriv (φ j.castSucc) x| ≤ _ at hh
    convert hh using 1
    dsimp [B, D, E]
    ring
  · intro x
    have hh := hbound' (Fin.last n) x
    rw [dlast] at hh
    rw [Real.one_rpow, mul_one] at hh
    have hh' := hh.trans (le_mul_of_one_le_right
      (mul_nonneg (mul_nonneg hA hB.le) hD.le) hE1)
    convert hh' using 1
    ring
  · intro j x
    rw [hφeq]
    have heq : d j x = Fin.lastCases 1 (fun i => smoothCircleRadius L h (x - marks i)) j := by
      refine Fin.lastCases ?_ (fun i => ?_) j <;> simp only [dlast, dcast,
        Fin.lastCases_last, Fin.lastCases_castSucc]
    rw [heq]
    congr 1
    rw [Fin.sum_univ_castSucc]
    simp only [dlast, dcast, Real.one_rpow]
    ring

end Riesz1.Internal
