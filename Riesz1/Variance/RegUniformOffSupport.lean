/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformTails
public import Riesz1.Variance.RegUniformAdmissibilityMacro

/-! # Off-support estimates at the admissibility cutoff

Auxiliary estimates for Lemma 5.1, with constants before
all observation circles. No new analytic objects are defined.
-/

public section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Riesz1.Internal

/-- A fixed real mark absorbs the constant term in the inner envelope,
uniformly over every circle length. -/
theorem inner_mark_power_sum (L : Length) (n : ℕ+)
    (marks : Fin (n : ℕ) → ℝ) {e x : ℝ} (he : e ≤ 0)
    (hx : dist (x : Circle L) 0 ≤ 1)
    (hne : ∀ j, (x : Circle L) ≠ (marks j : Circle L)) :
    1 ≤ (2 + |marks ⟨0, n.pos⟩|) ^ (-e) *
      ∑ j, dist (x : Circle L) (marks j : Circle L) ^ e := by
  let j : Fin (n : ℕ) := ⟨0, n.pos⟩
  let R := 2 + |marks j|
  have hR : 0 < R := by dsimp [R]; positivity
  have hd : dist (x : Circle L) (marks j : Circle L) ≤ R := by
    have hm : dist (marks j : Circle L) 0 ≤ |marks j| := by
      rw [dist_zero_right]
      exact QuotientAddGroup.norm_mk_le_norm
    have ht := dist_triangle (x : Circle L) 0 (marks j : Circle L)
    rw [dist_comm (0 : Circle L)] at ht
    dsimp [R]
    linarith
  have hp := Real.rpow_le_rpow_of_nonpos (dist_pos.mpr (hne j)) hd he
  have hs := Finset.single_le_sum (f := fun j =>
    dist (x : Circle L) (marks j : Circle L) ^ e)
    (fun _ _ => by positivity) (Finset.mem_univ j)
  have hid : R ^ (-e) * R ^ e = 1 := by
    rw [← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero]
  change 1 ≤ R ^ (-e) * _
  rw [← hid]
  exact mul_le_mul_of_nonneg_left (hp.trans hs) (by positivity)

/-- Uniform off-support second derivatives, on every lift at distance at
least three quarters. This includes the windows centered at distance one. -/
theorem compact_transport_second_off_support (P : Parameters) (p : Profile)
    (hp : CompactProfile p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Scale)
      (ψ : Circle (observationLength a) → ℝ), Continuous ψ →
      ∀ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
      (∀ k, coeff (observationLength a) ⟨(fun x => (ψ x : ℂ)),
        complexL2Integrable _ _ hψ⟩ k = transportCoeffs P (observationLength a)
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) →
      ∀ x : ℝ, 3 / 4 ≤ dist (x : Circle (observationLength a)) 0 →
        ContDiffAt ℝ ∞ (fun t : ℝ => ψ (t : Circle (observationLength a))) x ∧
        |deriv (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) x| ≤
          C * dist (x : Circle (observationLength a)) 0 ^ (P.val.2 - 3) := by
  obtain ⟨D, hD, hoff⟩ := uniform_transport_deriv_off_support P 2 (by norm_num)
  obtain ⟨r, hr, hrhalf, hsupp⟩ := hp
  let Z := ∫ y : ℝ, |zeroExtension p y|
  let C := D * Z * 4 ^ (3 - P.val.2) + 1
  have hZ : 0 ≤ Z := integral_nonneg fun _ => abs_nonneg _
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun a ψ hc hψ hcoeff x hx => ?_⟩
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  let z := centralRep L (x : Circle L)
  have hzx : (z : Circle L) = (x : Circle L) := AddCircle.coe_equivIco
  have hzL : |z| ≤ L.val / 2 := by
    have hm := centralRep_mem_Ico L (x : Circle L)
    exact abs_le.mpr ⟨hm.1, hm.2.le⟩
  have hdist : dist (x : Circle L) 0 = |z| := by
    rw [← hzx]
    simpa only [AddCircle.coe_zero, sub_zero] using
      CircleSingularity.dist_coe_eq_abs_sub L.property (x := z) (y := 0) (by simpa using hzL)
  have hz : 3 / 4 ≤ |z| := by rwa [hdist] at hx
  have hb := hoff p a ψ hc hψ hcoeff r (|z| / 4) z hr hrhalf
    (by linarith) hsupp (by linarith) hzL
  have hid : (|z| / 4) ^ (P.val.2 - 3) =
      |z| ^ (P.val.2 - 3) * 4 ^ (3 - P.val.2) := by
    rw [Real.div_rpow (abs_nonneg z) (by norm_num : (0 : ℝ) ≤ 4),
      div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    congr 2
    ring
  have hh : |deriv (deriv (fun t : ℝ => ψ (t : Circle L))) z| ≤
      C * |z| ^ (P.val.2 - 3) := by
    have ht := hb.2
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, Real.norm_eq_abs,
      Nat.cast_ofNat, show P.val.2 - 1 - 2 = P.val.2 - 3 by ring] at ht
    rw [hid] at ht
    dsimp [C]
    nlinarith [Real.rpow_nonneg (abs_nonneg z) (P.val.2 - 3)]
  rw [deriv_deriv_circle_lift_eq_of_coe_eq ψ hzx, ← hdist] at hh
  exact ⟨contDiffAt_circle_lift_of_coe_eq ψ hzx hb.1, hh⟩

/-- Smoothing preserves the second transport tail from distance one, for
small radii. The input can have singularities elsewhere on the circle. -/
theorem compact_smoothed_second_tail (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Scale)
      (ψ : Circle (observationLength a) → ℝ), Continuous ψ →
      ∀ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
      (∀ k, coeff (observationLength a) ⟨(fun x => (ψ x : ℂ)),
        complexL2Integrable _ _ hψ⟩ k = transportCoeffs P (observationLength a)
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) →
      LocallyIntegrable (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) volume →
      (∀ u v, AbsolutelyContinuousOnInterval
        (fun t : ℝ => ψ (t : Circle (observationLength a))) u v) →
      ∀ h : ℝ, 0 < h → h ≤ 1 / 4 → ∀ x : ℝ,
        1 ≤ dist (x : Circle (observationLength a)) 0 →
        |deriv (deriv (circleMollify ρ (observationLength a).val h
          (fun t : ℝ => ψ (t : Circle (observationLength a))))) x| ≤
          C * dist (x : Circle (observationLength a)) 0 ^ (P.val.2 - 3) := by
  obtain ⟨K, hK, hb⟩ := compact_transport_second_off_support P p hp
  refine ⟨K * 2 ^ (3 - P.val.2), by positivity, fun a ψ hc hψ hcoeff hi hAC h hh hh1 x hx => ?_⟩
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  let F := fun t : ℝ => ψ (t : Circle L)
  let δ := fun t : ℝ => dist (t : Circle L) 0
  have hδ (y z : ℝ) : δ y ≤ δ z + |y - z| := by
    simp only [δ, dist_coe_zero_eq_circDist]
    exact circDist_le_add_abs L.property y z
  have hpF : Function.Periodic F L.val := by intro t; simp only [F, AddCircle.coe_add_period]
  have heq : deriv (circleMollify ρ L.val h F) = mollifyLine ρ h (deriv F) := by
    funext t
    have hFc : Continuous F := hc.comp (AddCircle.continuous_mk' L.val)
    rw [deriv_circleMollify_of_absolutelyContinuous hρ L.property hh hFc hpF hAC,
      circleMollify_eq_mollifyLine hρ L.property hh hi (Riesz1.periodic_deriv hpF)]
  change |deriv (deriv (circleMollify ρ L.val h F)) x| ≤ _
  rw [heq]
  apply abs_deriv_mollifyLine_le_of_local hρ hh (by positivity) hi
  · intro y hy
    have ht := hδ x y
    rw [abs_sub_comm x y] at ht
    exact ((hb a ψ hc hψ hcoeff y (by change 3 / 4 ≤ δ y; change 1 ≤ δ x at hx; linarith)).1.derivWithin
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  · intro y hy
    have ht := hδ x y
    rw [abs_sub_comm x y] at ht
    have hyδ : 3 / 4 ≤ δ y := by change 1 ≤ δ x at hx; linarith
    have hhalf : δ x / 2 ≤ δ y := by change 1 ≤ δ x at hx; linarith
    have hp := Real.rpow_le_rpow_of_nonpos (by change 1 ≤ δ x at hx; linarith : 0 < δ x / 2)
      hhalf (show P.val.2 - 3 ≤ 0 by linarith [P.property.2.2])
    have hid : (δ x / 2) ^ (P.val.2 - 3) = δ x ^ (P.val.2 - 3) * 2 ^ (3 - P.val.2) := by
      simpa only [show -(3 - P.val.2) = P.val.2 - 3 by ring] using
        div_two_rpow_neg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hx) (p := 3 - P.val.2)
    rw [hid] at hp
    exact (hb a ψ hc hψ hcoeff y hyδ).2.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hK.le])

end Riesz1.Internal
