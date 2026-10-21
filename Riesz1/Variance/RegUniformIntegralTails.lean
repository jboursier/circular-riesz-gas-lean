/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformOffSupport

/-! # Compact transport tails with a common integral bound

Internal estimates for the family clause of Lemma 5.1.
-/

public section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace Riesz1.Internal

/-- Kernel tails depend on the profile only through a common line integral
bound. The constant precedes the profile and the observation circle. -/
theorem compact_transport_power_of_integral_bound (P : Parameters) (m : ℕ)
    (hm : 1 ≤ m) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Profile), CompactProfile p →
      (∫ y : ℝ, |zeroExtension p y|) ≤ Z →
      ∀ (a : Scale) (ψ : Circle (observationLength a) → ℝ), Continuous ψ →
      ∀ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
      (∀ k, coeff (observationLength a) ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
        transportCoeffs P (observationLength a)
          ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) →
      ∀ x : ℝ, 1 ≤ dist (x : Circle (observationLength a)) 0 →
        ContDiffAt ℝ ∞ (fun t : ℝ => ψ (t : Circle (observationLength a))) x ∧
        ‖iteratedDeriv m (fun t : ℝ => ψ (t : Circle (observationLength a))) x‖ ≤
          C * dist (x : Circle (observationLength a)) 0 ^ (P.val.2 - 1 - (m : ℝ)) := by
  obtain ⟨D, hD, hoff⟩ := uniform_transport_deriv_off_support P m hm
  let C := D * Z * 2 ^ (1 + (m : ℝ) - P.val.2) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun p hp hnorm a ψ hc hψ hcoeff x hx => ?_⟩
  obtain ⟨r, hr, hrhalf, hsupp⟩ := hp
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
  have hz : 1 ≤ |z| := by rwa [hdist] at hx
  have hb := hoff p a ψ hc hψ hcoeff r (|z| / 2) z hr hrhalf
    (by linarith) hsupp (by linarith) hzL
  have hid : (|z| / 2) ^ (P.val.2 - 1 - (m : ℝ)) =
      |z| ^ (P.val.2 - 1 - (m : ℝ)) * 2 ^ (1 + (m : ℝ) - P.val.2) := by
    rw [Real.div_rpow (abs_nonneg z) (by norm_num : (0 : ℝ) ≤ 2),
      div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    ring
  have hh : ‖iteratedDeriv m (fun t : ℝ => ψ (t : Circle L)) z‖ ≤
      C * |z| ^ (P.val.2 - 1 - (m : ℝ)) := by
    have ht := hb.2
    rw [hid] at ht
    have hZnonneg : 0 ≤ ∫ y : ℝ, |zeroExtension p y| := integral_nonneg fun _ => abs_nonneg _
    have hprod : D * (∫ y : ℝ, |zeroExtension p y|) ≤ D * Z :=
      mul_le_mul_of_nonneg_left hnorm hD.le
    have hpow : 0 ≤ |z| ^ (P.val.2 - 1 - (m : ℝ)) * 2 ^ (1 + (m : ℝ) - P.val.2) := by positivity
    simp only [Real.norm_eq_abs] at ht ⊢
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_right hprod hpow, Real.rpow_nonneg (abs_nonneg z) (P.val.2 - 1 - (m : ℝ))]
  have hiter : iteratedDeriv m (fun t : ℝ => ψ (t : Circle L)) z =
      iteratedDeriv m (fun t : ℝ => ψ (t : Circle L)) x := by
    have hper : Function.Periodic (fun t : ℝ => ψ (t : Circle L)) L.val := by
      intro t; simp only [AddCircle.coe_add_period]
    have heq := circle_lift_translation ψ hzx
    have hid' := congrArg (fun F : ℝ → ℝ => iteratedDeriv m F x) heq
    rw [iteratedDeriv_comp_const_add m (fun u : ℝ => ψ (u : Circle L)) (z - x)] at hid'
    simpa only [sub_add_cancel] using hid'
  rw [hiter, ← hdist] at hh
  exact ⟨contDiffAt_circle_lift_of_coe_eq ψ hzx hb.1, hh⟩

/-- Both smoothed compact transport tails with one constant before every
profile whose line integral norm is bounded by `Z`. -/
theorem compact_smoothed_tails_of_integral_bound (P : Parameters) (Z : ℝ) (hZ : 0 ≤ Z)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Profile), CompactProfile p →
      (∫ y : ℝ, |zeroExtension p y|) ≤ Z →
      ∀ (a : Scale) (ψ : Circle (observationLength a) → ℝ), Continuous ψ →
      ∀ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
      (∀ k, coeff (observationLength a) ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
        transportCoeffs P (observationLength a)
          ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) →
      LocallyIntegrable (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) volume →
      (∀ u v, AbsolutelyContinuousOnInterval (fun t : ℝ => ψ (t : Circle (observationLength a))) u v) →
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
        2 ≤ dist (x : Circle (observationLength a)) 0 →
        |deriv (circleMollify ρ (observationLength a).val h
          (fun t : ℝ => ψ (t : Circle (observationLength a)))) x| ≤
            C * dist (x : Circle (observationLength a)) 0 ^ (P.val.2 - 2) ∧
        |deriv (deriv (circleMollify ρ (observationLength a).val h
          (fun t : ℝ => ψ (t : Circle (observationLength a))))) x| ≤
            C * dist (x : Circle (observationLength a)) 0 ^ (P.val.2 - 3) := by
  obtain ⟨D, hD, hfirst⟩ := compact_transport_power_of_integral_bound P 1 le_rfl Z hZ
  obtain ⟨E, hE, hsecond⟩ := compact_transport_power_of_integral_bound P 2 (by norm_num) Z hZ
  let C := D * 2 ^ (2 - P.val.2) + E * 2 ^ (3 - P.val.2)
  have hC : 0 < C := by dsimp [C]; positivity
  have hDC : D * 2 ^ (2 - P.val.2) ≤ C := le_add_of_nonneg_right (by positivity)
  have hEC : E * 2 ^ (3 - P.val.2) ≤ C := le_add_of_nonneg_left (by positivity)
  refine ⟨C, hC, fun p hp hnorm a ψ hc hψ hcoeff hi hAC h hh hh1 x hx => ?_⟩
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  let F := fun t : ℝ => ψ (t : Circle L)
  let δ := fun t : ℝ => dist (t : Circle L) 0
  have hpF : Function.Periodic F L.val := by intro t; simp only [F, AddCircle.coe_add_period]
  have hδ (y z : ℝ) : δ y ≤ δ z + |y - z| := by
    simp only [δ, dist_coe_zero_eq_circDist]
    exact circDist_le_add_abs L.property y z
  have hb1 (y : ℝ) (hy : 1 ≤ δ y) : |deriv F y| ≤ D * δ y ^ (P.val.2 - 2) := by
    simpa only [iteratedDeriv_one, Real.norm_eq_abs, Nat.cast_one,
      show P.val.2 - 1 - 1 = P.val.2 - 2 by ring] using (hfirst p hp hnorm a ψ hc hψ hcoeff y hy).2
  have hb2 (y : ℝ) (hy : 1 ≤ δ y) : |deriv (deriv F) y| ≤ E * δ y ^ (P.val.2 - 3) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Real.norm_eq_abs, Nat.cast_ofNat,
      show P.val.2 - 1 - 2 = P.val.2 - 3 by ring] using (hsecond p hp hnorm a ψ hc hψ hcoeff y hy).2
  have hFc : Continuous F := hc.comp (AddCircle.continuous_mk' L.val)
  have heq : deriv (circleMollify ρ L.val h F) = mollifyLine ρ h (deriv F) := by
    funext y
    rw [deriv_circleMollify_of_absolutelyContinuous hρ L.property hh hFc hpF hAC,
      circleMollify_eq_mollifyLine hρ L.property hh hi (Riesz1.periodic_deriv hpF)]
  change |deriv (circleMollify ρ L.val h F) x| ≤ _ ∧ |deriv (deriv (circleMollify ρ L.val h F)) x| ≤ _
  rw [heq]
  have h1 := mollifyLine_power_tail hρ hh hh1 hD.le
    (show P.val.2 - 2 ≤ 0 by linarith [P.property.2.2]) hi.aestronglyMeasurable hδ hb1 hx
  have h2 := deriv_mollifyLine_power_tail hρ hh hh1 hE.le
    (show P.val.2 - 3 ≤ 0 by linarith [P.property.2.2]) hi hδ
    (fun y hy => ((hsecond p hp hnorm a ψ hc hψ hcoeff y hy).1.derivWithin
      (m := 1) (by norm_num)).differentiableAt (by norm_num)) hb2 hx
  constructor
  · rw [show -(P.val.2 - 2) = 2 - P.val.2 by ring] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hDC (by positivity))
  · rw [show -(P.val.2 - 3) = 3 - P.val.2 by ring] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right hEC (by positivity))

end Riesz1.Internal
