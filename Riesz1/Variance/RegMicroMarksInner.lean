/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformOffSupport

/-!
# Inner-envelope transfer after removing exterior marks

An internal calculus step. A smooth difference
between transports preserves their second derivative envelope on a fixed
inner interval. The reference circle has no wraparound there.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace Riesz1.Internal

/-- Transfer an inner singular envelope from a reference circle to a
second circle, absorbing the bounded contribution of exterior real marks. -/
theorem regMicro_marks_inner_comparison
    (L T : Length) (n m : ℕ+) (a : Fin (n : ℕ) → ℝ) (b : Fin (m : ℕ) → ℝ)
    (σ q e D Q : ℝ) (hσ : σ < 1) (hσq : σ < q) (he : e ≤ 0)
    (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hcover : ∀ i, |a i| ≤ q → ∃ j, b j = a i)
    (hdist : ∀ x, |x| < σ → ∀ i, dist (x : Circle T) (a i : Circle T) = |x-a i|)
    (ψ : Circle L → ℝ) (ψ' : Circle T → ℝ)
    (hp : ∀ x : ℝ, (∀ i, (x : Circle T) ≠ (a i : Circle T)) →
      ContDiffAt ℝ 2 (fun t : ℝ => ψ' (t : Circle T)) x ∧
      |deriv (deriv (fun t : ℝ => ψ' (t : Circle T))) x| ≤
        D*cappedMarkDistance (fun i => (a i : Circle T)) (x : Circle T)^e)
    (hdiff : ContDiffOn ℝ ∞ (fun t : ℝ => ψ (t : Circle L)-ψ' (t : Circle T)) (Ioo (-σ) σ))
    (hdb : ∀ x, x ∈ Ioo (-σ) σ →
      ‖iteratedDeriv 2 (fun t : ℝ => ψ (t : Circle L)-ψ' (t : Circle T)) x‖ ≤ Q)
    (x : ℝ) (hx : |x| < σ) (hxm : ∀ j, (x : Circle L) ≠ (b j : Circle L)) :
    ContDiffAt ℝ 2 (fun t : ℝ => ψ (t : Circle L)) x ∧
      |deriv (deriv (fun t : ℝ => ψ (t : Circle L))) x| ≤
        ((D*(1+(n : ℝ)*(q-σ)^e)+Q)*(2+|b ⟨0, m.pos⟩|)^(-e)+D*(n : ℝ))*
          (∑ j, dist (x : Circle L) (b j : Circle L)^e) := by
  have hx' : x ∈ Ioo (-σ) σ := abs_lt.mp hx
  have hne : ∀ i, (x : Circle T) ≠ (a i : Circle T) := by
    intro i hi
    have heq : x = a i := by
      have hz : |x-a i| = 0 := by rw [← hdist x hx i, hi, dist_self]
      exact sub_eq_zero.mp (abs_eq_zero.mp hz)
    obtain ⟨j, hj⟩ := hcover i (by rw [← heq]; exact hx.le.trans hσq.le)
    exact hxm j (by rw [hj, heq])
  let F := fun t : ℝ => ψ (t : Circle L)-ψ' (t : Circle T)
  let G := fun t : ℝ => ψ' (t : Circle T)
  have hF : ContDiffAt ℝ 2 F x := (hdiff.contDiffAt (isOpen_Ioo.mem_nhds hx')).of_le (by simp)
  have hG : ContDiffAt ℝ 2 G x := (hp x hne).1
  have heq : (fun t : ℝ => ψ (t : Circle L)) = fun t => F t+G t := by
    funext t
    dsimp [F, G]
    ring
  have hd : deriv (deriv (fun t : ℝ => ψ (t : Circle L))) x =
      deriv (deriv F) x+deriv (deriv G) x := by
    rw [heq]
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (iteratedDeriv_fun_add (n := 2) hF hG)
  have hFb : |deriv (deriv F) x| ≤ Q := by
    simpa only [F, iteratedDeriv_succ, iteratedDeriv_zero, Real.norm_eq_abs] using hdb x hx'
  let S := ∑ j, dist (x : Circle L) (b j : Circle L)^e
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let A := (2+|b ⟨0, m.pos⟩|)^(-e)
  have hx1 : dist (x : Circle L) 0 ≤ 1 := by
    rw [dist_zero_right]
    exact (show ‖(x : Circle L)‖ ≤ |x| from QuotientAddGroup.norm_mk_le_norm).trans
      (hx.le.trans hσ.le)
  have hone : 1 ≤ A*S := inner_mark_power_sum L m b he hx1 hxm
  have hsum : (∑ i, dist (x : Circle T) (a i : Circle T)^e) ≤ (n : ℝ)*((q-σ)^e+S) := by
    calc
      _ ≤ ∑ _i : Fin (n : ℕ), ((q-σ)^e+S) := by
        apply Finset.sum_le_sum
        intro i _
        rw [hdist x hx i]
        by_cases hi : |a i| ≤ q
        · obtain ⟨j, hj⟩ := hcover i hi
          have hreal : dist (x : Circle L) (b j : Circle L) ≤ |x-a i| := by
            rw [hj, dist_eq_norm, ← QuotientAddGroup.mk_sub]
            exact QuotientAddGroup.norm_mk_le_norm
          have hh := Real.rpow_le_rpow_of_nonpos (dist_pos.mpr (hxm j)) hreal he
          have hs := Finset.single_le_sum (s := Finset.univ)
            (f := fun j => dist (x : Circle L) (b j : Circle L)^e)
            (fun _ _ => by positivity) (Finset.mem_univ j)
          exact (hh.trans hs).trans (le_add_of_nonneg_left (by positivity))
        · have hda : q-σ ≤ |x-a i| := by
            have hh := abs_sub_abs_le_abs_sub (a i) x
            rw [abs_sub_comm (a i) x] at hh
            linarith [lt_of_not_ge hi]
          exact (Real.rpow_le_rpow_of_nonpos (by linarith : 0 < q-σ) hda he).trans
            (le_add_of_nonneg_right hS)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hGb : |deriv (deriv G) x| ≤ D*(1+(n : ℝ)*((q-σ)^e+S)) := by
    have hh := (hp x hne).2.trans (mul_le_mul_of_nonneg_left
      (cappedMarkDistance_rpow_le_one_add_sum _ _ _) hD)
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith) hD)
  refine ⟨by rw [heq]; exact hF.add hG, ?_⟩
  rw [hd]
  have hJ : 0 ≤ D*(1+(n : ℝ)*(q-σ)^e)+Q := by positivity
  have hh := mul_le_mul_of_nonneg_left hone hJ
  have hv := (abs_add_le (deriv (deriv F) x) (deriv (deriv G) x)).trans (add_le_add hFb hGb)
  change _ ≤ ((D*(1+(n : ℝ)*(q-σ)^e)+Q)*A+D*(n : ℝ))*S
  nlinarith

end Riesz1.Internal
