/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Tactic

/-!
# Reconstructing periodic functions from derivative pieces

A finite splitting of a periodic derivative can be integrated into periodic
pieces after correcting each piece's period integral with one common function.
The correction coefficients sum to zero. No separation of marked points is
involved in this construction.
-/

public section

open MeasureTheory intervalIntegral
open scoped ContDiff BigOperators

namespace Riesz1

/-- A smooth periodic function with zero period integral has a smooth
periodic primitive, with its value at zero fixed to zero. -/
theorem smooth_periodic_primitive {L : ℝ} {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q L)
    (hz : ∫ t in (0 : ℝ)..L, q t = 0) :
    ∃ Q : ℝ → ℝ, ContDiff ℝ ∞ Q ∧ Function.Periodic Q L ∧
      Q 0 = 0 ∧ deriv Q = q := by
  let Q : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, q t
  have hd (x : ℝ) : HasDerivAt Q (q x) x :=
    (hq.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hder : deriv Q = q := funext fun x => (hd x).deriv
  refine ⟨Q, contDiff_infty_iff_deriv.mpr ⟨fun x => (hd x).differentiableAt,
    by rwa [hder]⟩, ?_, by simp [Q], hder⟩
  intro x
  apply sub_eq_zero.mp
  change (∫ t in (0 : ℝ)..(x + L), q t) - (∫ t in (0 : ℝ)..x, q t) = 0
  rw [integral_interval_sub_left (hq.continuous.intervalIntegrable _ _)
    (hq.continuous.intervalIntegrable _ _), hp.intervalIntegral_add_eq x 0, zero_add, hz]

/-- Correct a smooth finite derivative splitting by a common function
of nonzero period integral, then reconstruct an exact periodic splitting.
The last identity records both derivatives needed by transport envelopes. -/
theorem periodic_derivative_reconstruction {ι : Type*} [Fintype ι]
    (j₀ : ι) {L : ℝ} {F u : ℝ → ℝ} {q : ι → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hFp : Function.Periodic F L)
    (hu : ContDiff ℝ ∞ u) (hup : Function.Periodic u L)
    (hum : (∫ t in (0 : ℝ)..L, u t) ≠ 0)
    (hq : ∀ j, ContDiff ℝ ∞ (q j) ∧ Function.Periodic (q j) L)
    (hsum : ∀ x, ∑ j, q j x = deriv F x) :
    ∃ (c : ι → ℝ) (φ : ι → ℝ → ℝ),
      (∀ j, c j = (∫ t in (0 : ℝ)..L, q j t) / (∫ t in (0 : ℝ)..L, u t)) ∧
      (∑ j, c j = 0) ∧
      (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) L) ∧
      (∀ x, ∑ j, φ j x = F x) ∧
      (∀ j x, deriv (φ j) x = q j x - c j * u x) ∧
      (∀ j x, deriv (deriv (φ j)) x = deriv (q j) x - c j * deriv u x) := by
  classical
  let c : ι → ℝ := fun j => (∫ t in (0 : ℝ)..L, q j t) / (∫ t in (0 : ℝ)..L, u t)
  have hc : ∑ j, c j = 0 := by
    dsimp [c]
    rw [← Finset.sum_div, ← intervalIntegral.integral_finsetSum
      (fun j _ => (hq j).1.continuous.intervalIntegrable _ _)]
    simp_rw [hsum]
    rw [integral_eq_sub_of_hasDerivAt (fun x _ =>
      (hF.differentiable (by simp) x).hasDerivAt)
      ((contDiff_infty_iff_deriv.mp hF).2.continuous.intervalIntegrable _ _)]
    rw [show F L = F 0 by simpa only [zero_add] using hFp 0, sub_self, zero_div]
  have hzero (j : ι) : ∫ t in (0 : ℝ)..L, (q j t - c j * u t) = 0 := by
    rw [intervalIntegral.integral_sub ((hq j).1.continuous.intervalIntegrable _ _)
      ((contDiff_const.mul hu).continuous.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
    dsimp [c]
    field_simp [hum]
    ring
  choose Q hQ using (fun j => smooth_periodic_primitive
    ((hq j).1.sub (contDiff_const.mul hu))
    (fun x => by rw [(hq j).2 x, hup x]) (hzero j))
  let φ : ι → ℝ → ℝ := fun j x => Q j x + if j = j₀ then F 0 else 0
  have hφ (j : ι) : ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) L :=
    ⟨(hQ j).1.add contDiff_const, fun x => by dsimp [φ]; rw [(hQ j).2.1 x]⟩
  have hder (j : ι) : deriv (φ j) = fun x => q j x - c j * u x := by
    dsimp [φ]
    rw [show (fun x => Q j x + if j = j₀ then F 0 else 0) =
      fun x => Q j x + (if j = j₀ then F 0 else 0) from rfl]
    simpa only [deriv_add_const'] using (hQ j).2.2.2
  have hsumder : deriv (fun x => ∑ j, φ j x) = deriv F := by
    funext x
    rw [deriv_fun_sum (fun j _ => (hφ j).1.differentiable (by simp) x)]
    simp_rw [hder]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hc, zero_mul, sub_zero, hsum]
  have hsumzero : ∑ j, φ j 0 = F 0 := by
    dsimp [φ]
    simp only [(hQ _).2.2.1, zero_add]
    simp
  have heq : (fun x => ∑ j, φ j x) = F := by
    funext x
    have hG := ContDiff.sum (fun j (_ : j ∈ Finset.univ) => (hφ j).1)
    have h₁ := integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := x)
      (fun y _ => (hG.differentiable (by simp) y).hasDerivAt)
      ((contDiff_infty_iff_deriv.mp hG).2.continuous.intervalIntegrable _ _)
    have h₂ := integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := x)
      (fun y _ => (hF.differentiable (by simp) y).hasDerivAt)
      ((contDiff_infty_iff_deriv.mp hF).2.continuous.intervalIntegrable _ _)
    rw [hsumder] at h₁
    change (∫ t in (0 : ℝ)..x, deriv F t) = (∑ j, φ j x) - (∑ j, φ j 0) at h₁
    linarith
  refine ⟨c, φ, fun _ => rfl, hc, hφ, congrFun heq, fun j => congrFun (hder j), ?_⟩
  intro j x
  rw [hder]
  exact deriv_fun_sub ((hq j).1.differentiable (by simp) x)
    ((contDiff_const.mul hu).differentiable (by simp) x) |>.trans (by
      rw [deriv_const_mul_field])

end Riesz1
