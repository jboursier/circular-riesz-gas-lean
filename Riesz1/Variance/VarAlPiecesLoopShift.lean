/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopScaleIntegrability
import all Riesz1.Variance.LoopForce
import all Riesz1.Variance.LoopForceKernel

/-!
# Shifts of the profile and of the configuration

Proposition 5.9, the shift step of the variance clause. A one-periodic profile
`g` has a loop kernel `(g a - g b) g_s'(a - b)` that is one-periodic in each argument. Two
consequences follow.

* Shifting the profile by `c` is the same as shifting the configuration by `c`:
  `Loop[g(· + c)](x) = Loop[g](x + c)`.
* An integer shift of all particle positions leaves the loop functional unchanged.

The shift identities use only periodicity, so they need no integrability assumption.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- The integral of a one-periodic function over `[0, 1]` is unchanged by a translation of the
integration variable. -/
lemma integral_add_const_periodic {F : ℝ → ℝ} (hF : Function.Periodic F 1) (c : ℝ) :
    ∫ y in (0 : ℝ)..1, F (y + c) = ∫ y in (0 : ℝ)..1, F y := by
  rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm (1 : ℝ) c]
  have h := hF.intervalIntegral_add_eq c 0
  rw [zero_add] at h
  exact h

/-- The loop kernel is one-periodic in its first argument, for a one-periodic profile. -/
lemma loopKernel_add_one_left (s : ℝ) {g : ℝ → ℝ} (hp : Function.Periodic g 1) (a b : ℝ) :
    loopKernel s g (a + 1) b = loopKernel s g a b := by
  unfold loopKernel
  rw [show a + 1 - b = (a - b) + 1 by ring, deriv_hurwitzKernel_add_one', hp a]

/-- The loop kernel is one-periodic in its second argument, for a one-periodic profile. -/
lemma loopKernel_add_one_right (s : ℝ) {g : ℝ → ℝ} (hp : Function.Periodic g 1) (a b : ℝ) :
    loopKernel s g a (b + 1) = loopKernel s g a b := by
  have h := deriv_hurwitzKernel_add_one' s (a - (b + 1))
  rw [show a - (b + 1) + 1 = a - b by ring] at h
  unfold loopKernel
  rw [hp b, h]

/-- The loop kernel is invariant under an integer shift of its first argument. -/
lemma loopKernel_add_int_left (s : ℝ) {g : ℝ → ℝ} (hp : Function.Periodic g 1) (m : ℤ)
    (a b : ℝ) : loopKernel s g (a + m) b = loopKernel s g a b := by
  have hper : Function.Periodic (fun a' => loopKernel s g a' b) 1 :=
    fun a' => loopKernel_add_one_left s hp a' b
  have h := hper.int_mul m a
  simpa using h

/-- The loop kernel is invariant under an integer shift of its second argument. -/
lemma loopKernel_add_int_right (s : ℝ) {g : ℝ → ℝ} (hp : Function.Periodic g 1) (m : ℤ)
    (a b : ℝ) : loopKernel s g a (b + m) = loopKernel s g a b := by
  have hper : Function.Periodic (fun b' => loopKernel s g a b') 1 :=
    fun b' => loopKernel_add_one_right s hp a b'
  have h := hper.int_mul m b
  simpa using h

/-- The loop functional is invariant under an integer shift of all particle positions. -/
lemma loopFunctional_add_int (s : ℝ) {g : ℝ → ℝ} (hp : Function.Periodic g 1) (N : ℕ)
    (x : Fin N → ℝ) (m : ℤ) :
    loopFunctional s N g (fun i => x i + m) = loopFunctional s N g x := by
  unfold loopFunctional
  have hPP : (∑ i : Fin N, ∑ j : Fin N,
      (if j = i then (0 : ℝ) else loopKernel s g (x i + m) (x j + m))) =
      ∑ i : Fin N, ∑ j : Fin N, (if j = i then (0 : ℝ) else loopKernel s g (x i) (x j)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rfl
    · rw [loopKernel_add_int_left s hp, loopKernel_add_int_right s hp]
  have hBS : (∑ i : Fin N, ∫ y in (0 : ℝ)..1, loopKernel s g (x i + m) y) =
      ∑ i : Fin N, ∫ y in (0 : ℝ)..1, loopKernel s g (x i) y :=
    Finset.sum_congr rfl fun i _ => by simp only [loopKernel_add_int_left s hp]
  have hCS : (∑ j : Fin N, ∫ u in (0 : ℝ)..1, loopKernel s g u (x j + m)) =
      ∑ j : Fin N, ∫ u in (0 : ℝ)..1, loopKernel s g u (x j) :=
    Finset.sum_congr rfl fun j _ => by simp only [loopKernel_add_int_right s hp]
  simp only
  rw [hPP, hBS, hCS]

/-- The loop kernel of a shifted profile is the loop kernel of the original at shifted points. -/
lemma loopKernel_shift_profile (s : ℝ) (g : ℝ → ℝ) (c a b : ℝ) :
    loopKernel s (fun u => g (u + c)) a b = loopKernel s g (a + c) (b + c) := by
  unfold loopKernel
  rw [show a + c - (b + c) = a - b by ring]

/-- **Shift of the profile is shift of the configuration** (Proposition 5.9, the
translation step). For a one-periodic profile `g` and a real shift `c`, the loop of the translated
profile `g(· + c)` at a configuration `x` equals the loop of `g` at the translated configuration
`x + c`. -/
theorem loopFunctional_shift_profile (s : ℝ) {g : ℝ → ℝ} (hp : Function.Periodic g 1)
    (N : ℕ) (c : ℝ) (x : Fin N → ℝ) :
    loopFunctional s N (fun u => g (u + c)) x = loopFunctional s N g (fun i => x i + c) := by
  unfold loopFunctional
  have hPP : (∑ i : Fin N, ∑ j : Fin N,
      (if j = i then (0 : ℝ) else loopKernel s (fun u => g (u + c)) (x i) (x j))) =
      ∑ i : Fin N, ∑ j : Fin N,
        (if j = i then (0 : ℝ) else loopKernel s g (x i + c) (x j + c)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rfl
    · exact loopKernel_shift_profile s g c (x i) (x j)
  -- Each particle-background integral is shift invariant, since `y ↦ loopKernel (x i + c) y`
  -- is one-periodic.
  have hBS : (∑ i : Fin N, ∫ y in (0 : ℝ)..1, loopKernel s (fun u => g (u + c)) (x i) y) =
      ∑ i : Fin N, ∫ y in (0 : ℝ)..1, loopKernel s g (x i + c) y := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [loopKernel_shift_profile s g c]
    have hper : Function.Periodic (fun y => loopKernel s g (x i + c) y) 1 :=
      fun y => loopKernel_add_one_right s hp (x i + c) y
    exact integral_add_const_periodic hper c
  have hKS : (∑ j : Fin N, ∫ u in (0 : ℝ)..1, loopKernel s (fun v => g (v + c)) u (x j)) =
      ∑ j : Fin N, ∫ u in (0 : ℝ)..1, loopKernel s g u (x j + c) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [loopKernel_shift_profile s g c]
    have hper : Function.Periodic (fun u => loopKernel s g u (x j + c)) 1 :=
      fun u => loopKernel_add_one_left s hp u (x j + c)
    exact integral_add_const_periodic hper c
  -- The background-background integral is shift invariant in both variables.
  have hH : Function.Periodic (fun w : ℝ => ∫ v in (0 : ℝ)..1, loopKernel s g w v) 1 := by
    intro w
    simp only [loopKernel_add_one_left s hp]
  have hDD : (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, loopKernel s (fun t => g (t + c)) u v) =
      ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, loopKernel s g u v := by
    have hin (u : ℝ) : (∫ v in (0 : ℝ)..1, loopKernel s (fun t => g (t + c)) u v) =
        ∫ v in (0 : ℝ)..1, loopKernel s g (u + c) v := by
      simp only [loopKernel_shift_profile s g c]
      have hper : Function.Periodic (fun v => loopKernel s g (u + c) v) 1 :=
        fun v => loopKernel_add_one_right s hp (u + c) v
      exact integral_add_const_periodic hper c
    simp_rw [hin]
    exact integral_add_const_periodic hH c
  simp only
  rw [hPP, hBS, hKS, hDD]

end Riesz1

end
