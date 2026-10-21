/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopScaleIntegrability
import all Riesz1.Variance.LoopForce

/-!
# Additivity of the loop functional in the profile

Proposition 5.9, the additivity step of the variance clause. For Lipschitz
one-periodic profiles `f` and `g`, the loop functional of `f + g` is the sum of the loop
functionals of `f` and `g`. The loop functional is a finite combination of the kernel
`loopKernel s f a b = (f a - f b) g_s'(a - b)`, and each integral in it converges absolutely by
the integrability lemmas of `LoopScaleIntegrability`. The finite-sum version follows by induction.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- The loop kernel is additive in the profile. -/
lemma loopKernel_add_profile (s : ℝ) (f g : ℝ → ℝ) (a b : ℝ) :
    loopKernel s (fun u => f u + g u) a b = loopKernel s f a b + loopKernel s g a b := by
  unfold loopKernel
  ring

/-- The loop functional of the zero profile vanishes. -/
lemma loopFunctional_zero_profile (s : ℝ) (N : ℕ) (x : Fin N → ℝ) :
    loopFunctional s N (fun _ => (0 : ℝ)) x = 0 := by
  simp [loopFunctional, loopKernel]

/-- **Additivity of the loop functional**, for two Lipschitz one-periodic profiles and a
Riesz exponent `0 < s < 1`: the loop of the sum is the sum of the loops, at every configuration
`x` of `N` particles. -/
theorem loopFunctional_add {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ) {f g : ℝ → ℝ}
    {Mf Mg : NNReal} (hf : LipschitzWith Mf f) (hpf : Function.Periodic f 1)
    (hg : LipschitzWith Mg g) (hpg : Function.Periodic g 1) (x : Fin N → ℝ) :
    loopFunctional s N (fun u => f u + g u) x =
      loopFunctional s N f x + loopFunctional s N g x := by
  set S : RieszExponent := ⟨s, hs0, hs1⟩ with hS
  -- The particle-particle sum splits term by term.
  have hA : (∑ i : Fin N, ∑ j : Fin N,
      (if j = i then (0 : ℝ) else loopKernel s (fun u => f u + g u) (x i) (x j))) =
      (∑ i : Fin N, ∑ j : Fin N, (if j = i then (0 : ℝ) else loopKernel s f (x i) (x j))) +
      ∑ i : Fin N, ∑ j : Fin N, (if j = i then (0 : ℝ) else loopKernel s g (x i) (x j)) := by
    simp only [loopKernel_add_profile]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j = i <;> simp [h]
  -- Each particle-background integral splits.
  have hB (i : Fin N) : (∫ y in (0 : ℝ)..1, loopKernel s (fun u => f u + g u) (x i) y) =
      (∫ y in (0 : ℝ)..1, loopKernel s f (x i) y) + ∫ y in (0 : ℝ)..1, loopKernel s g (x i) y := by
    simp only [loopKernel_add_profile]
    exact intervalIntegral.integral_add
      (loopScale_intervalIntegrable_kernel_right S hf hpf (x i))
      (loopScale_intervalIntegrable_kernel_right S hg hpg (x i))
  have hB' : (∑ i : Fin N, ∫ y in (0 : ℝ)..1, loopKernel s (fun u => f u + g u) (x i) y) =
      (∑ i : Fin N, ∫ y in (0 : ℝ)..1, loopKernel s f (x i) y) +
        ∑ i : Fin N, ∫ y in (0 : ℝ)..1, loopKernel s g (x i) y := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hB i
  -- Each background-particle integral splits.
  have hC (j : Fin N) : (∫ u in (0 : ℝ)..1, loopKernel s (fun u' => f u' + g u') u (x j)) =
      (∫ u in (0 : ℝ)..1, loopKernel s f u (x j)) + ∫ u in (0 : ℝ)..1, loopKernel s g u (x j) := by
    simp only [loopKernel_add_profile]
    exact intervalIntegral.integral_add
      (loopScale_intervalIntegrable_kernel_left S hf hpf (x j))
      (loopScale_intervalIntegrable_kernel_left S hg hpg (x j))
  have hC' : (∑ j : Fin N, ∫ u in (0 : ℝ)..1, loopKernel s (fun u' => f u' + g u') u (x j)) =
      (∑ j : Fin N, ∫ u in (0 : ℝ)..1, loopKernel s f u (x j)) +
        ∑ j : Fin N, ∫ u in (0 : ℝ)..1, loopKernel s g u (x j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hC j
  -- The background-background integral splits, first on the inner variable and then on the outer.
  have hD (u : ℝ) : (∫ v in (0 : ℝ)..1, loopKernel s (fun u' => f u' + g u') u v) =
      (∫ v in (0 : ℝ)..1, loopKernel s f u v) + ∫ v in (0 : ℝ)..1, loopKernel s g u v := by
    simp only [loopKernel_add_profile]
    exact intervalIntegral.integral_add
      (loopScale_intervalIntegrable_kernel_right S hf hpf u)
      (loopScale_intervalIntegrable_kernel_right S hg hpg u)
  have hDD : (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, loopKernel s (fun u' => f u' + g u') u v) =
      (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, loopKernel s f u v) +
        ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, loopKernel s g u v := by
    simp_rw [hD]
    exact intervalIntegral.integral_add (loopScale_intervalIntegrable_background S hf hpf)
      (loopScale_intervalIntegrable_background S hg hpg)
  -- Assemble the four pieces of the loop functional.
  unfold loopFunctional
  rw [hA, hB', hC', hDD]
  ring

/-- The loop functional of a finite sum of Lipschitz one-periodic profiles is Lipschitz in the
partial sums: the partial sums of Lipschitz functions are Lipschitz. -/
lemma lipschitz_finsetSum_profile {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ j, ∃ M : NNReal, LipschitzWith M (f j)) :
    ∃ M : NNReal, LipschitzWith M (fun u => ∑ j ∈ S, f j u) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a S ha ih =>
    obtain ⟨M, hM⟩ := ih
    obtain ⟨M', hM'⟩ := hf a
    refine ⟨M' + M, ?_⟩
    simp only [Finset.sum_insert ha]
    exact hM'.add hM

/-- A finite sum of one-periodic functions is one-periodic. -/
lemma periodic_finsetSum_profile {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℝ)
    (hp : ∀ j, Function.Periodic (f j) 1) :
    Function.Periodic (fun u => ∑ j ∈ S, f j u) 1 := by
  intro u
  exact Finset.sum_congr rfl fun j _ => hp j u

/-- **Additivity of the loop functional over a finite sum**: for Lipschitz one-periodic profiles
`f j`, indexed by a finite set `S`, the loop of `∑ⱼ f_j` is the sum of the loops `∑ⱼ Loop[f_j]`.
Its profile hypotheses are stated for each index. -/
theorem loopFunctional_finsetSum {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ) {ι : Type*}
    (S : Finset ι) (f : ι → ℝ → ℝ) (hf : ∀ j, ∃ M : NNReal, LipschitzWith M (f j))
    (hp : ∀ j, Function.Periodic (f j) 1) (x : Fin N → ℝ) :
    loopFunctional s N (fun u => ∑ j ∈ S, f j u) x = ∑ j ∈ S, loopFunctional s N (f j) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [loopFunctional_zero_profile s N x]
  | insert a S ha ih =>
    obtain ⟨Ma, hMa⟩ := hf a
    obtain ⟨MS, hMS⟩ := lipschitz_finsetSum_profile S f hf
    have hpS : Function.Periodic (fun u => ∑ j ∈ S, f j u) 1 := periodic_finsetSum_profile S f hp
    simp only [Finset.sum_insert ha]
    rw [loopFunctional_add hs0 hs1 N hMa (hp a) hMS hpS x, ih]

end Riesz1

end
