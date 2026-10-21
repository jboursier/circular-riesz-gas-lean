/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopForceKernel
public import Riesz1.Frozen.Energy
public import Riesz1.Frozen.Configuration

/-!
# Gradients of the energy and of the field potential in lifted coordinates

Proposition 5.5, the derivative part. A
configuration `X` of `N` points is its ordered real lift `X.val : Fin N → ℝ`. The energy
`energy s X` is the value at `X.val` of the function `energyLift s N`, which is given by the
same formula on all of `ℝ^N`. Partial derivatives are taken in the lifted coordinates. At a point where no two lifted
coordinates differ by an integer the energy is smooth.

The field potential `Φ(X) = ∑ᵢ ∫₀^{xᵢ} ψ` (Proposition 5.5) is
`fieldPotential ψ N`. This file proves:

* `partialDeriv_energyLift`: `∂ₖ H = N^(-s) * 2 * ∑_{j ≠ k} g_s'(x_k - x_j)`,
* `partialDeriv_fieldPotential`: `∂ₖ Φ = ψ(x_k)`,
* `gradDot_energy_fieldPotential`: `∇H · ∇Φ = N^(-s) * ∑_{i ≠ j} (ψ(x_i) - ψ(x_j)) g_s'(x_i - x_j)`.
-/

public section

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff

namespace Riesz1

/-- The energy `H_N` at an arbitrary real lift `x ∈ ℝ^N` of a configuration. It is given by the
formula of `energy`. -/
noncomputable def energyLift (s : RieszExponent) (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  (N : ℝ) ^ (-s.val) * ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
    hurwitzKernel s.val (x i - x j)

/-- The lifted energy is the energy on configurations. -/
lemma energy_eq_energyLift (s : RieszExponent) {N : ℕ+} (X : Configuration N) :
    energy s X = energyLift s N X.val := by
  unfold energy energyLift rieszRepresentative hurwitzKernel
  rfl

/-- The partial derivative of a function on `ℝ^N` in the `k`-th coordinate. -/
noncomputable def partialDeriv {N : ℕ} (F : (Fin N → ℝ) → ℝ) (k : Fin N) (x : Fin N → ℝ) : ℝ :=
  deriv (fun t : ℝ => F (Function.update x k t)) (x k)

/-- The field potential `Φ(x) = ∑ᵢ ∫₀^{xᵢ} ψ` on `ℝ^N`. -/
noncomputable def fieldPotential (ψ : ℝ → ℝ) (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ u in (0 : ℝ)..x i, ψ u

/-- The sum over `j ≠ i` written with an indicator. -/
lemma sum_erase_eq_ite {N : ℕ} (i : Fin N) (F : Fin N → ℝ) :
    ∑ j ∈ Finset.univ.erase i, F j = ∑ j : Fin N, if j = i then 0 else F j := by
  calc ∑ j ∈ Finset.univ.erase i, F j
      = ∑ j ∈ Finset.univ.erase i, (if j = i then 0 else F j) :=
        Finset.sum_congr rfl fun j hj => by rw [ite_eq_right (Finset.ne_of_mem_erase hj)]
    _ = ∑ j : Fin N, if j = i then 0 else F j := Finset.sum_erase _ (by simp)

lemma energyLift_eq_ite (s : RieszExponent) (N : ℕ) (x : Fin N → ℝ) :
    energyLift s N x = (N : ℝ) ^ (-s.val) *
      ∑ i : Fin N, ∑ j : Fin N, if j = i then 0 else hurwitzKernel s.val (x i - x j) := by
  unfold energyLift
  congr 1
  exact Finset.sum_congr rfl fun i _ => sum_erase_eq_ite i _

/-- Each term of the energy is differentiable in the `k`-th coordinate, at the point `x k`,
with derivative given by the indicator formula. -/
lemma hasDerivAt_energy_term {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ} (x : Fin N → ℝ)
    (hx : ∀ i j : Fin N, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0) (k i j : Fin N) :
    HasDerivAt (fun t : ℝ => if j = i then (0 : ℝ) else
        hurwitzKernel s (Function.update x k t i - Function.update x k t j))
      (if j = i then 0 else if i = k then deriv (hurwitzKernel s) (x i - x j)
        else if j = k then -deriv (hurwitzKernel s) (x i - x j) else 0) (x k) := by
  by_cases hji : j = i
  · simp only [hji, ite_true]
    exact hasDerivAt_const _ _
  · simp only [hji, ite_false]
    by_cases hik : i = k
    · -- the moving coordinate is the first index. The point `x k` is `x i`
      have hyi : ∀ t : ℝ, Function.update x k t i = t := fun t => by
        rw [hik]; exact Function.update_self _ _ _
      have hjk : j ≠ k := fun h => hji (h.trans hik.symm)
      have hyj : ∀ t : ℝ, Function.update x k t j = x j := fun t =>
        Function.update_of_ne hjk _ _
      have hne : ((x k - x j : ℝ) : UnitAddCircle) ≠ 0 := by
        rw [← hik]; exact hx i j (fun h => hji h.symm)
      have hg : HasDerivAt (hurwitzKernel s) (deriv (hurwitzKernel s) (x k - x j))
          (x k - x j) :=
        (differentiableAt_hurwitzKernel_of_ne s hs0 hs1 _ hne).hasDerivAt
      have hlin : HasDerivAt (fun t : ℝ => t - x j) 1 (x k) := by
        simpa using (hasDerivAt_id (x k)).sub_const (x j)
      have hcomp := hg.comp (x k) hlin
      have hfun : (fun t : ℝ => hurwitzKernel s (Function.update x k t i - Function.update x k t j))
          = hurwitzKernel s ∘ (fun t : ℝ => t - x j) := by
        funext t
        simp only [Function.comp, hyi, hyj]
      rw [hfun, ite_eq_left hik, hik]
      simpa using hcomp
    · by_cases hjk : j = k
      · -- the moving coordinate is the second index. The point `x k` is `x j`
        have hyi : ∀ t : ℝ, Function.update x k t i = x i := fun t =>
          Function.update_of_ne hik _ _
        have hyj : ∀ t : ℝ, Function.update x k t j = t := fun t => by
          rw [hjk]; exact Function.update_self _ _ _
        have hne : ((x i - x k : ℝ) : UnitAddCircle) ≠ 0 := by
          rw [← hjk]; exact hx i j (fun h => hji h.symm)
        have hg : HasDerivAt (hurwitzKernel s) (deriv (hurwitzKernel s) (x i - x k))
            (x i - x k) :=
          (differentiableAt_hurwitzKernel_of_ne s hs0 hs1 _ hne).hasDerivAt
        have hlin : HasDerivAt (fun t : ℝ => x i - t) (-1) (x k) := by
          simpa using (hasDerivAt_id (x k)).const_sub (x i)
        have hcomp := hg.comp (x k) hlin
        have hfun : (fun t : ℝ => hurwitzKernel s (Function.update x k t i - Function.update x k t j))
            = hurwitzKernel s ∘ (fun t : ℝ => x i - t) := by
          funext t
          simp only [Function.comp, hyi, hyj]
        rw [hfun, ite_eq_right hik, ite_eq_left hjk, hjk]
        simpa using hcomp
      · -- neither index moves: the term is constant
        have hyi : ∀ t : ℝ, Function.update x k t i = x i := fun t =>
          Function.update_of_ne hik _ _
        have hyj : ∀ t : ℝ, Function.update x k t j = x j := fun t =>
          Function.update_of_ne hjk _ _
        have hfun : (fun t : ℝ => hurwitzKernel s (Function.update x k t i - Function.update x k t j))
            = fun _ => hurwitzKernel s (x i - x j) := by
          funext t
          simp only [hyi, hyj]
        rw [hfun, ite_eq_right hik, ite_eq_right hjk]
        exact hasDerivAt_const _ _

/-- The derivative of the whole energy sum in the `k`-th coordinate. -/
lemma hasDerivAt_energy_update {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ} (x : Fin N → ℝ)
    (hx : ∀ i j : Fin N, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0) (k : Fin N) :
    HasDerivAt (fun t : ℝ => ∑ i : Fin N, ∑ j : Fin N, if j = i then (0 : ℝ) else
        hurwitzKernel s (Function.update x k t i - Function.update x k t j))
      (∑ i : Fin N, ∑ j : Fin N, if j = i then 0 else if i = k then
        deriv (hurwitzKernel s) (x i - x j) else if j = k then
        -deriv (hurwitzKernel s) (x i - x j) else 0) (x k) := by
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  exact hasDerivAt_energy_term hs0 hs1 x hx k i j

/-- The combinatorial evaluation of the derivative: the contributions of the ordered pairs
containing `k` add up, using the oddness of the derivative of the kernel. -/
lemma sum_sum_energyDeriv {N : ℕ} (k : Fin N) (G : Fin N → Fin N → ℝ)
    (hodd : ∀ i : Fin N, i ≠ k → G i k = -G k i) :
    ∑ i : Fin N, ∑ j : Fin N, (if j = i then (0 : ℝ) else if i = k then G i j
      else if j = k then -G i j else 0) = 2 * ∑ j : Fin N, if j = k then 0 else G k j := by
  have hpt : ∀ i j : Fin N, (if j = i then (0 : ℝ) else if i = k then G i j
      else if j = k then -G i j else 0) = (if i = k then (if j = k then 0 else G k j) else 0)
        + (if j = k then (if i = k then 0 else -G i k) else 0) := by
    intro i j
    by_cases hji : j = i <;> by_cases hik : i = k <;> by_cases hjk : j = k <;> simp_all
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j]
  simp only [Finset.sum_add_distrib]
  have h1 : ∑ i : Fin N, ∑ j : Fin N, (if i = k then (if j = k then (0 : ℝ) else G k j) else 0)
      = ∑ j : Fin N, if j = k then 0 else G k j := by
    rw [Finset.sum_eq_single k (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ k) h)]
    simp
  have h2 : ∑ i : Fin N, ∑ j : Fin N, (if j = k then (if i = k then (0 : ℝ) else -G i k) else 0)
      = ∑ i : Fin N, if i = k then 0 else -G i k := by
    simp
  have h3 : ∑ i : Fin N, (if i = k then (0 : ℝ) else -G i k)
      = ∑ j : Fin N, if j = k then 0 else G k j :=
    Finset.sum_congr rfl fun i _ => by
      by_cases hik : i = k
      · simp [hik]
      · simp [hik, hodd i hik]
  rw [h1, h2, h3, two_mul]

/-- The derivative of the lifted energy in the `k`-th coordinate. -/
lemma partialDeriv_energyLift {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ} (x : Fin N → ℝ)
    (hx : ∀ i j : Fin N, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0) (k : Fin N) :
    partialDeriv (energyLift ⟨s, hs0, hs1⟩ N) k x =
      (N : ℝ) ^ (-s) * (2 * ∑ j : Fin N, if j = k then 0 else
        deriv (hurwitzKernel s) (x k - x j)) := by
  unfold partialDeriv
  have hfun : (fun t : ℝ => energyLift ⟨s, hs0, hs1⟩ N (Function.update x k t))
      = fun t : ℝ => (N : ℝ) ^ (-s) * ∑ i : Fin N, ∑ j : Fin N, if j = i then (0 : ℝ) else
          hurwitzKernel s (Function.update x k t i - Function.update x k t j) := by
    funext t
    rw [energyLift_eq_ite]
  rw [hfun, ((hasDerivAt_energy_update hs0 hs1 x hx k).const_mul ((N : ℝ) ^ (-s))).deriv]
  congr 1
  rw [sum_sum_energyDeriv k (fun i j => deriv (hurwitzKernel s) (x i - x j)) ?_]
  intro i hik
  have h := deriv_hurwitzKernel_neg' s (x k - x i)
  rw [show -(x k - x i) = x i - x k by ring] at h
  exact h

/-- The field potential has partial derivative `ψ(x_k)` in the `k`-th coordinate. -/
lemma partialDeriv_fieldPotential {ψ : ℝ → ℝ} (hψ : Continuous ψ) {N : ℕ} (x : Fin N → ℝ)
    (k : Fin N) : partialDeriv (fieldPotential ψ N) k x = ψ (x k) := by
  have h : ∀ i : Fin N, HasDerivAt (fun t : ℝ => ∫ u in (0 : ℝ)..(Function.update x k t i), ψ u)
      (if i = k then ψ (x k) else 0) (x k) := by
    intro i
    by_cases hik : i = k
    · rw [ite_eq_left hik]
      have hfun : (fun t : ℝ => ∫ u in (0 : ℝ)..(Function.update x k t i), ψ u)
          = fun t : ℝ => ∫ u in (0 : ℝ)..t, ψ u := by
        funext t
        rw [hik, Function.update_self]
      rw [hfun]
      exact (hψ.integral_hasStrictDerivAt 0 (x k)).hasDerivAt
    · rw [ite_eq_right hik]
      have hfun : (fun t : ℝ => ∫ u in (0 : ℝ)..(Function.update x k t i), ψ u)
          = fun _ : ℝ => ∫ u in (0 : ℝ)..x i, ψ u := by
        funext t
        rw [Function.update_of_ne hik]
      rw [hfun]
      exact hasDerivAt_const _ _
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i)
  unfold partialDeriv fieldPotential
  rw [hsum.deriv]
  simp

/-- The second partial derivative of the field potential, which gives the Laplacian. -/
lemma partialDeriv_partialDeriv_fieldPotential {ψ : ℝ → ℝ} (hψ : Continuous ψ) {N : ℕ}
    (x : Fin N → ℝ) (k : Fin N) :
    partialDeriv (fun y => partialDeriv (fieldPotential ψ N) k y) k x = deriv ψ (x k) := by
  have hfun : (fun y => partialDeriv (fieldPotential ψ N) k y) = fun y => ψ (y k) :=
    funext fun y => partialDeriv_fieldPotential hψ y k
  rw [hfun]
  unfold partialDeriv
  simp

/-- The gradient inner product `∇H · ∇Φ` is the sum over ordered pairs `i ≠ j` of
`(ψ(x_i) - ψ(x_j)) g_s'(x_i - x_j)`, times `N^(-s)`. This is the particle-particle part of the
loop functional. -/
lemma gradDot_energy_fieldPotential {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) {N : ℕ} (x : Fin N → ℝ)
    (hx : ∀ i j : Fin N, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0) :
    ∑ k : Fin N, partialDeriv (energyLift ⟨s, hs0, hs1⟩ N) k x
        * partialDeriv (fieldPotential ψ N) k x
      = (N : ℝ) ^ (-s) * ∑ i : Fin N, ∑ j : Fin N, if j = i then (0 : ℝ) else
          (ψ (x i) - ψ (x j)) * deriv (hurwitzKernel s) (x i - x j) := by
  set G : Fin N → Fin N → ℝ := fun i j => deriv (hurwitzKernel s) (x i - x j) with hG
  have hodd : ∀ i k : Fin N, i ≠ k → G i k = -G k i := by
    intro i k _
    have h := deriv_hurwitzKernel_neg' s (x k - x i)
    rw [show -(x k - x i) = x i - x k by ring] at h
    exact h
  have hL : ∀ k : Fin N, partialDeriv (energyLift ⟨s, hs0, hs1⟩ N) k x
        * partialDeriv (fieldPotential ψ N) k x
      = (N : ℝ) ^ (-s) * (2 * ((∑ j : Fin N, if j = k then 0 else G k j) * ψ (x k))) := by
    intro k
    rw [partialDeriv_energyLift hs0 hs1 x hx k, partialDeriv_fieldPotential hψ x k]
    ring
  -- `A` collects `ψ(x_k)`, `B` collects `ψ(x_j)`. The antisymmetry of `G` gives `B = -A`.
  have hA : ∑ k : Fin N, ∑ j : Fin N, (if j = k then (0 : ℝ) else G k j * ψ (x j))
      = -∑ k : Fin N, ∑ j : Fin N, (if j = k then (0 : ℝ) else G k j * ψ (x k)) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases htu : t = u
    · subst htu
      simp
    · have hut : u ≠ t := fun h => htu h.symm
      simp [htu, hut, hodd u t hut]
  have hLHS : ∑ k : Fin N, 2 * ((∑ j : Fin N, if j = k then (0 : ℝ) else G k j) * ψ (x k))
      = 2 * ∑ k : Fin N, ∑ j : Fin N, (if j = k then (0 : ℝ) else G k j * ψ (x k)) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hjk : j = k <;> simp [hjk]
  have hR : ∑ i : Fin N, ∑ j : Fin N, (if j = i then (0 : ℝ) else (ψ (x i) - ψ (x j)) * G i j)
      = ∑ k : Fin N, ∑ j : Fin N, (if j = k then (0 : ℝ) else G k j * ψ (x k))
        - ∑ k : Fin N, ∑ j : Fin N, (if j = k then (0 : ℝ) else G k j * ψ (x j)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hjk : j = k <;> simp [hjk]
    ring
  rw [Finset.sum_congr rfl fun k _ => hL k, ← Finset.mul_sum]
  congr 1
  rw [hLHS, hR, hA]
  ring

end Riesz1

end
