/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopForceEnergy
public import Mathlib.Analysis.Calculus.Deriv.Pi

import all Riesz1.Variance.LoopForceEnergy

/-!
# Periodicity and boundedness of smooth functions on the torus

A function `F : (Fin N → ℝ) → ℝ` is one-periodic in each coordinate when
`F (update x k (x k + 1)) = F x` for every coordinate `k` and every point `x`. This file records
the consequences of this periodicity that the integration by parts of the loop equations needs:

* `periodic_translate_of_update`: `F` is invariant under translation by an integer in every
  coordinate, in particular `F (fun i => x i + m) = F x` for every integer `m`.
* `periodic_partialDeriv`: the partial derivative `partialDeriv F k` is again one-periodic in each
  coordinate.
* `exists_bound_of_periodic`: a continuous one-periodic function is bounded.
* `exists_bound_partialDeriv_of_periodic`: the partial derivatives of a smooth one-periodic
  function are bounded.

The partial derivative of a smooth function is continuous by
`continuous_partialDeriv_of_contDiff`, which feeds the bound for partial derivatives.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-! ### Invariance under integer translations -/

/-- Along one coordinate, the function `t ↦ F (update x k t)` is one-periodic. -/
lemma periodic_update_one {N : ℕ} {F : (Fin N → ℝ) → ℝ}
    (hF : ∀ (k : Fin N) (x : Fin N → ℝ), F (Function.update x k (x k + 1)) = F x)
    (k : Fin N) (x : Fin N → ℝ) :
    Function.Periodic (fun t : ℝ => F (Function.update x k t)) 1 := by
  intro t
  have h := hF k (Function.update x k t)
  rw [Function.update_idem, Function.update_self] at h
  exact h

/-- Translating one coordinate by an integer does not change the value of `F`. -/
lemma periodic_update_int {N : ℕ} {F : (Fin N → ℝ) → ℝ}
    (hF : ∀ (k : Fin N) (x : Fin N → ℝ), F (Function.update x k (x k + 1)) = F x)
    (k : Fin N) (x : Fin N → ℝ) (m : ℤ) :
    F (Function.update x k (x k + (m : ℝ))) = F x := by
  have h := (periodic_update_one hF k x).int_mul m (x k)
  simp only [mul_one, Function.update_eq_self] at h
  exact h

/-- Translating every coordinate `i` by its own integer `n i` does not change the value of `F`.
The proof adds the shifted coordinates one at a time along a finite set of coordinates. -/
lemma periodic_shift_coords {N : ℕ} {F : (Fin N → ℝ) → ℝ}
    (hF : ∀ (k : Fin N) (x : Fin N → ℝ), F (Function.update x k (x k + 1)) = F x)
    (n : Fin N → ℤ) (x : Fin N → ℝ) :
    F (fun i => x i + (n i : ℝ)) = F x := by
  -- For a finite set `s` of coordinates, shift the coordinates in `s` and keep the others.
  have key : ∀ s : Finset (Fin N), ∀ y : Fin N → ℝ,
      F (fun i => if i ∈ s then y i + (n i : ℝ) else y i) = F y := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro y
      simp
    · intro a t ha ih y
      -- Adding the coordinate `a` is one update of the function for `t`, since `a ∉ t`.
      have hfun : (fun i => if i ∈ insert a t then y i + (n i : ℝ) else y i) =
          Function.update (fun i => if i ∈ t then y i + (n i : ℝ) else y i) a
            ((fun i => if i ∈ t then y i + (n i : ℝ) else y i) a + (n a : ℝ)) := by
        funext i
        by_cases hi : i = a
        · subst hi
          simp [ha]
        · simp [hi]
      rw [hfun]
      exact (periodic_update_int hF a _ (n a)).trans (ih y)
  have h := key Finset.univ x
  simpa using h

/-- **Invariance under integer translations.** If `F` is one-periodic in each coordinate, then
translating the whole point by an integer `m` in every coordinate does not change `F`. -/
theorem periodic_translate_of_update {N : ℕ} {F : (Fin N → ℝ) → ℝ}
    (hF : ∀ (k : Fin N) (x : Fin N → ℝ), F (Function.update x k (x k + 1)) = F x)
    (m : ℤ) (x : Fin N → ℝ) : F (fun i => x i + (m : ℝ)) = F x :=
  periodic_shift_coords hF (fun _ => m) x

/-! ### Partial derivatives of periodic functions -/

/-- The partial derivative of a differentiable function is the derivative along the `k`-th
coordinate line, which is the directional derivative along `Pi.single k 1`. -/
lemma partialDeriv_eq_fderiv {N : ℕ} {F : (Fin N → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (k : Fin N) (x : Fin N → ℝ) :
    partialDeriv F k x = fderiv ℝ F x (Pi.single k 1) := by
  have hdiff : DifferentiableAt ℝ F (Function.update x k (x k)) := by
    rw [Function.update_eq_self]
    exact (hF.differentiable (by simp)) x
  have hcomp := HasFDerivAt.comp_hasDerivAt (x k) (DifferentiableAt.hasFDerivAt hdiff)
    (hasDerivAt_update x k (x k))
  rw [Function.update_eq_self] at hcomp
  unfold partialDeriv
  exact hcomp.deriv

/-- **The partial derivative of a smooth function is continuous.** -/
theorem continuous_partialDeriv_of_contDiff {N : ℕ} {F : (Fin N → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (k : Fin N) : Continuous (partialDeriv F k) := by
  have h : partialDeriv F k = fun x => fderiv ℝ F x (Pi.single k 1) :=
    funext fun x => partialDeriv_eq_fderiv hF k x
  rw [h]
  exact (hF.continuous_fderiv (by simp)).clm_apply continuous_const

/-- The derivative of a one-periodic function is one-periodic, evaluated at the shifted point. -/
lemma deriv_periodic_one {g : ℝ → ℝ} (hg : Function.Periodic g 1) (t : ℝ) :
    deriv g (t + 1) = deriv g t := by
  have h := deriv_comp_add_const (f := g) (a := 1) (x := t)
  rw [show (fun x => g (x + 1)) = g from funext hg] at h
  exact h.symm

/-- **The partial derivatives of a one-periodic function are one-periodic.** For fixed `k`, the
function `partialDeriv F k` is one-periodic in each coordinate. -/
theorem periodic_partialDeriv {N : ℕ} {F : (Fin N → ℝ) → ℝ}
    (hF : ∀ (k : Fin N) (x : Fin N → ℝ), F (Function.update x k (x k + 1)) = F x)
    (k j : Fin N) (x : Fin N → ℝ) :
    partialDeriv F k (Function.update x j (x j + 1)) = partialDeriv F k x := by
  by_cases hjk : j = k
  · -- Both sides are derivatives of the one-periodic function `t ↦ F (update x k t)`, at
    -- the points `x k + 1` and `x k`.
    rw [hjk]
    unfold partialDeriv
    simp only [Function.update_idem, Function.update_self]
    exact deriv_periodic_one (periodic_update_one hF k x) (x k)
  · -- The moving coordinate `k` does not see the shift in coordinate `j`, and `hF` at `j`
    -- removes that shift.
    have hkj : k ≠ j := fun h => hjk h.symm
    unfold partialDeriv
    rw [Function.update_of_ne hkj]
    congr 1
    funext t
    rw [Function.update_comm hjk]
    have h := hF j (Function.update x k t)
    rw [Function.update_of_ne hjk] at h
    exact h

/-! ### Boundedness of periodic functions -/

/-- **A continuous one-periodic function is bounded.** If `F` is continuous and one-periodic in
each coordinate, then `|F x| ≤ M` for all `x` and some real `M`. -/
theorem exists_bound_of_periodic {N : ℕ} {F : (Fin N → ℝ) → ℝ} (hcont : Continuous F)
    (hF : ∀ (k : Fin N) (x : Fin N → ℝ), F (Function.update x k (x k + 1)) = F x) :
    ∃ M : ℝ, ∀ x : Fin N → ℝ, |F x| ≤ M := by
  -- The product `[0,1]^N` is compact and contains a periodic representative of every orbit.
  obtain ⟨M, hM⟩ := (isCompact_univ_pi (fun _ : Fin N => isCompact_Icc (a := (0 : ℝ)) (b := 1)))
    |>.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨M, fun x => ?_⟩
  -- Each coordinate is moved to its fractional part by the integer `-⌊x i⌋`.
  have hfr : (fun i => Int.fract (x i)) = fun i => x i + ((-⌊x i⌋ : ℤ) : ℝ) := by
    funext i
    unfold Int.fract
    push_cast
    ring
  have hper : F (fun i => Int.fract (x i)) = F x := by
    rw [hfr]
    exact periodic_shift_coords hF (fun i => -⌊x i⌋) x
  have hmem : (fun i => Int.fract (x i)) ∈ Set.pi univ (fun _ : Fin N => Icc (0 : ℝ) 1) :=
    Set.mem_univ_pi.2 fun i => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  rw [← hper, ← Real.norm_eq_abs]
  exact hM _ hmem

/-- **The partial derivatives of a smooth one-periodic function are bounded.** For every
coordinate `k`, the function `partialDeriv F k` is bounded on `ℝ^N`. -/
theorem exists_bound_partialDeriv_of_periodic {N : ℕ} {F : (Fin N → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (hper : ∀ (k : Fin N) (x : Fin N → ℝ), F (Function.update x k (x k + 1)) = F x)
    (k : Fin N) : ∃ M : ℝ, ∀ x : Fin N → ℝ, |partialDeriv F k x| ≤ M :=
  exists_bound_of_periodic (continuous_partialDeriv_of_contDiff hF k)
    (fun j x => periodic_partialDeriv hper k j x)

end Riesz1

end
