/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPPairs
public import Riesz1.Variance.LoopScale
import all Riesz1.Variance.LoopForce
import all Riesz1.Variance.LoopForceEnergy

/-!
# Second derivatives of the lifted energy

Proposition 5.5, Hessian quadratic term. For the lifted energy
`H_N(x) = N^{-s} ∑_{i ≠ j} g_s(x_i - x_j)` the second partial derivatives off the collisions are
explicit sums of second derivatives of the kernel. Each entry is bounded by a constant multiple of
the power sum `∑ₖ gapₖ^{-(s+2)}`, which gives every finite moment of the Hessian quadratic term.
-/

@[expose] public section

open MeasureTheory Set Filter Topology UnitAddCircle

namespace Riesz1

/-- Moving one coordinate keeps every pair of the configuration off the integers, for every
parameter near the current value. -/
lemma eventually_noncollision {N : ℕ} (x : Fin N → ℝ)
    (hx : ∀ i j : Fin N, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0) (l : Fin N) :
    ∀ᶠ t in 𝓝 (x l), ∀ i j : Fin N, i ≠ j →
      ((Function.update x l t i - Function.update x l t j : ℝ) : UnitAddCircle) ≠ 0 := by
  have key : ∀ i j : Fin N, i ≠ j → ∀ᶠ t in 𝓝 (x l),
      ((Function.update x l t i - Function.update x l t j : ℝ) : UnitAddCircle) ≠ 0 := by
    intro i j hij
    by_cases hi : i = l
    · have hj : j ≠ l := fun h => hij (hi.trans h.symm)
      have hexpr : ∀ t : ℝ, Function.update x l t i - Function.update x l t j = t - x j := by
        intro t
        rw [hi, Function.update_self, Function.update_of_ne hj]
      have hc : Continuous fun t : ℝ => ((t - x j : ℝ) : UnitAddCircle) := by
        fun_prop
      have hmem : x l ∈ {t : ℝ | ((t - x j : ℝ) : UnitAddCircle) ≠ 0} := by
        show ((x l - x j : ℝ) : UnitAddCircle) ≠ 0
        rw [← hi]
        exact hx i j hij
      filter_upwards [(isOpen_ne_fun hc continuous_const).mem_nhds hmem] with t ht
      rw [hexpr t]
      exact ht
    · by_cases hj : j = l
      · have hexpr : ∀ t : ℝ, Function.update x l t i - Function.update x l t j = x i - t := by
          intro t
          rw [hj, Function.update_self, Function.update_of_ne hi]
        have hc : Continuous fun t : ℝ => ((x i - t : ℝ) : UnitAddCircle) := by
          fun_prop
        have hmem : x l ∈ {t : ℝ | ((x i - t : ℝ) : UnitAddCircle) ≠ 0} := by
          show ((x i - x l : ℝ) : UnitAddCircle) ≠ 0
          rw [← hj]
          exact hx i j hij
        filter_upwards [(isOpen_ne_fun hc continuous_const).mem_nhds hmem] with t ht
        rw [hexpr t]
        exact ht
      · refine Filter.Eventually.of_forall fun t => ?_
        rw [Function.update_of_ne hi, Function.update_of_ne hj]
        exact hx i j hij
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  by_cases hij : i ≠ j
  · exact (key i j hij).mono fun t ht _ => ht
  · exact Filter.Eventually.of_forall fun t h => absurd h hij

/-- The derivative of one summand of the first partial derivative of the lifted energy, in the
coordinate `l`, at the point `x l`. The summand is `g_s'(x_k - x_j)` for `j ≠ k` and zero for
`j = k`. -/
lemma hasDerivAt_kernelDeriv_term {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ}
    (x : Fin N → ℝ) (hx : ∀ i j : Fin N, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0)
    (l k j : Fin N) :
    HasDerivAt (fun t : ℝ => if j = k then (0 : ℝ) else
        deriv (hurwitzKernel s) (Function.update x l t k - Function.update x l t j))
      (if j = k then 0 else if k = l then deriv (deriv (hurwitzKernel s)) (x k - x j)
        else if j = l then -deriv (deriv (hurwitzKernel s)) (x k - x j) else 0) (x l) := by
  by_cases hjk : j = k
  · simp only [hjk, ↓reduceIte]
    exact hasDerivAt_const _ _
  · simp only [hjk, ↓reduceIte]
    by_cases hkl : k = l
    · subst hkl
      have hyk : ∀ t : ℝ, Function.update x k t k = t := fun t => Function.update_self _ _ _
      have hyj : ∀ t : ℝ, Function.update x k t j = x j := fun t =>
        Function.update_of_ne hjk _ _
      have hne : ((x k - x j : ℝ) : UnitAddCircle) ≠ 0 := hx k j (fun h => hjk h.symm)
      have hd := hasDerivAt_deriv_hurwitzKernel_of_ne s hs0 hs1 (x k - x j) hne
      have hlin : HasDerivAt (fun t : ℝ => t - x j) 1 (x k) := by
        simpa using (hasDerivAt_id (x k)).sub_const (x j)
      have hcomp := hd.comp (x k) hlin
      have hfun : (fun t : ℝ => deriv (hurwitzKernel s)
          (Function.update x k t k - Function.update x k t j)) =
          deriv (hurwitzKernel s) ∘ (fun t : ℝ => t - x j) := by
        funext t
        simp only [Function.comp, hyk, hyj]
      rw [hfun]
      simpa using hcomp
    · simp only [hkl, ↓reduceIte]
      by_cases hjl : j = l
      · subst hjl
        have hyj : ∀ t : ℝ, Function.update x j t j = t := fun t => Function.update_self _ _ _
        have hyk : ∀ t : ℝ, Function.update x j t k = x k := fun t =>
          Function.update_of_ne hkl _ _
        have hne : ((x k - x j : ℝ) : UnitAddCircle) ≠ 0 := hx k j (fun h => hjk h.symm)
        have hd := hasDerivAt_deriv_hurwitzKernel_of_ne s hs0 hs1 (x k - x j) hne
        have hlin : HasDerivAt (fun t : ℝ => x k - t) (-1) (x j) := by
          simpa using (hasDerivAt_id (x j)).const_sub (x k)
        have hcomp := hd.comp (x j) hlin
        have hfun : (fun t : ℝ => deriv (hurwitzKernel s)
            (Function.update x j t k - Function.update x j t j)) =
            deriv (hurwitzKernel s) ∘ (fun t : ℝ => x k - t) := by
          funext t
          simp only [Function.comp, hyk, hyj]
        rw [hfun]
        simpa using hcomp
      · simp only [hjl, ↓reduceIte]
        have hyk : ∀ t : ℝ, Function.update x l t k = x k := fun t =>
          Function.update_of_ne hkl _ _
        have hyj : ∀ t : ℝ, Function.update x l t j = x j := fun t =>
          Function.update_of_ne hjl _ _
        have hfun : (fun t : ℝ => deriv (hurwitzKernel s)
            (Function.update x l t k - Function.update x l t j)) =
            fun _ => deriv (hurwitzKernel s) (x k - x j) := by
          funext t
          rw [hyk, hyj]
        rw [hfun]
        exact hasDerivAt_const _ _

/-- The closed form of the second partial derivative `∂_l ∂_k H_N` of the lifted energy at a
noncollision point `x`: the sum over `j` of the second derivatives of the kernel at `x_k - x_j`,
with the sign and the index pattern of the product rule. -/
noncomputable def hessianSum (s : ℝ) (N : ℕ) (k l : Fin N) (x : Fin N → ℝ) : ℝ :=
  (N : ℝ) ^ (-s) * (2 * ∑ j : Fin N, (if j = k then (0 : ℝ) else
    if k = l then deriv (deriv (hurwitzKernel s)) (x k - x j)
    else if j = l then -deriv (deriv (hurwitzKernel s)) (x k - x j) else 0))

/-- The derivative of the first partial derivative in the direction `l`, at a noncollision point. -/
lemma hasDerivAt_hessianSum {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ}
    (x : Fin N → ℝ) (hx : ∀ i j : Fin N, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0)
    (k l : Fin N) :
    HasDerivAt (fun t : ℝ => (N : ℝ) ^ (-s) * (2 * ∑ j : Fin N, if j = k then (0 : ℝ) else
        deriv (hurwitzKernel s) (Function.update x l t k - Function.update x l t j)))
      (hessianSum s N k l x) (x l) := by
  unfold hessianSum
  apply HasDerivAt.const_mul
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro j _
  exact hasDerivAt_kernelDeriv_term hs0 hs1 x hx l k j

/-- The second partial derivative of the lifted energy is the closed form `hessianSum`
at every noncollision point. -/
theorem partialDeriv_partialDeriv_energyLift_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ}
    (x : Fin N → ℝ) (hx : ∀ i j : Fin N, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0)
    (k l : Fin N) :
    partialDeriv (fun y => partialDeriv (energyLift ⟨s, hs0, hs1⟩ N) k y) l x =
      hessianSum s N k l x := by
  have hev : (fun t : ℝ => partialDeriv (energyLift ⟨s, hs0, hs1⟩ N) k
      (Function.update x l t)) =ᶠ[𝓝 (x l)] (fun t : ℝ => (N : ℝ) ^ (-s) *
        (2 * ∑ j : Fin N, if j = k then (0 : ℝ) else
          deriv (hurwitzKernel s) (Function.update x l t k - Function.update x l t j))) := by
    filter_upwards [eventually_noncollision x hx l] with t ht
    exact partialDeriv_energyLift hs0 hs1 (Function.update x l t) ht k
  have hd := (hasDerivAt_hessianSum hs0 hs1 x hx k l).congr_of_eventuallyEq hev
  change deriv (fun t : ℝ => partialDeriv (energyLift ⟨s, hs0, hs1⟩ N) k
    (Function.update x l t)) (x l) = _
  exact hd.deriv

/-- The closed form is measurable in the point. -/
theorem measurable_hessianSum (s : ℝ) (N : ℕ) (k l : Fin N) :
    Measurable (fun x : Fin N → ℝ => hessianSum s N k l x) := by
  unfold hessianSum
  refine measurable_const.mul (measurable_const.mul ?_)
  refine Finset.measurable_sum _ fun j _ => ?_
  split_ifs <;> first
    | exact measurable_const
    | exact (measurable_deriv (deriv (hurwitzKernel s))).comp
        ((measurable_pi_apply k).sub (measurable_pi_apply j))
    | exact ((measurable_deriv (deriv (hurwitzKernel s))).comp
        ((measurable_pi_apply k).sub (measurable_pi_apply j))).neg

/-- Every second partial derivative of the lifted energy is bounded by a constant multiple of the
power sum `∑ₖ gapₖ^{-(s+2)}` on every configuration. -/
theorem exists_hessianSum_le (s : RieszExponent) (N : ℕ+) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : Configuration N) (k l : Fin (N : ℕ)),
      |hessianSum s.val (N : ℕ) k l X.val| ≤ C * gapPowerSum (s.val + 2) X := by
  obtain ⟨C₂, hC₂, hb⟩ := deriv_deriv_hurwitzKernel_bound s.val s.property.1 s.property.2
  have hNr : (0 : ℝ) ≤ (N : ℝ) ^ (-s.val) := (Real.rpow_pos_of_pos (by exact_mod_cast N.pos) _).le
  have hNs : (0 : ℝ) ≤ (N : ℝ) ^ (s.val + 2) := (Real.rpow_pos_of_pos (by exact_mod_cast N.pos) _).le
  have hNN : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le _)
  refine ⟨2 * (N : ℝ) ^ (-s.val) * (N : ℝ) * C₂ * (N : ℝ) ^ (s.val + 2),
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hNr) hNN) hC₂.le) hNs,
    fun X k l => ?_⟩
  have hG0 : 0 ≤ gapPowerSum (s.val + 2) X := by
    unfold gapPowerSum
    exact Finset.sum_nonneg fun j _ => Real.rpow_nonneg (gap_pos X _).le _
  set c : ℝ := C₂ * ((N : ℝ) ^ (s.val + 2) * gapPowerSum (s.val + 2) X) with hc
  have hc0 : 0 ≤ c := mul_nonneg hC₂.le (mul_nonneg hNs hG0)
  -- Each summand of the closed form is bounded by `c`.
  have hterm : ∀ j : Fin (N : ℕ),
      |(if j = k then (0 : ℝ) else
        if k = l then deriv (deriv (hurwitzKernel s.val)) (X.val k - X.val j)
        else if j = l then -deriv (deriv (hurwitzKernel s.val)) (X.val k - X.val j) else 0)| ≤ c := by
    intro j
    by_cases hjk : j = k
    · simp only [hjk, ↓reduceIte, abs_zero]
      exact hc0
    · simp only [hjk, ↓reduceIte]
      have hne : k ≠ j := fun h => hjk h.symm
      have hA : |deriv (deriv (hurwitzKernel s.val)) (X.val k - X.val j)| ≤ c := by
        have h1 := hb (X.val k - X.val j) (coe_sub_ne_zero X hne)
        rw [show -s.val - 2 = -(s.val + 2) by ring] at h1
        have h2 := dist_rpow_le_gapPowerSum X hne (r := s.val + 2) (by linarith [s.property.1])
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hC₂.le)
      split_ifs
      · exact hA
      · rw [abs_neg]; exact hA
      · rw [abs_zero]; exact hc0
  have hsum : |∑ j : Fin (N : ℕ), (if j = k then (0 : ℝ) else
        if k = l then deriv (deriv (hurwitzKernel s.val)) (X.val k - X.val j)
        else if j = l then -deriv (deriv (hurwitzKernel s.val)) (X.val k - X.val j) else 0)| ≤
      (N : ℝ) * c := by
    calc _ ≤ ∑ j : Fin (N : ℕ), |(if j = k then (0 : ℝ) else
          if k = l then deriv (deriv (hurwitzKernel s.val)) (X.val k - X.val j)
          else if j = l then -deriv (deriv (hurwitzKernel s.val)) (X.val k - X.val j) else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin (N : ℕ), c := Finset.sum_le_sum fun j _ => hterm j
      _ = (N : ℝ) * c := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  unfold hessianSum
  rw [abs_mul, abs_of_nonneg hNr, abs_mul, abs_two]
  calc (N : ℝ) ^ (-s.val) * (2 * |∑ j : Fin (N : ℕ), (if j = k then (0 : ℝ) else
        if k = l then deriv (deriv (hurwitzKernel s.val)) (X.val k - X.val j)
        else if j = l then -deriv (deriv (hurwitzKernel s.val)) (X.val k - X.val j) else 0)|)
      ≤ (N : ℝ) ^ (-s.val) * (2 * ((N : ℝ) * c)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by norm_num)) hNr
    _ = 2 * (N : ℝ) ^ (-s.val) * (N : ℝ) * C₂ * (N : ℝ) ^ (s.val + 2) *
        gapPowerSum (s.val + 2) X := by rw [hc]; ring

/-- The second partial derivative of the lifted energy, with the exponent as a `RieszExponent`. -/
theorem partialDeriv_partialDeriv_energyLift_eq' (s : RieszExponent) {N : ℕ}
    (x : Fin N → ℝ) (hx : ∀ i j : Fin N, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0)
    (k l : Fin N) :
    partialDeriv (fun y => partialDeriv (energyLift s N) k y) l x = hessianSum s.val N k l x :=
  partialDeriv_partialDeriv_energyLift_eq s.property.1 s.property.2 x hx k l

end Riesz1

end
