/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPProposition
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
import all Riesz1.Variance.LoopForceEnergy
import all Riesz1.Variance.LoopForce

/-!
# Partial derivatives in the exact approximate Gaussian identity

Calculus used in the proof of Theorem 3, stated for generic profiles:

* the partial derivative of the scaled fluctuation `Σᵢ f(xᵢ/ℓ) - N ∫ f(·/ℓ)`.
* the partial derivative of the potential `Φ_{ψ,a}`, which is `a ℓ ψ(xₖ/ℓ)`.
* the chain rule for `u ∘ G` on the configuration lift.
* the pairing identity `∂ₖG · ∂ₖΦ = K⁻¹ q(xₖ/ℓ)` with `K = Nℓ` and `q = ψ · R'`, where the
  product `ξ_reg'` is `R'` in the notation below.

The coordinatewise derivatives use `partialDeriv` of `Riesz1.LoopForceEnergy`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The derivative of the primitive `t ↦ ∫₀^{t/ℓ} Ψ` for a continuous `Ψ`. -/
lemma hasDerivAt_primitive_scaled {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ) {ℓ : ℝ}
    (t : ℝ) : HasDerivAt (fun t : ℝ => ∫ u in (0 : ℝ)..(t / ℓ), Ψ u) (Ψ (t / ℓ) * (1 / ℓ)) t := by
  have h1 := hΨ.integral_hasStrictDerivAt 0 (t / ℓ)
  have h2 : HasDerivAt (fun t : ℝ => t / ℓ) (1 / ℓ) t := by
    simpa using (hasDerivAt_id t).div_const ℓ
  exact h1.hasDerivAt.comp t h2

/-- The partial derivative of the scaled fluctuation `x ↦ Σᵢ f(xᵢ) - N ∫₀¹ f` at `f(u) = R(u/ℓ)`
is `R'(xₖ/ℓ)/ℓ`. -/
lemma partialDeriv_fluctIntegral_scaled {N : ℕ} {R : ℝ → ℝ} (hR : Differentiable ℝ R) {ℓ : ℝ}
    (k : Fin N) (x : Fin N → ℝ) :
    partialDeriv (fun y => fluctIntegral (fun u => R (u / ℓ)) N y) k x
      = deriv R (x k / ℓ) * (1 / ℓ) := by
  unfold partialDeriv
  have hi : ∀ i : Fin N, HasDerivAt
      (fun t : ℝ => R (Function.update x k t i / ℓ))
      (if i = k then deriv R (x k / ℓ) * (1 / ℓ) else 0) (x k) := by
    intro i
    by_cases hik : i = k
    · subst hik
      simp only [Function.update_self, ite_true]
      have h2 : HasDerivAt (fun t : ℝ => t / ℓ) (1 / ℓ) (x i) := by
        simpa using (hasDerivAt_id (x i)).div_const ℓ
      exact (hR (x i / ℓ)).hasDerivAt.comp (x i) h2
    · simp only [hik, ite_false]
      have : (fun t : ℝ => R (Function.update x k t i / ℓ)) =
          fun _ => R (x i / ℓ) := by
        funext t
        rw [Function.update_of_ne hik]
      rw [this]
      exact hasDerivAt_const _ _
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
  have hfull : HasDerivAt (fun t : ℝ => fluctIntegral (fun u => R (u / ℓ)) N (Function.update x k t))
      (∑ i : Fin N, if i = k then deriv R (x k / ℓ) * (1 / ℓ) else 0) (x k) := by
    unfold fluctIntegral
    have hc : HasDerivAt (fun _ : ℝ => (N : ℝ) * ∫ u in (0 : ℝ)..1, R (u / ℓ)) 0 (x k) :=
      hasDerivAt_const _ _
    have h := hsum.sub hc
    rw [sub_zero] at h
    exact h
  rw [hfull.deriv, Finset.sum_ite_eq' Finset.univ k]
  simp

/-- The partial derivative of `Σᵢ ∫₀^{xᵢ/ℓ} Ψ` is `Ψ(xₖ/ℓ)/ℓ`, so the potential
`x ↦ a ℓ² Σᵢ ∫₀^{xᵢ/ℓ} Ψ` has partial derivative `a ℓ Ψ(xₖ/ℓ)`. -/
lemma partialDeriv_primitive_sum {N : ℕ} {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : ℝ) (k : Fin N) (x : Fin N → ℝ) :
    partialDeriv (fun y : Fin N → ℝ => a * ℓ ^ 2 * ∑ i : Fin N, ∫ u in (0 : ℝ)..(y i / ℓ), Ψ u)
      k x = a * ℓ * Ψ (x k / ℓ) := by
  change deriv (fun t : ℝ => a * ℓ ^ 2 * ∑ i : Fin N,
    ∫ u in (0 : ℝ)..(Function.update x k t i / ℓ), Ψ u) (x k) = _
  have hi : ∀ i : Fin N, HasDerivAt
      (fun t : ℝ => ∫ u in (0 : ℝ)..(Function.update x k t i / ℓ), Ψ u)
      (if i = k then Ψ (x k / ℓ) * (1 / ℓ) else 0) (x k) := by
    intro i
    by_cases hik : i = k
    · subst hik
      simp only [Function.update_self, ite_true]
      exact hasDerivAt_primitive_scaled hΨ (x i)
    · simp only [hik, ite_false]
      have : (fun t : ℝ => ∫ u in (0 : ℝ)..(Function.update x k t i / ℓ), Ψ u) =
          fun _ => ∫ u in (0 : ℝ)..(x i / ℓ), Ψ u := by
        funext t
        rw [Function.update_of_ne hik]
      rw [this]
      exact hasDerivAt_const _ _
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
  have hfull : HasDerivAt (fun t : ℝ => ∑ i : Fin N,
      ∫ u in (0 : ℝ)..(Function.update x k t i / ℓ), Ψ u)
      (∑ i : Fin N, if i = k then Ψ (x k / ℓ) * (1 / ℓ) else 0) (x k) := by
    convert hsum using 1
  have hfin := hfull.const_mul (a * ℓ ^ 2)
  rw [hfin.deriv, Finset.sum_ite_eq' Finset.univ k]
  simp only [Finset.mem_univ, ite_true]
  field_simp

/-- The chain rule for `u ∘ G` in the coordinate `k`: the partial derivative of `u ∘ G` is
`u'(G) ∂ₖG`. -/
lemma partialDeriv_comp_outer {N : ℕ} {u : ℝ → ℝ} {G : (Fin N → ℝ) → ℝ} (hu : Differentiable ℝ u)
    (hG : Differentiable ℝ G) (k : Fin N) (x : Fin N → ℝ) :
    partialDeriv (fun y => u (G y)) k x = deriv u (G x) * partialDeriv G k x := by
  unfold partialDeriv
  have hinner : DifferentiableAt ℝ (fun t : ℝ => G (Function.update x k t)) (x k) := by
    refine (hG _).comp (x k) ?_
    exact differentiableAt_pi.mpr fun i => by
      by_cases hik : i = k
      · subst hik
        simp
      · simp only [Function.update_of_ne hik]
        exact differentiableAt_const _
  have h := deriv_comp (x k) (hu _) hinner
  rw [Function.update_eq_self] at h
  exact h

end Riesz1

end
