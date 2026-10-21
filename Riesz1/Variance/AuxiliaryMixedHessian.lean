/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPMoments
public import Riesz1.Variance.LoopForceKernel

/-!
# The pair form of the Hessian quadratic term

The Hessian step in the proof of the mixed identity in Proposition 5.6. For the field
`Ψ_ψ(X) = (ℓ ψ(x_i/ℓ))_i`, the quadratic term `β Ψ_ψ · ∇²H_N Ψ_ψ` of Proposition 5.5 is a
sum over ordered pairs
of distinct particles,
`β N^{-s} ∑_{i ≠ j} g_s''(x_i - x_j) (Ψ_i - Ψ_j)²`.
The file proves this identity from the closed form `hessianSum` of the second derivatives of the
lifted energy. The pair form is the input of the expansion.

The main results are `Riesz1.sum_hessianSum_mul` (the algebra on `Fin n`) and
`Riesz1.hessianQuadratic_eq_pairSum` (the statement for configurations).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The second derivative of the kernel is even: `g''(-x) = g''(x)`. -/
lemma deriv_deriv_hurwitzKernel_neg (s x : ℝ) :
    deriv (deriv (hurwitzKernel s)) (-x) = deriv (deriv (hurwitzKernel s)) x := by
  set f := deriv (hurwitzKernel s) with hf
  have hodd : ∀ y, f (-y) = -f y := fun y => deriv_hurwitzKernel_neg' s y
  have hfun : (fun y => -f (-y)) = f := funext fun y => by rw [hodd, neg_neg]
  have h1 : deriv f x = deriv (fun y => -f (-y)) x := by rw [hfun]
  have h2 : deriv (fun y => -f (-y)) x = -deriv (fun y => f (-y)) x :=
    deriv.neg (f := fun y => f (-y))
  have h3 : deriv (fun y => f (-y)) x = -deriv f (-x) := deriv_comp_neg f x
  rw [h1, h2, h3, neg_neg]

/-- The second derivative of the kernel at a difference is symmetric in its two arguments. -/
lemma deriv_deriv_hurwitzKernel_sub_comm (s a b : ℝ) :
    deriv (deriv (hurwitzKernel s)) (a - b) = deriv (deriv (hurwitzKernel s)) (b - a) := by
  rw [← deriv_deriv_hurwitzKernel_neg s (a - b), neg_sub]

/-- The algebra of the closed form of the Hessian sum: the quadratic form of the second
derivatives of the lifted energy at a field `Ψ`, summed over ordered pairs of distinct
particles. -/
lemma sum_hessianSum_mul (s : ℝ) (n : ℕ) (x Ψ : Fin n → ℝ) :
    ∑ k : Fin n, ∑ l : Fin n, Ψ k * Ψ l * hessianSum s n k l x =
      (n : ℝ) ^ (-s) * ∑ i : Fin n, ∑ j : Fin n,
        (if j = i then 0 else
          deriv (deriv (hurwitzKernel s)) (x i - x j) * (Ψ i - Ψ j) ^ 2) := by
  set g := deriv (deriv (hurwitzKernel s)) with hg
  -- The off-diagonal term `F k j` is `Ψ_k (Ψ_k - Ψ_j) g(x_k - x_j)`.
  set F : Fin n → Fin n → ℝ := fun k j =>
    if j = k then 0 else Ψ k * (Ψ k - Ψ j) * g (x k - x j) with hF
  -- The `l`-sum of the closed form collapses to the two indices `l = k` and `l = j`.
  have hl : ∀ k j : Fin n, ∑ l : Fin n, Ψ k * Ψ l *
      (if j = k then (0 : ℝ) else if k = l then g (x k - x j)
        else if j = l then -g (x k - x j) else 0) = F k j := by
    intro k j
    by_cases hjk : j = k
    · simp [hF, hjk]
    · have hterm : ∀ l : Fin n, Ψ k * Ψ l * (if k = l then g (x k - x j)
          else if j = l then -g (x k - x j) else 0) =
          (if k = l then Ψ k * Ψ l * g (x k - x j) else 0) +
          (if j = l then -(Ψ k * Ψ l * g (x k - x j)) else 0) := by
        intro l
        by_cases hkl : k = l
        · subst hkl
          simp [hjk]
        · by_cases hjl : j = l
          · subst hjl
            simp [hkl]
          · simp [hkl, hjl]
      simp only [hF, hjk, ↓reduceIte]
      simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring
  -- The closed form, written with the kernel `F`.
  have hA : ∀ k l : Fin n, hessianSum s n k l x = (n : ℝ) ^ (-s) * (2 * ∑ j : Fin n,
      (if j = k then (0 : ℝ) else if k = l then g (x k - x j)
        else if j = l then -g (x k - x j) else 0)) := fun k l => rfl
  have hexp : ∀ k l : Fin n, Ψ k * Ψ l * hessianSum s n k l x =
      ((n : ℝ) ^ (-s) * 2) * ∑ j : Fin n, Ψ k * Ψ l *
        (if j = k then (0 : ℝ) else if k = l then g (x k - x j)
          else if j = l then -g (x k - x j) else 0) := by
    intro k l
    rw [hA, ← Finset.mul_sum]
    ring
  -- The double sum equals `2 N^{-s}` times the double sum of `F`.
  have hstep1 : ∑ k : Fin n, ∑ l : Fin n, Ψ k * Ψ l * hessianSum s n k l x =
      ((n : ℝ) ^ (-s) * 2) * ∑ k : Fin n, ∑ j : Fin n, F k j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl fun l _ => hexp k l, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hl k j
  -- Symmetry of the kernel second derivative, and the symmetrization of `F`.
  have hpair : ∀ k j : Fin n, F k j + F j k =
      (if j = k then 0 else g (x k - x j) * (Ψ k - Ψ j) ^ 2) := by
    intro k j
    by_cases hjk : j = k
    · subst hjk
      simp [hF]
    · have hkj : ¬ k = j := fun h => hjk h.symm
      have hsym : g (x j - x k) = g (x k - x j) :=
        deriv_deriv_hurwitzKernel_sub_comm s (x j) (x k)
      simp only [hF, hjk, hkj, ↓reduceIte]
      rw [hsym]
      ring
  have hswap : ∑ k : Fin n, ∑ j : Fin n, F k j = ∑ k : Fin n, ∑ j : Fin n, F j k :=
    Finset.sum_comm
  have hsum : ∑ i : Fin n, ∑ j : Fin n, (if j = i then (0 : ℝ) else
      g (x i - x j) * (Ψ i - Ψ j) ^ 2) = ∑ k : Fin n, ∑ j : Fin n, (F k j + F j k) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (hpair i j).symm
  rw [hstep1, hsum]
  simp only [Finset.sum_add_distrib]
  rw [← hswap]
  ring

/-- The Hessian quadratic term in pair form: `β Ψ_ψ · ∇²H_N Ψ_ψ = β N^{-s} ∑_{i ≠ j}
g_s''(x_i - x_j) (Ψ_i - Ψ_j)²` with `Ψ_i = ℓ ψ(x_i/ℓ)`, as used in the mixed identity
of Proposition 5.6. -/
theorem hessianQuadratic_eq_pairSum (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) (X : Configuration N) :
    hessianQuadratic P N ℓ ψ X = P.val.1 * (N : ℝ) ^ (-(parametersExponent P).val) *
      ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), (if j = i then 0 else
        deriv (deriv (hurwitzKernel (parametersExponent P).val)) (X.val i - X.val j) *
          (loopScaleField ℓ.val ψ.val (X.val i) - loopScaleField ℓ.val ψ.val (X.val j)) ^ 2) := by
  have h := sum_hessianSum_mul (parametersExponent P).val (N : ℕ) X.val
    (fun k => loopScaleField ℓ.val ψ.val (X.val k))
  rw [hessianQuadratic_eq, h]
  ring

end Riesz1

end

end
