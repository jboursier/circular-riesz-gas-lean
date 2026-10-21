/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPCutoff
public import Riesz1.Variance.LoopForceEnergy
public import Riesz1.HelfferSjostrand.RieszAdmissiblePairs
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.Gradient.Basic
import all Riesz1.Variance.LoopForceEnergy

/-!
# Helffer–Sjöstrand derivatives of the Riesz pair Hamiltonian on the lifted chamber

The derivative identities behind the cutoff argument in
Proposition 5.5. On the open lifted chamber, the Riesz pair Hamiltonian equals
`β` times the lifted energy `energyLift`, so its partial derivatives are the partial derivatives of
the energy. This file proves:

* line derivatives of a function that agrees with a coordinate function near a point.
* the identity between the pair Hamiltonian and `β` times the lifted energy.
* the first and second partial derivatives of the Hamiltonian on the chamber.
* the Laplacian and the gradient inner product as sums of partial derivatives.
* the product identity for the gradient pairing and the Laplacian of a product with a cutoff.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-! ### Line derivatives -/

/-- Moving `x` along the `k`-th coordinate, with the parameter `x k` returning `x`. -/
lemma ofLp_line_eq {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) (k : Fin N) (t : ℝ) :
    WithLp.ofLp (x + (t - x k) • EuclideanSpace.single k (1 : ℝ)) =
      Function.update (WithLp.ofLp x) k t := by
  funext i
  by_cases hik : i = k
  · subst hik
    simp
  · simp [hik]

/-- A partial derivative of the Euclidean function `F` equals the partial derivative of `G` on
the coordinates, when `F` agrees with `G` on a neighborhood of `x`. -/
theorem hsPartial_eq_partialDeriv {N : ℕ+} {F : HsEuclidean N → ℝ}
    {G : (Fin (N : ℕ) → ℝ) → ℝ} {x : HsEuclidean N} {U : Set (HsEuclidean N)}
    (hU : U ∈ 𝓝 x) (hFG : ∀ y ∈ U, F y = G (WithLp.ofLp y))
    (hF : DifferentiableAt ℝ F x) (k : Fin (N : ℕ)) :
    hsPartial F k x = partialDeriv G k (WithLp.ofLp x) := by
  have hL : HasDerivAt (fun t : ℝ => x + (t - x k) • EuclideanSpace.single k (1 : ℝ))
      (EuclideanSpace.single k (1 : ℝ)) (x k) := by
    have h1 : HasDerivAt (fun t : ℝ => t - x k) 1 (x k) := by
      simpa using (hasDerivAt_id (x k)).sub_const (x k)
    simpa using (h1.smul_const (EuclideanSpace.single k (1 : ℝ))).const_add x
  have hcomp : HasDerivAt (fun t : ℝ => F (x + (t - x k) • EuclideanSpace.single k (1 : ℝ)))
      (fderiv ℝ F x (EuclideanSpace.single k (1 : ℝ))) (x k) :=
    HasFDerivAt.comp_hasDerivAt_of_eq (x k) hF.hasFDerivAt hL (by simp)
  have hev : (fun t : ℝ => F (x + (t - x k) • EuclideanSpace.single k (1 : ℝ)))
      =ᶠ[𝓝 (x k)] fun t : ℝ => G (Function.update (WithLp.ofLp x) k t) := by
    have hmem : (fun t : ℝ => x + (t - x k) • EuclideanSpace.single k (1 : ℝ)) ⁻¹' U ∈
        𝓝 (x k) := by
      apply hL.continuousAt.preimage_mem_nhds
      simpa using hU
    filter_upwards [hmem] with t ht
    rw [hFG _ ht, ofLp_line_eq]
  have key : deriv (fun t : ℝ => G (Function.update (WithLp.ofLp x) k t)) (x k) =
      fderiv ℝ F x (EuclideanSpace.single k (1 : ℝ)) := by
    rw [← hev.deriv_eq]
    exact hcomp.deriv
  unfold hsPartial partialDeriv
  exact key.symm

/-! ### The Hamiltonian is `β` times the lifted energy -/

/-- Twice the sum over unordered pairs, for a symmetric pair function, is the sum over all
ordered pairs of distinct indices. -/
theorem sum_erase_eq_two_mul_sum_filter {N : ℕ} (F : Fin N → Fin N → ℝ)
    (hF : ∀ i j, F i j = F j i) :
    ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, F i j =
      2 * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (i < ·), F i j := by
  have hpt : ∀ i j : Fin N, (if j = i then (0 : ℝ) else F i j) =
      (if i < j then F i j else 0) + (if j < i then F i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · have h1 : j ≠ i := h.ne'
      have h2 : ¬ j < i := not_lt.mpr h.le
      simp [h1, h, h2]
    · subst h
      simp
    · have h1 : j ≠ i := h.ne
      have h2 : ¬ i < j := not_lt.mpr h.le
      simp [h1, h, h2]
  have hrow : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, F i j =
      ∑ j : Fin N, (if i < j then F i j else 0) + ∑ j : Fin N, (if j < i then F i j else 0) := by
    intro i
    rw [sum_erase_eq_ite i (fun j => F i j), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hpt i j
  have hswap : ∑ i : Fin N, ∑ j : Fin N, (if j < i then F i j else 0) =
      ∑ i : Fin N, ∑ j : Fin N, (if i < j then F i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hF b a]
  simp only [Finset.sum_filter]
  simp only [hrow, Finset.sum_add_distrib]
  rw [hswap]
  ring

/-- The pair Hamiltonian of the Riesz pair data equals `β` times the lifted energy, at every
point of the Euclidean lift. -/
theorem hsPairExpression_hsRieszPairPotentials_eq_energyLift (N : ℕ+) (β : ℝ) (hβ : 0 < β)
    (s : RieszExponent) (x : HsEuclidean N) :
    hsPairExpression (hsRieszPairPotentials N β hβ s) x = β * energyLift s N (WithLp.ofLp x) := by
  rw [hsPairExpression_hsRieszPairPotentials]
  unfold energyLift
  have hsymm : ∀ i j : Fin (N : ℕ),
      hurwitzKernel s.val (x i - x j) = hurwitzKernel s.val (x j - x i) := by
    intro i j
    have h := hurwitzKernel_neg s.val (x j - x i)
    rw [neg_sub] at h
    exact h
  have hsum : ∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.erase i, hurwitzKernel s.val (x i - x j) =
      2 * ∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.filter (i < ·),
        hurwitzKernel s.val (x i - x j) :=
    sum_erase_eq_two_mul_sum_filter (fun i j => hurwitzKernel s.val (x i - x j)) hsymm
  have hfilt : ∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.filter (i < ·),
      rieszRepresentative s ((x j - x i : ℝ) : UnitAddCircle) =
      ∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.filter (i < ·),
        hurwitzKernel s.val (x i - x j) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact (hsymm i j).symm
  rw [hfilt, hsum]
  ring

/-! ### Chamber derivatives of the Hamiltonian -/

/-- Scalar multiples pass through the partial derivative of a function on the coordinates. -/
lemma hs_partialDeriv_const_mul {N : ℕ} (c : ℝ) (F : (Fin N → ℝ) → ℝ) (k : Fin N)
    (a : Fin N → ℝ) :
    partialDeriv (fun y => c * F y) k a = c * partialDeriv F k a := by
  unfold partialDeriv
  exact deriv_const_mul_field c

/-- The first partial derivatives of the Hamiltonian on the open chamber are `β` times those of
the lifted energy. -/
theorem hsPartial_hsPairExpression_of_mem_chamber (N : ℕ+) (β : ℝ) (hβ : 0 < β)
    (s : RieszExponent) {x : HsEuclidean N} (hx : x ∈ hsChamber N) (k : Fin (N : ℕ)) :
    hsPartial (hsPairExpression (hsRieszPairPotentials N β hβ s)) k x =
      β * partialDeriv (energyLift s N) k (WithLp.ofLp x) := by
  have hU : hsChamber N ∈ 𝓝 x := (isOpen_hsChamber N).mem_nhds hx
  have hF : DifferentiableAt ℝ (hsPairExpression (hsRieszPairPotentials N β hβ s)) x :=
    ((hsPairExpression_contDiffOn (hsRieszPairPotentials N β hβ s)).contDiffAt hU).differentiableAt
      (by simp)
  have h1 := hsPartial_eq_partialDeriv (G := fun y => β * energyLift s N y) hU
    (fun y hy => hsPairExpression_hsRieszPairPotentials_eq_energyLift N β hβ s y) hF k
  rw [h1, hs_partialDeriv_const_mul]

/-- The second partial derivatives of the Hamiltonian on the open chamber are `β` times those of
the lifted energy. -/
theorem hsPartial_hsPartial_hsPairExpression_of_mem_chamber (N : ℕ+) (β : ℝ) (hβ : 0 < β)
    (s : RieszExponent) {x : HsEuclidean N} (hx : x ∈ hsChamber N) (k l : Fin (N : ℕ)) :
    hsPartial (hsPartial (hsPairExpression (hsRieszPairPotentials N β hβ s)) k) l x =
      β * partialDeriv (partialDeriv (energyLift s N) k) l (WithLp.ofLp x) := by
  have hU : hsChamber N ∈ 𝓝 x := (isOpen_hsChamber N).mem_nhds hx
  have hHc := hsPairExpression_contDiffOn (hsRieszPairPotentials N β hβ s)
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ (hsPairExpression (hsRieszPairPotentials N β hβ s)))
      (hsChamber N) := hHc.fderiv_of_isOpen (isOpen_hsChamber N) (by simp)
  have hpd : ContDiffOn ℝ ∞ (hsPartial (hsPairExpression (hsRieszPairPotentials N β hβ s)) k)
      (hsChamber N) :=
    hfd.clm_apply contDiffOn_const
  have hFdiff : DifferentiableAt ℝ (hsPartial (hsPairExpression (hsRieszPairPotentials N β hβ s)) k)
      x := (hpd.contDiffAt hU).differentiableAt (by simp)
  have hEq : ∀ y ∈ hsChamber N,
      hsPartial (hsPairExpression (hsRieszPairPotentials N β hβ s)) k y =
        (fun z => β * partialDeriv (energyLift s N) k z) (WithLp.ofLp y) :=
    fun y hy => hsPartial_hsPairExpression_of_mem_chamber N β hβ s hy k
  have h1 := hsPartial_eq_partialDeriv (G := fun z => β * partialDeriv (energyLift s N) k z) hU
    hEq hFdiff l
  rw [h1, hs_partialDeriv_const_mul]

/-! ### The Laplacian and the gradient pairing as sums of partial derivatives -/

/-- The partial derivative along the `k`-th coordinate of a smooth function is smooth. -/
theorem contDiff_hsPartial {N : ℕ+} {F : HsEuclidean N → ℝ} (hF : ContDiff ℝ ∞ F)
    (k : Fin (N : ℕ)) : ContDiff ℝ ∞ (hsPartial F k) := by
  unfold hsPartial
  exact (contDiff_infty_iff_fderiv.mp hF).2.clm_apply contDiff_const

/-- For a smooth function, the Laplacian is the sum of the second partial derivatives along the
coordinates. -/
theorem laplacian_eq_sum_hsPartial_hsPartial {N : ℕ+} {F : HsEuclidean N → ℝ}
    (hF : ContDiff ℝ ∞ F) (x : HsEuclidean N) :
    Laplacian.laplacian F x = ∑ k : Fin (N : ℕ), hsPartial (hsPartial F k) k x := by
  have hdd : Differentiable ℝ (fderiv ℝ F) :=
    (contDiff_infty_iff_fderiv.mp hF).2.differentiable (by simp)
  have hdiag : ∀ v : HsEuclidean N,
      fderiv ℝ (fun z => fderiv ℝ F z v) x v = iteratedFDeriv ℝ 2 F x ![v, v] := by
    intro v
    rw [fderiv_clm_apply (hdd x) (differentiableAt_const v), iteratedFDeriv_two_apply]
    simp
  have hlap : Laplacian.laplacian F x = ∑ i : Fin (N : ℕ),
      iteratedFDeriv ℝ 2 F x ![EuclideanSpace.basisFun (Fin (N : ℕ)) ℝ i,
        EuclideanSpace.basisFun (Fin (N : ℕ)) ℝ i] :=
    congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis F
      (EuclideanSpace.basisFun (Fin (N : ℕ)) ℝ)) x
  rw [hlap]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [EuclideanSpace.basisFun_apply, ← hdiag]
  rfl

/-- The gradient pairing of two functions is the sum of the products of their partial
derivatives. -/
theorem inner_gradient_eq_sum_hsPartial {N : ℕ+} (F G : HsEuclidean N → ℝ) (x : HsEuclidean N) :
    inner ℝ (gradient F x) (gradient G x) =
      ∑ k : Fin (N : ℕ), hsPartial F k x * hsPartial G k x := by
  rw [← (EuclideanSpace.basisFun (Fin (N : ℕ)) ℝ).sum_inner_mul_inner (gradient F x)
    (gradient G x)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_comm (gradient G x) (EuclideanSpace.basisFun (Fin (N : ℕ)) ℝ k),
    inner_gradient_left, inner_gradient_left]
  simp only [EuclideanSpace.basisFun_apply, hsPartial]

/-! ### The product rule on the cutoff test -/

/-- The partial derivative of a product of two functions differentiable at `x`. -/
theorem hsPartial_mul {N : ℕ+} {F G : HsEuclidean N → ℝ} {x : HsEuclidean N}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (k : Fin (N : ℕ)) :
    hsPartial (fun y => F y * G y) k x = hsPartial F k x * G x + F x * hsPartial G k x := by
  unfold hsPartial
  have hd : fderiv ℝ (fun y => F y * G y) x = F x • fderiv ℝ G x + G x • fderiv ℝ F x :=
    fderiv_mul hF hG
  rw [hd]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The partial derivative of a sum of two functions differentiable at `x`. -/
theorem hsPartial_add {N : ℕ+} {F G : HsEuclidean N → ℝ} {x : HsEuclidean N}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (k : Fin (N : ℕ)) :
    hsPartial (fun y => F y + G y) k x = hsPartial F k x + hsPartial G k x := by
  unfold hsPartial
  have hd : fderiv ℝ (fun y => F y + G y) x = fderiv ℝ F x + fderiv ℝ G x :=
    fderiv_add hF hG
  rw [hd, add_apply]

/-- The product identity for the gradient pairing and the Laplacian of a product `χ Φ` of smooth
functions, with `H` arbitrary. -/
theorem hsGradientProductIdentity {N : ℕ+} (χ Φ H : HsEuclidean N → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hΦ : ContDiff ℝ ∞ Φ) (x : HsEuclidean N) :
    inner ℝ (gradient H x) (gradient (fun y => χ y * Φ y) x) -
      Laplacian.laplacian (fun y => χ y * Φ y) x =
      χ x * (∑ k : Fin (N : ℕ), hsPartial H k x * hsPartial Φ k x -
          ∑ k : Fin (N : ℕ), hsPartial (hsPartial Φ k) k x) +
        Φ x * (∑ k : Fin (N : ℕ), hsPartial H k x * hsPartial χ k x -
          ∑ k : Fin (N : ℕ), hsPartial (hsPartial χ k) k x) -
        2 * ∑ k : Fin (N : ℕ), hsPartial χ k x * hsPartial Φ k x := by
  have hf : ContDiff ℝ ∞ (fun y => χ y * Φ y) := hχ.mul hΦ
  rw [inner_gradient_eq_sum_hsPartial, laplacian_eq_sum_hsPartial_hsPartial hf x]
  have hχd : ∀ y, DifferentiableAt ℝ χ y := fun y => hχ.differentiable (by simp) y
  have hΦd : ∀ y, DifferentiableAt ℝ Φ y := fun y => hΦ.differentiable (by simp) y
  have hχk : ∀ k : Fin (N : ℕ), DifferentiableAt ℝ (hsPartial χ k) x := fun k =>
    (contDiff_hsPartial hχ k).differentiable (by simp) x
  have hΦk : ∀ k : Fin (N : ℕ), DifferentiableAt ℝ (hsPartial Φ k) x := fun k =>
    (contDiff_hsPartial hΦ k).differentiable (by simp) x
  have hfk : ∀ k : Fin (N : ℕ), hsPartial (fun y => χ y * Φ y) k x =
      hsPartial χ k x * Φ x + χ x * hsPartial Φ k x := fun k =>
    hsPartial_mul (hχd x) (hΦd x) k
  have hff : ∀ k : Fin (N : ℕ), hsPartial (hsPartial (fun y => χ y * Φ y) k) k x =
      hsPartial (hsPartial χ k) k x * Φ x + 2 * (hsPartial χ k x * hsPartial Φ k x) +
        χ x * hsPartial (hsPartial Φ k) k x := by
    intro k
    have hfun : hsPartial (fun y => χ y * Φ y) k =
        fun y => hsPartial χ k y * Φ y + χ y * hsPartial Φ k y :=
      funext fun y => hsPartial_mul (hχd y) (hΦd y) k
    have hA : DifferentiableAt ℝ (fun y => hsPartial χ k y * Φ y) x :=
      ((contDiff_hsPartial hχ k).mul hΦ).differentiable (by simp) x
    have hB : DifferentiableAt ℝ (fun y => χ y * hsPartial Φ k y) x :=
      (hχ.mul (contDiff_hsPartial hΦ k)).differentiable (by simp) x
    rw [hfun, hsPartial_add hA hB k, hsPartial_mul (hχk k) (hΦd x) k,
      hsPartial_mul (hχd x) (hΦk k) k]
    ring
  simp only [hfk, hff]
  have e1 : ∑ k : Fin (N : ℕ), hsPartial H k x * (hsPartial χ k x * Φ x + χ x * hsPartial Φ k x) =
      Φ x * ∑ k : Fin (N : ℕ), hsPartial H k x * hsPartial χ k x +
        χ x * ∑ k : Fin (N : ℕ), hsPartial H k x * hsPartial Φ k x := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ k : Fin (N : ℕ), (hsPartial (hsPartial χ k) k x * Φ x +
        2 * (hsPartial χ k x * hsPartial Φ k x) + χ x * hsPartial (hsPartial Φ k) k x) =
      Φ x * ∑ k : Fin (N : ℕ), hsPartial (hsPartial χ k) k x +
        2 * ∑ k : Fin (N : ℕ), hsPartial χ k x * hsPartial Φ k x +
        χ x * ∑ k : Fin (N : ℕ), hsPartial (hsPartial Φ k) k x := by
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  linear_combination e1 - e2

/-- The product identity for the gradient pairing and the Laplacian of the gap cutoff times a
smooth function `Φ`, for any function `H`. -/
theorem hsGradientCutoffIdentity {N : ℕ+} (h : ℝ) (Φ H : HsEuclidean N → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (x : HsEuclidean N) :
    inner ℝ (gradient H x) (gradient (fun y => hsUnitGapCutoff N h y * Φ y) x) -
      Laplacian.laplacian (fun y => hsUnitGapCutoff N h y * Φ y) x =
      hsUnitGapCutoff N h x * (∑ k : Fin (N : ℕ), hsPartial H k x * hsPartial Φ k x -
          ∑ k : Fin (N : ℕ), hsPartial (hsPartial Φ k) k x) +
        Φ x * (∑ k : Fin (N : ℕ), hsPartial H k x * hsPartial (hsUnitGapCutoff N h) k x -
          ∑ k : Fin (N : ℕ), hsPartial (hsPartial (hsUnitGapCutoff N h) k) k x) -
        2 * ∑ k : Fin (N : ℕ), hsPartial (hsUnitGapCutoff N h) k x * hsPartial Φ k x :=
  hsGradientProductIdentity (hsUnitGapCutoff N h) Φ H (contDiff_hsUnitGapCutoff N h) hΦ x

end Riesz1

end
