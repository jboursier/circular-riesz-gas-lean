/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingQuadratureBackground

/-!
# The reference field as a sum of remainder cells

The quadrature part of Lemma 5.7, reduction. The discrete part
of the reference field `V^{(2)}_i` is `2` times a sum over the path increments `k_{ij}` of the cell
integrand `F_x`, and the cell integrand splits into the kernel term `ψ'(x/ℓ) h'`
and the remainder `R_x`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The discrete part of `V^{(2)}_i` is `2` times the sum of the cell integrands `F_x(k_{ij})`
over the labels `j ≠ i`. -/
lemma gradVdisc2_eq_sum (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) (i : ℤ) :
    gradVdisc2 s ψ N ℓ γ X i
      = 2 * ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradCellF s (N : ℕ) ℓ ψ (gradLift N X i) ((gradPathIncr N ℓ γ i j : ℤ) : ℝ) := by
  unfold gradVdisc2
  simp only [gradCellF, iteratedDeriv_one, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The cell integrand splits into the kernel term and the remainder: `F_x(v) = -N^{-s} ψ'(x/ℓ)
h'(v/N) + R_x(v)` at every lattice-free `v`. -/
lemma gradCellF_eq_kernel_add (s : ℝ) (ψ : ℝ → ℝ) {ℓ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ)
    (x v : ℝ) (hv : ((v / (N : ℝ) : ℝ) : UnitAddCircle) ≠ 0) :
    gradCellF s N ℓ ψ x v
      = -((N : ℝ) ^ (-s) * deriv ψ (x / ℓ) * deriv (gradKernelH s) (v / (N : ℝ)))
        + gradCellR s N ℓ ψ x v := by
  have hq := gradQuad_pointwise ψ ℓ hs0 hs1 x hv
  unfold gradCellF gradCellR
  rw [iteratedDeriv_one]
  linear_combination ((N : ℝ) ^ (-s)) * hq

/-- A nonzero path increment `k` with `2|k| ≤ N` gives a nonsingular point `k/N` of the
circle, so the kernel derivative at `k/N` is the one of `gradCellF_eq_kernel_add`. -/
lemma coe_div_ne_zero_of_path (N : ℕ+) {k : ℤ} (hk : k ≠ 0) (hb : 2 * |k| ≤ ((N : ℕ) : ℤ)) :
    (((k : ℝ) / ((N : ℕ) : ℝ) : ℝ) : UnitAddCircle) ≠ 0 := by
  have hN : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hc : |(k : ℝ)| = ((|k| : ℤ) : ℝ) := (Int.cast_abs).symm
  have hbR : 2 * |(k : ℝ)| ≤ ((N : ℕ) : ℝ) := by
    rw [hc]
    exact_mod_cast hb
  apply gradSplit_coe_ne_zero
  · rw [abs_div, abs_of_pos hN]
    exact div_pos (abs_pos.mpr (Int.cast_ne_zero.mpr hk)) hN
  · rw [abs_div, abs_of_pos hN, div_lt_one hN]
    linarith [abs_nonneg (k : ℝ)]

/-- The reference field `V^{(2)}_i = gradVdisc2 + gradVbg` in the decomposition used for the
quadrature bound: a kernel sum with the coefficient `ψ'(x_i/ℓ)`, and a remainder sum minus its
integral over `[N(a), N(b)]`. -/
theorem gradV2_eq_split {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    (X : Fin (N : ℕ) → ℝ) (i : ℤ) (a b : ℝ)
    (ha : gradBLo N ℓ γ (gradLift N X i) - gradLift N X i = a)
    (hb : gradBHi N ℓ γ (gradLift N X i) - gradLift N X i = b)
    (hab : a < b) (ha1 : |a| < 1) (hb1 : |b| < 1)
    (hq0 : a = 0 → deriv ψ (gradLift N X i / ℓ) = 0)
    (hq1 : b = 0 → deriv ψ (gradLift N X i / ℓ) = 0)
    (hR : IntervalIntegrable (gradCellR s (N : ℕ) ℓ ψ (gradLift N X i)) volume
      (((N : ℕ) : ℝ) * a) (((N : ℕ) : ℝ) * b))
    (hK : ∀ j ∈ (gradLabels N ℓ γ).erase i, 2 * |(gradPathIncr N ℓ γ i j : ℤ)| ≤ ((N : ℕ) : ℤ)
      ∧ gradPathIncr N ℓ γ i j ≠ 0) :
    gradVdisc2 s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i
      = 2 * deriv ψ (gradLift N X i / ℓ) * (((N : ℕ) : ℝ) ^ (1 - s) * (gradKernelH s b - gradKernelH s a)
          - ((N : ℕ) : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
              deriv (gradKernelH s) (((gradPathIncr N ℓ γ i j : ℤ) : ℝ) / ((N : ℕ) : ℝ)))
        + 2 * (∑ j ∈ (gradLabels N ℓ γ).erase i,
              gradCellR s (N : ℕ) ℓ ψ (gradLift N X i) ((gradPathIncr N ℓ γ i j : ℤ) : ℝ)
            - ∫ w in (((N : ℕ) : ℝ) * a)..(((N : ℕ) : ℝ) * b),
              gradCellR s (N : ℕ) ℓ ψ (gradLift N X i) w) := by
  have hN0 : ((N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  have hbg := gradPV_background_eq_cellR hψ hℓ0 hp hs0 hs1 hsupp (gradLift N X i) a b ha hb
    hab ha1 hb1 hq0 hq1 hR
  have hsum : ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradCellF s (N : ℕ) ℓ ψ (gradLift N X i) ((gradPathIncr N ℓ γ i j : ℤ) : ℝ)
      = -(((N : ℕ) : ℝ) ^ (-s) * deriv ψ (gradLift N X i / ℓ) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
              deriv (gradKernelH s) (((gradPathIncr N ℓ γ i j : ℤ) : ℝ) / ((N : ℕ) : ℝ)))
        + ∑ j ∈ (gradLabels N ℓ γ).erase i,
              gradCellR s (N : ℕ) ℓ ψ (gradLift N X i) ((gradPathIncr N ℓ γ i j : ℤ) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hne := (hK j hj).2
    have hbound := (hK j hj).1
    have hcell := coe_div_ne_zero_of_path N hne hbound
    rw [gradCellF_eq_kernel_add s ψ hs0 hs1 (N : ℕ) _ _ hcell]
  unfold gradVbg
  rw [gradVdisc2_eq_sum, hsum]
  linear_combination hbg

end

end Riesz1
