/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.ConvexificationHessianForm

/-!
# The Hessian lower bound for the convexified potential

Lemma 5.2, third claim. Let `N = n + 1 ≥ 2`, let `y` lie in the anchored
domain, and let `U` be an anchored vector, with `u_1 = u_{N+1} = 0`. Then

`U · ∇²(β(H_N^* + F^*)) U ≥ c K^{-(s+2)ε} ∑_{i,i+1 ∈ I_γ} N² (u_{i+1} - u_i)²`,

with `c = β s (s+1) 2^{-(s+1)}`. The constant depends only on `s` and `β`.

Proof outline. The Hessian is a sum of Riesz pair terms over the pairs `i < j` and of forcing terms
over the window edges. Each window edge `e` is assigned a pair `edgePair e`. For `N ≥ 3` these
assignments are injective, so each edge uses its own Riesz term and its own forcing term. The
edge is in one of two cases.

* If `N G < 2 K^ε` for the gap `G` of the edge, the Riesz curvature `β N^{-s} s (s+1) G^{-s-2}`
  dominates `c K^{-(s+2)ε} N²`.
* Otherwise the forcing argument is at least `2`, so `θ'' = 2` and the forcing term is
  `2β N² K^{-2ε} ≥ c K^{-(s+2)ε} N²`.

For `N = 2` both edges share the single pair `(0, 1)`. A direct bound on that pair suffices.
-/

@[expose] public section

open Set Finset Filter Topology
open scoped ContDiff

namespace Riesz1

/-! ### The constant -/

/-- The constant `c = β s (s+1) 2^{-(s+1)}` of the Hessian lower bound. -/
noncomputable def hessConst (β s : ℝ) : ℝ := β * (s * (s + 1)) * (2 : ℝ) ^ (-(s + 1))

lemma hessConst_pos {β s : ℝ} (hβ : 0 < β) (hs : 0 < s) : 0 < hessConst β s := by
  unfold hessConst
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(s + 1)) := Real.rpow_pos_of_pos (by norm_num) _
  exact mul_pos (mul_pos hβ (mul_pos hs (by linarith))) h2

lemma hessConst_le {β s : ℝ} (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1) :
    hessConst β s ≤ 2 * β := by
  unfold hessConst
  have h1 : (2 : ℝ) ^ (-(s + 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h2 : s * (s + 1) ≤ 2 := by nlinarith
  have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(s + 1)) := Real.rpow_nonneg (by norm_num) _
  have hb : (0 : ℝ) ≤ β * 2 := by linarith
  calc β * (s * (s + 1)) * (2 : ℝ) ^ (-(s + 1)) ≤ β * 2 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h2 hβ.le) h1 h3 hb
    _ = 2 * β := by ring

/-- The scaling identity behind the Riesz case: for `N G < 2 X`, the Riesz curvature term at the gap
`G` dominates `c X^{-(s+2)} N²`. -/
lemma riesz_pair_scale {β s N X G : ℝ} (hβ : 0 < β) (hs : 0 < s) (hN : 0 < N) (hX : 0 < X)
    (hG : 0 < G) (hNG : N * G < 2 * X) :
    hessConst β s * X ^ (-(s + 2)) * N ^ 2 ≤ 2 * (β * N ^ (-s)) * (s * (s + 1)) * G ^ (-(s + 2)) := by
  have hGle : G ≤ 2 * X / N := by
    rw [le_div_iff₀ hN]
    linarith
  have hpow : (2 * X / N) ^ (-(s + 2)) ≤ G ^ (-(s + 2)) :=
    Real.rpow_le_rpow_of_nonpos hG hGle (by linarith)
  have h2 : (2 : ℝ) ^ (-(s + 1)) = 2 * (2 : ℝ) ^ (-(s + 2)) := by
    rw [show -(s + 1) = 1 + -(s + 2) by ring, Real.rpow_add (by norm_num), Real.rpow_one]
  have hN2 : N ^ (-s) * N ^ (s + 2) = N ^ 2 := by
    rw [← Real.rpow_add hN, show -s + (s + 2) = (2 : ℝ) by ring, Real.rpow_two]
  have hid : hessConst β s * X ^ (-(s + 2)) * N ^ 2 =
      2 * (β * N ^ (-s)) * (s * (s + 1)) * (2 * X / N) ^ (-(s + 2)) := by
    unfold hessConst
    rw [Real.div_rpow (by linarith) hN.le, Real.mul_rpow (by norm_num) hX.le,
      Real.rpow_neg hN.le (s + 2), div_inv_eq_mul, h2]
    linear_combination (-(2 * β * (s * (s + 1)) * (2 : ℝ) ^ (-(s + 2)) * X ^ (-(s + 2)))) * hN2
  rw [hid]
  have hnn : 0 ≤ 2 * (β * N ^ (-s)) * (s * (s + 1)) :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hβ.le (Real.rpow_nonneg hN.le _)))
      (mul_nonneg hs.le (by nlinarith))
  exact mul_le_mul_of_nonneg_left hpow hnn

/-! ### Pairs assigned to the window edges -/

/-- The label `i + 1` in the cyclic order: after the last label comes zero. -/
lemma nextLabel_val_of_ne (n : ℕ) (e : Fin (n.succPNat : ℕ)) (h : (e : ℕ) ≠ n) :
    ((nextLabel n.succPNat e : Fin (n.succPNat : ℕ)) : ℕ) = (e : ℕ) + 1 := by
  have he := e.isLt
  simp only [nextLabel, Nat.succPNat_coe] at he ⊢
  rw [Nat.mod_eq_of_lt (by omega)]

lemma nextLabel_eq_zero_of_eq (n : ℕ) (e : Fin (n.succPNat : ℕ)) (h : (e : ℕ) = n) :
    nextLabel n.succPNat e = 0 := by
  apply Fin.ext
  simp only [nextLabel, Nat.succPNat_coe, h, Nat.mod_self]
  rfl

/-- The pair carrying the curvature of the window edge `e`: the pair `(e, e + 1)` for an interior
label, and the wrap-around pair `(0, e)` for the last label `e = n`. -/
noncomputable def edgePair (n : ℕ) (e : Fin (n.succPNat : ℕ)) :
    Fin (n.succPNat : ℕ) × Fin (n.succPNat : ℕ) :=
  if (e : ℕ) = n then (0, e) else (e, nextLabel n.succPNat e)

lemma edgePair_mem {n : ℕ} (hn : 1 ≤ n) (e : Fin (n.succPNat : ℕ)) :
    edgePair n e ∈ pairSet n := by
  unfold edgePair pairSet
  rw [mem_filter]
  refine ⟨mem_univ _, ?_⟩
  split_ifs with h
  · show (0 : Fin (n.succPNat : ℕ)) < e
    rw [Fin.lt_def]
    simp only [Fin.val_zero]
    omega
  · show e < nextLabel n.succPNat e
    rw [Fin.lt_def, nextLabel_val_of_ne n e h]
    omega

/-- Along the edge pair, the squared separation of `U` equals the squared edge increment. -/
lemma edgePair_pairForm_sq {n : ℕ} (e : Fin (n.succPNat : ℕ)) (U : Fin n → ℝ) :
    (pairForm n (edgePair n e) U) ^ 2 = (edgeForm n e U) ^ 2 := by
  unfold edgePair
  split_ifs with h
  · rw [pairForm_apply, edgeForm_apply, nextLabel_eq_zero_of_eq n e h]
    simp only [anchorVector_zero]
    ring
  · rw [pairForm_apply, edgeForm_apply]

/-- The wrap-around gap is one minus the separation of its pair, and an interior gap is the
separation of its pair. -/
lemma edgeGap_eq {n : ℕ} (e : Fin (n.succPNat : ℕ)) (y : Fin n → ℝ) :
    edgeForm n e y + wrapOffset n e =
      if (e : ℕ) = n then 1 - pairForm n (edgePair n e) y else pairForm n (edgePair n e) y := by
  unfold edgePair
  split_ifs with h
  · simp only [pairForm_apply, edgeForm_apply, nextLabel_eq_zero_of_eq n e h, wrapOffset, h,
      ite_true, anchorVector_zero]
    ring
  · simp only [pairForm_apply, edgeForm_apply, wrapOffset, h, ite_false]
    ring

/-! ### The curvature of the assigned pair -/

/-- The separation of the pair assigned to a window edge lies in `(0, 1)`. -/
lemma edgePair_sep_mem {n : ℕ} (hn : 1 ≤ n) {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n)
    (e : Fin (n.succPNat : ℕ)) : pairForm n (edgePair n e) y ∈ Ioo (0 : ℝ) 1 := by
  have hlt : (edgePair n e).1 < (edgePair n e).2 := (mem_filter.mp (edgePair_mem hn e)).2
  rw [pairForm_apply]
  exact anchorVector_sub_mem_Ioo hy hlt

/-- The gap of the window edge `e` lies in `(0, 1)`. -/
lemma edgeGap_mem {n : ℕ} (hn : 1 ≤ n) {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n)
    (e : Fin (n.succPNat : ℕ)) :
    0 < edgeForm n e y + wrapOffset n e ∧ edgeForm n e y + wrapOffset n e < 1 := by
  have hsep := edgePair_sep_mem hn hy e
  rw [edgeGap_eq]
  split_ifs
  · constructor <;> linarith [hsep.1, hsep.2]
  · exact hsep

/-- The curvature of the Riesz pair data is nonnegative at every pair of the domain. -/
lemma pair_deriv_nonneg {β : ℝ} (hβ : 0 < β) (s : RieszExponent) {n : ℕ}
    {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n) {p : Fin (n.succPNat : ℕ) × Fin (n.succPNat : ℕ)}
    (hp : p ∈ pairSet n) :
    0 ≤ deriv (deriv ((hsRieszPairPotentials n.succPNat β hβ s).potential p.1 p.2))
      (pairForm n p y) := by
  have hlt : p.1 < p.2 := (mem_filter.mp hp).2
  have hsep : pairForm n p y ∈ Ioo (0 : ℝ) 1 := by
    rw [pairForm_apply]
    exact anchorVector_sub_mem_Ioo hy hlt
  rw [deriv_deriv_riesz_pair]
  exact mul_nonneg (mul_nonneg hβ.le (Real.rpow_nonneg (by positivity) _))
    (hurwitzKernel_curvature_nonneg s.val s.2.1 s.2.2 hsep)

/-- The number of particles, as a real number, is `n + 1`. -/
lemma succPNat_cast_eq (n : ℕ) : ((n.succPNat : ℕ) : ℝ) = (n : ℝ) + 1 := by
  simp

/-- The curvature of the pair assigned to the window edge `e` dominates the Riesz curvature term
`β N^{-s} s(s+1) G^{-s-2}` at the gap `G` of the edge, where `N = n + 1`. -/
lemma pair_curvature_ge {β : ℝ} (hβ : 0 < β) (s : RieszExponent) {n : ℕ} (hn : 1 ≤ n)
    {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n) (e : Fin (n.succPNat : ℕ)) :
    β * ((n : ℝ) + 1) ^ (-s.val) *
        (s.val * (s.val + 1) * (edgeForm n e y + wrapOffset n e) ^ (-(s.val + 2))) ≤
      deriv (deriv ((hsRieszPairPotentials n.succPNat β hβ s).potential
        (edgePair n e).1 (edgePair n e).2)) (pairForm n (edgePair n e) y) := by
  have hsep := edgePair_sep_mem hn hy e
  have hG0 := (edgeGap_mem hn hy e).1
  rw [deriv_deriv_riesz_pair, succPNat_cast_eq]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hβ.le (Real.rpow_nonneg (by positivity) _))
  by_cases hw : (e : ℕ) = n
  · -- The wrap-around edge: the pair separation is `1 - G`, and the term with `k = 1` gives `G`.
    have hG_eq : edgeForm n e y + wrapOffset n e = 1 - pairForm n (edgePair n e) y := by
      simp [edgeGap_eq, hw]
    have habs : |pairForm n (edgePair n e) y - ((1 : ℤ) : ℝ)| = edgeForm n e y + wrapOffset n e := by
      rw [Int.cast_one, abs_of_neg (by linarith [hsep.2]), hG_eq]
      ring
    have h := hurwitzKernel_curvature_ge_term s.val s.2.1 s.2.2 hsep 1
    rw [habs, show -s.val - 2 = -(s.val + 2) by ring] at h
    exact h
  · -- An interior edge: the pair separation is the gap `G`, and the term with `k = 0` gives `G`.
    have hG_eq : edgeForm n e y + wrapOffset n e = pairForm n (edgePair n e) y := by
      simp [edgeGap_eq, hw]
    have habs : |pairForm n (edgePair n e) y - ((0 : ℤ) : ℝ)| = edgeForm n e y + wrapOffset n e := by
      rw [Int.cast_zero, sub_zero, abs_of_pos hsep.1, hG_eq]
    have h := hurwitzKernel_curvature_ge_term s.val s.2.1 s.2.2 hsep 0
    rw [habs, show -s.val - 2 = -(s.val + 2) by ring] at h
    exact h

/-! ### The per-edge bound -/

/-- The forcing term of the window edge `e` is nonnegative: its argument `N G / K^ε` is nonnegative,
and `θ'' ≥ 0` there. -/
lemma forcing_term_nonneg {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (β : ℝ) (hβ : 0 < β) {n : ℕ}
    (hn : 1 ≤ n) (K ε : ℝ) {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n) (U : Fin n → ℝ)
    (e : Fin (n.succPNat : ℕ)) (hK : 0 < K ^ ε) :
    0 ≤ β * deriv (deriv θ) (((n : ℝ) + 1) * wrapOffset n e / K ^ ε +
      ((n : ℝ) + 1) / K ^ ε * edgeForm n e y) * (((n : ℝ) + 1) / K ^ ε * edgeForm n e U) ^ 2 := by
  have hG0 := (edgeGap_mem hn hy e).1
  have harg : 0 ≤ ((n : ℝ) + 1) * wrapOffset n e / K ^ ε +
      ((n : ℝ) + 1) / K ^ ε * edgeForm n e y := by
    have hrw : ((n : ℝ) + 1) * wrapOffset n e / K ^ ε +
        ((n : ℝ) + 1) / K ^ ε * edgeForm n e y =
          ((n : ℝ) + 1) * (edgeForm n e y + wrapOffset n e) / K ^ ε := by ring
    rw [hrw]
    exact div_nonneg (mul_nonneg (by positivity) hG0.le) hK.le
  exact mul_nonneg (mul_nonneg hβ.le (hθ.2.2.2.1 _ harg).1) (sq_nonneg _)

/-- The per-edge bound. The Riesz term of the pair assigned to the edge `e`, or else the forcing term
of `e`, dominates `c (K^ε)^{-(s+2)} N² (edgeForm U)²`, where `N = n + 1`. -/
lemma edge_lower_bound (β : ℝ) (hβ : 0 < β) (s : RieszExponent) (θ : ℝ → ℝ)
    (hθ : IsForcingCutoff θ) {n : ℕ} (hn : 1 ≤ n) (K ε : ℝ) (hK : 1 ≤ K) (hε : 0 ≤ ε)
    {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n) (U : Fin n → ℝ) (e : Fin (n.succPNat : ℕ)) :
    hessConst β s.val * (K ^ ε) ^ (-(s.val + 2)) * (((n : ℝ) + 1) ^ 2 * (edgeForm n e U) ^ 2) ≤
      2 * deriv (deriv ((hsRieszPairPotentials n.succPNat β hβ s).potential
          (edgePair n e).1 (edgePair n e).2)) (pairForm n (edgePair n e) y) *
          (pairForm n (edgePair n e) U) ^ 2 +
        β * deriv (deriv θ) (((n : ℝ) + 1) * wrapOffset n e / K ^ ε +
          ((n : ℝ) + 1) / K ^ ε * edgeForm n e y) * (((n : ℝ) + 1) / K ^ ε * edgeForm n e U) ^ 2 := by
  have hX1 : 1 ≤ K ^ ε := Real.one_le_rpow hK hε
  have hX0 : 0 < K ^ ε := by linarith
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hG0 := (edgeGap_mem hn hy e).1
  rw [edgePair_pairForm_sq e U]
  have hargs : ((n : ℝ) + 1) * wrapOffset n e / K ^ ε + ((n : ℝ) + 1) / K ^ ε * edgeForm n e y =
      ((n : ℝ) + 1) * (edgeForm n e y + wrapOffset n e) / K ^ ε := by ring
  rw [hargs]
  have hD := pair_curvature_ge hβ s hn hy e
  have hD0 := pair_deriv_nonneg hβ s hy (edgePair_mem hn e)
  have hF0 := forcing_term_nonneg hθ β hβ hn K ε hy U e hX0
  rw [hargs] at hF0
  by_cases hNG : ((n : ℝ) + 1) * (edgeForm n e y + wrapOffset n e) < 2 * K ^ ε
  · -- Riesz case: the pair curvature dominates. The forcing term is dropped.
    have hk := riesz_pair_scale hβ s.2.1 hN hX0 hG0 hNG
    have hk2 : hessConst β s.val * (K ^ ε) ^ (-(s.val + 2)) *
        (((n : ℝ) + 1) ^ 2 * (edgeForm n e U) ^ 2) ≤
        2 * (β * ((n : ℝ) + 1) ^ (-s.val)) * (s.val * (s.val + 1)) *
          (edgeForm n e y + wrapOffset n e) ^ (-(s.val + 2)) * (edgeForm n e U) ^ 2 := by
      calc hessConst β s.val * (K ^ ε) ^ (-(s.val + 2)) * (((n : ℝ) + 1) ^ 2 * (edgeForm n e U) ^ 2)
          = (hessConst β s.val * (K ^ ε) ^ (-(s.val + 2)) * ((n : ℝ) + 1) ^ 2) *
              (edgeForm n e U) ^ 2 := by ring
        _ ≤ (2 * (β * ((n : ℝ) + 1) ^ (-s.val)) * (s.val * (s.val + 1)) *
              (edgeForm n e y + wrapOffset n e) ^ (-(s.val + 2))) * (edgeForm n e U) ^ 2 :=
            mul_le_mul_of_nonneg_right hk (sq_nonneg _)
        _ = 2 * (β * ((n : ℝ) + 1) ^ (-s.val)) * (s.val * (s.val + 1)) *
              (edgeForm n e y + wrapOffset n e) ^ (-(s.val + 2)) * (edgeForm n e U) ^ 2 := by ring
    have hD2 : 2 * (β * ((n : ℝ) + 1) ^ (-s.val)) * (s.val * (s.val + 1)) *
          (edgeForm n e y + wrapOffset n e) ^ (-(s.val + 2)) ≤
        2 * deriv (deriv ((hsRieszPairPotentials n.succPNat β hβ s).potential
          (edgePair n e).1 (edgePair n e).2)) (pairForm n (edgePair n e) y) := by
      calc 2 * (β * ((n : ℝ) + 1) ^ (-s.val)) * (s.val * (s.val + 1)) *
            (edgeForm n e y + wrapOffset n e) ^ (-(s.val + 2))
          = 2 * (β * ((n : ℝ) + 1) ^ (-s.val) * (s.val * (s.val + 1) *
              (edgeForm n e y + wrapOffset n e) ^ (-(s.val + 2)))) := by ring
        _ ≤ 2 * deriv (deriv ((hsRieszPairPotentials n.succPNat β hβ s).potential
              (edgePair n e).1 (edgePair n e).2)) (pairForm n (edgePair n e) y) :=
            mul_le_mul_of_nonneg_left hD (by norm_num)
    have hD3 : 2 * (β * ((n : ℝ) + 1) ^ (-s.val)) * (s.val * (s.val + 1)) *
          (edgeForm n e y + wrapOffset n e) ^ (-(s.val + 2)) * (edgeForm n e U) ^ 2 ≤
        2 * deriv (deriv ((hsRieszPairPotentials n.succPNat β hβ s).potential
          (edgePair n e).1 (edgePair n e).2)) (pairForm n (edgePair n e) y) *
          (edgeForm n e U) ^ 2 :=
      mul_le_mul_of_nonneg_right hD2 (sq_nonneg _)
    linarith [hk2, hD3, hF0]
  · -- Forcing case: the argument is at least two, so `θ'' = 2`.
    have ht : 2 ≤ ((n : ℝ) + 1) * (edgeForm n e y + wrapOffset n e) / K ^ ε := by
      rw [le_div_iff₀ hX0]
      linarith [not_lt.mp hNG]
    rw [hθ.2.2.2.2 _ ht]
    have hXm : (K ^ ε) ^ (-(s.val + 2)) ≤ ((K ^ ε) ^ 2)⁻¹ := by
      calc (K ^ ε) ^ (-(s.val + 2)) ≤ (K ^ ε) ^ (-(2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hX1 (by linarith [s.2.1])
        _ = ((K ^ ε) ^ 2)⁻¹ := by rw [Real.rpow_neg hX0.le, Real.rpow_two]
    have hc := hessConst_le hβ s.2.1 s.2.2
    have hpos : 0 ≤ (K ^ ε) ^ (-(s.val + 2)) := Real.rpow_nonneg hX0.le _
    have hD0' : 0 ≤ 2 * deriv (deriv ((hsRieszPairPotentials n.succPNat β hβ s).potential
          (edgePair n e).1 (edgePair n e).2)) (pairForm n (edgePair n e) y) * (edgeForm n e U) ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hD0) (sq_nonneg _)
    have hfin : hessConst β s.val * (K ^ ε) ^ (-(s.val + 2)) * (((n : ℝ) + 1) ^ 2 *
        (edgeForm n e U) ^ 2) ≤ β * 2 * (((n : ℝ) + 1) / K ^ ε * edgeForm n e U) ^ 2 := by
      calc hessConst β s.val * (K ^ ε) ^ (-(s.val + 2)) * (((n : ℝ) + 1) ^ 2 * (edgeForm n e U) ^ 2)
          ≤ (2 * β) * (K ^ ε) ^ (-(s.val + 2)) * (((n : ℝ) + 1) ^ 2 * (edgeForm n e U) ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hpos) (by positivity)
        _ ≤ (2 * β) * ((K ^ ε) ^ 2)⁻¹ * (((n : ℝ) + 1) ^ 2 * (edgeForm n e U) ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXm (by linarith)) (by positivity)
        _ = β * 2 * (((n : ℝ) + 1) / K ^ ε * edgeForm n e U) ^ 2 := by ring
    linarith [hfin, hD0']

/-! ### The assignment of pairs to edges -/

/-- For `N ≥ 3` the assignment `e ↦ edgePair e` of pairs to window edges is injective. -/
lemma edgePair_injective {n : ℕ} (hn : 2 ≤ n) : Function.Injective (edgePair n) := by
  intro e e' h
  unfold edgePair at h
  split_ifs at h with h1 h2 h2
  · exact (Prod.mk.inj h).2
  · exfalso
    obtain ⟨h3, h4⟩ := Prod.mk.inj h
    have h5 := congrArg Fin.val h3
    have h6 := congrArg Fin.val h4
    rw [nextLabel_val_of_ne n e' h2] at h6
    simp only [Fin.val_zero] at h5
    omega
  · exfalso
    obtain ⟨h3, h4⟩ := Prod.mk.inj h
    have h5 := congrArg Fin.val h3
    have h6 := congrArg Fin.val h4
    rw [nextLabel_val_of_ne n e h1] at h6
    simp only [Fin.val_zero] at h5
    omega
  · exact (Prod.mk.inj h).1

/-! ### Bounds for the single pair when `N = 2` -/

/-- Every pair curvature is at least `β N^{-s} s(s+1) 2^{s+2}` on the anchored domain. -/
lemma pair_deriv_ge_const {β : ℝ} (hβ : 0 < β) (s : RieszExponent) {n : ℕ}
    {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n) {p : Fin (n.succPNat : ℕ) × Fin (n.succPNat : ℕ)}
    (hp : p ∈ pairSet n) :
    β * ((n : ℝ) + 1) ^ (-s.val) * (s.val * (s.val + 1) * 2 ^ (s.val + 2)) ≤
      deriv (deriv ((hsRieszPairPotentials n.succPNat β hβ s).potential p.1 p.2))
        (pairForm n p y) := by
  have hlt : p.1 < p.2 := (mem_filter.mp hp).2
  have hsep : pairForm n p y ∈ Ioo (0 : ℝ) 1 := by
    rw [pairForm_apply]
    exact anchorVector_sub_mem_Ioo hy hlt
  rw [deriv_deriv_riesz_pair, succPNat_cast_eq]
  exact mul_le_mul_of_nonneg_left (hurwitzKernel_curvature_ge_const s.val s.2.1 s.2.2 hsep)
    (mul_nonneg hβ.le (Real.rpow_nonneg (by positivity) _))

/-- The constant `c = β s(s+1) 2^{-(s+1)}` is at most `β s(s+1)`. -/
lemma hessConst_le_mul (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) :
    hessConst β s ≤ β * (s * (s + 1)) := by
  unfold hessConst
  have h1 : (2 : ℝ) ^ (-(s + 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hnn : 0 ≤ β * (s * (s + 1)) := mul_nonneg hβ.le (mul_nonneg hs.le (by linarith))
  calc β * (s * (s + 1)) * (2 : ℝ) ^ (-(s + 1)) ≤ β * (s * (s + 1)) * 1 :=
        mul_le_mul_of_nonneg_left h1 hnn
    _ = β * (s * (s + 1)) := mul_one _

/-- For one particle pair (`N = 2`), both edge increments have the same square, `(U 0)²`. -/
lemma edgeForm_sq_two (U : Fin 1 → ℝ) (e : Fin (Nat.succPNat 1 : ℕ)) :
    (edgeForm 1 e U) ^ 2 = (U 0) ^ 2 := by
  obtain ⟨v, hv⟩ := e
  have hN : (Nat.succPNat 1 : ℕ) = 2 := rfl
  rw [hN] at hv
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
  · have hn : nextLabel (Nat.succPNat 1) ⟨0, hv⟩ = Fin.succ 0 := Fin.ext (by simp [nextLabel])
    have h1 : anchorVector U (Fin.succ 0) = U 0 := anchorVector_succ U 0
    have he : anchorVector U ⟨0, hv⟩ = 0 := anchorVector_zero U
    rw [edgeForm_apply, hn, h1, he]
    ring
  · have hn : nextLabel (Nat.succPNat 1) ⟨1, hv⟩ = 0 := Fin.ext (by simp [nextLabel])
    have h1 : anchorVector U ⟨1, hv⟩ = U 0 := anchorVector_succ U 0
    have he : anchorVector U 0 = 0 := anchorVector_zero U
    rw [edgeForm_apply, hn, h1, he]
    ring

/-! ### The main theorem -/

/-- **Lemma 5.2, third claim: Hessian lower bound.** For every forcing
cutoff `θ`, every `n ≥ 1` (that is, `N = n + 1 ≥ 2` particles), every `K ≥ 1` and `ε ≥ 0`, every point
`y` of the anchored domain, and every anchored direction `U`, the Hessian of the anchored potential
`β (H_N^* + F^*)` satisfies
`U · ∇²(β(H_N^* + F^*)) U ≥ c K^{-(s+2)ε} ∑_{i,i+1 ∈ I_γ} N² (u_{i+1} - u_i)²`,
where `u_1 = u_{N+1} = 0` and the constant `c > 0` depends only on `s` and `β`. -/
theorem anchoredPotential_hessian_lower (β : ℝ) (hβ : 0 < β) (s : RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ ∀ (θ : ℝ → ℝ), IsForcingCutoff θ → ∀ (n : ℕ), 1 ≤ n →
      ∀ (K γ ε : ℝ), 1 ≤ K → 0 ≤ ε → ∀ y ∈ anchoredDomain n, ∀ U : Fin n → ℝ,
        c * K ^ (-((s.val + 2) * ε)) *
            ∑ i ∈ nearestPairs n.succPNat (window n.succPNat K γ),
              (((n : ℝ) + 1) ^ 2 * (edgeForm n i U) ^ 2) ≤
          fderiv ℝ (fderiv ℝ (anchoredPotential β hβ s θ n K γ ε)) y U U := by
  refine ⟨hessConst β s.val, hessConst_pos hβ s.2.1, fun θ hθ n hn K γ ε hK hε y hy U => ?_⟩
  rw [anchoredPotential_hessian β hβ s θ hθ n K γ ε hy U]
  have hconv : K ^ (-((s.val + 2) * ε)) = (K ^ ε) ^ (-(s.val + 2)) := by
    rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ K)]
    congr 1
    ring
  rw [hconv, Finset.mul_sum]
  have hFnn : ∀ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
      0 ≤ β * deriv (deriv θ) (((n : ℝ) + 1) * wrapOffset n e / K ^ ε +
        ((n : ℝ) + 1) / K ^ ε * edgeForm n e y) * (((n : ℝ) + 1) / K ^ ε * edgeForm n e U) ^ 2 :=
    fun e _ => forcing_term_nonneg hθ β hβ hn K ε hy U e (Real.rpow_pos_of_pos (by linarith) ε)
  have hPnn : ∀ p ∈ pairSet n, 0 ≤ 2 * deriv (deriv ((hsRieszPairPotentials n.succPNat β hβ s).potential
      p.1 p.2)) (pairForm n p y) * (pairForm n p U) ^ 2 := fun p hp =>
    mul_nonneg (mul_nonneg (by norm_num) (pair_deriv_nonneg hβ s hy hp)) (sq_nonneg _)
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · -- `N = 2`: both window edges share the single pair `(0, 1)`.
    have hn1 : n = 1 := by omega
    subst hn1
    have hpow4 : (2 : ℝ) ^ (-s.val) * (2 : ℝ) ^ (s.val + 2) = 4 := by
      rw [← Real.rpow_add (by norm_num), show -s.val + (s.val + 2) = (2 : ℝ) by ring, Real.rpow_two]
      norm_num
    have hX1 : 1 ≤ K ^ ε := Real.one_le_rpow hK hε
    have hX0 : 0 < K ^ ε := by linarith
    -- The lower bound for the single pair `q = edgePair 1 0`.
    let e0 : Fin (Nat.succPNat 1 : ℕ) := ⟨0, Nat.succ_pos 1⟩
    have hq := hPnn (edgePair 1 e0) (edgePair_mem hn e0)
    have hD := pair_deriv_ge_const hβ s hy (edgePair_mem hn e0)
    have hN2 : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
    rw [hN2] at hD
    have hpair : 8 * (β * (s.val * (s.val + 1))) * (U 0) ^ 2 ≤
        2 * deriv (deriv ((hsRieszPairPotentials (Nat.succPNat 1) β hβ s).potential
          (edgePair 1 e0).1 (edgePair 1 e0).2)) (pairForm 1 (edgePair 1 e0) y) *
          (pairForm 1 (edgePair 1 e0) U) ^ 2 := by
      rw [edgePair_pairForm_sq, edgeForm_sq_two]
      calc 8 * (β * (s.val * (s.val + 1))) * (U 0) ^ 2
          = 2 * (β * (2 : ℝ) ^ (-s.val) * (s.val * (s.val + 1) * (2 : ℝ) ^ (s.val + 2))) *
              (U 0) ^ 2 := by
            linear_combination (-2 * β * (s.val * (s.val + 1)) * (U 0) ^ 2) * hpow4
        _ ≤ 2 * deriv (deriv ((hsRieszPairPotentials (Nat.succPNat 1) β hβ s).potential
              (edgePair 1 e0).1 (edgePair 1 e0).2)) (pairForm 1 (edgePair 1 e0) y) *
              (U 0) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD (by norm_num)) (sq_nonneg _)
    -- The left side is at most `8 c (U 0)²`, since each window edge has `N² (edgeForm U)² = 4 (U 0)²`.
    have hLHS : ∑ i ∈ nearestPairs (Nat.succPNat 1) (window (Nat.succPNat 1) K γ),
        hessConst β s.val * (K ^ ε) ^ (-(s.val + 2)) * ((((1 : ℕ) : ℝ) + 1) ^ 2 *
          (edgeForm 1 i U) ^ 2) ≤
        ((nearestPairs (Nat.succPNat 1) (window (Nat.succPNat 1) K γ)).card : ℝ) *
          (hessConst β s.val * 4 * (U 0) ^ 2) := by
      rw [← nsmul_eq_mul]
      apply Finset.sum_le_card_nsmul
      intro e _
      rw [edgeForm_sq_two, hN2]
      have hpow1 : (K ^ ε) ^ (-(s.val + 2)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hX1 (by linarith [s.2.1])
      have hc0 : 0 ≤ hessConst β s.val := (hessConst_pos hβ s.2.1).le
      have h4 : (0 : ℝ) ≤ (U 0) ^ 2 := sq_nonneg _
      calc hessConst β s.val * (K ^ ε) ^ (-(s.val + 2)) * (2 ^ 2 * (U 0) ^ 2)
          ≤ hessConst β s.val * 1 * (2 ^ 2 * (U 0) ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hpow1 hc0
        _ = hessConst β s.val * 4 * (U 0) ^ 2 := by ring
    have hcard : ((nearestPairs (Nat.succPNat 1) (window (Nat.succPNat 1) K γ)).card : ℝ) ≤ 2 := by
      have hle := Finset.card_le_univ (nearestPairs (Nat.succPNat 1) (window (Nat.succPNat 1) K γ))
      have hcard2 : Fintype.card (Fin (Nat.succPNat 1 : ℕ)) = 2 := rfl
      have hle' : (nearestPairs (Nat.succPNat 1) (window (Nat.succPNat 1) K γ)).card ≤ 2 :=
        hle.trans hcard2.le
      exact_mod_cast hle'
    have hcU : 0 ≤ hessConst β s.val * 4 * (U 0) ^ 2 :=
      mul_nonneg (mul_nonneg (hessConst_pos hβ s.2.1).le (by norm_num)) (sq_nonneg _)
    have hcmul : ((nearestPairs (Nat.succPNat 1) (window (Nat.succPNat 1) K γ)).card : ℝ) *
        (hessConst β s.val * 4 * (U 0) ^ 2) ≤ 2 * (hessConst β s.val * 4 * (U 0) ^ 2) :=
      mul_le_mul_of_nonneg_right hcard hcU
    have hc8 : hessConst β s.val * 4 * (U 0) ^ 2 ≤ 4 * (β * (s.val * (s.val + 1))) * (U 0) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hessConst_le_mul β s.val hβ s.2.1)) (sq_nonneg (U 0))]
    have hF := Finset.sum_nonneg hFnn
    have hA := Finset.single_le_sum (f := fun p : Fin (Nat.succPNat 1 : ℕ) × Fin (Nat.succPNat 1 : ℕ) =>
        2 * deriv (deriv ((hsRieszPairPotentials (Nat.succPNat 1) β hβ s).potential p.1 p.2))
          (pairForm 1 p y) * (pairForm 1 p U) ^ 2) (fun p hp => hPnn p hp) (edgePair_mem hn e0)
    have hchain : ∑ i ∈ nearestPairs (Nat.succPNat 1) (window (Nat.succPNat 1) K γ),
        hessConst β s.val * (K ^ ε) ^ (-(s.val + 2)) * ((((1 : ℕ) : ℝ) + 1) ^ 2 *
          (edgeForm 1 i U) ^ 2) ≤ 8 * (β * (s.val * (s.val + 1))) * (U 0) ^ 2 := by
      linarith [hLHS, hcmul, hc8]
    exact hchain.trans (hpair.trans (hA.trans (le_add_of_nonneg_right hF)))
  · -- `N ≥ 3`: each window edge has its own pair, and its own forcing term.
    have hsum := Finset.sum_le_sum fun e (_ : e ∈ nearestPairs n.succPNat (window n.succPNat K γ)) =>
      edge_lower_bound β hβ s θ hθ hn K ε hK hε hy U e
    rw [Finset.sum_add_distrib] at hsum
    have hinj : Set.InjOn (edgePair n) (nearestPairs n.succPNat (window n.succPNat K γ) : Set _) :=
      (edgePair_injective hn2).injOn
    have himg := Finset.sum_image (f := fun p : Fin (n.succPNat : ℕ) × Fin (n.succPNat : ℕ) =>
      2 * deriv (deriv ((hsRieszPairPotentials n.succPNat β hβ s).potential p.1 p.2))
        (pairForm n p y) * (pairForm n p U) ^ 2) hinj
    have hsubset : (nearestPairs n.succPNat (window n.succPNat K γ)).image (edgePair n) ⊆
        pairSet n := Finset.image_subset_iff.mpr fun e _ => edgePair_mem hn e
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun p hp _ => hPnn p hp)
    have hF := Finset.sum_nonneg hFnn
    linarith

end Riesz1

end
