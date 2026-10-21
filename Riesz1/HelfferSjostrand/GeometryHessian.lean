/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SettingHamiltonian

/-!
# Hessian of the pair Hamiltonian on the chamber

This file proves the first assertions of Lemma 3.6:
on the open chamber, the Hessian of the pair Hamiltonian is the explicit bilinear form
`2 ∑_{i<j} χ_ij''(x_j - x_i) (u_j - u_i) (v_j - v_i)`. Consequently `∇²H e = 0` for the
common-translation direction `e`, and on vectors orthogonal to `e` the quadratic form is at
least `2 c N |a|²`.

The Hessian is `fderiv ℝ (fderiv ℝ H) x`, the second Fréchet derivative of the ambient
expression `hsPairExpression χ`. It is a derivative in the usual sense because the chamber is open.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Finset
open scoped Topology

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

/-- The separation `y ↦ y_j - y_i` as a continuous linear functional on the lift space. -/
def hsSeparation (i j : Fin (N : ℕ)) : HsEuclidean N →L[ℝ] ℝ :=
  EuclideanSpace.proj j - EuclideanSpace.proj i

theorem hsSeparation_apply (i j : Fin (N : ℕ)) (y : HsEuclidean N) :
    hsSeparation i j y = y j - y i := by
  simp [hsSeparation]

/-- Derivative of one pair term `y ↦ χ_ij(y_j - y_i)` at a chamber point. -/
theorem hasFDerivAt_pairTerm (χ : HsPairPotentials N c) {i j : Fin (N : ℕ)} (hij : i < j)
    {y : HsEuclidean N} (hy : y ∈ hsChamber N) :
    HasFDerivAt (fun z : HsEuclidean N => χ.potential i j (z j - z i))
      (deriv (χ.potential i j) (y j - y i) • hsSeparation i j) y := by
  have hr := hsChamber_separation_mem hy hij
  have hd : HasDerivAt (χ.potential i j) (deriv (χ.potential i j) (y j - y i)) (y j - y i) :=
    (((χ.smooth i j hij).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hr)).hasDerivAt
  have hs := (hsSeparation i j).hasFDerivAt (x := y)
  have h := hd.comp_hasFDerivAt y hs
  simpa only [Function.comp_def, hsSeparation_apply] using h

/-- The first derivative of the pair Hamiltonian, written at an arbitrary point. -/
def hsPairGradient (χ : HsPairPotentials N c) (y : HsEuclidean N) :
    HsEuclidean N →L[ℝ] ℝ :=
  (2 : ℝ) • ∑ i : Fin (N : ℕ), ∑ j ∈ univ.filter (i < ·),
    deriv (χ.potential i j) (y j - y i) • hsSeparation i j

/-- The second derivative of the pair Hamiltonian at a point, as a bilinear map. -/
def hsPairHessian (χ : HsPairPotentials N c) (y : HsEuclidean N) :
    HsEuclidean N →L[ℝ] (HsEuclidean N →L[ℝ] ℝ) :=
  (2 : ℝ) • ∑ i : Fin (N : ℕ), ∑ j ∈ univ.filter (i < ·),
    ((deriv (deriv (χ.potential i j)) (y j - y i)) • hsSeparation i j).smulRight
      (hsSeparation i j)

theorem hasFDerivAt_hsPairExpression (χ : HsPairPotentials N c) {y : HsEuclidean N}
    (hy : y ∈ hsChamber N) :
    HasFDerivAt (hsPairExpression χ) (hsPairGradient χ y) y := by
  unfold hsPairExpression hsPairGradient
  apply HasFDerivAt.const_mul
  apply HasFDerivAt.fun_sum
  intro i _
  apply HasFDerivAt.fun_sum
  intro j hj
  have hij : i < j := (mem_filter.mp hj).2
  exact hasFDerivAt_pairTerm χ hij hy

theorem hasFDerivAt_hsPairGradient (χ : HsPairPotentials N c) {y : HsEuclidean N}
    (hy : y ∈ hsChamber N) :
    HasFDerivAt (hsPairGradient χ) (hsPairHessian χ y) y := by
  unfold hsPairGradient hsPairHessian
  have hsum : HasFDerivAt
      (fun z : HsEuclidean N => ∑ i : Fin (N : ℕ), ∑ j ∈ univ.filter (i < ·),
        deriv (χ.potential i j) (z j - z i) • hsSeparation i j)
      (∑ i : Fin (N : ℕ), ∑ j ∈ univ.filter (i < ·),
        ((deriv (deriv (χ.potential i j)) (y j - y i)) • hsSeparation i j).smulRight
          (hsSeparation i j)) y := by
    apply HasFDerivAt.fun_sum
    intro i _
    apply HasFDerivAt.fun_sum
    intro j hj
    have hij : i < j := (mem_filter.mp hj).2
    have hr := hsChamber_separation_mem hy hij
    have hd : HasDerivAt (deriv (χ.potential i j))
        (deriv (deriv (χ.potential i j)) (y j - y i)) (y j - y i) := by
      have h1 : ContDiffOn ℝ 1 (deriv (χ.potential i j)) (Ioo 0 1) :=
        (χ.smooth i j hij).deriv_of_isOpen isOpen_Ioo (by simp)
      exact ((h1.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hr)).hasDerivAt
    have hs := (hsSeparation i j).hasFDerivAt (x := y)
    have hc : HasFDerivAt (fun z : HsEuclidean N => deriv (χ.potential i j) (z j - z i))
        (deriv (deriv (χ.potential i j)) (y j - y i) • hsSeparation i j) y := by
      have h := hd.comp_hasFDerivAt y hs
      simpa only [Function.comp_def, hsSeparation_apply] using h
    exact hc.smul_const (hsSeparation i j)
  exact hsum.const_smul (2 : ℝ)

/-- On the chamber, the gradient of the pair Hamiltonian is the explicit form. -/
theorem fderiv_hsPairExpression_eventually (χ : HsPairPotentials N c) {x : HsEuclidean N}
    (hx : x ∈ hsChamber N) :
    fderiv ℝ (hsPairExpression χ) =ᶠ[𝓝 x] hsPairGradient χ := by
  filter_upwards [(isOpen_hsChamber N).mem_nhds hx] with y hy
  exact (hasFDerivAt_hsPairExpression χ hy).fderiv

/-- The Hessian of the pair Hamiltonian on the chamber is the second derivative of the
gradient form. -/
theorem fderiv_fderiv_hsPairExpression (χ : HsPairPotentials N c) {x : HsEuclidean N}
    (hx : x ∈ hsChamber N) :
    fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x = hsPairHessian χ x := by
  rw [(fderiv_hsPairExpression_eventually χ hx).fderiv_eq]
  exact (hasFDerivAt_hsPairGradient χ hx).fderiv

/-- The bilinear Hessian form `∇²H(u, v) = 2 ∑_{i<j} χ_ij''(x_j - x_i)(u_j - u_i)(v_j - v_i)`,
which is the first assertion of Lemma 3.6. -/
theorem hessian_hsPairExpression_apply (χ : HsPairPotentials N c) {x : HsEuclidean N}
    (hx : x ∈ hsChamber N) (u v : HsEuclidean N) :
    fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x u v =
      2 * ∑ i : Fin (N : ℕ), ∑ j ∈ univ.filter (i < ·),
        deriv (deriv (χ.potential i j)) (x j - x i) * ((u j - u i) * (v j - v i)) := by
  rw [fderiv_fderiv_hsPairExpression χ hx]
  unfold hsPairHessian
  simp only [smul_apply, _root_.sum_apply,
    ContinuousLinearMap.smulRight_apply, hsSeparation_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The quadratic form `a ↦ a · ∇²H a`. -/
theorem hessian_hsPairExpression_self (χ : HsPairPotentials N c) {x : HsEuclidean N}
    (hx : x ∈ hsChamber N) (a : HsEuclidean N) :
    fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x a a =
      2 * ∑ i : Fin (N : ℕ), ∑ j ∈ univ.filter (i < ·),
        deriv (deriv (χ.potential i j)) (x j - x i) * (a j - a i) ^ 2 := by
  rw [hessian_hsPairExpression_apply χ hx]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The unit vector `e = N^{-1/2} (1, …, 1)` along the common translations. -/
def hsUnitVector (N : ℕ+) : HsEuclidean N := (Real.sqrt (N : ℕ))⁻¹ • hsRotationVector N

/-- The common-translation direction is a kernel of the Hessian: `∇²H e = 0`. -/
theorem hessian_hsPairExpression_unit (χ : HsPairPotentials N c) {x : HsEuclidean N}
    (hx : x ∈ hsChamber N) (v : HsEuclidean N) :
    fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x (hsUnitVector N) v = 0 := by
  rw [hessian_hsPairExpression_apply χ hx]
  have hz : ∀ i j : Fin (N : ℕ), hsUnitVector N j - hsUnitVector N i = 0 := by
    intro i j
    simp [hsUnitVector, hsRotationVector]
  simp only [hz, zero_mul, mul_zero, Finset.sum_const_zero, mul_zero]

/-- The sum of squared differences over the pairs, as a closed form. -/
theorem sum_sum_sq_sub_eq (n : ℕ) (a : Fin n → ℝ) :
    ∑ i, ∑ j, (a j - a i) ^ 2 = 2 * n * ∑ i, a i ^ 2 - 2 * (∑ i, a i) ^ 2 := by
  have h : ∀ i j, (a j - a i) ^ 2 = a j ^ 2 + a i ^ 2 - 2 * (a i * a j) := fun i j => by ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_mul,
    sq, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Half of the full double sum is the sum over the pairs `i < j`. -/
theorem sum_filter_lt_sq_eq (n : ℕ) (a : Fin n → ℝ) :
    ∑ i, ∑ j ∈ univ.filter (i < ·), (a j - a i) ^ 2 =
      n * ∑ i, a i ^ 2 - (∑ i, a i) ^ 2 := by
  -- Pointwise, each square is counted once by the pair `i < j` or once by `j < i`.
  have hpt : ∀ i j : Fin n, (a j - a i) ^ 2 =
      (if i < j then (a j - a i) ^ 2 else 0) + (if j < i then (a j - a i) ^ 2 else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp only [h, not_lt.mpr h.le, reduceIte, add_zero]
    · subst h
      simp
    · simp only [h, not_lt.mpr h.le, reduceIte, zero_add]
  -- Swapping the labels maps the `j < i` half onto the `i < j` half.
  have hsym : ∑ i, ∑ j, (if j < i then (a j - a i) ^ 2 else 0) =
      ∑ i, ∑ j, (if i < j then (a j - a i) ^ 2 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hsplit : ∑ i, ∑ j, (a j - a i) ^ 2 =
      ∑ i, ∑ j, (if i < j then (a j - a i) ^ 2 else 0) +
        ∑ i, ∑ j, (if j < i then (a j - a i) ^ 2 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hpt i j
  have htot := sum_sum_sq_sub_eq n a
  simp only [Finset.sum_filter]
  rw [hsym] at hsplit
  linarith

/-- Lower bound for the quadratic form on vectors orthogonal to the translation direction. -/
theorem hessian_hsPairExpression_lower_bound (χ : HsPairPotentials N c)
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) (a : HsEuclidean N)
    (ha : inner ℝ a (hsUnitVector N) = 0) :
    2 * c * N * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x a a := by
  have hsqrt : Real.sqrt (N : ℕ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr N.pos)).ne'
  -- The orthogonality to `e` is the vanishing of the sum of the coordinates.
  have hS1 : ∑ i, a i = 0 := by
    have h1 : inner ℝ a (hsUnitVector N) = (Real.sqrt (N : ℕ))⁻¹ * ∑ i, a i := by
      simp [hsUnitVector, hsRotationVector, PiLp.inner_apply, inner_smul_right,
        Finset.mul_sum]
    rw [h1] at ha
    rcases mul_eq_zero.mp ha with h | h
    · exact absurd (inv_eq_zero.mp h) hsqrt
    · exact h
  have hnorm : ‖a‖ ^ 2 = ∑ i, a i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hT := sum_filter_lt_sq_eq (N : ℕ) (fun i => a i)
  simp only [hS1] at hT
  have hle : c * ∑ i : Fin (N : ℕ), ∑ j ∈ univ.filter (i < ·), (a j - a i) ^ 2 ≤
      ∑ i : Fin (N : ℕ), ∑ j ∈ univ.filter (i < ·),
        deriv (deriv (χ.potential i j)) (x j - x i) * (a j - a i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hij : i < j := (mem_filter.mp hj).2
    exact mul_le_mul_of_nonneg_right
      (χ.curvature i j hij (x j - x i) (hsChamber_separation_mem hx hij)) (sq_nonneg _)
  have key : 2 * c * N * ‖a‖ ^ 2 =
      2 * (c * ∑ i : Fin (N : ℕ), ∑ j ∈ univ.filter (i < ·), (a j - a i) ^ 2) := by
    rw [hT, hnorm]
    ring
  rw [hessian_hsPairExpression_self χ hx, key]
  linarith

/-- Off-diagonal entries: for `i < j`, `∂_{ij} H = -2 χ_ij''(x_j - x_i)`. -/
theorem hessian_hsPairExpression_offdiag (χ : HsPairPotentials N c) {x : HsEuclidean N}
    (hx : x ∈ hsChamber N) {i j : Fin (N : ℕ)} (hij : i < j) :
    fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = -(2 * deriv (deriv (χ.potential i j)) (x j - x i)) := by
  rw [hessian_hsPairExpression_apply χ hx, Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [hij.ne, hij.ne']
    · intro l hl hlj
      have hil : i < l := (mem_filter.mp hl).2
      simp [hlj, hij.ne, hil.ne']
    · intro hj
      exact absurd (mem_filter.mpr ⟨Finset.mem_univ _, hij⟩) hj
  · intro k _ hki
    apply Finset.sum_eq_zero
    intro l hl
    have hkl : k < l := (mem_filter.mp hl).2
    by_cases hli : l = i
    · have hkj : k ≠ j := ne_of_lt (hli ▸ hkl |>.trans hij)
      simp [PiLp.single_apply, hli, hki, hkj, hij.ne]
    · simp [PiLp.single_apply, hli, hki]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The anchored coordinate map `y ↦ y - y_0 e_0`, which sets the first coordinate to zero. -/
def hsAnchorMap (N : ℕ+) : HsEuclidean N →L[ℝ] HsEuclidean N :=
  ContinuousLinearMap.id ℝ (HsEuclidean N) -
    (EuclideanSpace.proj (⟨0, N.pos⟩ : Fin (N : ℕ))).smulRight
      (EuclideanSpace.single (⟨0, N.pos⟩ : Fin (N : ℕ)) (1 : ℝ))

theorem hsAnchorMap_apply_zero (y : HsEuclidean N) :
    hsAnchorMap N y ⟨0, N.pos⟩ = 0 := by
  simp [hsAnchorMap]

theorem hsAnchorMap_apply_of_ne (y : HsEuclidean N) {i : Fin (N : ℕ)}
    (hi : i ≠ ⟨0, N.pos⟩) : hsAnchorMap N y i = y i := by
  have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
  simp [hsAnchorMap, Fin.ext_iff, hi']

/-- The anchored Hamiltonian `H*(y) = H(0, y)`, with the first coordinate pinned at zero. -/
def hsAnchoredExpression (χ : HsPairPotentials N c) (y : HsEuclidean N) : ℝ :=
  hsPairExpression χ (hsAnchorMap N y)

theorem hsAnchorMap_of_coord_zero {b : HsEuclidean N} (hb : b ⟨0, N.pos⟩ = 0) :
    hsAnchorMap N b = b := by
  ext i
  by_cases h : i = ⟨0, N.pos⟩
  · subst h
    rw [hsAnchorMap_apply_zero, hb]
  · rw [hsAnchorMap_apply_of_ne _ h]

theorem hsAnchorMap_single_ne {i : Fin (N : ℕ)} (hi : i ≠ ⟨0, N.pos⟩) :
    hsAnchorMap N (EuclideanSpace.single i (1 : ℝ)) = EuclideanSpace.single i 1 := by
  apply hsAnchorMap_of_coord_zero
  rw [PiLp.single_apply, ite_eq_right_iff]
  exact fun h => absurd h (Ne.symm hi)

/-- The chain rule for the anchored Hessian: the anchored Hessian is the ambient Hessian at the
anchored point, evaluated on anchored vectors. -/
theorem fderiv_fderiv_hsAnchoredExpression (χ : HsPairPotentials N c) {y : HsEuclidean N}
    (hy : hsAnchorMap N y ∈ hsChamber N) (u v : HsEuclidean N) :
    fderiv ℝ (fderiv ℝ (hsAnchoredExpression χ)) y u v =
      fderiv ℝ (fderiv ℝ (hsPairExpression χ)) (hsAnchorMap N y)
        (hsAnchorMap N u) (hsAnchorMap N v) := by
  have hgrad : fderiv ℝ (hsAnchoredExpression χ) =ᶠ[𝓝 y]
      fun z => (hsPairGradient χ (hsAnchorMap N z)).comp (hsAnchorMap N) := by
    have hopen : IsOpen ((hsAnchorMap N) ⁻¹' hsChamber N) :=
      (isOpen_hsChamber N).preimage (hsAnchorMap N).continuous
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact ((hasFDerivAt_hsPairExpression χ hz).comp z (hsAnchorMap N).hasFDerivAt).fderiv
  rw [hgrad.fderiv_eq]
  have hc : HasFDerivAt (fun z => hsPairGradient χ (hsAnchorMap N z))
      ((hsPairHessian χ (hsAnchorMap N y)).comp (hsAnchorMap N)) y :=
    (hasFDerivAt_hsPairGradient χ hy).comp y (hsAnchorMap N).hasFDerivAt
  have hd := hc.clm_comp (hasFDerivAt_const (hsAnchorMap N) y)
  rw [hd.fderiv, fderiv_fderiv_hsPairExpression χ hy]
  simp [ContinuousLinearMap.comp_apply]

/-- Ambient lower bound for vectors whose first coordinate vanishes: the pairs `(0, j)` alone
give `2c|b|²`, since every term is nonnegative. -/
theorem hessian_hsPairExpression_first_lower (χ : HsPairPotentials N c) (hc : 0 < c)
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) (b : HsEuclidean N) (hb : b ⟨0, N.pos⟩ = 0) :
    2 * c * ‖b‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x b b := by
  rw [hessian_hsPairExpression_self χ hx]
  have hnn : ∀ i : Fin (N : ℕ), 0 ≤ ∑ j ∈ univ.filter (i < ·),
      deriv (deriv (χ.potential i j)) (x j - x i) * (b j - b i) ^ 2 := by
    intro i
    apply Finset.sum_nonneg
    intro j hj
    have hij : i < j := (mem_filter.mp hj).2
    exact mul_nonneg (hc.le.trans (χ.curvature i j hij _ (hsChamber_separation_mem hx hij)))
      (sq_nonneg _)
  -- The pairs whose first label is `0`.
  have hfirst : c * ∑ j ∈ univ.filter (⟨0, N.pos⟩ < ·), (b j - b ⟨0, N.pos⟩) ^ 2 ≤
      ∑ j ∈ univ.filter (⟨0, N.pos⟩ < ·),
        deriv (deriv (χ.potential ⟨0, N.pos⟩ j)) (x j - x ⟨0, N.pos⟩) *
          (b j - b ⟨0, N.pos⟩) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hij : (⟨0, N.pos⟩ : Fin (N : ℕ)) < j := (mem_filter.mp hj).2
    exact mul_le_mul_of_nonneg_right
      (χ.curvature _ _ hij _ (hsChamber_separation_mem hx hij)) (sq_nonneg _)
  have hsingle := Finset.single_le_sum (f := fun i : Fin (N : ℕ) =>
      ∑ j ∈ univ.filter (i < ·), deriv (deriv (χ.potential i j)) (x j - x i) *
        (b j - b i) ^ 2) (fun i _ => hnn i) (Finset.mem_univ ⟨0, N.pos⟩)
  -- Over the pairs with first label `0`, the sum is `∑_j b_j²`, because `b_0 = 0`.
  have hsum_all : ∑ j ∈ univ.filter (⟨0, N.pos⟩ < ·), (b j - b ⟨0, N.pos⟩) ^ 2 =
      ∑ j, b j ^ 2 := by
    simp only [hb, sub_zero]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hnot : ¬ (⟨0, N.pos⟩ : Fin (N : ℕ)) < j := fun h =>
      hj (mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have hj0 : j = ⟨0, N.pos⟩ := by
      apply Fin.ext
      have hle := not_lt.mp hnot
      rw [Fin.le_def] at hle
      simp only at hle ⊢
      omega
    rw [hj0, hb]
    norm_num
  have hnorm : ‖b‖ ^ 2 = ∑ j, b j ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have key : 2 * c * ‖b‖ ^ 2 = 2 * (c * ∑ j ∈ univ.filter (⟨0, N.pos⟩ < ·),
      (b j - b ⟨0, N.pos⟩) ^ 2) := by
    rw [hsum_all, hnorm]
    ring
  rw [key]
  simp only at hsingle
  linarith

/-- Anchored lower bound: for `b` with first coordinate zero, `b · ∇²H* b ≥ 2c|b|²`. -/
theorem hessian_hsAnchoredExpression_lower (χ : HsPairPotentials N c) (hc : 0 < c)
    {y : HsEuclidean N} (hy : hsAnchorMap N y ∈ hsChamber N) (b : HsEuclidean N)
    (hb : b ⟨0, N.pos⟩ = 0) :
    2 * c * ‖b‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (hsAnchoredExpression χ)) y b b := by
  rw [fderiv_fderiv_hsAnchoredExpression χ hy, hsAnchorMap_of_coord_zero hb]
  exact hessian_hsPairExpression_first_lower χ hc hy b hb

/-- Anchored off-diagonal entries: `∂_{ij} H* = -2 χ_ij''(y_j - y_i)` for `2 ≤ i < j ≤ N`. -/
theorem hessian_hsAnchoredExpression_offdiag (χ : HsPairPotentials N c)
    {y : HsEuclidean N} (hy : hsAnchorMap N y ∈ hsChamber N) {i j : Fin (N : ℕ)}
    (hi : i ≠ ⟨0, N.pos⟩) (hij : i < j) :
    fderiv ℝ (fderiv ℝ (hsAnchoredExpression χ)) y (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) =
      -(2 * deriv (deriv (χ.potential i j)) (hsAnchorMap N y j - hsAnchorMap N y i)) := by
  have hj : j ≠ ⟨0, N.pos⟩ := fun h => by
    rw [h] at hij
    exact absurd hij (not_lt.mpr (Fin.zero_le _))
  rw [fderiv_fderiv_hsAnchoredExpression χ hy, hsAnchorMap_single_ne hi,
    hsAnchorMap_single_ne hj, hessian_hsPairExpression_offdiag χ hy hij]

/-- The anchored off-diagonal entries are nonpositive. -/
theorem hessian_hsAnchoredExpression_offdiag_nonpos (χ : HsPairPotentials N c) (hc : 0 < c)
    {y : HsEuclidean N} (hy : hsAnchorMap N y ∈ hsChamber N) {i j : Fin (N : ℕ)}
    (hi : i ≠ ⟨0, N.pos⟩) (hij : i < j) :
    fderiv ℝ (fderiv ℝ (hsAnchoredExpression χ)) y (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) ≤ 0 := by
  rw [hessian_hsAnchoredExpression_offdiag χ hy hi hij]
  have h := χ.curvature i j hij _ (hsChamber_separation_mem hy hij)
  linarith

end Riesz1

end
