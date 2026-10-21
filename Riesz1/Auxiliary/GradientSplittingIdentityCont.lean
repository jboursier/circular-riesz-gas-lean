/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingIdentityExist

/-!
# Continuity of the fields on the ordered domain

The configurations whose label differences avoid the integers form an open set `U` that contains the
ordered domain `D_N`. On `U` the loop `H_γ` is smooth, so `∇H_γ` is continuous there. The field `W`
is continuous on `U` directly, because its integrand involves only the kernel `Z` and the derivative
of `h` at non-integer separations. Hence `V = (V + W) - W` is continuous on `D_N` as well.
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- A real number whose class in the unit circle is nonzero avoids every integer. -/
lemma nonint_of_coe_ne_zero {r : ℝ} (h : (r : UnitAddCircle) ≠ 0) (n : ℤ) : r ≠ n := by
  rintro rfl
  exact h ((AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨n, by simp⟩)

/-- The configurations at which every two distinct labels have non-integer lifted difference. -/
lemma isOpen_gradNonInt (N : ℕ+) (ℓ γ : ℝ) :
    IsOpen {X : Fin (N : ℕ) → ℝ | ∀ i ∈ gradLabels N ℓ γ, ∀ j ∈ gradLabels N ℓ γ, i ≠ j →
      ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0} := by
  have h : {X : Fin (N : ℕ) → ℝ | ∀ i ∈ gradLabels N ℓ γ, ∀ j ∈ gradLabels N ℓ γ, i ≠ j →
      ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0}
      = ⋂ i ∈ gradLabels N ℓ γ, ⋂ j ∈ gradLabels N ℓ γ,
          {X : Fin (N : ℕ) → ℝ | i = j ∨ ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0} := by
    ext X
    simp only [mem_ofPred_eq, Set.mem_iInter, imp_iff_not_or, ne_eq, not_not]
  rw [h]
  refine isOpen_biInter_finset fun i _ => isOpen_biInter_finset fun j _ => ?_
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, false_or]
    exact gradSplit_isOpen_nonInt.preimage
      (((contDiff_gradLift N j).continuous).sub ((contDiff_gradLift N i).continuous))

/-- Every configuration of the ordered domain has non-integer label differences. -/
lemma nonInt_of_mem_orderedDomain {N : ℕ+} {ℓ γ : ℝ} (hℓ : 0 ≤ ℓ) {X : Fin (N : ℕ) → ℝ}
    (hX : X ∈ orderedDomain N) :
    ∀ i ∈ gradLabels N ℓ γ, ∀ j ∈ gradLabels N ℓ γ, i ≠ j →
      ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0 :=
  fun _ hi _ hj hij => coe_ne_zero_of_forall_ne_int (gradLift_sub_not_int hℓ hX hi hj hij)

/-- The ordered domain lies in the open set of non-integer label differences. -/
lemma orderedDomain_subset_nonInt {N : ℕ+} {ℓ γ : ℝ} (hℓ : 0 ≤ ℓ) :
    orderedDomain N ⊆ {X : Fin (N : ℕ) → ℝ | ∀ i ∈ gradLabels N ℓ γ, ∀ j ∈ gradLabels N ℓ γ,
      i ≠ j → ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0} :=
  fun _ hX => nonInt_of_mem_orderedDomain hℓ hX

lemma continuous_gradSep (N : ℕ+) (ℓ γ : ℝ) (i j : ℤ) :
    Continuous fun Y : Fin (N : ℕ) → ℝ => gradSep N ℓ γ Y i j := by
  unfold gradSep
  exact ((contDiff_gradLift N _).continuous).sub ((contDiff_gradLift N i).continuous)

/-- The separation `x_j - x_i` of two labels with non-integer difference is not an integer
(the path increment only shifts it by an integer). -/
lemma gradSep_ne_coe_zero {N : ℕ+} {ℓ γ : ℝ} {X : Fin (N : ℕ) → ℝ} {i j : ℤ}
    (hX : ∀ i ∈ gradLabels N ℓ γ, ∀ j ∈ gradLabels N ℓ γ, i ≠ j →
      ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0)
    (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ) (hij : i ≠ j) :
    ((gradSep N ℓ γ X i j : ℝ) : UnitAddCircle) ≠ 0 := by
  obtain ⟨c, hc⟩ := gradPathIncr_modEq N ℓ γ i j
  have hsep : gradSep N ℓ γ X i j = gradLift N X j - gradLift N X i + c := by
    unfold gradSep
    rw [hc, gradLift_add_mul]
    ring
  apply coe_ne_zero_of_forall_ne_int
  intro m hm
  have hne := nonint_of_coe_ne_zero (hX i hi j hj hij) (m - c)
  apply hne
  push_cast
  linarith

/-- The kernel `Z(x, y) = ∫_0^1 ψ'(x + θ (y - x)) dθ` (in the normalization of `gradZ`) is jointly
continuous in the two arguments. -/
lemma continuous_gradZ_pair {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (ℓ : ℝ) :
    Continuous fun p : ℝ × ℝ => gradZ ψ ℓ p.1 p.2 := by
  have hd : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hg : Continuous fun q : (ℝ × ℝ) × ℝ => (q.1.1 + q.2 * (q.1.2 - q.1.1)) / ℓ := by
    fun_prop
  have hf : Continuous (Function.uncurry fun (p : ℝ × ℝ) (θ : ℝ) =>
      deriv ψ ((p.1 + θ * (p.2 - p.1)) / ℓ)) := hd.comp hg
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 1

/-- The derivative of the kernel `h = gradKernelH s` is continuous off the integers. -/
lemma continuousAt_deriv_gradKernelH {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {r : ℝ}
    (hr : (r : UnitAddCircle) ≠ 0) : ContinuousAt (deriv (gradKernelH s)) r := by
  have hA : ContinuousAt (fun r => deriv (hurwitzKernel s) r
      + r * iteratedDeriv 2 (hurwitzKernel s) r) r :=
    (contDiffAt_deriv_hurwitzKernel hs0 hs1 hr).continuousAt.add
      (continuousAt_id.mul ((gradSplit_contDiffOn_iteratedDeriv s hs0 hs1 2).contDiffAt
        (gradSplit_isOpen_nonInt.mem_nhds hr)).continuousAt)
  refine hA.congr ?_
  filter_upwards [gradSplit_isOpen_nonInt.mem_nhds hr] with r' hr'
  exact (deriv_gradKernelH_eq (r := r') hs0 hs1 hr').symm

/-- Each summand of `W_i` is continuous at every configuration with non-integer label differences. -/
lemma continuousAt_gradWlab {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+} {i : ℤ} {X : Fin (N : ℕ) → ℝ}
    (hX : ∀ i ∈ gradLabels N ℓ γ, ∀ j ∈ gradLabels N ℓ γ, i ≠ j →
      ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0)
    (hi : i ∈ gradLabels N ℓ γ) :
    ContinuousAt (fun Y => gradWlab s ψ N ℓ γ Y i) X := by
  unfold gradWlab
  apply ContinuousAt.mul continuousAt_const
  apply tendsto_finsetSum
  intro j hj
  have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
  have hjI : j ∈ gradLabels N ℓ γ := Finset.mem_of_mem_erase hj
  have hpair : Continuous fun Y : Fin (N : ℕ) → ℝ =>
      (gradLift N Y i, gradLift N Y i + gradSep N ℓ γ Y i j) :=
    (contDiff_gradLift N i).continuous.prodMk
      ((contDiff_gradLift N i).continuous.add (continuous_gradSep N ℓ γ i j))
  apply ContinuousAt.mul
  · exact ((continuous_gradZ_pair hψ ℓ).comp hpair).continuousAt
  · apply ContinuousAt.sub
    · exact ContinuousAt.comp (g := deriv (gradKernelH s)) (f := fun Y => gradSep N ℓ γ Y i j)
        (continuousAt_deriv_gradKernelH hs0 hs1 (gradSep_ne_coe_zero hX hi hjI hij))
        (continuous_gradSep N ℓ γ i j).continuousAt
    · exact continuousAt_const

/-- The loop is smooth on the open set of non-integer label differences. -/
lemma contDiffOn_gradLoop_nonInt {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) :
    ContDiffOn ℝ ∞ (gradLoop s ψ N ℓ γ) {X : Fin (N : ℕ) → ℝ | ∀ i ∈ gradLabels N ℓ γ,
      ∀ j ∈ gradLabels N ℓ γ, i ≠ j → ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0} :=
  fun X hX => (contDiffAt_gradLoop hψ hℓ0 hp hs0 hs1 hsupp (X := X) hX).contDiffWithinAt

/-- The coordinate directional derivatives of the loop are continuous on the open set. -/
lemma continuousOn_fderiv_gradLoop_apply {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ}
    (hℓ0 : 0 < ℓ) (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    (k : Fin (N : ℕ)) :
    ContinuousOn (fun X : Fin (N : ℕ) → ℝ => fderiv ℝ (gradLoop s ψ N ℓ γ) X (Pi.single k 1))
      {X : Fin (N : ℕ) → ℝ | ∀ i ∈ gradLabels N ℓ γ, ∀ j ∈ gradLabels N ℓ γ, i ≠ j →
        ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0} :=
  ((contDiffOn_gradLoop_nonInt hψ hℓ0 hp hs0 hs1 hsupp).continuousOn_fderiv_of_isOpen
    (isOpen_gradNonInt N ℓ γ) (by simp)).clm_apply continuousOn_const

/-- The sum `V_k + W_k` is continuous on the ordered domain. -/
lemma continuousOn_gradVplusW {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ}
    (hℓ0 : 0 < ℓ) (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    (k : Fin (N : ℕ)) :
    ContinuousOn (fun X => gradVfield s ψ N ℓ γ X k + gradWfield s ψ N ℓ γ X k) (orderedDomain N) := by
  have h := (continuousOn_fderiv_gradLoop_apply hψ hℓ0 hp hs0 hs1 hsupp k).mono
    (orderedDomain_subset_nonInt hℓ0.le)
  exact h.congr fun X hX => (fderiv_gradLoop_single hψ hℓ0 hp hs0 hs1 hsupp hX k).symm

/-- The field `W_k` is continuous on the ordered domain. -/
lemma continuousOn_gradWfield {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ}
    (hℓ0 : 0 < ℓ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+} (k : Fin (N : ℕ)) :
    ContinuousOn (fun X => gradWfield s ψ N ℓ γ X k) (orderedDomain N) := by
  simp only [gradWfield]
  apply continuousOn_finsetSum
  intro i hi
  have hi' := (Finset.mem_filter.1 hi).1
  intro X hX
  exact (continuousAt_gradWlab hψ hs0 hs1 (nonInt_of_mem_orderedDomain hℓ0.le hX) hi').continuousWithinAt

/-- The field `V_k` is continuous on the ordered domain. -/
lemma continuousOn_gradVfield {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ}
    (hℓ0 : 0 < ℓ) (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    (k : Fin (N : ℕ)) :
    ContinuousOn (fun X => gradVfield s ψ N ℓ γ X k) (orderedDomain N) :=
  ((continuousOn_gradVplusW hψ hℓ0 hp hs0 hs1 hsupp k).sub
    (continuousOn_gradWfield hψ hℓ0 hs0 hs1 k)).congr fun _ _ => (add_sub_cancel_right _ _).symm

end

end Riesz1
