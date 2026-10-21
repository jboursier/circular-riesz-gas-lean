/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingEstimatesComplete
public import Riesz1.Auxiliary.LoopAnchoringPath

/-!
# The gradient identity along the anchoring path

The common-translation path in the anchoring part of Lemma 5.8
has a negative anchor. Extend the coordinate derivative identities
from the fundamental chart to configurations with no circular collisions.
All objects remain the gradient fields and loop.
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The closed-form `V + W` identity needs only absence of circular collisions. -/
lemma loopAnchoring_gradVlab_add_gradWlab_eq_nonInt {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    {X : Fin (N : ℕ) → ℝ} (hX : ∀ i ∈ gradLabels N ℓ γ, ∀ j ∈ gradLabels N ℓ γ, i ≠ j →
      ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0) {i : ℤ} (hi : i ∈ gradLabels N ℓ γ) :
    gradVlab s ψ N ℓ γ X i + gradWlab s ψ N ℓ γ X i
      = 2 * (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j)
        - 2 * (N : ℝ) ^ (1 - s) * gradJderiv s ψ N ℓ γ (gradLift N X i) := by
  have hPV := gradPV_sub_eq_gradJderiv hψ hℓ0 hp hs0 hs1 hsupp (gradLift N X i)
  have hterm : ∀ j ∈ (gradLabels N ℓ γ).erase i,
      gradZx ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
          * gradKernelH s (gradSep N ℓ γ X i j)
        - gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
          * deriv (gradKernelH s) (gradSep N ℓ γ X i j)
        = gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j) := by
    intro j hj
    have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
    have hjl : j ∈ gradLabels N ℓ γ := Finset.mem_of_mem_erase hj
    obtain ⟨c, hc⟩ := gradPathIncr_modEq N ℓ γ i j
    have hlift : gradLift N X i + gradSep N ℓ γ X i j = gradLift N X j + c := by
      unfold gradSep
      rw [show gradLift N X (i + gradPathIncr N ℓ γ i j) = gradLift N X j + c by
        rw [hc, gradLift_add_mul]]
      ring
    have hnint : ((gradLift N X i + gradSep N ℓ γ X i j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0 := by
      apply coe_ne_zero_of_forall_ne_int
      intro m hm
      apply nonint_of_coe_ne_zero (hX i hi j hjl hij) (m - c)
      push_cast
      linarith
    have e := gradPairP1_eq hψ hℓ0.ne' hs0 hs1 (gradLift N X i)
      (gradLift N X i + gradSep N ℓ γ X i j) hnint
    rw [add_sub_cancel_left] at e
    have hP := gradPairP1_add_int_right hp s (gradLift N X i) (gradLift N X j) c
    rw [← hP, ← hlift, e]
  have hW : ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
        * (deriv (gradKernelH s) (gradSep N ℓ γ X i j)
          - deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / N))
      = ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
            * deriv (gradKernelH s) (gradSep N ℓ γ X i j)
        - ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
            * deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / N) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hS : ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradZx ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
          * gradKernelH s (gradSep N ℓ γ X i j)
        - ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
            * deriv (gradKernelH s) (gradSep N ℓ γ X i j)
      = ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hterm
  unfold gradVlab gradWlab
  rw [hW]
  linear_combination (2 * (N : ℝ) ^ (-s)) * hS - (2 * (N : ℝ) ^ (1 - s)) * hPV


/-- Coordinate differentiation of the loop on the collision-free chart. -/
lemma loopAnchoring_hasDerivAt_gradLoop_single_nonInt {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    {X : Fin (N : ℕ) → ℝ} (hX : ∀ i ∈ gradLabels N ℓ γ, ∀ j ∈ gradLabels N ℓ γ, i ≠ j →
      ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0) (k : Fin (N : ℕ)) :
    HasDerivAt (fun t : ℝ => gradLoop s ψ N ℓ γ (X + t • Pi.single k 1))
      (∑ i ∈ gradLabels N ℓ γ, (if gradIndex N i = k then (1 : ℝ) else 0) *
        (2 * (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j)
          - 2 * (N : ℝ) ^ (1 - s) * gradJderiv s ψ N ℓ γ (gradLift N X i))) 0 := by
  set α : ℤ → ℝ := fun i => if gradIndex N i = k then (1 : ℝ) else 0 with hα
  set I := gradLabels N ℓ γ with hI
  -- the decomposition of `H_γ` along the line
  have hdec : (fun t : ℝ => gradLoop s ψ N ℓ γ (X + t • Pi.single k 1))
      = fun t : ℝ => (N : ℝ) ^ (-s) * ∑ i ∈ I, ∑ j ∈ I.erase i,
          gradPairKernel s ψ ℓ (gradLift N (X + t • Pi.single k 1) i)
            (gradLift N (X + t • Pi.single k 1) j)
        - 2 * (N : ℝ) ^ (1 - s) * ∑ i ∈ I,
          gradBackground s ψ N ℓ γ (gradLift N (X + t • Pi.single k 1) i) := by
    funext t
    exact gradLoop_eq_pairs_background hψ hℓ0.ne' hp s N γ _
  rw [hdec]
  -- the lifts along the line
  have hlin : ∀ m : ℤ, gradLift N (X + (0 : ℝ) • Pi.single k 1) m = gradLift N X m := by
    intro m; simp
  have hline : ∀ m : ℤ, ∀ t : ℝ, gradLift N (X + t • Pi.single k 1) m = gradLift N X m + t * α m := by
    intro m t
    exact gradLift_add_smul_single N X k t m
  -- the pair derivative
  have hpair : ∀ i ∈ I, ∀ j ∈ I.erase i,
      HasDerivAt (fun t : ℝ => gradPairKernel s ψ ℓ (gradLift N (X + t • Pi.single k 1) i)
          (gradLift N (X + t • Pi.single k 1) j))
        (α i * gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j)
          + α j * gradPairP2 s ψ ℓ (gradLift N X i) (gradLift N X j)) 0 := by
    intro i hi j hj
    have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
    have hjI : j ∈ I := Finset.mem_of_mem_erase hj
    have hab : ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0 :=
      hX i hi j hjI hij
    have h := hasDerivAt_gradPairKernel_line hψ hℓ0.ne' hs0 hs1 (gradLift N X i) (gradLift N X j)
      (α i) (α j) hab
    simp only [hline]
    exact h
  have hbg : ∀ i ∈ I, HasDerivAt (fun t : ℝ => gradBackground s ψ N ℓ γ (gradLift N (X + t • Pi.single k 1) i))
      (gradJderiv s ψ N ℓ γ (gradLift N X i) * α i) 0 := by
    intro i _
    have hJ := gradBackground_hasDerivAt hψ hℓ0 hp hs0 hs1 hsupp (gradLift N X i)
    have hl : HasDerivAt (fun t : ℝ => gradLift N X i + t * α i) (α i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (α i)).const_add (gradLift N X i)
    have hJ' : HasDerivAt (fun y => gradBackground s ψ N ℓ γ y) (gradJderiv s ψ N ℓ γ (gradLift N X i))
        (gradLift N X i + (0 : ℝ) * α i) := by
      rw [zero_mul, add_zero]
      exact hJ
    have h := hJ'.comp (0 : ℝ) hl
    have hfun : (fun t : ℝ => gradBackground s ψ N ℓ γ (gradLift N (X + t • Pi.single k 1) i))
        = (fun y => gradBackground s ψ N ℓ γ y) ∘ (fun t : ℝ => gradLift N X i + t * α i) := by
      funext t
      simp only [Function.comp, hline]
    rw [hfun]
    simpa using h
  -- assemble the two sums
  have hsumP : HasDerivAt (fun t : ℝ => ∑ i ∈ I, ∑ j ∈ I.erase i,
        gradPairKernel s ψ ℓ (gradLift N (X + t • Pi.single k 1) i)
          (gradLift N (X + t • Pi.single k 1) j))
      (∑ i ∈ I, ∑ j ∈ I.erase i, (α i * gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j)
          + α j * gradPairP2 s ψ ℓ (gradLift N X i) (gradLift N X j))) 0 := by
    apply HasDerivAt.fun_sum
    intro i hi
    apply HasDerivAt.fun_sum
    intro j hj
    exact hpair i hi j hj
  have hsumB : HasDerivAt (fun t : ℝ => ∑ i ∈ I,
        gradBackground s ψ N ℓ γ (gradLift N (X + t • Pi.single k 1) i))
      (∑ i ∈ I, gradJderiv s ψ N ℓ γ (gradLift N X i) * α i) 0 := by
    apply HasDerivAt.fun_sum
    intro i hi
    exact hbg i hi
  have hcomb := (hsumP.const_mul ((N : ℝ) ^ (-s))).sub (hsumB.const_mul (2 * (N : ℝ) ^ (1 - s)))
  refine hcomb.congr_deriv ?_
  -- the derivative is the claimed sum, by the symmetry of the pair sum
  have hP2 : ∀ i j, gradPairP2 s ψ ℓ (gradLift N X i) (gradLift N X j)
      = gradPairP1 s ψ ℓ (gradLift N X j) (gradLift N X i) := fun i j => gradPairP2_eq_swap s _ _
  have hsym := sum_pair_alpha_eq I
    (fun i j => gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j))
    (fun i j => gradPairP2 s ψ ℓ (gradLift N X i) (gradLift N X j))
    α (fun i j => hP2 i j)
  have hsym' : ∑ i ∈ I, ∑ j ∈ I.erase i, (α i * gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j)
          + α j * gradPairP2 s ψ ℓ (gradLift N X i) (gradLift N X j))
      = 2 * ∑ i ∈ I, ∑ j ∈ I.erase i, α i * gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j) :=
    hsym
  rw [hsym']
  simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, hα]
  congr 1
  · apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring


/-- The coordinate Fréchet derivative is the sum of the two fields. -/
lemma loopAnchoring_fderiv_gradLoop_single_nonInt {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    {X : Fin (N : ℕ) → ℝ} (hX : ∀ i ∈ gradLabels N ℓ γ, ∀ j ∈ gradLabels N ℓ γ, i ≠ j →
      ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0) (k : Fin (N : ℕ)) :
    fderiv ℝ (gradLoop s ψ N ℓ γ) X (Pi.single k 1)
      = gradVfield s ψ N ℓ γ X k + gradWfield s ψ N ℓ γ X k := by
  have hH := (contDiffAt_gradLoop hψ hℓ0 hp hs0 hs1 hsupp (X := X)
    hX)
    |>.differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ => X + t • Pi.single (k : Fin (N : ℕ)) (1 : ℝ))
      (Pi.single k 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single (k : Fin (N : ℕ)) (1 : ℝ))).const_add X
  have hH0 : HasFDerivAt (gradLoop s ψ N ℓ γ) (fderiv ℝ (gradLoop s ψ N ℓ γ) X)
      (X + (0 : ℝ) • Pi.single (k : Fin (N : ℕ)) (1 : ℝ)) := by
    rw [zero_smul, add_zero]
    exact hH.hasFDerivAt
  have hcomp := hH0.comp_hasDerivAt (0 : ℝ) hline
  have hder := loopAnchoring_hasDerivAt_gradLoop_single_nonInt hψ hℓ0 hp hs0 hs1 hsupp hX k
  have hval : fderiv ℝ (gradLoop s ψ N ℓ γ) X (Pi.single k 1)
      = ∑ i ∈ gradLabels N ℓ γ, (if gradIndex N i = k then (1 : ℝ) else 0) *
        (2 * (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j)
          - 2 * (N : ℝ) ^ (1 - s) * gradJderiv s ψ N ℓ γ (gradLift N X i)) :=
    hcomp.unique hder
  rw [hval]
  simp only [gradVfield, gradWfield]
  rw [← Finset.sum_add_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  rw [loopAnchoring_gradVlab_add_gradWlab_eq_nonInt hψ hℓ0 hp hs0 hs1 hsupp hX hi]
  split_ifs <;> ring


/-- The derivative of the even modified kernel is odd, also at its
nondifferentiable points under the usual derivative convention. -/
lemma loopAnchoring_deriv_kernelH_neg (s r : ℝ) :
    deriv (gradKernelH s) (-r) = -deriv (gradKernelH s) r := by
  have hf : (fun y => gradKernelH s (-y)) = gradKernelH s :=
    funext (gradSplit_gradKernelH_even s)
  have h := deriv_comp_neg (f := gradKernelH s) (x := r)
  rw [hf] at h
  linarith

/-- Antisymmetry of the displacement pair term on every real vector. -/
lemma loopAnchoring_pairTerm_antisymm {s ℓ γ : ℝ} {ψ : ℝ → ℝ} (hψ : Function.Periodic ψ ℓ⁻¹)
    {N : ℕ+} (X : Fin (N : ℕ) → ℝ)
    {l m : ℤ} (hl : l ∈ gradLabels N ℓ γ) (hm : m ∈ gradLabels N ℓ γ) (hlm : l ≠ m) :
    gradPairTerm s ψ N ℓ γ X m l = -gradPairTerm s ψ N ℓ γ X l m := by
  obtain ⟨hk1, hk2, hk0, c, hc⟩ := gradPathIncr_spec hl hm hlm
  have hanti := gradPathIncr_antisymm hl hm hlm
  have hsep := gradSep_antisymm X hl hm hlm
  -- the lifts of `m` and of the reversed path
  have e2 : gradLift N X m = gradLift N X (l + gradPathIncr N ℓ γ l m) + c := by
    have h := gradLift_add_mul N X (l + gradPathIncr N ℓ γ l m) c
    rw [show l + gradPathIncr N ℓ γ l m + N * c = m by linarith] at h
    exact h
  have e1 : gradLift N X (l + gradPathIncr N ℓ γ l m) + c + -gradSep N ℓ γ X l m
      = gradLift N X l + c := by
    unfold gradSep
    ring
  have e3 : gradLift N X l + gradSep N ℓ γ X l m = gradLift N X (l + gradPathIncr N ℓ γ l m) := by
    unfold gradSep
    ring
  have hZ : gradZ ψ ℓ (gradLift N X m) (gradLift N X m + -gradSep N ℓ γ X l m) =
      gradZ ψ ℓ (gradLift N X l) (gradLift N X l + gradSep N ℓ γ X l m) := by
    have A : gradZ ψ ℓ (gradLift N X m) (gradLift N X m + -gradSep N ℓ γ X l m) =
        gradZ ψ ℓ (gradLift N X (l + gradPathIncr N ℓ γ l m) + c)
          (gradLift N X l + c) := by
      rw [e2, e1]
    rw [A, gradZ_add_int hψ c, gradZ_symm ψ ℓ (gradLift N X (l + gradPathIncr N ℓ γ l m))
      (gradLift N X l), e3]
  unfold gradPairTerm
  rw [hsep, hanti, Int.cast_neg, neg_div, hZ]
  rw [loopAnchoring_deriv_kernelH_neg, loopAnchoring_deriv_kernelH_neg]
  ring

/-- The displacement field has zero sum on every real vector. This
cancellation uses periodicity and pair antisymmetry, without a chart premise. -/
lemma loopAnchoring_Wfield_sum (s ℓ γ : ℝ) (N : ℕ+) {ψ : ℝ → ℝ}
    (hp : Function.Periodic ψ ℓ⁻¹) (X : Fin (N : ℕ) → ℝ) :
    ∑ k : Fin (N : ℕ), gradWfield s ψ N ℓ γ X k = 0 := by
  classical
  have hsum : ∑ k : Fin (N : ℕ), gradWfield s ψ N ℓ γ X k =
      -2 * (N : ℝ) ^ (-s) * ∑ i ∈ gradLabels N ℓ γ,
        ∑ j ∈ (gradLabels N ℓ γ).erase i, gradPairTerm s ψ N ℓ γ X i j := by
    simp only [gradWfield, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp [gradWlab, gradPairTerm, Finset.mul_sum]
  have hanti : ∑ i ∈ gradLabels N ℓ γ,
        ∑ j ∈ (gradLabels N ℓ γ).erase i, gradPairTerm s ψ N ℓ γ X i j =
      -(∑ i ∈ gradLabels N ℓ γ,
        ∑ j ∈ (gradLabels N ℓ γ).erase i, gradPairTerm s ψ N ℓ γ X i j) := by
    conv_lhs => rw [← sum_erase_swap (gradLabels N ℓ γ)
      (gradPairTerm s ψ N ℓ γ X)]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact loopAnchoring_pairTerm_antisymm hp X hi (Finset.mem_of_mem_erase hj)
      (Finset.mem_erase.mp hj).1.symm
  rw [hsum, show (∑ i ∈ gradLabels N ℓ γ,
        ∑ j ∈ (gradLabels N ℓ γ).erase i, gradPairTerm s ψ N ℓ γ X i j) = 0 by linarith]
  ring

/-- On a collision-free vector, the total derivative is the sum of the
reference and displacement-correction field `V`. -/
theorem loopAnchoring_sum_fderiv {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {ℓ γ : ℝ} (hℓ : 0 < ℓ) (hp : Function.Periodic ψ ℓ⁻¹)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ,
      (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    {X : Fin (N : ℕ) → ℝ}
    (hX : ∀ i ∈ gradLabels N ℓ γ, ∀ j ∈ gradLabels N ℓ γ, i ≠ j →
      ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0) :
    ∑ k : Fin (N : ℕ), fderiv ℝ (gradLoop s ψ N ℓ γ) X (Pi.single k 1) =
      ∑ i ∈ gradLabels N ℓ γ, gradVlab s ψ N ℓ γ X i := by
  simp_rw [loopAnchoring_fderiv_gradLoop_single_nonInt hψ hℓ
    (by simpa only [one_div] using hp) hs hs1 hsupp hX]
  rw [Finset.sum_add_distrib, loopAnchoring_Wfield_sum s ℓ γ N hp X,
    add_zero, gradEst_sum_Vfield]

end

end Riesz1
