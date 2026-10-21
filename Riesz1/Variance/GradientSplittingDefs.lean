/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingEstimates
public import Riesz1.Auxiliary.GradientSplittingGapIdentity
public import Riesz1.Auxiliary.GradientSplittingWindowKernel

/-!
# The localized-loop objects for the variance: definition tests

This file covers the transport envelopes, the localized loop, and the lattice subtraction with its
gap covector. Each object of the paper is the corresponding object of the gradient-splitting
development. No second encoding is introduced. This file proves the identifications that connect
the formulas of the paper with the Lean definitions.

* Transport envelopes: the weights `w_K^{(1)}`, `w_K^{(2)}` are `gradWeightOne`, `gradWeightTwo`
  with `a = 1 - s + α`, `L` the period and `K = Nℓ`. The Lean definitions are the two-branch
  formulas of the paper verbatim. The tests check that both pieces agree at circular distance one
  and that the weights are positive.
* Localized loop: in a partial window, `gradLoop_partial_eq_source` identifies `gradLoop` with the
  formula of the paper, pair sum and background integral included. The full-window identification
  uses periodicity of the kernel and is not formalized here.
* Lattice subtraction: the field `dV = ∇Loop - dW` is `gradVfield`
  (`gradVfield_eq_fderiv_sub_gradWfield`), `dW` is `gradWfield`, and the gap covector
  `dW^gap` is `gradWgap`, whose sum runs over the positively oriented chosen paths as in
  the paper. The divided difference `Z_{lm}` of the paper is `gradZ_eq_divided_difference`.
  The paper describes `dW` by adding `∓2N^{-s} C_{lm}` for each unordered pair. The ordered sum
  of `gradWlab` gives the same vector because the pair term is antisymmetric
  (`gradPairTerm_antisymm`). That regrouping is not formalized as a separate lemma.
-/

@[expose] public section

open Set
open scoped ContDiff

namespace Riesz1

noncomputable section

/-! ## Transport envelopes -/

/-- Test of the envelope weights: at circular distance one both weights equal one, so the two
pieces of each definition agree on `|u| = 1`. -/
lemma gradWeightOne_eq_one_of_circDist_eq_one {s a K L u : ℝ} (h : circDist L u = 1) :
    gradWeightOne s a K L u = 1 := by
  rw [gradWeightOne_of_one_le (by rw [h]), h, Real.one_rpow]

/-- Test of the envelope weights: the second weight also equals one at circular distance one. -/
lemma gradWeightTwo_eq_one_of_circDist_eq_one {s a K L u : ℝ} (h : circDist L u = 1) :
    gradWeightTwo s a K L u = 1 := by
  rw [gradWeightTwo_eq_of_one_le (by rw [h]), h, Real.one_rpow]

/-- Test of the envelope weights: the first weight is positive for every `u`, since the first
branch is a positive power of `max(|u|, K⁻¹)` and the second branch is a positive power of
`|u| ≥ 1`. -/
lemma gradWeightOne_pos {s a K L u : ℝ} (hK : 0 < K) : 0 < gradWeightOne s a K L u := by
  unfold gradWeightOne
  split_ifs with h
  · exact Real.rpow_pos_of_pos (lt_max_of_lt_right (inv_pos.2 hK)) _
  · exact Real.rpow_pos_of_pos (by linarith [not_lt.mp h]) _

/-- Test of the envelope weights: the second weight is positive for every `u`, by the same
two-branch argument as `gradWeightOne_pos`. -/
lemma gradWeightTwo_pos {s a K L u : ℝ} (hK : 0 < K) : 0 < gradWeightTwo s a K L u := by
  unfold gradWeightTwo
  split_ifs with h
  · exact Real.rpow_pos_of_pos (lt_max_of_lt_right (inv_pos.2 hK)) _
  · exact Real.rpow_pos_of_pos (by linarith [not_lt.mp h]) _

/-! ## The localized loop -/

/-- Test of the localized loop: in a partial window, `gradLoop` is the formula of the paper.
Both the particle pair sum over `i ≠ j` in `I_γ` and the background integral over
`B_γ = [-t_γ, t_γ]` agree with the paper, where `g_s' = deriv (hurwitzKernel s)` and the paper's
`-2N` times `N^{-s}` equals `-2N^{1-s}` in `gradLoop`. -/
lemma gradLoop_partial_eq_source {s : ℝ} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {N : ℕ+}
    {ℓ γ : ℝ} (hℓ : 0 < ℓ) (hP : GradPartial N ℓ γ) (X : Fin (N : ℕ) → ℝ) :
    gradLoop s ψ N ℓ γ X =
      (N : ℝ) ^ (-s) * ∑ i ∈ gradLabels N ℓ γ, ∑ j ∈ (gradLabels N ℓ γ).erase i,
          ℓ * (ψ (gradLift N X i / ℓ) - ψ (gradLift N X j / ℓ)) *
            deriv (hurwitzKernel s) (gradLift N X i - gradLift N X j)
        - 2 * (N : ℝ) * (N : ℝ) ^ (-s) * ∑ i ∈ gradLabels N ℓ γ,
          ∫ y in (-gradT N ℓ γ)..gradT N ℓ γ,
            ℓ * (ψ (gradLift N X i / ℓ) - ψ (y / ℓ)) * deriv (hurwitzKernel s) (gradLift N X i - y) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hsep : ∀ i j : ℤ, gradSep N ℓ γ X i j = gradLift N X j - gradLift N X i := by
    intro i j
    simp only [gradSep, gradPathIncr, hP, ↓reduceIte, add_sub_cancel]
  have hkey : ∀ a b : ℝ, gradZ ψ ℓ a b * gradKernelH s (b - a) =
      ℓ * (ψ (a / ℓ) - ψ (b / ℓ)) * deriv (hurwitzKernel s) (a - b) := by
    intro a b
    have h2 := gradPairKernel_symm s ψ ℓ a b
    unfold gradPairKernel at h2
    rw [gradZ_mul_kernelH hψ hℓ.ne' s a b]
    exact h2
  have hpair : ∀ i j : ℤ, gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j) *
      gradKernelH s (gradSep N ℓ γ X i j) =
        ℓ * (ψ (gradLift N X i / ℓ) - ψ (gradLift N X j / ℓ)) *
          deriv (hurwitzKernel s) (gradLift N X i - gradLift N X j) := by
    intro i j
    rw [hsep, add_sub_cancel]
    exact hkey _ _
  have hbg : ∀ i : ℤ, gradBackground s ψ N ℓ γ (gradLift N X i) =
      ∫ y in (-gradT N ℓ γ)..gradT N ℓ γ,
        ℓ * (ψ (gradLift N X i / ℓ) - ψ (y / ℓ)) * deriv (hurwitzKernel s) (gradLift N X i - y) := by
    intro i
    unfold gradBackground
    have hlo : gradBLo N ℓ γ (gradLift N X i) = -gradT N ℓ γ := by
      simp only [gradBLo, hP, ↓reduceIte]
    have hhi : gradBHi N ℓ γ (gradLift N X i) = gradT N ℓ γ := by
      simp only [gradBHi, hP, ↓reduceIte]
    rw [hlo, hhi]
    exact intervalIntegral.integral_congr (fun y _ => hkey _ _)
  have hN1 : (N : ℝ) ^ (1 - s) = (N : ℝ) * (N : ℝ) ^ (-s) := by
    rw [sub_eq_add_neg, Real.rpow_add hN0, Real.rpow_one]
  unfold gradLoop
  simp only [hpair, hbg]
  rw [hN1]
  ring

/-! ## Lattice subtraction and its gap covector -/

/-- The divided difference `Z_{lm}` of the paper is `ℓ(ψ(y/ℓ) - ψ(x/ℓ))/(y - x)` for `y ≠ x`:
`gradZ` is the integral average of `ψ'`, which is this quotient by the fundamental
theorem of calculus (`gradZ_mul_sub`). -/
lemma gradZ_eq_divided_difference {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ x y : ℝ} (hℓ : 0 < ℓ)
    (hxy : y ≠ x) :
    gradZ ψ ℓ x y = ℓ * (ψ (y / ℓ) - ψ (x / ℓ)) / (y - x) :=
  eq_div_of_mul_eq (sub_ne_zero.mpr hxy) (gradZ_mul_sub hψ hℓ.ne' x y)

/-- Test of the lattice subtraction: the field `dV = ∇Loop - dW` is `gradVfield`. This is the
identity `∇H_γ = V + W` of `gradient_splitting_identity`, read as the definition of `dV`. -/
lemma gradVfield_eq_fderiv_sub_gradWfield {s : ℝ} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ}
    (hℓ : 0 < ℓ) (hp : Function.Periodic ψ (1 / ℓ)) (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    {X : Fin (N : ℕ) → ℝ} (hX : X ∈ orderedDomain N) (k : Fin (N : ℕ)) :
    gradVfield s ψ N ℓ γ X k = fderiv ℝ (gradLoop s ψ N ℓ γ) X (Pi.single k 1) -
      gradWfield s ψ N ℓ γ X k := by
  rw [(gradient_splitting_identity hψ hℓ hp hs0 hs1 hsupp).2.1 X hX k]
  ring

end

end Riesz1
