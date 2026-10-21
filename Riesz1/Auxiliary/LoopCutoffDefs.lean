/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingConvolutionEvent

/-!
# The anchored cutoff and the localized transport: definitions

The cutoff data part of Lemma 5.8. This file defines the objects only. Their
properties are proved in `LoopCutoffEvent.lean` and `LoopCutoffProbability.lean`.

* The cutoff profile `c(r) = min(1, max(0, 2 - r))` is `cutoffC`.
* The anchored cutoff `η` is `loopCutoff`. It is a product over the window `I_{2γ}`, so it uses
  `gradLabels N ℓ (2 * γ)` and `gradInWindow N ℓ (2 * γ)`. The good event `𝒜_{ε,2γ}` is the
  `gradEvent s (2 * γ) ε N ℓ`.
* The localized transport `ψ_γ` is `loopTransport`. It is defined on the whole circle through
  the representative `loopCircleRep`, which lies in `[-(2ℓ)^{-1}, (2ℓ)^{-1})`.
* The anchored function `F^*_γ = η^* H^*` is `loopCutoffF`. The anchor is the label `0`, so the
  point `(0, y)` of the paper is `y` itself, with `y 0 = 0` on the anchored domain.

The cutoff `η` is a total formula on `ℝ^N`. Its factors take nonnegative values on the
ordered domain `orderedDomain N`, where the statements about `η` are made.
-/

@[expose] public section

open Finset

namespace Riesz1

noncomputable section

/-- The cutoff profile `c(r) = min(1, max(0, 2 - r))`.
It equals one for `r ≤ 1`, vanishes for `r ≥ 2`, and takes values in `[0, 1]`. The paper
states it for `r ≥ 0`. The same formula is used for every real `r`, and the factors of `η` are
nonnegative on the ordered domain. -/
def cutoffC (r : ℝ) : ℝ := min 1 (max 0 (2 - r))

/-- The representative `u - ⌊ℓ u + 1/2⌋ / ℓ` of `u` on the circle `ℓ^{-1}𝕋`, lying in
`[-(2ℓ)^{-1}, (2ℓ)^{-1})`. It is the identity on that interval and is invariant under the
period `ℓ^{-1}`. The paper's `ψ_γ` is defined on the fundamental domain
`|u| ≤ (2ℓ)^{-1}`. This representative extends it to the whole circle. -/
def loopCircleRep (ℓ u : ℝ) : ℝ := u - ⌊ℓ * u + 1 / 2⌋ / ℓ

/-- The localized transport `ψ_γ`, with cutoff
`χ`. In a full window `ψ_γ = ψ`. In a partial window, with `t = gradT N ℓ γ` and the
representative `v = loopCircleRep ℓ u`, it is `ψ_γ(u) = χ(ℓ v / t) (ψ(v) - ψ((2ℓ)^{-1}))`. On
`|u| ≤ (2ℓ)^{-1}` this is the paper's formula, because `v = u` there. -/
def loopTransport (χ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (ψ : ℝ → ℝ) (u : ℝ) : ℝ :=
  if GradPartial N ℓ γ then
    χ (ℓ * loopCircleRep ℓ u / gradT N ℓ γ) * (ψ (loopCircleRep ℓ u) - ψ (1 / (2 * ℓ)))
  else ψ u

/-- The window condition is decidable: it is an implication between a decidable real inequality and
a finite-set membership. -/
instance decidableGradInWindow (N : ℕ+) (ℓ γ : ℝ) (j : ℤ) : Decidable (gradInWindow N ℓ γ j) := by
  unfold gradInWindow
  infer_instance

/-- The anchored cutoff `η`, on the window
`I_{2γ}` with the scale `K^ε`, `K = N ℓ`. It is the product of

* `c(2|N(x_{i+k} - x_i) - k| / (K^ε |k|^{s/2}))` over labels `i ∈ I_{2γ}` and integers
  `k ≠ 0` with `|k| ≤ N/2` and `i + k ∈ I_{2γ}`, and
* `c(2N(x_{i+1} - x_i)/K^ε) c(2/(K^ε N(x_{i+1} - x_i)))` over labels `i ∈ I_{2γ}` with
  `i + 1 ∈ I_{2γ}`.

Here `x_j = gradLift N X j` is the cyclic lift of `X`. The formula of the paper is meaningful on
the ordered domain, where the gaps are positive. -/
def loopCutoff (s γ ε : ℝ) (N : ℕ+) (ℓ : ℝ) (X : Fin (N : ℕ) → ℝ) : ℝ :=
  (∏ i ∈ gradLabels N ℓ (2 * γ), ∏ k ∈ Finset.Icc (-((N : ℤ) / 2)) ((N : ℤ) / 2),
      if k ≠ 0 ∧ gradInWindow N ℓ (2 * γ) (i + k) then
        cutoffC (2 * |(N : ℝ) * (gradLift N X (i + k) - gradLift N X i) - k| /
          (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2)))
      else 1) *
    ∏ i ∈ gradLabels N ℓ (2 * γ),
      if gradInWindow N ℓ (2 * γ) (i + 1) then
        cutoffC (2 * ((N : ℝ) * (gradLift N X (i + 1) - gradLift N X i)) / ((N : ℝ) * ℓ) ^ ε) *
          cutoffC (2 / (((N : ℝ) * ℓ) ^ ε * ((N : ℝ) * (gradLift N X (i + 1) - gradLift N X i))))
      else 1

/-- The anchored function `F^*_γ = η^* H^*`, with
`η^*(y) = η(y)` and `H^*(y) = H_γ[ψ_γ](y)`. On the anchored domain, `y 0 = 0`, and the point
`(0, y)` of the paper is `y`. The loop uses the window `I_γ`, and the cutoff uses `I_{2γ}`. -/
def loopCutoffF (χ : ℝ → ℝ) (s γ ε : ℝ) (N : ℕ+) (ℓ : ℝ) (ψ : ℝ → ℝ)
    (y : Fin (N : ℕ) → ℝ) : ℝ :=
  loopCutoff s γ ε N ℓ y * gradLoop s (loopTransport χ N ℓ γ ψ) N ℓ γ y

/-! ## Elementary facts about the profile and the representative -/

/-- The profile takes values in `[0, 1]`. -/
lemma cutoffC_mem_Icc (r : ℝ) : 0 ≤ cutoffC r ∧ cutoffC r ≤ 1 := by
  unfold cutoffC
  exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

/-- The profile equals one when `r ≤ 1`. -/
lemma cutoffC_eq_one_of_le {r : ℝ} (hr : r ≤ 1) : cutoffC r = 1 := by
  unfold cutoffC
  rw [min_eq_left]
  exact le_max_of_le_right (by linarith)

/-- The profile is positive exactly when `r < 2`. -/
lemma cutoffC_pos_iff (r : ℝ) : 0 < cutoffC r ↔ r < 2 := by
  unfold cutoffC
  constructor
  · intro h
    by_contra hr
    have h2 : max (0 : ℝ) (2 - r) = 0 := max_eq_left (by linarith [not_lt.mp hr])
    have h3 : min (1 : ℝ) (max 0 (2 - r)) ≤ 0 := by
      rw [h2]
      exact min_le_right _ _
    linarith
  · intro hr
    have h1 : (0 : ℝ) < max 0 (2 - r) := lt_max_of_lt_right (by linarith)
    exact lt_min zero_lt_one h1

/-- The representative lies in the half-open interval `[-(2ℓ)^{-1}, (2ℓ)^{-1})` for `ℓ > 0`. -/
lemma loopCircleRep_mem_Ico {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ) :
    -(1 / (2 * ℓ)) ≤ loopCircleRep ℓ u ∧ loopCircleRep ℓ u < 1 / (2 * ℓ) := by
  have h1 : ((⌊ℓ * u + 1 / 2⌋ : ℤ) : ℝ) ≤ ℓ * u + 1 / 2 := Int.floor_le _
  have h2 : ℓ * u + 1 / 2 < ((⌊ℓ * u + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hrep : loopCircleRep ℓ u * ℓ = ℓ * u - ((⌊ℓ * u + 1 / 2⌋ : ℤ) : ℝ) := by
    unfold loopCircleRep
    rw [sub_mul, div_mul_cancel₀ _ hℓ.ne', mul_comm]
  have e1 : -(1 / (2 * ℓ)) = -(1 / 2) / ℓ := by ring
  have e2 : 1 / (2 * ℓ) = (1 / 2) / ℓ := by ring
  rw [e1, e2]
  constructor
  · rw [div_le_iff₀ hℓ]
    linarith
  · rw [lt_div_iff₀ hℓ]
    linarith

/-- The representative is the identity on `[-(2ℓ)^{-1}, (2ℓ)^{-1})`. -/
lemma loopCircleRep_eq_self {ℓ : ℝ} (hℓ : 0 < ℓ) {u : ℝ}
    (hu0 : -(1 / (2 * ℓ)) ≤ u) (hu1 : u < 1 / (2 * ℓ)) :
    loopCircleRep ℓ u = u := by
  have e1 : -(1 / (2 * ℓ)) = -(1 / 2) / ℓ := by ring
  have e2 : 1 / (2 * ℓ) = (1 / 2) / ℓ := by ring
  rw [e1, div_le_iff₀ hℓ] at hu0
  rw [e2, lt_div_iff₀ hℓ] at hu1
  have hfl : ⌊ℓ * u + 1 / 2⌋ = 0 := by
    rw [Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  unfold loopCircleRep
  rw [hfl]
  simp

/-- The representative is invariant under the period `ℓ^{-1}` of the circle. -/
lemma loopCircleRep_add_period {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ) :
    loopCircleRep ℓ (u + 1 / ℓ) = loopCircleRep ℓ u := by
  have e : ℓ * (u + 1 / ℓ) = ℓ * u + 1 := by
    rw [mul_add, mul_one_div_cancel hℓ.ne']
  have hfl : ⌊ℓ * (u + 1 / ℓ) + 1 / 2⌋ = ⌊ℓ * u + 1 / 2⌋ + 1 := by
    rw [e, show ℓ * u + 1 + 1 / 2 = (ℓ * u + 1 / 2) + 1 by ring]
    exact Int.floor_add_one _
  unfold loopCircleRep
  rw [hfl]
  push_cast
  ring

end

end Riesz1
end
