/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingKernel
public import Riesz1.Auxiliary.GradientSplittingZDifferences
public import Riesz1.Frozen.OrderedDomain

/-!
# The window, the pair paths and the localized loop: definitions

The window `I` and the set `B` are the data of Lemma 5.7. This file also defines the pair paths and
the localized loop `H_γ` with its fields `V`, `W`. Both background integrals in `V` are principal
values at every periodic image `x_i + m`, `m ∈ ℤ`, and `H_γ` is an ordinary Lebesgue integral.

Conventions.

* `N : ℕ+` is the number of particles, `ℓ > 0` with `K = Nℓ ≥ 1` (not enforced here), and `γ`.
* The window is partial when `M < N/8` with `M = K^γ` (`GradPartial`). Then the labels are the
  integers `-n, …, n` with `n = ⌊M⌋`, and `B = [-t, t]` with `t = M/N`. Otherwise the labels are
  `0, …, N-1` (one cyclic period), `t = 1/2`, and the background integral runs over `y - x ∈ (-1/2, 1/2)`.
* A configuration is a point `X ∈ ℝ^N` (in `orderedDomain N` in the paper). Its lifts
  `x_j = gradLift N X j`, `j ∈ ℤ`, satisfy `x_{j+N} = x_j + 1` (the formula of `cyclicLift`).
* The second argument of each divided difference is the path lift `x_i + r_ij`.

The divided difference `Z`, its derivative `Z_x`, the modified kernel `h` and `h'` are the
objects `gradZ`, `gradZx` (`GradientSplittingZDifferences.lean`) and `gradKernelH`
(`GradientSplittingKernel.lean`). The derivative `h'` is `deriv (gradKernelH s)`, taken off the
integers. Only values off the integers enter, because the principal
values exclude every neighbourhood of the integers.

Principal values are defined as limits (`gradPV`). Their existence is proved in
`GradientSplittingWindowPV.lean`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- `M = K^γ` with `K = Nℓ`. See Lemma 5.7. -/
def gradM (N : ℕ+) (ℓ γ : ℝ) : ℝ := ((N : ℝ) * ℓ) ^ γ

/-- The window is partial when `M < N/8`. See Lemma 5.7. -/
abbrev GradPartial (N : ℕ+) (ℓ γ : ℝ) : Prop := gradM N ℓ γ < (N : ℝ) / 8

/-- The half length `t` of the background set `B`: `t = M/N` in a partial window and `t = 1/2`
in a full window. See Lemma 5.7. -/
def gradT (N : ℕ+) (ℓ γ : ℝ) : ℝ := if GradPartial N ℓ γ then gradM N ℓ γ / N else 1 / 2

/-- The labels of the window `I`: `{-n, …, n}` with `n = ⌊M⌋` in a partial window, and the cyclic
labels `{0, …, N-1}` in a full window. See Lemma 5.7. -/
def gradLabels (N : ℕ+) (ℓ γ : ℝ) : Finset ℤ :=
  if GradPartial N ℓ γ then Finset.Icc (-⌊gradM N ℓ γ⌋) ⌊gradM N ℓ γ⌋ else Finset.Ico 0 (N : ℤ)

/-- The lower limit of the `y`-integral over `B`: `-t` in a partial window, and `x - 1/2` in a full
window, where `y - x` ranges over `(-1/2, 1/2)`. -/
def gradBLo (N : ℕ+) (ℓ γ x : ℝ) : ℝ := if GradPartial N ℓ γ then -gradT N ℓ γ else x - 1 / 2

/-- The upper limit of the `y`-integral over `B`: `t` in a partial window, and `x + 1/2` in a full
window. -/
def gradBHi (N : ℕ+) (ℓ γ x : ℝ) : ℝ := if GradPartial N ℓ γ then gradT N ℓ γ else x + 1 / 2

/-- The index in `Fin N` of the label `j ∈ ℤ`, by Euclidean division. -/
def gradIndex (N : ℕ+) (j : ℤ) : Fin (N : ℕ) :=
  ⟨(j % (N : ℤ)).toNat, by
    have h := Int.emod_lt_of_pos j (show (0 : ℤ) < (N : ℤ) by exact_mod_cast N.pos)
    exact_mod_cast (Int.toNat_lt (Int.emod_nonneg j (by exact_mod_cast N.ne_zero))).mpr h⟩

/-- The cyclic lift `x_j` of the label `j ∈ ℤ` of `X ∈ ℝ^N`, with `x_{j+N} = x_j + 1`. It is the
formula of `Riesz1.cyclicLift`, extended to all of `ℝ^N`. -/
def gradLift (N : ℕ+) (X : Fin (N : ℕ) → ℝ) (j : ℤ) : ℝ :=
  X (gradIndex N j) + ((j / (N : ℤ) : ℤ) : ℝ)

/-- The signed increment `k_{ij}` of the chosen path from the label `i` to the label `j`.
In a partial window it is `j - i`. In a full window the path has length at
most `N/2`: it is the positive path when `(j - i) mod N < N/2`, the negative path when
`(j - i) mod N > N/2`, and for opposite labels (`N` even) the positive path starting at the smaller
representative in `{0, …, N-1}`. -/
def gradPathIncr (N : ℕ+) (ℓ γ : ℝ) (i j : ℤ) : ℤ :=
  if GradPartial N ℓ γ then j - i
  else
    if 2 * ((j - i) % (N : ℤ)) < (N : ℤ) then (j - i) % (N : ℤ)
    else if (N : ℤ) < 2 * ((j - i) % (N : ℤ)) then (j - i) % (N : ℤ) - (N : ℤ)
    else if i % (N : ℤ) < j % (N : ℤ) then (N : ℤ) / 2 else -((N : ℤ) / 2)

/-- The lifted separation `r_{ij}` of the path from `i` to `j`: `r_{ij} = x_{i+k_{ij}} - x_i`.
The path lift of `x_j` is `x_i + r_{ij} = x_{i+k_{ij}}`. -/
def gradSep (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) (i j : ℤ) : ℝ :=
  gradLift N X (i + gradPathIncr N ℓ γ i j) - gradLift N X i

/-- The principal value `PV ∫_B f(y) dy`, centred at the lift `x`: the
limit as `δ ↓ 0` of the integral over `B` from which every interval `|y - x - m| < δ` (`m ∈ ℤ`)
has been removed. Only the value of `f` off the excluded intervals enters. -/
def gradPV (N : ℕ+) (ℓ γ x : ℝ) (f : ℝ → ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun δ : ℝ =>
    ∫ y in gradBLo N ℓ γ x..gradBHi N ℓ γ x,
      Set.indicator {y : ℝ | ∀ m : ℤ, δ ≤ |y - x - m|} f y

/-- The background integral `∫_B Z(x,y) h(y - x) dy` (an ordinary
Lebesgue integral). -/
def gradBackground (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ x : ℝ) : ℝ :=
  ∫ y in gradBLo N ℓ γ x..gradBHi N ℓ γ x, gradZ ψ ℓ x y * gradKernelH s (y - x)

/-- The localized loop `H_γ(X)`, with `X ∈ ℝ^N` and the cyclic lifts of
`X`. The particle-particle sum runs over ordered pairs of distinct labels in the window. The
background part is `-2N^{1-s} ∑_i ∫_B Z(x_i,y) h(y - x_i) dy`. -/
def gradLoop (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) : ℝ :=
  (N : ℝ) ^ (-s) * ∑ i ∈ gradLabels N ℓ γ, ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j) *
        gradKernelH s (gradSep N ℓ γ X i j)
    - 2 * (N : ℝ) ^ (1 - s) * ∑ i ∈ gradLabels N ℓ γ, gradBackground s ψ N ℓ γ (gradLift N X i)

/-- The first field `V_i` at the label `i`, with the two principal values
`PV ∫_B Z_x(x_i,y) h(y - x_i) dy` and `PV ∫_B Z(x_i,y) h'(y - x_i) dy`. The discrete terms use
the path lift `x_i + r_{ij}` as the second argument, and the lattice increment `k_{ij}/N` in `h'`. -/
def gradVlab (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) (i : ℤ) : ℝ :=
  2 * (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradZx ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j) *
        gradKernelH s (gradSep N ℓ γ X i j)
    - 2 * (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j) *
        deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / N)
    - 2 * (N : ℝ) ^ (1 - s) * gradPV N ℓ γ (gradLift N X i)
        (fun y => gradZx ψ ℓ (gradLift N X i) y * gradKernelH s (y - gradLift N X i))
    + 2 * (N : ℝ) ^ (1 - s) * gradPV N ℓ γ (gradLift N X i)
        (fun y => gradZ ψ ℓ (gradLift N X i) y * deriv (gradKernelH s) (y - gradLift N X i))

/-- The second field `W_i` at the label `i`. -/
def gradWlab (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) (i : ℤ) : ℝ :=
  -2 * (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
    gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j) *
      (deriv (gradKernelH s) (gradSep N ℓ γ X i j)
        - deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / N))

/-- The field `V` as a vector indexed by the particles `k ∈ Fin N`: the sum of `V_i` over the
labels `i ∈ I` that lie over `k`. In a partial window the labels of `I` lie over distinct
particles, so this is `V_i` on the particle of `i`, and it is zero on the other particles. -/
def gradVfield (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) : Fin (N : ℕ) → ℝ :=
  fun k => ∑ i ∈ (gradLabels N ℓ γ).filter (fun i => gradIndex N i = k), gradVlab s ψ N ℓ γ X i

/-- The field `W` as a vector indexed by the particles `k ∈ Fin N` (see `gradVfield`). -/
def gradWfield (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) : Fin (N : ℕ) → ℝ :=
  fun k => ∑ i ∈ (gradLabels N ℓ γ).filter (fun i => gradIndex N i = k), gradWlab s ψ N ℓ γ X i

end

end Riesz1
