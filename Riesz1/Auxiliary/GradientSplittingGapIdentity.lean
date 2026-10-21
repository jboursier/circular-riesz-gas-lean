/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingConvolutionEvent

/-!
# The gap representative and the telescoping identity

The gap representative `W^gap` of the displacement field and the first
claims of the gap part of Lemma 5.7: for every `U ∈ ℝ^N` with `u_{N+1} = u_1`,
`W·U = -∑_i W^gap_i N (u_{i+1} - u_i)`, and `∑_i W_i = 0`. The identity holds on the configuration
space `D_N = orderedDomain N`, which is the ambient set of the paper's fields.

The displacement field `W` is `gradWfield` of `GradientSplittingWindowDefs.lean`. The pair paths
are `gradPathIncr` and `gradSep` of that file. The edge `e ∈ {0, …, N-1}` runs from the particle `e`
to the particle `e + 1` (indices cyclic, `u_{N+1} = u_1`).
-/

@[expose] public section

open Finset
open scoped Classical

namespace Riesz1

noncomputable section

/-! ## Two facts about `gradZ` -/

/-- The divided difference is symmetric in its two arguments. -/
lemma gradZ_symm (ψ : ℝ → ℝ) (ℓ x y : ℝ) : gradZ ψ ℓ x y = gradZ ψ ℓ y x := by
  unfold gradZ
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => deriv ψ ((y + θ * (x - y)) / ℓ)) (1 : ℝ) (a := 0) (b := 1)
  simp only [sub_self, sub_zero] at h
  rw [← h]
  congr 1
  funext θ
  congr 1
  ring

/-- A periodic function has periodic derivative: `deriv ψ (u + c) = deriv ψ u`. -/
lemma deriv_add_period {ψ : ℝ → ℝ} {c : ℝ} (hψ : Function.Periodic ψ c) (u : ℝ) :
    deriv ψ (u + c) = deriv ψ u := by
  have h1 : (fun y => ψ (y + c)) = ψ := funext fun y => hψ y
  have h2 := deriv_comp_add_const ψ c u
  rw [h1] at h2
  exact h2.symm

/-- The divided difference is invariant under the simultaneous shift `x ↦ x + q`, `y ↦ y + q`
by an integer `q`, since `ψ` is `ℓ⁻¹`-periodic. -/
lemma gradZ_add_int {ψ : ℝ → ℝ} {ℓ : ℝ} (hψ : Function.Periodic ψ ℓ⁻¹) (q : ℤ) (x y : ℝ) :
    gradZ ψ ℓ (x + q) (y + q) = gradZ ψ ℓ x y := by
  unfold gradZ
  congr 1
  funext θ
  have hper : Function.Periodic ψ ((q : ℝ) * ℓ⁻¹) := hψ.int_mul q
  have e : (x + q + θ * (y + q - (x + q))) / ℓ = (x + θ * (y - x)) / ℓ + (q : ℝ) * ℓ⁻¹ := by
    ring
  rw [e, deriv_add_period hper]

/-! ## Monotonicity of the lifts on the ordered domain -/

/-- On a nonnegative label below `N`, the lift is the coordinate of the corresponding particle. -/
lemma gradLift_of_mem_range {N : ℕ+} {X : Fin (N : ℕ) → ℝ} {i : ℤ} (h0 : 0 ≤ i)
    (hN : i < (N : ℤ)) :
    gradLift N X i = X ⟨i.toNat, by omega⟩ := by
  unfold gradLift
  have hidx : gradIndex N i = ⟨i.toNat, by omega⟩ := by
    apply Fin.ext
    simp only [gradIndex]
    rw [Int.emod_eq_of_lt h0 hN]
  have hdiv : i / (N : ℤ) = 0 := Int.ediv_eq_zero_of_lt h0 hN
  rw [hidx, hdiv]
  simp

/-- The lift strictly increases from every label to the next one, on the ordered domain. -/
lemma gradLift_lt_succ {N : ℕ+} {X : Fin (N : ℕ) → ℝ} (hX : X ∈ orderedDomain N) (j : ℤ) :
    gradLift N X j < gradLift N X (j + 1) := by
  obtain ⟨hmono, h0, _, hlast⟩ := hX
  have hN : (0 : ℤ) < (N : ℤ) := by exact_mod_cast N.pos
  obtain ⟨i, hi⟩ : ∃ i, i = j % (N : ℤ) := ⟨_, rfl⟩
  have hj : j = i + (N : ℤ) * (j / (N : ℤ)) := by
    rw [hi, Int.emod_def]
    ring
  have hi0 : 0 ≤ i := by rw [hi]; exact Int.emod_nonneg _ hN.ne'
  have hiN : i < (N : ℤ) := by rw [hi]; exact Int.emod_lt_of_pos _ hN
  have hshift1 : gradLift N X (j + 1) = gradLift N X (i + 1) + ((j / (N : ℤ) : ℤ) : ℝ) := by
    have h := gradLift_add_mul N X (i + 1) (j / (N : ℤ))
    have e2 : i + 1 + (N : ℤ) * (j / (N : ℤ)) = j + 1 := by linarith [hj]
    rw [e2] at h
    exact h
  have hshift0 : gradLift N X j = gradLift N X i + ((j / (N : ℤ) : ℤ) : ℝ) := by
    have h := gradLift_add_mul N X i (j / (N : ℤ))
    rw [← hj] at h
    exact h
  rw [hshift1, hshift0]
  have key : gradLift N X i < gradLift N X (i + 1) ∨ i + 1 = (N : ℤ) := by
    rcases lt_or_eq_of_le (show i + 1 ≤ (N : ℤ) from by omega) with h | h
    · left
      rw [gradLift_of_mem_range hi0 hiN, gradLift_of_mem_range (by omega) h]
      apply hmono
      rw [Fin.mk_lt_mk]
      omega
    · right
      exact h
  rcases key with key | key
  · linarith
  · have hi' : i = (N : ℤ) - 1 := by omega
    have hA : gradLift N X (i + 1) = gradLift N X 0 + 1 := by
      have h := gradLift_add_mul N X 0 1
      rw [key]
      have e3 : (0 : ℤ) + (N : ℤ) * 1 = (N : ℤ) := by ring
      rw [e3] at h
      simpa using h
    rw [hA, gradLift_of_mem_range hi0 hiN]
    have hl := hlast ⟨i.toNat, by omega⟩
    have h0' : gradLift N X 0 = X ⟨0, N.pos⟩ := by
      rw [gradLift_of_mem_range (le_refl _) (by exact_mod_cast N.pos)]
      rfl
    rw [h0']
    have : X ⟨i.toNat, by omega⟩ < X ⟨0, N.pos⟩ + 1 := hl
    have hsum : X ⟨0, N.pos⟩ + 1 - X ⟨i.toNat, by omega⟩ > 0 := by linarith
    linarith

/-! ## Facts about the pair paths -/

/-- The chosen path from `l` to `m` has increment `k` with `|k| < N`, `k ≠ 0`, and `m - l - k` a
multiple of `N`, so that the path ends at a lift of `m`. -/
lemma gradPathIncr_spec {ℓ γ : ℝ} {N : ℕ+} {l m : ℤ} (hl : l ∈ gradLabels N ℓ γ)
    (hm : m ∈ gradLabels N ℓ γ) (hlm : l ≠ m) :
    -(N : ℤ) < gradPathIncr N ℓ γ l m ∧ gradPathIncr N ℓ γ l m < N ∧
      gradPathIncr N ℓ γ l m ≠ 0 ∧ ∃ c : ℤ, m - l - gradPathIncr N ℓ γ l m = N * c := by
  by_cases hP : GradPartial N ℓ γ
  · rw [mem_gradLabels_partial hP] at hl hm
    have h8 := gradPartial_eight_mul_lt hP
    have hk : gradPathIncr N ℓ γ l m = m - l := by
      unfold gradPathIncr
      simp only [hP, ↓reduceIte]
    rw [hk]
    exact ⟨by omega, by omega, by omega, ⟨0, by ring⟩⟩
  · rw [mem_gradLabels_full hP] at hl hm
    have hN : (0 : ℤ) < N := by exact_mod_cast N.pos
    have hdm : m - l = (m - l) % N + N * ((m - l) / N) := by
      rw [Int.emod_def]
      ring
    have hr0 : (m - l) % (N : ℤ) ≠ 0 := by
      intro h
      have e1 : m - l = N * ((m - l) / N) := by omega
      rcases lt_trichotomy ((m - l) / N) 0 with hc | hc | hc
      · have h1 : (N : ℤ) * ((m - l) / N) ≤ (N : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left (by omega) hN.le
        omega
      · rw [hc, mul_zero] at e1
        exact hlm (by omega)
      · have h1 : (N : ℤ) * 1 ≤ (N : ℤ) * ((m - l) / N) :=
          mul_le_mul_of_nonneg_left (by omega) hN.le
        omega
    have hr_nn : 0 ≤ (m - l) % (N : ℤ) := Int.emod_nonneg _ hN.ne'
    have hr_lt : (m - l) % (N : ℤ) < N := Int.emod_lt_of_pos _ hN
    have hN2 : (2 : ℤ) ≤ N := by omega
    unfold gradPathIncr
    simp only [hP, ↓reduceIte]
    split_ifs with h1 h2 h3
    · exact ⟨by omega, by omega, hr0, ⟨(m - l) / N, by omega⟩⟩
    · exact ⟨by omega, by omega, by omega, ⟨(m - l) / N + 1, by rw [mul_add, mul_one]; omega⟩⟩
    · exact ⟨by omega, by omega, by omega, ⟨(m - l) / N, by omega⟩⟩
    · exact ⟨by omega, by omega, by omega, ⟨(m - l) / N + 1, by rw [mul_add, mul_one]; omega⟩⟩

/-- The path increments of the two orientations of a pair are opposite. -/
lemma gradPathIncr_antisymm {ℓ γ : ℝ} {N : ℕ+} {l m : ℤ} (hl : l ∈ gradLabels N ℓ γ)
    (hm : m ∈ gradLabels N ℓ γ) (hlm : l ≠ m) :
    gradPathIncr N ℓ γ m l = -gradPathIncr N ℓ γ l m := by
  by_cases hP : GradPartial N ℓ γ
  · unfold gradPathIncr
    simp only [hP, ↓reduceIte]
    ring
  · rw [mem_gradLabels_full hP] at hl hm
    have hN : (0 : ℤ) < N := by exact_mod_cast N.pos
    have hC : l % (N : ℤ) = l := Int.emod_eq_of_lt (by omega) (by omega)
    have hD : m % (N : ℤ) = m := Int.emod_eq_of_lt (by omega) (by omega)
    unfold gradPathIncr
    simp only [hP, ↓reduceIte]
    rcases lt_or_gt_of_ne hlm with h | h
    · have hA : (m - l) % (N : ℤ) = m - l := Int.emod_eq_of_lt (by omega) (by omega)
      have hB : (l - m) % (N : ℤ) = l - m + N := by
        rw [← Int.add_mul_emod_self_left (l - m) (N : ℤ) 1, mul_one,
          Int.emod_eq_of_lt (by omega) (by omega)]
      rw [hA, hB, hC, hD]
      split_ifs <;> omega
    · have hA : (m - l) % (N : ℤ) = m - l + N := by
        rw [← Int.add_mul_emod_self_left (m - l) (N : ℤ) 1, mul_one,
          Int.emod_eq_of_lt (by omega) (by omega)]
      have hB : (l - m) % (N : ℤ) = l - m := Int.emod_eq_of_lt (by omega) (by omega)
      rw [hA, hB, hC, hD]
      split_ifs <;> omega

/-! ## Lifts at distance less than the period -/

/-- Two distinct labels at cyclic distance less than `N` have lifts at distance in `(0, 1)`. -/
lemma gradLift_sub_abs_lt_one {N : ℕ+} {X : Fin (N : ℕ) → ℝ} (hX : X ∈ orderedDomain N)
    {a b : ℤ} (hab : a ≠ b) (hk : |b - a| < (N : ℤ)) :
    0 < |gradLift N X b - gradLift N X a| ∧ |gradLift N X b - gradLift N X a| < 1 := by
  have hmono : StrictMono (gradLift N X) := strictMono_int_of_lt_succ (gradLift_lt_succ hX)
  rcases lt_or_gt_of_ne hab with h | h
  · have h1 : gradLift N X a < gradLift N X b := hmono h
    have hb : b < a + N := by
      rw [abs_lt] at hk
      omega
    have h2 : gradLift N X b < gradLift N X (a + N) := hmono hb
    have h3 : gradLift N X (a + N) = gradLift N X a + 1 := by
      have h := gradLift_add_mul N X a 1
      rw [mul_one, Int.cast_one] at h
      exact h
    rw [abs_of_pos (by linarith)]
    constructor <;> linarith
  · have h1 : gradLift N X b < gradLift N X a := hmono h
    have ha : a < b + N := by
      rw [abs_lt] at hk
      omega
    have h2 : gradLift N X a < gradLift N X (b + N) := hmono ha
    have h3 : gradLift N X (b + N) = gradLift N X b + 1 := by
      have h := gradLift_add_mul N X b 1
      rw [mul_one, Int.cast_one] at h
      exact h
    rw [abs_of_neg (by linarith)]
    constructor <;> linarith

/-! ## The gap representative -/

/-- The pair term `P(l,m) = Z(x_l, x_l + r_{lm}) (h'(r_{lm}) - h'(k_{lm}/N))`: the summand of
`W_l` over the partner `m`, with the path lift as second argument. -/
def gradPairTerm (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) (l m : ℤ) : ℝ :=
  gradZ ψ ℓ (gradLift N X l) (gradLift N X l + gradSep N ℓ γ X l m) *
    (deriv (gradKernelH s) (gradSep N ℓ γ X l m) -
      deriv (gradKernelH s) ((gradPathIncr N ℓ γ l m : ℝ) / N))

/-- The edge `e` (from the residue `e` to `e + 1`) lies on the positive path from `l` to `m`: the
path visits the edges `l + t → l + t + 1` for `0 ≤ t < k_{lm}`, taken modulo `N`. -/
def gradEdgeOnPath (N : ℕ+) (ℓ γ : ℝ) (l m e : ℤ) : Prop :=
  ∃ t : ℕ, (t : ℤ) < gradPathIncr N ℓ γ l m ∧ (l + t) % (N : ℤ) = e

open scoped Classical in
/-- The gap representative `W^gap_e`, at the edge `e` for the residues
`e ∈ {0, …, N-1}`: the sum over ordered pairs `(l, m)` of distinct labels of the window with
positive path `k_{lm} > 0` whose path contains the edge `e`. Each unordered pair is counted once,
in its positive orientation. -/
def gradWgap (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) (e : ℤ) : ℝ :=
  -2 * (N : ℝ) ^ (-1 - s) * ∑ l ∈ gradLabels N ℓ γ, ∑ m ∈ (gradLabels N ℓ γ).erase l,
    if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m e then
      gradPairTerm s ψ N ℓ γ X l m
    else 0

/-! ## The pair terms are antisymmetric -/

/-- The derivative of the modified kernel is odd off the integers. -/
lemma deriv_gradKernelH_neg {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {r : ℝ} (h0 : 0 < |r|)
    (h1 : |r| < 1) : deriv (gradKernelH s) (-r) = -deriv (gradKernelH s) r := by
  have h := gradSplit_iteratedDeriv_one_gradKernelH_neg s hs0 hs1 (gradSplit_coe_ne_zero h0 h1)
  rw [iteratedDeriv_one] at h
  exact h

/-- The reversed separation is the negative separation. -/
lemma gradSep_antisymm {ℓ γ : ℝ} {N : ℕ+} (X : Fin (N : ℕ) → ℝ) {l m : ℤ}
    (hl : l ∈ gradLabels N ℓ γ) (hm : m ∈ gradLabels N ℓ γ) (hlm : l ≠ m) :
    gradSep N ℓ γ X m l = -gradSep N ℓ γ X l m := by
  obtain ⟨_, _, _, c, hc⟩ := gradPathIncr_spec hl hm hlm
  have hanti := gradPathIncr_antisymm hl hm hlm
  have e1 : gradLift N X (m + gradPathIncr N ℓ γ m l) = gradLift N X l + c := by
    rw [hanti, show m + -gradPathIncr N ℓ γ l m = l + N * c by linarith]
    exact gradLift_add_mul N X l c
  have e2 : gradLift N X m = gradLift N X (l + gradPathIncr N ℓ γ l m) + c := by
    have h := gradLift_add_mul N X (l + gradPathIncr N ℓ γ l m) c
    rw [show l + gradPathIncr N ℓ γ l m + N * c = m by linarith] at h
    exact h
  unfold gradSep
  rw [e1, e2]
  ring

/-- The pair term of `W_l` is antisymmetric: `P(m,l) = -P(l,m)`, with
`P(l,m) = Z(x_l, x_l + r_{lm}) (h'(r_{lm}) - h'(k_{lm}/N))`. -/
lemma gradPairTerm_antisymm {s ℓ γ : ℝ} {ψ : ℝ → ℝ} (hψ : Function.Periodic ψ ℓ⁻¹)
    (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+} {X : Fin (N : ℕ) → ℝ} (hX : X ∈ orderedDomain N)
    {l m : ℤ} (hl : l ∈ gradLabels N ℓ γ) (hm : m ∈ gradLabels N ℓ γ) (hlm : l ≠ m) :
    gradPairTerm s ψ N ℓ γ X m l = -gradPairTerm s ψ N ℓ γ X l m := by
  obtain ⟨hk1, hk2, hk0, c, hc⟩ := gradPathIncr_spec hl hm hlm
  have hanti := gradPathIncr_antisymm hl hm hlm
  have hsep := gradSep_antisymm X hl hm hlm
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hkZ : -(N : ℤ) < gradPathIncr N ℓ γ l m ∧ gradPathIncr N ℓ γ l m < N := ⟨hk1, hk2⟩
  -- the separation `r_{lm}` lies in `(0, 1)` in absolute value
  have hr := gradLift_sub_abs_lt_one hX (a := l) (b := l + gradPathIncr N ℓ γ l m)
    (by omega) (by
      have : |(l + gradPathIncr N ℓ γ l m) - l| = |gradPathIncr N ℓ γ l m| := by ring_nf
      rw [this, abs_lt]
      constructor <;> omega)
  have hkN : 0 < |((gradPathIncr N ℓ γ l m : ℤ) : ℝ) / N| ∧
      |((gradPathIncr N ℓ γ l m : ℤ) : ℝ) / N| < 1 := by
    have hk0R : (0 : ℝ) < |((gradPathIncr N ℓ γ l m : ℤ) : ℝ)| := by
      rw [abs_pos]
      exact_mod_cast hk0
    have hk1R : |((gradPathIncr N ℓ γ l m : ℤ) : ℝ)| < N := by
      rw [abs_lt]
      constructor <;> exact_mod_cast (by omega)
    rw [abs_div, abs_of_pos hN]
    exact ⟨div_pos hk0R hN, (div_lt_one hN).mpr hk1R⟩
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
  have hsepabs : 0 < |gradSep N ℓ γ X l m| ∧ |gradSep N ℓ γ X l m| < 1 := by
    unfold gradSep
    exact hr
  rw [deriv_gradKernelH_neg hs0 hs1 hsepabs.1 hsepabs.2,
    deriv_gradKernelH_neg hs0 hs1 hkN.1 hkN.2]
  ring

/-! ## Telescoping along a path -/

/-- The increment `u_{e+1} - u_e` of a vector along the cyclic edge `e`. -/
def gradEdgeDiff (N : ℕ+) (U : Fin (N : ℕ) → ℝ) (e : ℤ) : ℝ :=
  U (gradIndex N (e + 1)) - U (gradIndex N e)

/-- Labels differing by a multiple of `N` have the same particle. -/
lemma gradIndex_eq_of_sub {N : ℕ+} {a b c : ℤ} (h : a = b + (N : ℤ) * c) :
    gradIndex N a = gradIndex N b := by
  apply Fin.ext
  simp only [gradIndex]
  rw [h, Int.add_mul_emod_self_left]

/-- The edge increments are periodic in the label. -/
lemma gradEdgeDiff_add_mul (N : ℕ+) (U : Fin (N : ℕ) → ℝ) (e c : ℤ) :
    gradEdgeDiff N U (e + (N : ℤ) * c) = gradEdgeDiff N U e := by
  have h1 : gradIndex N (e + (N : ℤ) * c + 1) = gradIndex N (e + 1) :=
    gradIndex_eq_of_sub (c := c) (by ring)
  have h2 : gradIndex N (e + (N : ℤ) * c) = gradIndex N e :=
    gradIndex_eq_of_sub (c := c) (by ring)
  unfold gradEdgeDiff
  rw [h1, h2]

/-- Telescoping of a vector along `K` consecutive edges from `l`. -/
lemma gradEdgeDiff_telescope {N : ℕ+} (U : Fin (N : ℕ) → ℝ) (l : ℤ) (K : ℕ) :
    U (gradIndex N (l + K)) - U (gradIndex N l) =
      ∑ t ∈ Finset.range K, gradEdgeDiff N U (l + t) := by
  have h := Finset.sum_range_sub (fun t : ℕ => U (gradIndex N (l + t))) K
  have hterm : ∀ t : ℕ, U (gradIndex N (l + ((t + 1 : ℕ) : ℤ))) - U (gradIndex N (l + t)) =
      gradEdgeDiff N U (l + t) := by
    intro t
    unfold gradEdgeDiff
    rw [show l + ((t + 1 : ℕ) : ℤ) = l + t + 1 by push_cast; ring]
  simp only [Nat.cast_zero, add_zero] at h
  rw [Finset.sum_congr rfl (fun t _ => hterm t)] at h
  exact h.symm

/-- Along a positive path from `l` to `m`, `u_l - u_m` is minus the sum of the edge increments. -/
lemma gradPath_telescope {ℓ γ : ℝ} {N : ℕ+} (U : Fin (N : ℕ) → ℝ) {l m : ℤ}
    (hk : 0 < gradPathIncr N ℓ γ l m) (c : ℤ) (hc : m - l - gradPathIncr N ℓ γ l m = N * c) :
    U (gradIndex N l) - U (gradIndex N m) =
      -∑ t ∈ Finset.range (gradPathIncr N ℓ γ l m).toNat, gradEdgeDiff N U (l + t) := by
  have hm : gradIndex N m = gradIndex N (l + ((gradPathIncr N ℓ γ l m).toNat : ℤ)) := by
    apply gradIndex_eq_of_sub (c := c)
    rw [Int.toNat_of_nonneg hk.le]
    linarith
  rw [hm]
  have ht := gradEdgeDiff_telescope U l (gradPathIncr N ℓ γ l m).toNat
  linarith

/-! ## Edge sums over a path -/

/-- A sum over `t < K` of an indicator that holds for at most one `t` is the indicator of the
existence of such `t`. -/
lemma sum_range_ite_unique {K : ℕ} (P : ℕ → Prop) [DecidablePred P] (x : ℝ)
    (huniq : ∀ t t' : ℕ, t < K → t' < K → P t → P t' → t = t') :
    ∑ t ∈ Finset.range K, (if P t then x else 0) = if ∃ t, t < K ∧ P t then x else 0 := by
  by_cases h : ∃ t, t < K ∧ P t
  · obtain ⟨t0, ht0, hP0⟩ := h
    have hex : ∃ t, t < K ∧ P t := ⟨t0, ht0, hP0⟩
    simp only [hex, ↓reduceIte]
    rw [Finset.sum_eq_single t0]
    · simp only [hP0, ↓reduceIte]
    · intro b hb hne
      rw [ite_eq_right_iff]
      intro hPb
      exact absurd (huniq b t0 (Finset.mem_range.mp hb) ht0 hPb hP0) hne
    · intro h'
      exact absurd (Finset.mem_range.mpr ht0) h'
  · simp only [h, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro t ht
    rw [ite_eq_right_iff]
    intro hP
    exact absurd ⟨t, Finset.mem_range.mp ht, hP⟩ h

/-- Two integers at distance less than `N` with the same residue are equal. -/
lemma eq_of_emod_eq_of_abs_lt {N : ℤ} (hN : 0 < N) {a b : ℤ} (h : a % N = b % N)
    (hab : |a - b| < N) : a = b := by
  have hdvd : N ∣ a - b := Int.dvd_of_emod_eq_zero (by
    rw [Int.sub_emod, h, sub_self, Int.zero_emod])
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : c = 0 := by
    rw [abs_lt] at hab
    rcases lt_trichotomy c 0 with h1 | h1 | h1
    · have : N * c ≤ N * (-1) := mul_le_mul_of_nonneg_left (by omega) hN.le
      omega
    · exact h1
    · have : N * 1 ≤ N * c := mul_le_mul_of_nonneg_left (by omega) hN.le
      omega
  rw [hc0, mul_zero] at hc
  omega

/-- The edge increments along a positive path of length `< N` are summed over the edges `e` of the
cycle that the path contains. -/
lemma gradEdge_expand {ℓ γ : ℝ} {N : ℕ+} (U : Fin (N : ℕ) → ℝ) {l m : ℤ}
    (hk' : gradPathIncr N ℓ γ l m < N) :
    ∑ t ∈ Finset.range (gradPathIncr N ℓ γ l m).toNat, gradEdgeDiff N U (l + t) =
      ∑ e ∈ Finset.Ico (0 : ℤ) N,
        if gradEdgeOnPath N ℓ γ l m e then gradEdgeDiff N U e else 0 := by
  have hN : (0 : ℤ) < (N : ℤ) := by exact_mod_cast N.pos
  have hdiv : ∀ j : ℤ, gradEdgeDiff N U j = gradEdgeDiff N U (j % (N : ℤ)) := by
    intro j
    have hj : j = j % (N : ℤ) + (N : ℤ) * (j / (N : ℤ)) := by
      rw [Int.emod_def]
      ring
    have h := gradEdgeDiff_add_mul N U (j % (N : ℤ)) (j / (N : ℤ))
    rw [← hj] at h
    exact h
  have hmem : ∀ j : ℤ, j % (N : ℤ) ∈ Finset.Ico (0 : ℤ) N := by
    intro j
    rw [Finset.mem_Ico]
    exact ⟨Int.emod_nonneg _ hN.ne', Int.emod_lt_of_pos _ hN⟩
  have hsum : ∑ t ∈ Finset.range (gradPathIncr N ℓ γ l m).toNat, gradEdgeDiff N U (l + t) =
      ∑ t ∈ Finset.range (gradPathIncr N ℓ γ l m).toNat, gradEdgeDiff N U ((l + t) % (N : ℤ)) :=
    Finset.sum_congr rfl (fun t _ => hdiv (l + t))
  rw [hsum]
  have hsw : ∀ t ∈ Finset.range (gradPathIncr N ℓ γ l m).toNat,
      gradEdgeDiff N U ((l + t) % (N : ℤ)) =
        ∑ e ∈ Finset.Ico (0 : ℤ) N,
          if (l + t) % (N : ℤ) = e then gradEdgeDiff N U e else 0 := by
    intro t _
    rw [Finset.sum_ite_eq]
    simp only [hmem _, ↓reduceIte]
  rw [Finset.sum_congr rfl hsw, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have hKk : ∀ t : ℕ, t < (gradPathIncr N ℓ γ l m).toNat ↔ (t : ℤ) < gradPathIncr N ℓ γ l m :=
    fun t => Int.lt_toNat
  have hiff : (∃ t : ℕ, t < (gradPathIncr N ℓ γ l m).toNat ∧ (l + (t : ℤ)) % (N : ℤ) = e) ↔
      gradEdgeOnPath N ℓ γ l m e := by
    constructor
    · rintro ⟨t, ht, hte⟩
      exact ⟨t, (hKk t).mp ht, hte⟩
    · rintro ⟨t, ht, hte⟩
      exact ⟨t, (hKk t).mpr ht, hte⟩
  have huniq : ∀ t t' : ℕ, t < (gradPathIncr N ℓ γ l m).toNat →
      t' < (gradPathIncr N ℓ γ l m).toNat → (l + (t : ℤ)) % (N : ℤ) = e →
      (l + (t' : ℤ)) % (N : ℤ) = e → t = t' := by
    intro t t' ht ht' hte hte'
    have hlt : (t : ℤ) < N := by
      have := (hKk t).mp ht
      omega
    have hlt' : (t' : ℤ) < N := by
      have := (hKk t').mp ht'
      omega
    have hab : |(l + (t : ℤ)) - (l + (t' : ℤ))| < N := by
      rw [abs_lt]
      constructor <;> omega
    have := eq_of_emod_eq_of_abs_lt hN (hte.trans hte'.symm) hab
    omega
  rw [sum_range_ite_unique (fun t : ℕ => (l + (t : ℤ)) % (N : ℤ) = e) (gradEdgeDiff N U e) huniq]
  exact if_congr hiff rfl rfl

/-! ## The displacement identity -/

/-- The pair coefficient `Q(l,m) = P(l,m)` for `l ≠ m`, and `0` on the diagonal. -/
def gradQ (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) (l m : ℤ) : ℝ :=
  if l = m then 0 else gradPairTerm s ψ N ℓ γ X l m

/-- The path increment of a label with itself is zero. -/
lemma gradPathIncr_self (ℓ γ : ℝ) (N : ℕ+) (l : ℤ) : gradPathIncr N ℓ γ l l = 0 := by
  have hN : (0 : ℤ) < N := by exact_mod_cast N.pos
  unfold gradPathIncr
  by_cases hP : GradPartial N ℓ γ
  · simp only [hP, ↓reduceIte, sub_self]
  · simp only [hP, ↓reduceIte, sub_self, Int.zero_emod, mul_zero]
    simp only [hN, ↓reduceIte]

/-- The coefficient `Q` is antisymmetric on the window. -/
lemma gradQ_antisymm {s γ ℓ : ℝ} {ψ : ℝ → ℝ} (hψ : Function.Periodic ψ ℓ⁻¹)
    (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+} {X : Fin (N : ℕ) → ℝ} (hX : X ∈ orderedDomain N)
    {l m : ℤ} (hl : l ∈ gradLabels N ℓ γ) (hm : m ∈ gradLabels N ℓ γ) :
    gradQ s ψ N ℓ γ X m l = -gradQ s ψ N ℓ γ X l m := by
  unfold gradQ
  by_cases hlm : l = m
  · subst hlm
    simp
  · have hml : m ≠ l := fun h => hlm h.symm
    simp only [hml, hlm, ↓reduceIte]
    exact gradPairTerm_antisymm hψ hs0 hs1 hX hl hm hlm

/-- The positive-orientation part `Q(l,m)(u_l - u_m)` over pairs whose path runs from `l` to `m`
(zero when the increment `k_{lm}` is not positive). -/
def gradG (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) (U : Fin (N : ℕ) → ℝ)
    (l m : ℤ) : ℝ :=
  if 0 < gradPathIncr N ℓ γ l m then
    gradQ s ψ N ℓ γ X l m * (U (gradIndex N l) - U (gradIndex N m))
  else 0

/-- The displacement identity of the gap part of Lemma 5.7, first claim: for every
`U ∈ ℝ^N` (with the cyclic convention `u_{N+1} = u_1`) on the configuration space `D_N`,
`W · U = -∑_i W^gap_i N (u_{i+1} - u_i)`, where the sum runs over the cyclic edges. -/
theorem gradient_splitting_gap_identity {s γ ℓ : ℝ} {N : ℕ+} {ψ : ℝ → ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hψ : Function.Periodic ψ ℓ⁻¹) {X : Fin (N : ℕ) → ℝ}
    (hX : X ∈ orderedDomain N) (U : Fin (N : ℕ) → ℝ) :
    ∑ k : Fin (N : ℕ), gradWfield s ψ N ℓ γ X k * U k =
      -∑ e ∈ Finset.Ico (0 : ℤ) N, gradWgap s ψ N ℓ γ X e * (N : ℝ) * gradEdgeDiff N U e := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  set I := gradLabels N ℓ γ with hIdef
  -- Step A: the fibres of the particle map are the labels of the window
  have hA : ∑ k : Fin (N : ℕ), gradWfield s ψ N ℓ γ X k * U k =
      ∑ i ∈ I, gradWlab s ψ N ℓ γ X i * U (gradIndex N i) := by
    show ∑ k : Fin (N : ℕ), (∑ i ∈ I.filter (fun i => gradIndex N i = k),
        gradWlab s ψ N ℓ γ X i) * U k = _
    have h1 : ∀ k : Fin (N : ℕ),
        (∑ i ∈ I.filter (fun i => gradIndex N i = k), gradWlab s ψ N ℓ γ X i) * U k =
          ∑ i ∈ I.filter (fun i => gradIndex N i = k),
            gradWlab s ψ N ℓ γ X i * U (gradIndex N i) := by
      intro k
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    simp only [h1]
    exact Finset.sum_fiberwise I (gradIndex N)
      (fun i => gradWlab s ψ N ℓ γ X i * U (gradIndex N i))
  -- Step B: the field `W_l` as a full sum over the window with the diagonal removed
  have hB : ∀ l ∈ I, gradWlab s ψ N ℓ γ X l =
      -2 * (N : ℝ) ^ (-s) * ∑ m ∈ I, gradQ s ψ N ℓ γ X l m := by
    intro l hl
    have hsum : ∑ m ∈ I, gradQ s ψ N ℓ γ X l m =
        ∑ m ∈ I.erase l, gradPairTerm s ψ N ℓ γ X l m := by
      rw [← Finset.sum_erase_add I _ hl]
      simp only [gradQ, ite_true, add_zero]
      apply Finset.sum_congr rfl
      intro m hm
      have hne : l ≠ m := fun h => (Finset.ne_of_mem_erase hm) h.symm
      simp only [hne, ↓reduceIte]
    rw [hsum]
    rfl
  -- Step C: `W · U` is `-2N^{-s}` times the double sum `S`
  set S : ℝ := ∑ l ∈ I, ∑ m ∈ I, gradQ s ψ N ℓ γ X l m * U (gradIndex N l) with hS
  have hC : ∑ i ∈ I, gradWlab s ψ N ℓ γ X i * U (gradIndex N i) =
      -2 * (N : ℝ) ^ (-s) * S := by
    rw [hS, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hB i hi]
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  -- Step D: the double sum `S` equals the sum of the positive-orientation parts
  have hswap : ∑ l ∈ I, ∑ m ∈ I, gradQ s ψ N ℓ γ X l m * U (gradIndex N m) = -S := by
    rw [hS]
    calc ∑ l ∈ I, ∑ m ∈ I, gradQ s ψ N ℓ γ X l m * U (gradIndex N m)
        = ∑ m ∈ I, ∑ l ∈ I, gradQ s ψ N ℓ γ X l m * U (gradIndex N m) := Finset.sum_comm
      _ = ∑ l ∈ I, ∑ m ∈ I, gradQ s ψ N ℓ γ X m l * U (gradIndex N l) := rfl
      _ = ∑ l ∈ I, ∑ m ∈ I, -(gradQ s ψ N ℓ γ X l m * U (gradIndex N l)) := by
          apply Finset.sum_congr rfl
          intro l hl
          apply Finset.sum_congr rfl
          intro m hm
          rw [gradQ_antisymm hψ hs0 hs1 hX hl hm]
          ring
      _ = -∑ l ∈ I, ∑ m ∈ I, gradQ s ψ N ℓ γ X l m * U (gradIndex N l) := by
          simp only [Finset.sum_neg_distrib]
  have h2S : ∑ l ∈ I, ∑ m ∈ I, gradQ s ψ N ℓ γ X l m * (U (gradIndex N l) - U (gradIndex N m))
      = 2 * S := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hswap, ← hS]
    ring
  have hpt : ∀ l ∈ I, ∀ m ∈ I, gradQ s ψ N ℓ γ X l m * (U (gradIndex N l) - U (gradIndex N m)) =
      gradG s ψ N ℓ γ X U l m + gradG s ψ N ℓ γ X U m l := by
    intro l hl m hm
    by_cases hlm : l = m
    · subst hlm
      simp [gradG, gradPathIncr_self, gradQ]
    · have hk := gradPathIncr_antisymm hl hm hlm
      have hk0 := (gradPathIncr_spec hl hm hlm).2.2.1
      have hQ := gradQ_antisymm hψ hs0 hs1 hX hl hm
      unfold gradG
      rcases lt_or_gt_of_ne hk0 with hneg | hpos
      · have hpos' : 0 < gradPathIncr N ℓ γ m l := by rw [hk]; omega
        have hnot : ¬ (0 < gradPathIncr N ℓ γ l m) := by omega
        simp only [hnot, hpos', ↓reduceIte, hQ]
        ring
      · have hnot : ¬ (0 < gradPathIncr N ℓ γ m l) := by rw [hk]; omega
        simp only [hpos, hnot, ↓reduceIte]
        ring
  have hGG : ∑ l ∈ I, ∑ m ∈ I, gradQ s ψ N ℓ γ X l m * (U (gradIndex N l) - U (gradIndex N m))
      = 2 * ∑ l ∈ I, ∑ m ∈ I, gradG s ψ N ℓ γ X U l m := by
    rw [Finset.sum_congr rfl (fun l hl => Finset.sum_congr rfl (fun m hm => hpt l hl m hm))]
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun l m => gradG s ψ N ℓ γ X U m l)]
    ring
  have hSG : S = ∑ l ∈ I, ∑ m ∈ I, gradG s ψ N ℓ γ X U l m := by
    linarith [h2S, hGG]
  -- Step E: the positive path expands over the edges it contains
  set E : ℤ → ℝ := fun e => ∑ l ∈ I, ∑ m ∈ I,
    if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m e then
      gradQ s ψ N ℓ γ X l m else 0 with hEdef
  have hGedge : ∀ l ∈ I, ∀ m ∈ I, gradG s ψ N ℓ γ X U l m =
      ∑ e ∈ Finset.Ico (0 : ℤ) N,
        if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m e then
          -(gradEdgeDiff N U e * gradQ s ψ N ℓ γ X l m)
        else 0 := by
    intro l hl m hm
    unfold gradG
    by_cases hk : 0 < gradPathIncr N ℓ γ l m
    · have hlm : l ≠ m := by
        rintro rfl
        rw [gradPathIncr_self] at hk
        exact lt_irrefl 0 hk
      obtain ⟨_, hk', _, c, hc⟩ := gradPathIncr_spec hl hm hlm
      have htel := gradPath_telescope U hk c hc
      rw [gradEdge_expand U hk'] at htel
      simp only [hk, ↓reduceIte]
      rw [htel, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : gradEdgeOnPath N ℓ γ l m e
      · simp only [he, and_self, ↓reduceIte]
        ring
      · simp only [he, and_false, ↓reduceIte]
        ring
    · simp only [hk, ↓reduceIte]
      symm
      apply Finset.sum_eq_zero
      intro e _
      simp only [false_and, ↓reduceIte]
  have hperE : ∀ e : ℤ, ∑ l ∈ I, ∑ m ∈ I,
      (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m e then
        -(gradEdgeDiff N U e * gradQ s ψ N ℓ γ X l m) else 0) = -(gradEdgeDiff N U e * E e) := by
    intro e
    have hEe : gradEdgeDiff N U e * E e = ∑ l ∈ I, ∑ m ∈ I,
        gradEdgeDiff N U e * (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m e then
          gradQ s ψ N ℓ γ X l m else 0) := by
      simp only [hEdef, Finset.mul_sum]
    rw [hEe, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m _
    split_ifs <;> ring
  have hEall : ∑ l ∈ I, ∑ m ∈ I, gradG s ψ N ℓ γ X U l m =
      -∑ e ∈ Finset.Ico (0 : ℤ) N, gradEdgeDiff N U e * E e := by
    calc ∑ l ∈ I, ∑ m ∈ I, gradG s ψ N ℓ γ X U l m
        = ∑ l ∈ I, ∑ m ∈ I, ∑ e ∈ Finset.Ico (0 : ℤ) N,
            (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m e then
              -(gradEdgeDiff N U e * gradQ s ψ N ℓ γ X l m) else 0) := by
          apply Finset.sum_congr rfl
          intro l hl
          apply Finset.sum_congr rfl
          intro m hm
          exact hGedge l hl m hm
      _ = ∑ l ∈ I, ∑ e ∈ Finset.Ico (0 : ℤ) N, ∑ m ∈ I,
            (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m e then
              -(gradEdgeDiff N U e * gradQ s ψ N ℓ γ X l m) else 0) :=
          Finset.sum_congr rfl (fun l _ => Finset.sum_comm)
      _ = ∑ e ∈ Finset.Ico (0 : ℤ) N, ∑ l ∈ I, ∑ m ∈ I,
            (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m e then
              -(gradEdgeDiff N U e * gradQ s ψ N ℓ γ X l m) else 0) := Finset.sum_comm
      _ = ∑ e ∈ Finset.Ico (0 : ℤ) N, -(gradEdgeDiff N U e * E e) :=
          Finset.sum_congr rfl (fun e _ => hperE e)
      _ = -∑ e ∈ Finset.Ico (0 : ℤ) N, gradEdgeDiff N U e * E e := by
          rw [← Finset.sum_neg_distrib]
  -- Step F: the gap representative is `-2N^{-1-s}` times the edge sum `E`
  have hWE : ∀ e : ℤ, gradWgap s ψ N ℓ γ X e = -2 * (N : ℝ) ^ (-1 - s) * E e := by
    intro e
    have hline : ∀ l ∈ I, ∑ m ∈ I.erase l,
        (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m e then
          gradPairTerm s ψ N ℓ γ X l m else 0) =
        ∑ m ∈ I, (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m e then
          gradQ s ψ N ℓ γ X l m else 0) := by
      intro l hl
      rw [← Finset.sum_erase_add I _ hl]
      simp only [gradPathIncr_self, lt_irrefl, false_and, ↓reduceIte, add_zero]
      apply Finset.sum_congr rfl
      intro m hm
      have hne : l ≠ m := fun h => (Finset.ne_of_mem_erase hm) h.symm
      simp only [gradQ, hne, ↓reduceIte]
    have hE : E e = ∑ l ∈ I, ∑ m ∈ I, (if 0 < gradPathIncr N ℓ γ l m ∧
        gradEdgeOnPath N ℓ γ l m e then gradQ s ψ N ℓ γ X l m else 0) := by
      simp only [hEdef]
    show -2 * (N : ℝ) ^ (-1 - s) * ∑ l ∈ I, ∑ m ∈ I.erase l,
        (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m e then
          gradPairTerm s ψ N ℓ γ X l m else 0) = _
    rw [Finset.sum_congr rfl hline, hE]
  -- Step G: assemble, using `N^{-s} = N^{-1-s} N`
  have hpow : (N : ℝ) ^ (-s) = (N : ℝ) ^ (-1 - s) * N := by
    rw [← Real.rpow_add_one hN0]
    congr 1
    ring
  rw [hA, hC, hSG, hEall]
  simp only [hWE, hpow]
  simp only [mul_neg, neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib, neg_neg]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- The field `W` has zero total sum on `D_N`: `∑_i W_i = 0` (gap part of Lemma 5.7,
second claim), by the identity with `U = 1`. -/
theorem gradWfield_sum_eq_zero {s γ ℓ : ℝ} {N : ℕ+} {ψ : ℝ → ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hψ : Function.Periodic ψ ℓ⁻¹) {X : Fin (N : ℕ) → ℝ}
    (hX : X ∈ orderedDomain N) :
    ∑ k : Fin (N : ℕ), gradWfield s ψ N ℓ γ X k = 0 := by
  have h := gradient_splitting_gap_identity (γ := γ) hs0 hs1 hψ hX (fun _ => 1)
  simpa [gradEdgeDiff] using h

/-- In a partial window the gap representative vanishes on every edge outside `I`: a path from `l`
to `m` inside `I` uses only the edges `j → j+1` with `-n ≤ j < n`. -/
lemma gradWgap_eq_zero_of_partial {s γ ℓ : ℝ} {N : ℕ+} (ψ : ℝ → ℝ) (X : Fin (N : ℕ) → ℝ)
    (hP : GradPartial N ℓ γ) (e : ℤ)
    (he : ∀ j : ℤ, -⌊gradM N ℓ γ⌋ ≤ j → j < ⌊gradM N ℓ γ⌋ → j % (N : ℤ) ≠ e) :
    gradWgap s ψ N ℓ γ X e = 0 := by
  unfold gradWgap
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro l hl
  apply Finset.sum_eq_zero
  intro m hm
  split_ifs with hc
  · exfalso
    obtain ⟨hk, t, ht, hte⟩ := hc
    have hmI : m ∈ gradLabels N ℓ γ := Finset.mem_of_mem_erase hm
    have hlI := (mem_gradLabels_partial hP l).mp hl
    have hmI' := (mem_gradLabels_partial hP m).mp hmI
    have hk' : gradPathIncr N ℓ γ l m = m - l := by
      unfold gradPathIncr
      simp only [hP, ↓reduceIte]
    rw [hk'] at hk ht
    exact he (l + t) (by omega) (by omega) hte
  · rfl

end

end Riesz1
end
