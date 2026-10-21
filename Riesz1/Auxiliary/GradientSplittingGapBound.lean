/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingGapPath
public import Riesz1.Auxiliary.GradientSplittingGapKernel
public import Riesz1.Auxiliary.GradientSplittingZBounds
public import Riesz1.Auxiliary.GradientSplittingZDifferences

/-!
# The pointwise bound on the gap representative

The gap part of Lemma 5.7, the first estimate
`|W^gap_i| ≤ C C_0 K^{κε} ∑_{j ∈ I} w_1(x_j/ℓ) (1 + d(i,j))^{-(1+s/2)}` on the event `𝒜_{ε,γ}`.

Each positive pair `(l, m)` contributes `Z(x_l, x_l + r_{lm}) (h'(r_{lm}) - h'(k_{lm}/N))`.
The divided difference `Z` is bounded by its two endpoint weights (`gradZavg_abs_le`), and the kernel
increment by `gradient_splitting_kernel` on the event (`gapKernel_deriv_pair_bound`). The path
counting of `GradientSplittingGapPath.lean` then sums over the pairs whose path contains the edge.
-/

@[expose] public section

open Finset
open scoped ContDiff
open scoped Classical

namespace Riesz1

noncomputable section

/-! ## The weight along a path lift -/

/-- The weight `w_1` is invariant under a shift by an integer multiple of its period. -/
lemma gapWeightOne_add_int_mul {s a K L : ℝ} (hL : 0 < L) (u : ℝ) (c : ℤ) :
    gradWeightOne s a K L (u + c * L) = gradWeightOne s a K L u := by
  unfold gradWeightOne
  rw [circDist_add_int_mul hL u c]

/-- The weight at the path endpoint `l + k` equals the weight at the label `m`, since the two lifts
differ by an integer multiple of the period `1`. -/
lemma gapWeightOne_lift_path {s a K ℓ γ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} {l m : ℤ}
    (hℓ : 0 < ℓ) (hpath : ∃ c : ℤ, m - l - gradPathIncr N ℓ γ l m = (N : ℤ) * c) :
    gradWeightOne s a K ℓ⁻¹ (gradLift N X (l + gradPathIncr N ℓ γ l m) / ℓ)
      = gradWeightOne s a K ℓ⁻¹ (gradLift N X m / ℓ) := by
  obtain ⟨c, hc⟩ := hpath
  have hmc : m = (l + gradPathIncr N ℓ γ l m) + (N : ℤ) * c := by linarith
  have hlift : gradLift N X m = gradLift N X (l + gradPathIncr N ℓ γ l m) + c := by
    have h := gradLift_add_mul N X (l + gradPathIncr N ℓ γ l m) c
    rw [← hmc] at h
    exact h
  have hshift : gradLift N X (l + gradPathIncr N ℓ γ l m) / ℓ
      = gradLift N X m / ℓ + ((-c : ℤ) : ℝ) * ℓ⁻¹ := by
    rw [hlift]
    push_cast
    field_simp
    ring
  rw [hshift, gapWeightOne_add_int_mul (inv_pos.mpr hℓ)]

/-! ## The divided difference on a pair -/

/-- The divided difference `Z` is bounded by the two endpoint weights (differences part of
Lemma 5.7, through `gradZavg_abs_le`). -/
lemma gapZ_abs_le {s a K ℓ C0 : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) (hs0 : 0 < s) (hs1 : s < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hK : 1 ≤ K) (hC0 : 0 ≤ C0) (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic ψ ℓ⁻¹) (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K ℓ⁻¹ t)
    (x y : ℝ) :
    |gradZ ψ ℓ x y| ≤ gradZConst a s * C0
      * (gradWeightOne s a K ℓ⁻¹ (x / ℓ) + gradWeightOne s a K ℓ⁻¹ (y / ℓ)) := by
  rw [gradZ_eq_gradZavg]
  exact gradZavg_abs_le (inv_pos.mpr hℓ) hs0 hs1 ha0 ha1 hK hC0 hψ hper hbd (x / ℓ) (y / ℓ)

/-- The second derivative of `h = gradKernelH s` on `(0, 3/4]`, with the power `u^{-s-2}`. -/
lemma gapKernel_second_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 < u → u ≤ 3 / 4 →
      |iteratedDeriv 2 (gradKernelH s) u| ≤ C * u ^ (-s - 2) := by
  obtain ⟨C, hC, hb⟩ := gradSplit_derivative_bounds s hs0 hs1
  refine ⟨C, hC.le, fun u hu0 hu1 => ?_⟩
  have habs : 0 < |u| := by rw [abs_pos]; exact hu0.ne'
  have h := (hb u habs (by rw [abs_of_pos hu0]; exact hu1)).2 2 (le_refl 2)
  rw [abs_of_pos hu0] at h
  simpa using h

/-! ## One positive pair -/

/-- One positive pair `(l, m)`: the pair term, with the weight `N^{-1-s}` removed, is
bounded by its endpoint weights and by the length of the path. -/
lemma gapPair_bound {s a γ ε ℓ C0 Cd : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} {ψ : ℝ → ℝ}
    {l m : ℤ} (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ) (hε : 0 < ε)
    (hεs : ε < (1 - s / 2) / 8) (hC0 : 0 ≤ C0) (hCd : 0 ≤ Cd)
    (hkd : ∀ u : ℝ, 0 < u → u ≤ 3 / 4 → |iteratedDeriv 2 (gradKernelH s) u| ≤ Cd * u ^ (-s - 2))
    (hψ : ContDiff ℝ ∞ ψ) (hper : Function.Periodic ψ ℓ⁻¹)
    (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ t)
    (hX : gradEvent s γ ε N ℓ X) (hl : l ∈ gradLabels N ℓ γ) (hm : m ∈ gradLabels N ℓ γ)
    (hne : m ≠ l) (hk : 0 < gradPathIncr N ℓ γ l m) :
    ((N : ℕ) : ℝ) ^ (-1 - s) * |gradPairTerm s ψ N ℓ γ X l m|
      ≤ gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
        * (gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X l / ℓ)
          + gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X m / ℓ))
        * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-(2 + s / 2)) := by
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hK0 : 0 < ((N : ℕ) : ℝ) * ℓ := by linarith
  have hKN : ((N : ℕ) : ℝ) * ℓ ≤ ((N : ℕ) : ℝ) := by nlinarith
  have hkR : (0 : ℝ) < ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) := by exact_mod_cast hk
  have h2k : 2 * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ≤ ((N : ℕ) : ℝ) := by
    have h := two_abs_gradPathIncr_le hl hm
    rw [abs_of_pos hk] at h
    exact_mod_cast h
  obtain ⟨hb1, _, hb3⟩ := gradSep_abs_bounds hK hX hl hm hne
  have hDpos : 0 < gradSep N ℓ γ X l m := (pos_iff_pos_of_mul_pos hb3).2 hkR
  have hF2a : (((N : ℕ) : ℝ) * ℓ) ^ (-ε) * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ)
      ≤ ((N : ℕ) : ℝ) * gradSep N ℓ γ X l m := by
    rw [abs_of_pos hkR, abs_of_pos hDpos] at hb1
    exact hb1
  have hF1 : |((N : ℕ) : ℝ) * gradSep N ℓ γ X l m - ((gradPathIncr N ℓ γ l m : ℤ) : ℝ)|
      ≤ (((N : ℕ) : ℝ) * ℓ) ^ ε * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (s / 2) := by
    have h := gradSep_event_bound hX hl hm hne
    rw [abs_of_pos hkR] at h
    exact h
  have hD34 : ((N : ℕ) : ℝ) < (4 : ℝ) ^ (2 / (1 - s / 2)) → gradSep N ℓ γ X l m ≤ 3 / 4 := by
    intro hNN
    have hlam := rpow_le_two_of_lt_threshold hs1 hε hεs hK0 hKN hNN
    have h := gradSep_abs_le_three_quarters hK hlam hX hl hm hne
    rw [abs_of_pos hDpos] at h
    exact h
  have hmain := gapKernel_deriv_pair_bound hs0 hs1 hCd hkd hK hKN hε hεs hNpos hkR h2k hF2a hF1
    hD34
  -- the endpoint weights: the lift of `l + k` is the lift of `m` up to an integer
  have hw := gapWeightOne_lift_path (s := s) (a := a) (K := ((N : ℕ) : ℝ) * ℓ) (X := X) hℓ
    (gradPathIncr_spec hl hm (Ne.symm hne)).2.2.2
  have hyl : gradLift N X l + gradSep N ℓ γ X l m = gradLift N X (l + gradPathIncr N ℓ γ l m) := by
    unfold gradSep
    ring
  have hZ := gapZ_abs_le hℓ hs0 hs1 ha0 ha1 hK hC0 hψ hper hbd (gradLift N X l)
    (gradLift N X l + gradSep N ℓ γ X l m)
  have hwy : gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
      ((gradLift N X l + gradSep N ℓ γ X l m) / ℓ)
      = gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X m / ℓ) := by
    rw [hyl]
    exact hw
  rw [hwy] at hZ
  have hkey : ((N : ℕ) : ℝ) ^ (-1 - s) * |gradPairTerm s ψ N ℓ γ X l m|
      = |gradZ ψ ℓ (gradLift N X l) (gradLift N X l + gradSep N ℓ γ X l m)|
        * (((N : ℕ) : ℝ) ^ (-1 - s) * |iteratedDeriv 1 (gradKernelH s) (gradSep N ℓ γ X l m)
          - iteratedDeriv 1 (gradKernelH s) (((gradPathIncr N ℓ γ l m : ℤ) : ℝ) / ((N : ℕ) : ℝ))|) := by
    unfold gradPairTerm
    rw [← iteratedDeriv_one, abs_mul]
    ring
  have hG : 0 ≤ gradZConst a s * C0 := mul_nonneg (gradZConst_nonneg ha1 hs1) hC0
  have hWb : 0 ≤ gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X l / ℓ)
      + gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X m / ℓ) :=
    add_nonneg (gradWeightOne_nonneg hK) (gradWeightOne_nonneg hK)
  rw [hkey, show (-(2 + s / 2) : ℝ) = -2 - s / 2 by ring]
  calc |gradZ ψ ℓ (gradLift N X l) (gradLift N X l + gradSep N ℓ γ X l m)|
        * (((N : ℕ) : ℝ) ^ (-1 - s) * |iteratedDeriv 1 (gradKernelH s) (gradSep N ℓ γ X l m)
          - iteratedDeriv 1 (gradKernelH s) (((gradPathIncr N ℓ γ l m : ℤ) : ℝ) / ((N : ℕ) : ℝ))|)
      ≤ (gradZConst a s * C0 * (gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X l / ℓ)
          + gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X m / ℓ)))
        * (Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε) * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-2 - s / 2)) :=
        mul_le_mul hZ hmain (by positivity) (mul_nonneg hG hWb)
    _ = gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
        * (gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X l / ℓ)
          + gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X m / ℓ))
        * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-2 - s / 2) := by
        ring

/-! ## The sum over the pairs whose path contains an edge -/

/-- The power `(1 + d)^{1 - (2 + s/2)}` is the reciprocal of `(1 + d)^{1 + s/2}`. -/
lemma gapRpow_one_sub {s x : ℝ} (hx : 0 < x) :
    x ^ (1 - (2 + s / 2)) = 1 / x ^ (1 + s / 2) := by
  rw [show (1 : ℝ) - (2 + s / 2) = -(1 + s / 2) by ring, Real.rpow_neg hx.le, one_div]

/-- The swap of the two sums over ordered pairs of distinct labels of the window. -/
lemma gapSum_comm {I : Finset ℤ} {f : ℤ → ℤ → ℝ} :
    ∑ l ∈ I, ∑ m ∈ I.erase l, f l m = ∑ m ∈ I, ∑ l ∈ I.erase m, f l m := by
  apply Finset.sum_comm'
  intro x y
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hx, hne, hy⟩
    exact ⟨⟨fun h => hne h.symm, hx⟩, hy⟩
  · rintro ⟨⟨hne, hx⟩, hy⟩
    exact ⟨hx, fun h => hne h.symm, hy⟩

/-- The gap part of Lemma 5.7, the pointwise estimate: for every edge label `e` of
the window, `|W^gap_e| ≤ 4 C_Z C_0 C_d K^{(s+3)ε} C_q ∑_{j∈I} w_1(x_j/ℓ) (1 + d(e,j))^{-(1+s/2)}`,
with `C_q = 2^{1+s/2} (1 + 1/(1+s/2))` and the residue `e mod N` of the edge. -/
lemma gapWgap_abs_le {s a γ ε ℓ C0 Cd : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} {ψ : ℝ → ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ) (hε : 0 < ε)
    (hεs : ε < (1 - s / 2) / 8) (hC0 : 0 ≤ C0) (hCd : 0 ≤ Cd)
    (hkd : ∀ u : ℝ, 0 < u → u ≤ 3 / 4 → |iteratedDeriv 2 (gradKernelH s) u| ≤ Cd * u ^ (-s - 2))
    (hψ : ContDiff ℝ ∞ ψ) (hper : Function.Periodic ψ ℓ⁻¹)
    (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ t)
    (hX : gradEvent s γ ε N ℓ X) {e : ℤ} (he : e ∈ gradLabels N ℓ γ) :
    |gradWgap s ψ N ℓ γ X (e % ((N : ℕ) : ℤ))|
      ≤ 4 * (gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
          * (2 ^ (1 + s / 2) * (1 + 1 / (1 + s / 2))))
        * ∑ j ∈ gradLabels N ℓ γ,
          gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X j / ℓ)
            / (1 + (gradLabelDist N e j : ℝ)) ^ (1 + s / 2) := by
  have hq : (1 : ℝ) < 2 + s / 2 := by linarith
  have hK0 : 0 < ((N : ℕ) : ℝ) * ℓ := by linarith
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hNp : (0 : ℝ) < ((N : ℕ) : ℝ) ^ (-1 - s) := Real.rpow_pos_of_pos hNpos _
  have hG : 0 ≤ gradZConst a s * C0 * Cd :=
    mul_nonneg (mul_nonneg (gradZConst_nonneg ha1 hs1) hC0) hCd
  have hc0 : 0 ≤ gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε) :=
    mul_nonneg hG (Real.rpow_nonneg hK0.le _)
  have hwt0 : ∀ j : ℤ, 0 ≤ gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X j / ℓ) :=
    fun j => gradWeightOne_nonneg hK
  -- Step 1: each pair is bounded by its endpoint weights and its length
  have hpair : ∀ l ∈ gradLabels N ℓ γ, ∀ m ∈ (gradLabels N ℓ γ).erase l,
      ((N : ℕ) : ℝ) ^ (-1 - s) * |(if 0 < gradPathIncr N ℓ γ l m ∧
          gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then gradPairTerm s ψ N ℓ γ X l m else 0)|
        ≤ (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then
            gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
              * (gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X l / ℓ)
                + gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X m / ℓ))
              * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-(2 + s / 2)) else 0) := by
    intro l hl m hm
    rw [Finset.mem_erase] at hm
    split_ifs with hcnd
    · exact gapPair_bound hs0 hs1 ha0 ha1 hℓ hℓ1 hK hε hεs hC0 hCd hkd hψ hper hbd hX hl hm.2
        hm.1 hcnd.1
    · simp
  -- Step 2: the double sum of the pair bounds
  have hsum1 : ((N : ℕ) : ℝ) ^ (-1 - s) * |∑ l ∈ gradLabels N ℓ γ, ∑ m ∈ (gradLabels N ℓ γ).erase l,
      (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then
        gradPairTerm s ψ N ℓ γ X l m else 0)|
      ≤ ∑ l ∈ gradLabels N ℓ γ, ∑ m ∈ (gradLabels N ℓ γ).erase l,
        (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then
            gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
              * (gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X l / ℓ)
                + gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X m / ℓ))
              * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-(2 + s / 2)) else 0) := by
    calc _ ≤ ((N : ℕ) : ℝ) ^ (-1 - s) * ∑ l ∈ gradLabels N ℓ γ,
            ∑ m ∈ (gradLabels N ℓ γ).erase l, |(if 0 < gradPathIncr N ℓ γ l m ∧
              gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then gradPairTerm s ψ N ℓ γ X l m
                else 0)| := by
          apply mul_le_mul_of_nonneg_left _ hNp.le
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun l _ => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ l ∈ gradLabels N ℓ γ, ∑ m ∈ (gradLabels N ℓ γ).erase l,
            ((N : ℕ) : ℝ) ^ (-1 - s) * |(if 0 < gradPathIncr N ℓ γ l m ∧
              gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then gradPairTerm s ψ N ℓ γ X l m
                else 0)| := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun l hl => Finset.sum_le_sum fun m hm => hpair l hl m hm
  -- Step 3: split the weight into its two endpoints
  have hsplit : ∑ l ∈ gradLabels N ℓ γ, ∑ m ∈ (gradLabels N ℓ γ).erase l,
      (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then
            gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
              * (gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X l / ℓ)
                + gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X m / ℓ))
              * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-(2 + s / 2)) else 0)
      = ∑ l ∈ gradLabels N ℓ γ, ∑ m ∈ (gradLabels N ℓ γ).erase l,
          (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then
            gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
              * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X l / ℓ)
              * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-(2 + s / 2)) else 0)
        + ∑ l ∈ gradLabels N ℓ γ, ∑ m ∈ (gradLabels N ℓ γ).erase l,
          (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then
            gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
              * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X m / ℓ)
              * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-(2 + s / 2)) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> ring
  -- Step 4: the two one-sided path sums
  have hLeft : ∀ l ∈ gradLabels N ℓ γ,
      ∑ m ∈ (gradLabels N ℓ γ).erase l,
        (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then
          gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
            * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X l / ℓ)
            * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-(2 + s / 2)) else 0)
      ≤ gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
          * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X l / ℓ)
          * (2 ^ (1 + s / 2) * (1 + 1 / (1 + s / 2)) * (1 / (1 + (gradLabelDist N e l : ℝ)) ^ (1 + s / 2))) := by
    intro l hl
    have h := gapSum_left (ℓ := ℓ) (γ := γ) (N := N) (q := 2 + s / 2) hq hl he
    have hd0 := gapLabelDist_nonneg he hl
    rw [show (2 + s / 2 - 1 : ℝ) = 1 + s / 2 by ring, gapRpow_one_sub (by linarith)] at h
    have hsum : ∑ m ∈ (gradLabels N ℓ γ).erase l,
        (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then
          gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
            * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X l / ℓ)
            * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-(2 + s / 2)) else 0)
        = gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
          * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X l / ℓ)
          * ∑ m ∈ (gradLabels N ℓ γ).erase l,
            (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then
              ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-(2 + s / 2)) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> ring
    rw [hsum]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc0 (hwt0 l))
    exact h
  have hRight : ∀ m ∈ gradLabels N ℓ γ,
      ∑ l ∈ (gradLabels N ℓ γ).erase m,
        (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then
          gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
            * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X m / ℓ)
            * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-(2 + s / 2)) else 0)
      ≤ gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
          * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X m / ℓ)
          * (2 ^ (1 + s / 2) * (1 + 1 / (1 + s / 2)) * (1 / (1 + (gradLabelDist N e m : ℝ)) ^ (1 + s / 2))) := by
    intro m hm
    have h := gapSum_right (ℓ := ℓ) (γ := γ) (N := N) (q := 2 + s / 2) hq hm he
    have hd0 := gapLabelDist_nonneg he hm
    rw [show (2 + s / 2 - 1 : ℝ) = 1 + s / 2 by ring, gapRpow_one_sub (by linarith)] at h
    have hsum : ∑ l ∈ (gradLabels N ℓ γ).erase m,
        (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then
          gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
            * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X m / ℓ)
            * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-(2 + s / 2)) else 0)
        = gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
          * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X m / ℓ)
          * ∑ l ∈ (gradLabels N ℓ γ).erase m,
            (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then
              ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-(2 + s / 2)) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs <;> ring
    rw [hsum]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc0 (hwt0 m))
    exact h
  -- Step 5: assemble
  have hW : |gradWgap s ψ N ℓ γ X (e % ((N : ℕ) : ℤ))|
      = 2 * (((N : ℕ) : ℝ) ^ (-1 - s) * |∑ l ∈ gradLabels N ℓ γ,
          ∑ m ∈ (gradLabels N ℓ γ).erase l, (if 0 < gradPathIncr N ℓ γ l m ∧
            gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then gradPairTerm s ψ N ℓ γ X l m
              else 0)|) := by
    unfold gradWgap
    rw [abs_mul, abs_mul, abs_neg, abs_two, abs_of_pos hNp]
    ring
  rw [hW]
  have hT := hsplit
  calc 2 * (((N : ℕ) : ℝ) ^ (-1 - s) * |∑ l ∈ gradLabels N ℓ γ,
          ∑ m ∈ (gradLabels N ℓ γ).erase l, (if 0 < gradPathIncr N ℓ γ l m ∧
            gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then gradPairTerm s ψ N ℓ γ X l m
              else 0)|)
      ≤ 2 * ((∑ l ∈ gradLabels N ℓ γ, ∑ m ∈ (gradLabels N ℓ γ).erase l,
          (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then
            gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
              * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X l / ℓ)
              * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-(2 + s / 2)) else 0))
        + ∑ l ∈ gradLabels N ℓ γ, ∑ m ∈ (gradLabels N ℓ γ).erase l,
          (if 0 < gradPathIncr N ℓ γ l m ∧ gradEdgeOnPath N ℓ γ l m (e % ((N : ℕ) : ℤ)) then
            gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
              * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X m / ℓ)
              * ((gradPathIncr N ℓ γ l m : ℤ) : ℝ) ^ (-(2 + s / 2)) else 0)) :=
        mul_le_mul_of_nonneg_left (hsum1.trans hT.le) (by norm_num)
    _ ≤ 2 * ((∑ l ∈ gradLabels N ℓ γ, gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
          * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X l / ℓ)
          * (2 ^ (1 + s / 2) * (1 + 1 / (1 + s / 2)) * (1 / (1 + (gradLabelDist N e l : ℝ)) ^ (1 + s / 2))))
        + ∑ m ∈ gradLabels N ℓ γ, gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
          * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X m / ℓ)
          * (2 ^ (1 + s / 2) * (1 + 1 / (1 + s / 2)) * (1 / (1 + (gradLabelDist N e m : ℝ)) ^ (1 + s / 2)))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add (Finset.sum_le_sum fun l hl => hLeft l hl)
          (by rw [gapSum_comm]; exact Finset.sum_le_sum fun m hm => hRight m hm)
    _ = 4 * (gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
          * (2 ^ (1 + s / 2) * (1 + 1 / (1 + s / 2))))
        * ∑ j ∈ gradLabels N ℓ γ,
          gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X j / ℓ)
            / (1 + (gradLabelDist N e j : ℝ)) ^ (1 + s / 2) := by
        have hX : ∑ j ∈ gradLabels N ℓ γ, gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
              * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X j / ℓ)
              * (2 ^ (1 + s / 2) * (1 + 1 / (1 + s / 2)) * (1 / (1 + (gradLabelDist N e j : ℝ)) ^ (1 + s / 2)))
            = gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
              * (2 ^ (1 + s / 2) * (1 + 1 / (1 + s / 2)))
              * ∑ j ∈ gradLabels N ℓ γ, gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X j / ℓ)
                / (1 + (gradLabelDist N e j : ℝ)) ^ (1 + s / 2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        rw [hX]
        ring


end

end Riesz1
