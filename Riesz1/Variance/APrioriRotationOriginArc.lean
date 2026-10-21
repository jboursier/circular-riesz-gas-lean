/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BlockMoments
public import Riesz1.Variance.APrioriRotationExterior
public import Riesz1.Variance.APrioriRotationKernel
public import Riesz1.Variance.APrioriRotationMoments

/-!
# Arc bounds for the exterior sum seen from the origin

Part of Lemma 5.2 (the rotation part), the `L²` claim for the joint exterior sum. In the anchored
coordinates with particle `0` at the origin of the labels, the spatial origin sits at position
`D / N` inside the gap `(x_0, x_1)`, for `0 < D < N (x_1 - x_0)`. For a label `i` outside the
window, the two arcs from the origin to `x_i` dominate the fixed-label block lengths
`N (x_i - x_1)` and `N (x_0 + 1 - x_i)`. This file bounds each exterior term by inverse powers of
these block lengths and sums the bounds over the exterior labels. The file
`Riesz1/Variance/APrioriRotationOriginL2.lean` assembles the `L²` bound.

The predecessor block `N (x_i - x_1)` has `i - 1` gaps, so its tail sums use `i - 1 ≥ J`
instead of `i > J`. The factor `2^a` of `pred_rpow_neg_le` absorbs the shift.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace Riesz1

/-- The predecessor shift of an inverse power: for `2 ≤ m` and `0 ≤ a`, the block of `m - 1`
labels satisfies `((m - 1 : ℕ) : ℝ)^(-a) ≤ 2^a (m : ℝ)^(-a)`, since `m ≤ 2 (m - 1)`. -/
theorem pred_rpow_neg_le {m : ℕ} (hm : 2 ≤ m) {a : ℝ} (ha : 0 ≤ a) :
    ((m - 1 : ℕ) : ℝ) ^ (-a) ≤ 2 ^ a * (m : ℝ) ^ (-a) := by
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hhalf : (0 : ℝ) < (m : ℝ) / 2 := by linarith
  have h1 : ((m : ℝ) - 1) ^ (-a) ≤ ((m : ℝ) / 2) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos hhalf (by linarith) (by linarith)
  have h2 : ((m : ℝ) / 2) ^ (-a) = 2 ^ a * (m : ℝ) ^ (-a) := by
    rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul, mul_comm]
  rw [hcast, ← h2]
  exact h1

/-- The labels outside the window lie beyond `J = ⌊K^γ⌋₊` from both ends of the cyclic order:
`J < i` and `J < N - i`. -/
theorem exterior_label_bounds {N : ℕ+} {K γ : ℝ} (hK : 1 ≤ K) {i : Fin (N : ℕ)}
    (hi : i ∈ (window N K γ)ᶜ) :
    ⌊K ^ γ⌋₊ < (i : ℕ) ∧ ⌊K ^ γ⌋₊ < (N : ℕ) - (i : ℕ) := by
  have hi' : i ∉ window N K γ := Finset.mem_compl.1 hi
  have hd := labelDist_gt_of_not_mem_window (K := K) (γ := γ) hi'
  rw [labelDistToOne_eq] at hd
  have hK0 : 0 < K := by linarith
  have hJd : ((⌊K ^ γ⌋₊ : ℕ) : ℝ) ≤ K ^ γ := Nat.floor_le (Real.rpow_nonneg hK0.le _)
  have hlt : ((⌊K ^ γ⌋₊ : ℕ) : ℝ) < ((min (i : ℕ) ((N : ℕ) - (i : ℕ)) : ℕ) : ℝ) :=
    lt_of_le_of_lt hJd hd
  have hlt' : ⌊K ^ γ⌋₊ < min (i : ℕ) ((N : ℕ) - (i : ℕ)) := by exact_mod_cast hlt
  exact lt_min_iff.1 hlt'

/-- **Arc bound for one exterior label, seen from the origin.** Let `X` be a configuration with
`0 < D < N (x_1 - x_0)` and let `2 ≤ i < N`. The argument `F / K` of `f`, with
`F = N (x_i - x_0) - D`, `K = N ℓ` and `G = N - F`, lies in `(0, 1/ℓ)`. The arcs satisfy
`F ≥ N (x_i - x_1) > 0` and `G ≥ N (x_0 + 1 - x_i) > 0`. Hence `|f(F/K)|` is bounded by the four
inverse powers of the two block lengths. The constants are `α` and `β` of the arc estimate
`abs_le_blocks`. -/
theorem abs_arc_origin {N : ℕ+} (X : Configuration N) {ℓ s lam ε A α β : ℝ} (hℓ : 0 < ℓ)
    (hs : s < 2) (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ) (hlam : 0 ≤ lam) (hε : 0 < ε) (hA : 0 ≤ A)
    (hα : α = kernelConst s lam ε * (((N : ℕ) : ℝ) * ℓ) ^ (lam + ε) *
      (2 * (((N : ℕ) : ℝ) * ℓ)) ^ A)
    (hβ : β = (((N : ℕ) : ℝ) * ℓ) ^ (2 - s) / (2 - s))
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hper : Function.Periodic f (1 / ℓ))
    (hzero : f (1 / ℓ / 2) = 0)
    (hder : ∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
      |deriv f u| ≤ cutoffMajorant s lam (((N : ℕ) : ℝ) * ℓ) |u|)
    {i : ℕ} (hi2 : 2 ≤ i) (hiN : i < (N : ℕ)) {D : ℝ} (hD0 : 0 < D)
    (hD1 : D < blockLength X 0 1) :
    |f ((((N : ℕ) : ℝ) * (cyclicLift X i - cyclicLift X 0) - D) / (((N : ℕ) : ℝ) * ℓ))| ≤
      α * blockLength X 1 (i - 1) ^ (-A) + α * blockLength X (i : ℤ) ((N : ℕ) - i) ^ (-A) +
      β * blockLength X 1 (i - 1) ^ (-(2 - s)) +
      β * blockLength X (i : ℤ) ((N : ℕ) - i) ^ (-(2 - s)) := by
  set K : ℝ := ((N : ℕ) : ℝ) * ℓ with hK_def
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hK0 : 0 < K := by linarith
  have hL0 : 0 < 1 / ℓ := one_div_pos.mpr hℓ
  -- The two block lengths, as explicit differences of lifts.
  have hP_pos : 0 < blockLength X 1 (i - 1) := blockLength_pos X 1 (by omega)
  have hR_pos : 0 < blockLength X (i : ℤ) ((N : ℕ) - i) := blockLength_pos X _ (by omega)
  have hPid : blockLength X 1 (i - 1) = ((N : ℕ) : ℝ) * (cyclicLift X i - cyclicLift X 1) := by
    unfold blockLength
    have h1 : (1 : ℤ) + ((i - 1 : ℕ) : ℤ) = (i : ℤ) := by omega
    rw [h1]
  have hcN : cyclicLift X ((N : ℕ) : ℤ) = cyclicLift X 0 + 1 := by
    have h := cyclicLift_add_N X 0
    rwa [zero_add] at h
  have hRid : blockLength X (i : ℤ) ((N : ℕ) - i) =
      ((N : ℕ) : ℝ) * (cyclicLift X 0 + 1 - cyclicLift X i) := by
    unfold blockLength
    have h1 : (i : ℤ) + (((N : ℕ) - i : ℕ) : ℤ) = ((N : ℕ) : ℤ) := by omega
    rw [h1, hcN]
  have hB1 : blockLength X 0 1 = ((N : ℕ) : ℝ) * (cyclicLift X 1 - cyclicLift X 0) := by
    unfold blockLength
    norm_num
  rw [hB1] at hD1
  -- The arcs `F` and `G = N - F`, and the lower bounds from the block lengths.
  set F : ℝ := ((N : ℕ) : ℝ) * (cyclicLift X i - cyclicLift X 0) - D with hF_def
  set G : ℝ := ((N : ℕ) : ℝ) - F with hG_def
  have hFP : blockLength X 1 (i - 1) < F := by
    rw [hPid, hF_def]
    have e : ((N : ℕ) : ℝ) * (cyclicLift X i - cyclicLift X 0) - D -
        ((N : ℕ) : ℝ) * (cyclicLift X i - cyclicLift X 1) =
        ((N : ℕ) : ℝ) * (cyclicLift X 1 - cyclicLift X 0) - D := by ring
    linarith
  have hGR : blockLength X (i : ℤ) ((N : ℕ) - i) < G := by
    rw [hRid, hG_def, hF_def]
    have e : ((N : ℕ) : ℝ) - (((N : ℕ) : ℝ) * (cyclicLift X i - cyclicLift X 0) - D) -
        ((N : ℕ) : ℝ) * (cyclicLift X 0 + 1 - cyclicLift X i) = D := by ring
    linarith
  have hFpos : 0 < F := lt_trans hP_pos hFP
  have hGpos : 0 < G := lt_trans hR_pos hGR
  have hℓne : ℓ ≠ 0 := hℓ.ne'
  have hNne : ((N : ℕ) : ℝ) ≠ 0 := hN0.ne'
  have hLx : 1 / ℓ - F / K = G / K := by
    rw [hK_def, hG_def]
    field_simp
  have hxpos : 0 < F / K := div_pos hFpos hK0
  have hxlt : F / K < 1 / ℓ := by
    have : 0 < G / K := div_pos hGpos hK0
    linarith
  have key := abs_le_blocks hL0 hs hK hlam hε hA hf hper hzero hder hxpos hxlt hFpos hGpos rfl
    hLx
  -- Monotonicity of the inverse powers in the arcs.
  have hA1 : F ^ (-A) ≤ blockLength X 1 (i - 1) ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos hP_pos hFP.le (by linarith)
  have hA2 : G ^ (-A) ≤ blockLength X (i : ℤ) ((N : ℕ) - i) ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos hR_pos hGR.le (by linarith)
  have hB1' : F ^ (-(2 - s)) ≤ blockLength X 1 (i - 1) ^ (-(2 - s)) :=
    Real.rpow_le_rpow_of_nonpos hP_pos hFP.le (by linarith)
  have hB2' : G ^ (-(2 - s)) ≤ blockLength X (i : ℤ) ((N : ℕ) - i) ^ (-(2 - s)) :=
    Real.rpow_le_rpow_of_nonpos hR_pos hGR.le (by linarith)
  have hαnn : 0 ≤ α := by
    rw [hα]
    exact mul_nonneg (mul_nonneg (kernelConst_nonneg hs hlam hε)
      (Real.rpow_nonneg hK0.le _)) (Real.rpow_nonneg (by linarith) _)
  have hβnn : 0 ≤ β := by
    rw [hβ]
    exact div_nonneg (Real.rpow_nonneg hK0.le _) (by linarith)
  have hkey : kernelConst s lam ε * K ^ (lam + ε) * (2 * K) ^ A = α := hα.symm
  have hkey2 : K ^ (2 - s) / (2 - s) = β := hβ.symm
  rw [hkey, hkey2] at key
  have hfin : α * (F ^ (-A) + G ^ (-A)) + β * (F ^ (-(2 - s)) + G ^ (-(2 - s))) ≤
      α * (blockLength X 1 (i - 1) ^ (-A) + blockLength X (i : ℤ) ((N : ℕ) - i) ^ (-A)) +
      β * (blockLength X 1 (i - 1) ^ (-(2 - s)) +
        blockLength X (i : ℤ) ((N : ℕ) - i) ^ (-(2 - s))) :=
    add_le_add (mul_le_mul_of_nonneg_left (add_le_add hA1 hA2) hαnn)
      (mul_le_mul_of_nonneg_left (add_le_add hB1' hB2') hβnn)
  exact key.trans (hfin.trans (le_of_eq (by ring)))

/-- **Tail sum of the predecessor blocks.** For `J = ⌊K^γ⌋₊ ≥ 1` and a finite set `E` of labels
with `J < i` and `J < N - i`, and `1 < a`, the sum of `((i - 1 : ℕ) : ℝ)^(-a)` over `E` is at most
`2^a J^(1-a)/(a-1)`. -/
theorem sum_pred_rpow_neg_le {N : ℕ+} {a : ℝ} (ha : 1 < a) {J : ℕ} (hJ : 1 ≤ J)
    (E : Finset (Fin (N : ℕ))) (hE : ∀ i ∈ E, J < (i : ℕ) ∧ J < (N : ℕ) - (i : ℕ)) :
    ∑ i ∈ E, (((i : ℕ) - 1 : ℕ) : ℝ) ^ (-a) ≤ 2 ^ a * ((J : ℝ) ^ (1 - a) / (a - 1)) := by
  calc ∑ i ∈ E, (((i : ℕ) - 1 : ℕ) : ℝ) ^ (-a)
      ≤ ∑ i ∈ E, 2 ^ a * ((i : ℕ) : ℝ) ^ (-a) := by
        refine Finset.sum_le_sum fun i hi => pred_rpow_neg_le ?_ (by linarith)
        have := (hE i hi).1
        omega
    _ = 2 ^ a * ∑ i ∈ E, ((i : ℕ) : ℝ) ^ (-a) := by rw [Finset.mul_sum]
    _ ≤ 2 ^ a * ((J : ℝ) ^ (1 - a) / (a - 1)) :=
        mul_le_mul_of_nonneg_left
          (sum_rpow_neg_le_of_injOn ha hJ E (fun i => (i : ℕ)) (fun i _ j _ h => Fin.ext h)
            (fun i hi => ⟨(hE i hi).1, le_of_lt i.isLt⟩))
          (by positivity)

/-- **Tail sum of the blocks with `N - i` gaps.** Under the same hypotheses, the sum of
`((N - i : ℕ) : ℝ)^(-a)` over `E` is at most `J^(1-a)/(a-1)`. -/
theorem sum_suff_rpow_neg_le {N : ℕ+} {a : ℝ} (ha : 1 < a) {J : ℕ} (hJ : 1 ≤ J)
    (E : Finset (Fin (N : ℕ))) (hE : ∀ i ∈ E, J < (i : ℕ) ∧ J < (N : ℕ) - (i : ℕ)) :
    ∑ i ∈ E, (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-a) ≤ (J : ℝ) ^ (1 - a) / (a - 1) :=
  sum_rpow_neg_le_of_injOn ha hJ E (fun i => (N : ℕ) - (i : ℕ))
    (fun i _ j _ h => Fin.ext (by
      have := i.isLt
      have := j.isLt
      dsimp only at h
      omega))
    (fun i hi => ⟨(hE i hi).2, Nat.sub_le _ _⟩)

/-- **Tail sum of a pair of blocks.** For a coefficient `c ≥ 0`, the sum over `E` of
`c ((i - 1)^(-a) + (N - i)^(-a))` is at most `c (2^a + 1) J^(1-a)/(a-1)`. -/
theorem sum_pair_rpow_le {N : ℕ+} {a c : ℝ} (ha : 1 < a) (hc : 0 ≤ c) {J : ℕ} (hJ : 1 ≤ J)
    (E : Finset (Fin (N : ℕ))) (hE : ∀ i ∈ E, J < (i : ℕ) ∧ J < (N : ℕ) - (i : ℕ)) :
    ∑ i ∈ E, (c * (((i : ℕ) - 1 : ℕ) : ℝ) ^ (-a) + c * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-a)) ≤
      c * (2 ^ a + 1) * ((J : ℝ) ^ (1 - a) / (a - 1)) := by
  have h1 := sum_pred_rpow_neg_le ha hJ E hE
  have h2 := sum_suff_rpow_neg_le ha hJ E hE
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc c * ∑ i ∈ E, (((i : ℕ) - 1 : ℕ) : ℝ) ^ (-a) + c * ∑ i ∈ E, (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-a)
      = c * (∑ i ∈ E, (((i : ℕ) - 1 : ℕ) : ℝ) ^ (-a) + ∑ i ∈ E, (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-a)) := by
        ring
    _ ≤ c * (2 ^ a * ((J : ℝ) ^ (1 - a) / (a - 1)) + (J : ℝ) ^ (1 - a) / (a - 1)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hc
    _ = c * (2 ^ a + 1) * ((J : ℝ) ^ (1 - a) / (a - 1)) := by ring

end Riesz1

end
