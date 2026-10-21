/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodGradientDefs

/-!
# Where the gap-coordinate cutoff has zero derivative

Gradient claim in the proof of Lemma 5.2. The gap-coordinate cutoff `gapCutoff` of
`Riesz1/Variance/APrioriGoodGradientDefs.lean` takes values in `[0, 1]`. Two vanishing statements
follow.

* On the plateau `{gapCutoff = 1}` the derivative vanishes, since the cutoff attains its maximum
  there (`fderiv_gapCutoff_eq_zero_of_eq_one`, for every gap vector).
* Off the good event, the derivative vanishes at every gap vector with positive coordinates
  (`fderiv_gapCutoff_eq_zero_of_not_mem`). The positivity hypothesis is needed: for a
  nonpositive gap the nearest-neighbour factor `scalarCutoff (2 / (K^ε z_i))` is locally equal
  to one but not zero, and the total formula can have a nonzero derivative there.
-/

@[expose] public section

noncomputable section

open Finset Filter Topology

namespace Riesz1

variable {N : ℕ+}

/-- The pair factor is nonnegative. The nearest-neighbour factors are products of values in
`[0, 1]`. -/
theorem gapCutoff_nonneg (s K γ ε : ℝ) (z : Fin (N : ℕ) → ℝ) :
    0 ≤ gapCutoff N s K γ ε z := by
  unfold gapCutoff
  apply mul_nonneg
  · exact Finset.prod_nonneg fun p _ => scalarCutoff_nonneg _
  · exact Finset.prod_nonneg fun i _ => mul_nonneg (scalarCutoff_nonneg _) (scalarCutoff_nonneg _)

/-- The gap-coordinate cutoff takes values in `[0, 1]` at every gap vector. -/
theorem gapCutoff_le_one (s K γ ε : ℝ) (z : Fin (N : ℕ) → ℝ) :
    gapCutoff N s K γ ε z ≤ 1 := by
  unfold gapCutoff
  have h1 := prod_mem_unitInterval (cutoffPairs N (window N K γ))
    (fun p => scalarCutoff (2 * |gapPairDev N z p| / pairScale s K ε p))
    (fun p _ => scalarCutoff_nonneg _) (fun p _ => scalarCutoff_le_one _)
  have h2 := prod_mem_unitInterval (nearestPairs N (window N K γ))
    (fun i => scalarCutoff (2 * z i / K ^ ε) * scalarCutoff (2 / (K ^ ε * z i)))
    (fun i _ => mul_nonneg (scalarCutoff_nonneg _) (scalarCutoff_nonneg _))
    (fun i _ => mul_le_one_of_unitInterval (scalarCutoff_nonneg _) (scalarCutoff_le_one _)
      (scalarCutoff_le_one _))
  calc (∏ p ∈ cutoffPairs N (window N K γ),
          scalarCutoff (2 * |gapPairDev N z p| / pairScale s K ε p)) *
        ∏ i ∈ nearestPairs N (window N K γ),
          (scalarCutoff (2 * z i / K ^ ε) * scalarCutoff (2 / (K ^ ε * z i)))
      ≤ 1 * 1 := mul_le_mul h1.2 h2.2 h2.1 zero_le_one
    _ = 1 := one_mul 1

/-- **Vanishing on the plateau.** At a gap vector where the cutoff equals one, its derivative
vanishes: the cutoff attains its global maximum there. -/
theorem fderiv_gapCutoff_eq_zero_of_eq_one (s K γ ε : ℝ) (z : Fin (N : ℕ) → ℝ)
    (h : gapCutoff N s K γ ε z = 1) :
    fderiv ℝ (gapCutoff N s K γ ε) z = 0 := by
  apply IsLocalMax.fderiv_eq_zero
  refine Filter.Eventually.of_forall fun w => ?_
  rw [h]
  exact gapCutoff_le_one s K γ ε w

/-- The pair deviation is continuous in the gap vector. -/
theorem continuous_gapPairDev (p : Fin (N : ℕ) × ℤ) :
    Continuous fun z : Fin (N : ℕ) → ℝ => gapPairDev N z p := by
  unfold gapPairDev gapOrientedSum
  fun_prop

/-- The tolerance of a pair is positive, for `K > 0` and a pair of `cutoffPairs`. -/
theorem pairScale_pos_of_mem_cutoffPairs {s K ε : ℝ} (hK : 0 < K) {I : Finset (Fin (N : ℕ))}
    {p : Fin (N : ℕ) × ℤ} (hp : p ∈ cutoffPairs N I) :
    0 < pairScale s K ε p := by
  have hp2 : p.2 ≠ 0 := (Finset.mem_erase.1 (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).2).1
  have hnat : (1 : ℝ) ≤ ((p.2.natAbs : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hp2)
  unfold pairScale
  exact mul_pos (Real.rpow_pos_of_pos hK ε) (Real.rpow_pos_of_pos (by linarith) _)

/-- **Vanishing off the good event.** Let `K > 0`, and let `z` be a gap vector with
positive coordinates that is not in `gapGoodEvent`. Then the derivative of the cutoff at `z`
vanishes, because the cutoff is zero on a neighbourhood of `z`. -/
theorem fderiv_gapCutoff_eq_zero_of_not_mem (s K γ ε : ℝ) (hK : 0 < K)
    (z : Fin (N : ℕ) → ℝ) (hpos : ∀ i : Fin (N : ℕ), 0 < z i)
    (hz : z ∉ gapGoodEvent N s K γ ε) :
    fderiv ℝ (gapCutoff N s K γ ε) z = 0 := by
  have hKε : 0 < K ^ ε := Real.rpow_pos_of_pos hK ε
  have hKinv : K ^ ε * K ^ (-ε) = 1 := by
    rw [Real.rpow_neg hK.le, mul_inv_cancel₀ hKε.ne']
  have hbad : (∃ p ∈ cutoffPairs N (window N K γ), pairScale s K ε p < |gapPairDev N z p|) ∨
      (∃ i ∈ nearestPairs N (window N K γ), K ^ ε < z i) ∨
      (∃ i ∈ nearestPairs N (window N K γ), z i < K ^ (-ε)) := by
    by_contra hcon
    push Not at hcon
    exact hz ⟨hcon.1, fun i hi => ⟨hcon.2.2 i hi, hcon.2.1 i hi⟩⟩
  have hev : gapCutoff N s K γ ε =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    rcases hbad with ⟨p, hp, hlt⟩ | ⟨i, hi, hlt⟩ | ⟨i, hi, hlt⟩
    · -- A pair deviation exceeds its tolerance: its factor vanishes near `z`.
      have hMpos : 0 < pairScale s K ε p := pairScale_pos_of_mem_cutoffPairs hK hp
      have hev' : ∀ᶠ w in 𝓝 z, pairScale s K ε p < |gapPairDev N w p| :=
        ((continuous_gapPairDev p).abs.tendsto z).eventually (lt_mem_nhds hlt)
      filter_upwards [hev'] with w hw
      show gapCutoff N s K γ ε w = 0
      unfold gapCutoff
      have hfac : scalarCutoff (2 * |gapPairDev N w p| / pairScale s K ε p) = 0 := by
        apply scalarCutoff_eq_zero_of_two_le
        rw [le_div_iff₀ hMpos]
        linarith
      rw [Finset.prod_eq_zero hp hfac, zero_mul]
    · -- A nearest-neighbour gap exceeds `K^ε`: its factor vanishes near `z`.
      have hev' : ∀ᶠ w in 𝓝 z, K ^ ε < w i :=
        ((continuous_apply i).tendsto z).eventually (lt_mem_nhds hlt)
      filter_upwards [hev'] with w hw
      show gapCutoff N s K γ ε w = 0
      unfold gapCutoff
      have hfac : scalarCutoff (2 * w i / K ^ ε) = 0 := by
        apply scalarCutoff_eq_zero_of_two_le
        rw [le_div_iff₀ hKε]
        linarith
      rw [Finset.prod_eq_zero hi (by rw [hfac, zero_mul]), mul_zero]
    · -- A nearest-neighbour gap lies below `K^{-ε}` and is positive: its second factor vanishes
      -- near `z`.
      have hev' : ∀ᶠ w in 𝓝 z, w i ∈ Set.Ioo 0 (K ^ (-ε)) :=
        ((continuous_apply i).tendsto z).eventually (Ioo_mem_nhds (hpos i) hlt)
      filter_upwards [hev'] with w hw
      show gapCutoff N s K γ ε w = 0
      unfold gapCutoff
      have hfac : scalarCutoff (2 / (K ^ ε * w i)) = 0 := by
        apply scalarCutoff_eq_zero_of_two_le
        have hlt' : K ^ ε * w i < 1 := by
          have := mul_lt_mul_of_pos_left hw.2 hKε
          linarith
        rw [le_div_iff₀ (mul_pos hKε hw.1)]
        linarith
      rw [Finset.prod_eq_zero hi (by rw [hfac, mul_zero]), mul_zero]
  rw [hev.fderiv_eq]
  simp

end Riesz1

end
end
