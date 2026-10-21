/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodGradientCount
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# One-variable and single-factor derivatives of the gap cutoff

Gradient claim in the proof of Lemma 5.2. This file differentiates the factors of the
gap-coordinate cutoff `gapCutoff` of `Riesz1/Variance/APrioriGoodGradientDefs.lean`.

* `scalarCutoff_hasDerivAt`: the scalar cutoff is differentiable off the kinks `r = 1` and `r = 2`,
  with slope `-1` on `(1, 2)` and slope `0` elsewhere.
* `pair_scalarCutoff_hasDerivAt`: a pair factor `c(2 |u| / M)` has derivative of size at most
  `2 / M` off its kinks.
* `nearest_scalarCutoff_hasDerivAt`: a nearest-neighbour factor
  `c(2 u / κ) c(2 / (κ u))` has derivative of size at most `4 κ` off its kinks, for `κ ≥ 1`.
* `gapArcCLM`: the oriented arc sum of a gap vector is a continuous linear functional, and
  `pair_factor_hasFDerivAt` differentiates a pair factor as a function of the gap vector.
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace Riesz1

/-! ### The scalar cutoff -/

/-- The scalar cutoff takes the value `1` on `(-∞, 1]`, the value `2 - t` on `[1, 2]` and `0` on
`[2, ∞)`. -/
theorem scalarCutoff_hasDerivAt {r : ℝ} (h1 : r ≠ 1) (h2 : r ≠ 2) :
    HasDerivAt scalarCutoff (if 1 < r ∧ r < 2 then -1 else 0) r := by
  rcases lt_or_gt_of_ne h1 with hr1 | hr1
  · rw [ite_eq_right (fun h => by linarith [h.1])]
    refine (hasDerivAt_const r (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hr1] with t ht
    exact scalarCutoff_eq_one_of_le_one (Set.mem_Iio.1 ht).le
  · rcases lt_or_gt_of_ne h2 with hr2 | hr2
    · rw [ite_eq_left ⟨hr1, hr2⟩]
      refine ((hasDerivAt_id' r).const_sub 2).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hr1 hr2] with t ht
      unfold scalarCutoff
      rw [max_eq_right (by linarith [ht.2]), min_eq_right (by linarith [ht.1])]
    · rw [ite_eq_right (fun h => by linarith [h.2])]
      refine (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hr2] with t ht
      exact scalarCutoff_eq_zero_of_two_le (Set.mem_Ioi.1 ht).le

/-- The slope of the scalar cutoff has absolute value at most one. -/
theorem abs_ite_slope_le_one (P : Prop) [Decidable P] : |(if P then (-1 : ℝ) else 0)| ≤ 1 := by
  split_ifs <;> simp

/-! ### Pair factors: the cutoff of an absolute value -/

/-- **Pair factor derivative.** Let `M > 0`, and let `t ≠ 0` avoid the kinks `2 |t| / M ∈ {1, 2}`.
Then `u ↦ c(2 |u| / M)` has a derivative at `t` of absolute value at most `2 / M`. -/
theorem pair_scalarCutoff_hasDerivAt {M t : ℝ} (hM : 0 < M) (ht : t ≠ 0)
    (h1 : 2 * |t| / M ≠ 1) (h2 : 2 * |t| / M ≠ 2) :
    ∃ d : ℝ, |d| ≤ 2 / M ∧ HasDerivAt (fun u : ℝ => scalarCutoff (2 * |u| / M)) d t := by
  have hinner : HasDerivAt (fun u : ℝ => 2 * |u| / M) (2 * ((SignType.sign t : SignType) : ℝ) / M) t :=
    ((hasDerivAt_abs ht).const_mul 2).div_const M
  have hout := scalarCutoff_hasDerivAt h1 h2
  have hcomp := HasDerivAt.comp t hout hinner
  have hsign : |((SignType.sign t : SignType) : ℝ)| ≤ 1 := by
    rcases lt_or_gt_of_ne ht with h | h
    · rw [sign_neg h]
      norm_num
    · rw [sign_pos h]
      norm_num
  refine ⟨_, ?_, hcomp⟩
  rw [abs_mul]
  have hB : |2 * ((SignType.sign t : SignType) : ℝ) / M| ≤ 2 / M := by
    rw [abs_div, abs_mul, abs_of_pos hM]
    apply div_le_div_of_nonneg_right _ hM.le
    norm_num
    linarith [hsign]
  calc |(if 1 < 2 * |t| / M ∧ 2 * |t| / M < 2 then (-1 : ℝ) else 0)| *
        |2 * ((SignType.sign t : SignType) : ℝ) / M|
      ≤ 1 * (2 / M) := mul_le_mul (abs_ite_slope_le_one _) hB (abs_nonneg _) zero_le_one
    _ = 2 / M := one_mul _

/-! ### Nearest-neighbour factors -/

/-- If `1 < 2 / x < 2` then `1 < x`. -/
theorem one_lt_of_one_lt_div_two_div_lt_two {x : ℝ} (h1 : 1 < 2 / x) (h2 : 2 / x < 2) :
    1 < x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have : 2 / x < 0 := div_neg_of_pos_of_neg (by norm_num) hx
    linarith
  · rw [hx, div_zero] at h1
    linarith
  · have h2' : 2 < 2 * x := (div_lt_iff₀ hx).1 h2
    linarith

/-- **Nearest-neighbour factor derivative.** Let `κ ≥ 1` and `z ≠ 0`, and let `z` avoid the kinks
`2 z / κ ∈ {1, 2}` and `2 / (κ z) ∈ {1, 2}`. Then `u ↦ c(2 u / κ) c(2 / (κ u))` has a derivative
at `z` of absolute value at most `4 κ`. -/
theorem nearest_scalarCutoff_hasDerivAt {κ z : ℝ} (hκ : 1 ≤ κ) (hz : z ≠ 0)
    (h1 : 2 * z / κ ≠ 1) (h2 : 2 * z / κ ≠ 2) (h3 : 2 / (κ * z) ≠ 1) (h4 : 2 / (κ * z) ≠ 2) :
    ∃ d : ℝ, |d| ≤ 4 * κ ∧
      HasDerivAt (fun u : ℝ => scalarCutoff (2 * u / κ) * scalarCutoff (2 / (κ * u))) d z := by
  have hκpos : 0 < κ := by linarith
  have hκz : κ * z ≠ 0 := mul_ne_zero hκpos.ne' hz
  have hin1 : HasDerivAt (fun u : ℝ => 2 * u / κ) (2 * 1 / κ) z :=
    ((hasDerivAt_id' z).const_mul 2).div_const κ
  have hc1 := HasDerivAt.comp z (scalarCutoff_hasDerivAt h1 h2) hin1
  have hin2 : HasDerivAt (fun u : ℝ => 2 / (κ * u))
      ((0 * (κ * z) - 2 * (κ * 1)) / (κ * z) ^ 2) z :=
    (hasDerivAt_const z (2 : ℝ)).div ((hasDerivAt_id' z).const_mul κ) hκz
  have hc2 := HasDerivAt.comp z (scalarCutoff_hasDerivAt h3 h4) hin2
  refine ⟨_, ?_, hc1.mul hc2⟩
  -- Bound on the derivative of the first factor.
  have hb1 : |(if 1 < 2 * z / κ ∧ 2 * z / κ < 2 then (-1 : ℝ) else 0) * (2 * 1 / κ)| ≤ 2 / κ := by
    rw [abs_mul, mul_one, abs_of_pos (div_pos two_pos hκpos)]
    calc |(if 1 < 2 * z / κ ∧ 2 * z / κ < 2 then (-1 : ℝ) else 0)| * (2 / κ)
        ≤ 1 * (2 / κ) := mul_le_mul_of_nonneg_right (abs_ite_slope_le_one _)
          (div_pos two_pos hκpos).le
      _ = 2 / κ := one_mul _
  -- Bound on the derivative of the second factor, where it is nonzero `κ z > 1`.
  have hb2 : |(if 1 < 2 / (κ * z) ∧ 2 / (κ * z) < 2 then (-1 : ℝ) else 0) *
      ((0 * (κ * z) - 2 * (κ * 1)) / (κ * z) ^ 2)| ≤ 2 * κ := by
    by_cases hc : 1 < 2 / (κ * z) ∧ 2 / (κ * z) < 2
    · rw [ite_eq_left hc, neg_one_mul, abs_neg]
      have hx : 1 < κ * z := one_lt_of_one_lt_div_two_div_lt_two hc.1 hc.2
      have hd : (0 * (κ * z) - 2 * (κ * 1)) / (κ * z) ^ 2 = -(2 * κ) / (κ * z) ^ 2 := by ring
      rw [hd, abs_div, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < 2 * κ),
        abs_of_pos (pow_pos (by linarith : (0 : ℝ) < κ * z) 2)]
      apply div_le_self (by linarith)
      nlinarith
    · rw [ite_eq_right hc, zero_mul, abs_zero]
      linarith
  -- Both factors lie in `[0, 1]`.
  have hc1_0 : 0 ≤ scalarCutoff (2 * z / κ) := scalarCutoff_nonneg _
  have hc1_1 : scalarCutoff (2 * z / κ) ≤ 1 := scalarCutoff_le_one _
  have hc2_0 : 0 ≤ scalarCutoff (2 / (κ * z)) := scalarCutoff_nonneg _
  have hc2_1 : scalarCutoff (2 / (κ * z)) ≤ 1 := scalarCutoff_le_one _
  calc |(if 1 < 2 * z / κ ∧ 2 * z / κ < 2 then (-1 : ℝ) else 0) * (2 * 1 / κ) *
          scalarCutoff (2 / (κ * z)) +
        scalarCutoff (2 * z / κ) *
          ((if 1 < 2 / (κ * z) ∧ 2 / (κ * z) < 2 then (-1 : ℝ) else 0) *
            ((0 * (κ * z) - 2 * (κ * 1)) / (κ * z) ^ 2))|
      ≤ |(if 1 < 2 * z / κ ∧ 2 * z / κ < 2 then (-1 : ℝ) else 0) * (2 * 1 / κ) *
          scalarCutoff (2 / (κ * z))| +
        |scalarCutoff (2 * z / κ) *
          ((if 1 < 2 / (κ * z) ∧ 2 / (κ * z) < 2 then (-1 : ℝ) else 0) *
            ((0 * (κ * z) - 2 * (κ * 1)) / (κ * z) ^ 2))| := abs_add_le _ _
    _ = |(if 1 < 2 * z / κ ∧ 2 * z / κ < 2 then (-1 : ℝ) else 0) * (2 * 1 / κ)| *
          scalarCutoff (2 / (κ * z)) +
        scalarCutoff (2 * z / κ) *
          |(if 1 < 2 / (κ * z) ∧ 2 / (κ * z) < 2 then (-1 : ℝ) else 0) *
            ((0 * (κ * z) - 2 * (κ * 1)) / (κ * z) ^ 2)| := by
          rw [abs_mul _ (scalarCutoff (2 / (κ * z))), abs_of_nonneg hc2_0,
            abs_mul (scalarCutoff (2 * z / κ)) _, abs_of_nonneg hc1_0]
    _ ≤ 2 / κ * 1 + 1 * (2 * κ) := by
          apply add_le_add
          · exact mul_le_mul hb1 hc2_1 hc2_0 (div_pos two_pos hκpos).le
          · exact mul_le_mul hc1_1 hb2 (abs_nonneg _) zero_le_one
    _ ≤ 4 * κ := by
          have : 2 / κ ≤ 2 := by
            rw [div_le_iff₀ hκpos]
            linarith
          nlinarith

/-! ### Linear functionals of the gap vector -/

/-- The oriented arc sum of a gap vector, as a continuous linear functional: the sum of the
coordinates `proj (labelOf N r)` over `[a, b)`, minus the sum over `[b, a)`. -/
def gapArcCLM (N : ℕ+) (a b : ℤ) : (Fin (N : ℕ) → ℝ) →L[ℝ] ℝ :=
  ∑ r ∈ Ico a b, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N : ℕ) => ℝ) (labelOf N r) -
    ∑ r ∈ Ico b a, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N : ℕ) => ℝ) (labelOf N r)

/-- The continuous linear functional `gapArcCLM` evaluates to the oriented arc sum. -/
theorem gapArcCLM_apply (N : ℕ+) (a b : ℤ) (w : Fin (N : ℕ) → ℝ) :
    gapArcCLM N a b w = gapOrientedSum N w a b := by
  simp [gapArcCLM, gapOrientedSum]

/-- The pair deviation, as a function of the gap vector, is the arc functional shifted by the
integer `k`. -/
theorem gapPairDev_eq_arc (N : ℕ+) (p : Fin (N : ℕ) × ℤ) :
    (fun w : Fin (N : ℕ) → ℝ => gapPairDev N w p) =
      fun w => gapArcCLM N (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2) w - p.2 := by
  funext w
  rw [gapArcCLM_apply]
  rfl

/-- **Pair factor as a function of the gap vector.** Let `M > 0` and let `z` be a gap vector at
which the pair deviation `D = gapPairDev N z p` is nonzero and avoids the kinks `2 |D| / M ∈ {1, 2}`.
Then the pair factor has a derivative at `z` of the form `d • gapArcCLM`, with `|d| ≤ 2 / M`. -/
theorem pair_factor_hasFDerivAt (N : ℕ+) {M : ℝ} (hM : 0 < M) (p : Fin (N : ℕ) × ℤ)
    (z : Fin (N : ℕ) → ℝ) (h0 : gapPairDev N z p ≠ 0)
    (h1 : 2 * |gapPairDev N z p| / M ≠ 1) (h2 : 2 * |gapPairDev N z p| / M ≠ 2) :
    ∃ d : ℝ, |d| ≤ 2 / M ∧
      HasFDerivAt (fun w : Fin (N : ℕ) → ℝ => scalarCutoff (2 * |gapPairDev N w p| / M))
        (d • gapArcCLM N (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2)) z := by
  obtain ⟨d, hd, hdD⟩ := pair_scalarCutoff_hasDerivAt hM h0 h1 h2
  have hD : HasFDerivAt (fun w : Fin (N : ℕ) → ℝ => gapPairDev N w p)
      (gapArcCLM N (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2)) z := by
    rw [gapPairDev_eq_arc]
    have hL := (gapArcCLM N (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2)).hasFDerivAt (x := z)
    exact hL.sub_const (p.2 : ℝ)
  exact ⟨d, hd, HasDerivAt.comp_hasFDerivAt (f := fun w : Fin (N : ℕ) → ℝ => gapPairDev N w p)
    (h₂ := fun u : ℝ => scalarCutoff (2 * |u| / M)) z hdD hD⟩

end Riesz1

end
end
