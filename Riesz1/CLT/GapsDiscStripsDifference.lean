/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscStrips
public import Riesz1.CLT.GapsDiscStripsShift

/-!
# Boundary strips, second assertion

Part of the proof of Corollary 1, second assertion. The difference of the
centred counts of two concentric open arcs of half-widths `ℓ_N a` and `ℓ a` is a sum of two
centred counts of arcs of length `t_N = a |ℓ_N - ℓ|`, centred at `±(lo + hi)/2` (up to a null set,
`arc_difference_ae`). The first assertion then bounds its `L¹` norm by a constant times
`1 + (N t_N)^{s/2}`, which gives the normalized bound `N^{-s/2} (N^{-s/2} + t_N^{s/2})`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Riesz1

lemma linearStatistic_sub_fun {N : ℕ+} (f g : UnitAddCircle → ℝ) (X : Configuration N) :
    linearStatistic (fun x => f x - g x) X = linearStatistic f X - linearStatistic g X := by
  unfold linearStatistic
  rw [← Finset.sum_sub_distrib]

lemma linearStatistic_add_fun {N : ℕ+} (f g : UnitAddCircle → ℝ) (X : Configuration N) :
    linearStatistic (fun x => f x + g x) X = linearStatistic f X + linearStatistic g X := by
  unfold linearStatistic
  rw [← Finset.sum_add_distrib]

/-- The centred counts of the annulus: almost surely, the difference of the counts of the arcs
`|x| < hi` and `|x| < lo` is the sum of the counts of the arcs about `±(lo+hi)/2`. -/
theorem arcCount_difference_ae (P : Parameters) (N : ℕ+) (lo hi : ℝ) (hlo : 0 < lo)
    (hlh : lo ≤ hi) (hhi : hi < 1 / 2) :
    ∀ᵐ X ∂(gibbsMeasure P N), arcCount 0 hi X - arcCount 0 lo X =
      arcCount (((lo + hi) / 2 : ℝ) : UnitAddCircle) ((hi - lo) / 2) X +
        arcCount ((-((lo + hi) / 2) : ℝ) : UnitAddCircle) ((hi - lo) / 2) X := by
  have h := linearStatistic_ae_eq P N (arc_difference_ae lo hi hlo hlh hhi)
  filter_upwards [h] with X hX
  rw [linearStatistic_sub_fun, linearStatistic_add_fun] at hX
  exact hX

/-- The centred count of an arc is integrable, with its absolute value. -/
lemma integrable_abs_arcCount_sub (P : Parameters) (N : ℕ+) [IsProbabilityMeasure (gibbsMeasure P N)]
    (c : UnitAddCircle) (a m : ℝ) (hmem : MemLp (arcIndicator c a) 2 volume) :
    Integrable (fun X : Configuration N => arcCount c a X - m) (gibbsMeasure P N) := by
  have h := memLp_linearStatistic P N hmem
  have h' : Integrable (fun X : Configuration N => arcCount c a X) (gibbsMeasure P N) :=
    h.integrable one_le_two
  exact h'.sub (integrable_const m)

/-- **Two concentric arcs.** For `0 < lo ≤ hi < 1/2` with `hi - lo ≤ 1/4`, the `L¹` norm of the
difference of the two centred counts is bounded by `C (1 + (N (hi - lo))^{s/2})`, with `C` the
constant of `gapsDisc_strips_arc` times a numerical factor. -/
theorem gapsDisc_shift_pair (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hQV : Internal.QuantitativeVarianceConclusion beta s hbeta hs hs1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (lo hi : ℝ), 0 < lo → lo ≤ hi → hi < 1 / 2 → hi - lo ≤ 1 / 4 →
      ∫ X, |(arcCount 0 hi X - (N : ℝ) * (2 * hi)) - (arcCount 0 lo X - (N : ℝ) * (2 * lo))|
        ∂(gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N) ≤
          C * (1 + ((N : ℝ) * (hi - lo)) ^ (s / 2)) := by
  obtain ⟨C₁, hC₁, hbound⟩ := gapsDisc_strips_arc beta s hbeta hs hs1 hQV
  refine ⟨4 + 2 * C₁, by positivity, fun N lo hi hlo hlh hhi ht => ?_⟩
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hPdef
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  rcases eq_or_lt_of_le hlh with heq | hlt
  · rw [← heq]
    simp only [sub_self, abs_zero, integral_zero, mul_zero]
    rw [Real.zero_rpow (by positivity)]
    positivity
  · have ht0 : 0 < hi - lo := by linarith
    have hmemR : ∀ (c : UnitAddCircle) (a : ℝ), MemLp (arcIndicator c a) 2 volume := fun c a => by
      simpa using (memLp_arcIndicator c a).re
    have hint0 := integrable_abs_arcCount_sub P N 0 hi (0 : ℝ) (hmemR 0 hi)
    have hint1 := integrable_abs_arcCount_sub P N 0 lo (0 : ℝ) (hmemR 0 lo)
    have hGint : Integrable (fun X : Configuration N =>
        (arcCount 0 hi X - (N : ℝ) * (2 * hi)) - (arcCount 0 lo X - (N : ℝ) * (2 * lo)))
          (gibbsMeasure P N) := by
      have h0 := memLp_linearStatistic P N (hmemR 0 hi)
      have h1 := memLp_linearStatistic P N (hmemR 0 lo)
      have a0 : Integrable (fun X : Configuration N => arcCount 0 hi X) (gibbsMeasure P N) :=
        h0.integrable one_le_two
      have a1 : Integrable (fun X : Configuration N => arcCount 0 lo X) (gibbsMeasure P N) :=
        h1.integrable one_le_two
      exact (a0.sub (integrable_const _)).sub (a1.sub (integrable_const _))
    have hc1 : MemLp (arcIndicator (((lo + hi) / 2 : ℝ) : UnitAddCircle) ((hi - lo) / 2)) 2 volume :=
      hmemR _ _
    have hc2 : MemLp (arcIndicator ((-((lo + hi) / 2) : ℝ) : UnitAddCircle) ((hi - lo) / 2)) 2
        volume := hmemR _ _
    have hF1 : Integrable (fun X : Configuration N =>
        arcCount (((lo + hi) / 2 : ℝ) : UnitAddCircle) ((hi - lo) / 2) X - (N : ℝ) * (hi - lo))
          (gibbsMeasure P N) := by
      have h := integrable_abs_arcCount_sub P N (((lo + hi) / 2 : ℝ) : UnitAddCircle)
        ((hi - lo) / 2) ((N : ℝ) * (hi - lo)) hc1
      exact h
    have hF2 : Integrable (fun X : Configuration N =>
        arcCount ((-((lo + hi) / 2) : ℝ) : UnitAddCircle) ((hi - lo) / 2) X - (N : ℝ) * (hi - lo))
          (gibbsMeasure P N) := by
      exact integrable_abs_arcCount_sub P N _ _ _ hc2
    have hpt : ∀ᵐ X ∂(gibbsMeasure P N),
        |(arcCount 0 hi X - (N : ℝ) * (2 * hi)) - (arcCount 0 lo X - (N : ℝ) * (2 * lo))| ≤
          |arcCount (((lo + hi) / 2 : ℝ) : UnitAddCircle) ((hi - lo) / 2) X - (N : ℝ) * (hi - lo)| +
            |arcCount ((-((lo + hi) / 2) : ℝ) : UnitAddCircle) ((hi - lo) / 2) X -
              (N : ℝ) * (hi - lo)| := by
      filter_upwards [arcCount_difference_ae P N lo hi hlo hlh hhi] with X hX
      have hsum : (arcCount 0 hi X - (N : ℝ) * (2 * hi)) - (arcCount 0 lo X - (N : ℝ) * (2 * lo)) =
          (arcCount (((lo + hi) / 2 : ℝ) : UnitAddCircle) ((hi - lo) / 2) X - (N : ℝ) * (hi - lo)) +
            (arcCount ((-((lo + hi) / 2) : ℝ) : UnitAddCircle) ((hi - lo) / 2) X -
              (N : ℝ) * (hi - lo)) := by
        linear_combination hX
      rw [hsum]
      exact abs_add_le _ _
    have hbd1 := hbound N ((((lo + hi) / 2 : ℝ) : UnitAddCircle)) (hi - lo) ht0 ht
    have hbd2 := hbound N ((-((lo + hi) / 2) : ℝ) : UnitAddCircle) (hi - lo) ht0 ht
    have hnn : 0 ≤ ((N : ℝ) * (hi - lo)) ^ (s / 2) := Real.rpow_nonneg (by
      have : (0 : ℝ) ≤ N := by positivity
      exact mul_nonneg this ht0.le) _
    have hshape : (if (N : ℝ) * (hi - lo) < 1 then 2 * ((N : ℝ) * (hi - lo))
        else C₁ * ((N : ℝ) * (hi - lo)) ^ (s / 2)) ≤ 2 + C₁ * ((N : ℝ) * (hi - lo)) ^ (s / 2) := by
      split_ifs with h
      · nlinarith [mul_nonneg hC₁.le hnn]
      · linarith
    have hb1 := (hbd1.trans hshape)
    have hb2 := (hbd2.trans hshape)
    have hmono := integral_mono_ae hGint.abs ((hF1.abs).add (hF2.abs)) hpt
    simp only [Pi.add_apply] at hmono
    rw [integral_add hF1.abs hF2.abs] at hmono
    calc _ ≤ _ := hmono
      _ ≤ (2 + C₁ * ((N : ℝ) * (hi - lo)) ^ (s / 2)) + (2 + C₁ * ((N : ℝ) * (hi - lo)) ^ (s / 2)) :=
          add_le_add hb1 hb2
      _ ≤ (4 + 2 * C₁) * (1 + ((N : ℝ) * (hi - lo)) ^ (s / 2)) := by
        nlinarith [mul_nonneg hC₁.le hnn]

/-- **Boundary strips, second assertion.** For a fixed `0 < a < 1/2`, scales `ℓ_N, ℓ ∈ (0, 1]` with
`t_N = a |ℓ_N - ℓ| ≤ 1/4`, the normalized `L¹` norm of the difference of the two centred arc counts
satisfies `N^{-s/2} ‖Fluct_N[1_{(-aℓ_N,aℓ_N)} - 1_{(-aℓ,aℓ)}]‖_1 ≤ C (N^{-s/2} + t_N^{s/2})`,
with `C` depending only on `s, β` (and not on `a`, `ℓ_N`, `ℓ` or `N`). -/
theorem gapsDisc_strips_shift (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hQV : Internal.QuantitativeVarianceConclusion beta s hbeta hs hs1) (a : ℝ) (ha0 : 0 < a)
    (ha1 : a < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (lN l : ℝ), 0 < lN → lN ≤ 1 → 0 < l → l ≤ 1 →
      a * |lN - l| ≤ 1 / 4 →
      (N : ℝ) ^ (-s / 2) *
        ∫ X, |(arcCount 0 (a * lN) X - (N : ℝ) * (2 * (a * lN))) -
            (arcCount 0 (a * l) X - (N : ℝ) * (2 * (a * l)))|
          ∂(gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N) ≤
        C * ((N : ℝ) ^ (-s / 2) + (a * |lN - l|) ^ (s / 2)) := by
  obtain ⟨C, hC, hshift⟩ := gapsDisc_shift_pair beta s hbeta hs hs1 hQV
  refine ⟨C, hC, fun N lN l hlN0 hlN1 hl0 hl1 ht => ?_⟩
  have hlo0 : 0 < min (a * lN) (a * l) := lt_min (mul_pos ha0 hlN0) (mul_pos ha0 hl0)
  have hhi1 : max (a * lN) (a * l) < 1 / 2 := max_lt (by nlinarith) (by nlinarith)
  have hlh : min (a * lN) (a * l) ≤ max (a * lN) (a * l) := min_le_max
  have hdiff : max (a * lN) (a * l) - min (a * lN) (a * l) = a * |lN - l| := by
    rw [max_sub_min_eq_abs', ← mul_sub, abs_mul, abs_of_pos ha0]
  have hpt : ∀ X : Configuration N,
      |(arcCount 0 (a * lN) X - (N : ℝ) * (2 * (a * lN))) -
          (arcCount 0 (a * l) X - (N : ℝ) * (2 * (a * l)))| =
        |(arcCount 0 (max (a * lN) (a * l)) X - (N : ℝ) * (2 * max (a * lN) (a * l))) -
          (arcCount 0 (min (a * lN) (a * l)) X - (N : ℝ) * (2 * min (a * lN) (a * l)))| := by
    intro X
    rcases le_total (a * lN) (a * l) with h | h
    · rw [min_eq_left h, max_eq_right h, abs_sub_comm]
    · rw [min_eq_right h, max_eq_left h]
  have hmain := hshift N (min (a * lN) (a * l)) (max (a * lN) (a * l)) hlo0 hlh hhi1
    (by rw [hdiff]; exact ht)
  rw [hdiff] at hmain
  simp only [hpt]
  have hNpos : (0 : ℝ) < N := by positivity
  have ht0 : 0 ≤ a * |lN - l| := by positivity
  have key : (N : ℝ) ^ (-s / 2) * ((N : ℝ) * (a * |lN - l|)) ^ (s / 2) =
      (a * |lN - l|) ^ (s / 2) := by
    rw [Real.mul_rpow hNpos.le ht0, ← mul_assoc, ← Real.rpow_add hNpos,
      show -s / 2 + s / 2 = (0 : ℝ) by ring, Real.rpow_zero, one_mul]
  have hNs : 0 ≤ (N : ℝ) ^ (-s / 2) := Real.rpow_nonneg hNpos.le _
  calc (N : ℝ) ^ (-s / 2) * ∫ X, |(arcCount 0 (max (a * lN) (a * l)) X -
            (N : ℝ) * (2 * max (a * lN) (a * l))) -
          (arcCount 0 (min (a * lN) (a * l)) X - (N : ℝ) * (2 * min (a * lN) (a * l)))|
          ∂(gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N)
      ≤ (N : ℝ) ^ (-s / 2) * (C * (1 + ((N : ℝ) * (a * |lN - l|)) ^ (s / 2))) :=
        mul_le_mul_of_nonneg_left hmain hNs
    _ = C * ((N : ℝ) ^ (-s / 2) + (a * |lN - l|) ^ (s / 2)) := by
        linear_combination C * key

end Riesz1

end
end
