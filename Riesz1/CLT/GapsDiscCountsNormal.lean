/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscCountsArc
public import Riesz1.CLT.GapsDiscStripsVariance
public import Riesz1.Frozen.NormalizedCount
public import Riesz1.Frozen.NormalizedStatistic
public import Riesz1.Frozen.Fluctuation

/-!
# Normalized interval counts and the CLT normalization

Part of Corollary 1. For `0 < a < 1/2` and a scale `ℓ ∈ (0, 1]`, the
normalized count `normalizedCount` (the statistic of `Riesz1.fluctuations_gaps_discrepancy`)
equals `κ(ℓ)` times the CLT normalized statistic `(Nℓ)^{-s/2} Fluct_N[1_{arc(aℓ)}]` of the arc
profile, where `κ(ℓ) = sqrt(v_s) / sqrt(σ²(ℓ))` and `σ²(ℓ)` is the circle variance of the profile
`arcProfile a` at scale `ℓ`. The constant `κ(ℓ)` turns the CLT with varying variance into the count
CLT with the fixed variance `v_s = countVariance P`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Riesz1

/-- The indicator of an arc is `L²`. -/
lemma memLp_arcIndicator_real (c : UnitAddCircle) (a : ℝ) :
    MemLp (arcIndicator c a) 2 volume := by
  simpa using (memLp_arcIndicator c a).re

/-- The fluctuation of the arc indicator is the centred arc count. -/
lemma fluctuation_arcIndicator_eq {N : ℕ+} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (X : Configuration N) :
    fluctuation ⟨arcIndicator 0 a, (memLp_arcIndicator_real 0 a).integrable one_le_two⟩ X =
      arcCount 0 a X - (N : ℝ) * (2 * a) :=
  (arcCount_sub_eq_fluctuation 0 ha0 ha1 _ X).symm

/-- The CLT normalized statistic of the arc profile is the centred arc count, scaled by
`(Nℓ)^{-s/2}`. -/
lemma normalizedStatistic_arcProfile (P : Parameters) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (ell : Scales) (N : ℕ+) (X : Configuration N) :
    normalizedStatistic P (arcProfile a) ell N X =
      ((N : ℝ) * (ell N).val) ^ (-P.val.2 / 2) *
        (arcCount 0 (a * (ell N).val) X - (N : ℝ) * (2 * (a * (ell N).val))) := by
  have hℓ : 0 < (ell N).val := (ell N).property.1
  have hℓ1 : (ell N).val ≤ 1 := (ell N).property.2
  have hsub : (⟨testAtScale (arcProfile a) (ell N), testAtScaleL1 (arcProfile a) (ell N)⟩ :
      {f : UnitAddCircle → ℝ // Integrable f volume}) =
        ⟨arcIndicator 0 (a * (ell N).val),
          (memLp_arcIndicator_real 0 (a * (ell N).val)).integrable one_le_two⟩ :=
    Subtype.ext (testAtScale_arcProfile ha0 ha1 (ell N))
  unfold normalizedStatistic
  rw [hsub, fluctuation_arcIndicator_eq _ (by positivity) (by nlinarith)]

/-- The normalized count is the centred arc count divided by the square root of the
variance factor. -/
lemma normalizedCount_eq_arcCount (P : Parameters) {a : ℝ} (ha : 0 < a) (ha1 : a < 1 / 2)
    (ell : Scales) (N : ℕ+) (X : Configuration N) :
    normalizedCount P a ha ha1 ell N X =
      (arcCount 0 (a * (ell N).val) X - (N : ℝ) * (2 * (a * (ell N).val))) /
        Real.sqrt ((N : ℝ) ^ P.val.2 *
          periodicZeta (parametersExponent P) ((2 * a * (ell N).val : ℝ) : UnitAddCircle)) := by
  unfold normalizedCount
  congr 1
  ring

/-- The rpow identity behind the normalization: for positive `N, ℓ, v, V` and real `s`,
`1 / sqrt(N^s V) = (sqrt v / sqrt(ℓ^{-s} v V)) (Nℓ)^{-s/2}`. -/
lemma inv_sqrt_eq_normalization (s N ℓ v V : ℝ) (hN : 0 < N) (hℓ : 0 < ℓ) (hv : 0 < v)
    (hV : 0 < V) :
    1 / Real.sqrt (N ^ s * V) =
      Real.sqrt v / Real.sqrt (ℓ ^ (-s) * v * V) * (N * ℓ) ^ (-s / 2) := by
  have hNs : 0 < N ^ s := Real.rpow_pos_of_pos hN s
  have hℓs : 0 < ℓ ^ (-s) := Real.rpow_pos_of_pos hℓ _
  have hq1 : 0 < Real.sqrt (N ^ s * V) := Real.sqrt_pos.mpr (by positivity)
  have hq2 : 0 < Real.sqrt (ℓ ^ (-s) * v * V) := Real.sqrt_pos.mpr (by positivity)
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hpow : (N * ℓ) ^ (-s / 2) = N ^ (-s / 2) * ℓ ^ (-s / 2) :=
    Real.mul_rpow hN.le hℓ.le
  have h1 : Real.sqrt (N ^ s * V) = N ^ (s / 2) * Real.sqrt V := by
    rw [Real.sqrt_mul hNs.le, Real.sqrt_eq_rpow (N ^ s), ← Real.rpow_mul hN.le,
      show s * (1 / 2) = s / 2 by ring, Real.sqrt_eq_rpow V]
  have h2 : Real.sqrt (ℓ ^ (-s) * v * V) = ℓ ^ (-s / 2) * Real.sqrt v * Real.sqrt V := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hℓs.le, Real.sqrt_eq_rpow (ℓ ^ (-s)),
      ← Real.rpow_mul hℓ.le, show -s * (1 / 2) = -s / 2 by ring]
  have hNp : 0 < N ^ (s / 2) := Real.rpow_pos_of_pos hN _
  have hℓp : 0 < ℓ ^ (s / 2) := Real.rpow_pos_of_pos hℓ _
  rw [h1, h2, hpow, show -s / 2 = -(s / 2) by ring, Real.rpow_neg hN.le, Real.rpow_neg hℓ.le]
  field_simp

end Riesz1

end
end
