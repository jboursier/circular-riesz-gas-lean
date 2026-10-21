/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscStripsArc
public import Riesz1.CLT.MainConclusions
public import Riesz1.Gibbs.FluctuationMoments
public import Riesz1.Bridges.FluctuationSquare
public import Riesz1.Kernel.AdmissibleExamplesCompact
public import Riesz1.Kernel.PeriodicZeta
public import Riesz1.Frozen.Variance

/-!
# Variance of the arc count at scales `t ≤ 1/4`

Part of the proof of Corollary 1, the second-moment step for `Nt ≥ 1`. The variance theorem
(Theorem 2) enters as the conclusion `Internal.QuantitativeVarianceConclusion`. For an arc of
length `t` the scale sequence used there equals `2t` at the index `N` and tends to zero, which the
compact branch admits. The output is the bound
`∫ (arcCount - Nt)² ≤ K (Nt)^s`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Riesz1

/-- The count constant `v_s = countVariance P` is positive. -/
lemma gapsDisc_countVariance_pos (P : Parameters) : 0 < countVariance P := by
  obtain ⟨hb, hs, hs1⟩ := P.property
  unfold countVariance
  have hpi := Real.pi_pos
  have hc : 0 < Real.cos (Real.pi * P.val.2 / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith, by nlinarith⟩
  have hsn : 0 < Real.sin (Real.pi * P.val.2 / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
  have hd : 0 < 2 * P.val.1 * Real.pi * P.val.2 := by positivity
  exact div_pos (div_pos hc hsn) hd

/-- The `s`-power bound for the periodic zeta function on short arcs: there is `K` with
`V_s(t) ≤ K t^s` for `0 < t ≤ 1/4`. The bound comes from the asymptotic at zero on `(0, t1]`,
with `t1 = min t0 (1/4)`, and from compactness on `[t1, 1/4]`. -/
lemma periodicZeta_le_mul_rpow (s : RieszExponent) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 4 →
      periodicZeta s (t : UnitAddCircle) ≤ K * t ^ s.val := by
  obtain ⟨C, hC, t0, ht0, hasymp⟩ := periodicZeta_asymptotic s
  set t1 := min t0 (1 / 4) with ht1def
  have ht1 : 0 < t1 := lt_min ht0 (by norm_num)
  have ht1t0 : t1 ≤ t0 := min_le_left _ _
  have hs : 0 < s.val := s.2.1
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := t1) (b := 1 / 4)).exists_bound_of_continuousOn
    (periodicZeta_continuous s).continuousOn
  have hp : 0 < t1 ^ s.val := Real.rpow_pos_of_pos ht1 _
  have hBnn : 0 ≤ |B| := abs_nonneg B
  have hquot : 0 ≤ |B| / t1 ^ s.val := div_nonneg hBnn hp.le
  refine ⟨(1 + C) + |B| / t1 ^ s.val, by linarith, fun t ht0' ht14 => ?_⟩
  have hspos : 0 < t ^ s.val := Real.rpow_pos_of_pos ht0' _
  by_cases htc : t ≤ t1
  · have ha := hasymp t ht0' (htc.trans ht1t0)
    have ht1' : t ≤ 1 := by linarith
    have h2 : t ^ (2 : ℝ) ≤ t ^ s.val :=
      Real.rpow_le_rpow_of_exponent_ge ht0' ht1' (by linarith [s.2.2])
    have h2' : t ^ 2 ≤ t ^ s.val := by
      have e : t ^ (2 : ℝ) = t ^ 2 := Real.rpow_two t
      rw [← e]
      exact h2
    have hab := (abs_le.mp ha).2
    have hC2 : C * t ^ 2 ≤ C * t ^ s.val := mul_le_mul_of_nonneg_left h2' hC.le
    have hK1 : (1 + C) * t ^ s.val ≤ ((1 + C) + |B| / t1 ^ s.val) * t ^ s.val :=
      mul_le_mul_of_nonneg_right (by linarith) hspos.le
    nlinarith
  · have htc' : t1 ≤ t := (not_le.mp htc).le
    have hbd : |periodicZeta s (t : UnitAddCircle)| ≤ B := by
      have := hB t ⟨htc', ht14⟩
      rwa [Real.norm_eq_abs] at this
    have hmono : t1 ^ s.val ≤ t ^ s.val := Real.rpow_le_rpow ht1.le htc' hs.le
    have hkey : |B| ≤ |B| / t1 ^ s.val * t ^ s.val := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hp]
      exact mul_le_mul_of_nonneg_left hmono hBnn
    have hV : periodicZeta s (t : UnitAddCircle) ≤ |B| / t1 ^ s.val * t ^ s.val := by
      have h1 := le_abs_self (periodicZeta s (t : UnitAddCircle))
      have h3 := le_abs_self B
      linarith
    have hK2 : |B| / t1 ^ s.val * t ^ s.val ≤ ((1 + C) + |B| / t1 ^ s.val) * t ^ s.val :=
      mul_le_mul_of_nonneg_right (by linarith) hspos.le
    linarith

/-- The centred count of an arc is the fluctuation of its indicator: for `0 ≤ a ≤ 1/2`,
`arcCount c a X - N (2a) = Fluct_N[1_{arc}](X)`. -/
lemma arcCount_sub_eq_fluctuation {N : ℕ+} (c : UnitAddCircle) {a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1 / 2) (hint : Integrable (arcIndicator c a) volume) (X : Configuration N) :
    arcCount c a X - (N : ℝ) * (2 * a) =
      fluctuation ⟨arcIndicator c a, hint⟩ X := by
  show arcCount c a X - (N : ℝ) * (2 * a) =
    linearStatistic (arcIndicator c a) X - (N : ℝ) * ∫ x, arcIndicator c a x
  rw [integral_arcIndicator c ha0 ha1]
  congr 1

/-- For a probability measure and a square-integrable mean-zero `F`, the variance in the
convention `Riesz1.variance` is the second moment `∫ F²`. -/
lemma toReal_variance_eq_integral_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : Integrable F μ) (hmean : ∫ ω, F ω ∂μ = 0)
    (hsq : Integrable (fun ω => F ω ^ 2) μ) :
    (variance μ F hF).toReal = ∫ ω, F ω ^ 2 ∂μ := by
  unfold variance
  rw [hmean]
  have hint : ∫ ω, F ω ^ 2 ∂μ = (∫⁻ ω, ENNReal.ofReal (F ω ^ 2) ∂μ).toReal := by
    rw [← integral_toReal hsq.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    congr 1
    funext ω
    rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [hint]
  simp only [sub_zero]

/-- The scale `1/M` at the index `M`, a positive scale tending to zero. -/
def invScale (M : ℕ+) : Scale :=
  ⟨1 / (M : ℝ), by
    have hM : (1 : ℝ) ≤ (M : ℝ) := Nat.one_le_cast.mpr M.pos
    exact ⟨by positivity, by rw [div_le_one (by linarith)]; exact hM⟩⟩

/-- The scale sequence with value `2t` at the index `N` and value `1/M` at every other index `M`. -/
def gapsScaleAt (N : ℕ+) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) : Scales :=
  fun M => if M = N then ⟨2 * t, by linarith, by linarith⟩ else invScale M

lemma gapsScaleAt_self (N : ℕ+) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) :
    (gapsScaleAt N t ht0 ht1 N).val = 2 * t := by
  simp [gapsScaleAt]

/-- Away from the index `N`, the scale sequence is `1/M`. -/
lemma gapsScaleAt_val_of_ne (N M : ℕ+) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) (hM : M ≠ N) :
    (gapsScaleAt N t ht0 ht1 M).val = 1 / (M : ℝ) := by
  unfold gapsScaleAt
  simp only [hM, ↓reduceIte]
  rfl

lemma gapsScaleAt_tendsto (N : ℕ+) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) :
    Tendsto (fun n : ℕ => (gapsScaleAt N t ht0 ht1 ⟨n + 1, Nat.succ_pos n⟩).val) atTop (𝓝 0) := by
  have h : (fun n : ℕ => (gapsScaleAt N t ht0 ht1 ⟨n + 1, Nat.succ_pos n⟩).val) =ᶠ[atTop]
      fun n : ℕ => 1 / ((n : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop (N : ℕ)] with n hn
    have hne : (⟨n + 1, Nat.succ_pos n⟩ : ℕ+) ≠ N := by
      intro heq
      have h2 : n + 1 = (N : ℕ) := congrArg PNat.val heq
      omega
    rw [gapsScaleAt_val_of_ne N _ t ht0 ht1 hne]
    simp
  exact Tendsto.congr' h.symm tendsto_one_div_add_atTop_nhds_zero_nat

/-- The power identity `(a b)^s b^{-s} = a^s` for positive `b`. -/
lemma rpow_mul_rpow_neg_cancel (a b s : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    (a * b) ^ s * b ^ (-s) = a ^ s := by
  rw [Real.mul_rpow ha hb.le, Real.rpow_neg hb.le, mul_assoc,
    mul_inv_cancel₀ (Real.rpow_pos_of_pos hb s).ne', mul_one]

/-- The arc count is the fluctuation of the arc profile, with the mean `Nt` of the arc of length
`t`: `arcCount 0 (t/2) X - N t = Fluct_N[1_{arc}](X)`. -/
lemma gapsArc_fluctuation_eq (N : ℕ+) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) :
    ∃ hmem : MemLp (arcIndicator 0 (t / 2)) 2 volume,
      ∀ X : Configuration N, fluctuation ⟨arcIndicator 0 (t / 2), hmem.integrable one_le_two⟩ X =
        arcCount 0 (t / 2) X - (N : ℝ) * t := by
  have hmem : MemLp (arcIndicator 0 (t / 2)) 2 volume := by
    simpa using (memLp_arcIndicator 0 (t / 2)).re
  refine ⟨hmem, fun X => ?_⟩
  rw [← arcCount_sub_eq_fluctuation 0 (by linarith) (by linarith) (hmem.integrable one_le_two) X]
  congr 1
  ring

/-- **The arc second moment.** For the open arc of length `t` about `0`, with `Nt ≥ 1`, the second
moment of the centred count is at most `K (Nt)^s` for a constant `K` depending only on `beta, s`.
The input is the variance conclusion `QuantitativeVarianceConclusion`, used with the
compact profile `gapsArcProfile` and the scale sequence `gapsScaleAt N t`. -/
theorem gapsArc_integral_sq_le (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hQV : Internal.QuantitativeVarianceConclusion beta s hbeta hs hs1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ+) (t : ℝ), 0 < t → t ≤ 1 / 4 → 1 ≤ (N : ℝ) * t →
      ∫ X, (arcCount 0 (t / 2) X - (N : ℝ) * t) ^ 2 ∂(gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N) ≤
        K * ((N : ℝ) * t) ^ s := by
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hPdef
  have hv : 0 < countVariance P := gapsDisc_countVariance_pos P
  obtain ⟨K₀, hK₀, hV⟩ := periodicZeta_le_mul_rpow (parametersExponent P)
  set ε : ℝ := min s (1 - s) / 2 with hεdef
  have hεpos : 0 < ε := by
    have : 0 < min s (1 - s) := lt_min hs (by linarith)
    rw [hεdef]
    linarith
  have hεs : ε ≤ s := by
    have := min_le_left s (1 - s)
    rw [hεdef]
    linarith
  have hε1 : ε ≤ 1 - s := by
    have := min_le_right s (1 - s)
    rw [hεdef]
    linarith
  obtain ⟨d, hd⟩ := admissible_compact_arcIndicator P (c := 0) (a := 1 / 4) (by norm_num)
    (by norm_num)
  obtain ⟨C, hC, hbound⟩ := (hQV gapsArcProfile 0 d).2.1 ε hεpos
  refine ⟨countVariance P * K₀ + 2 * C, by positivity, fun N t ht0 ht1 hNt => ?_⟩
  obtain ⟨hmem, hpt⟩ := gapsArc_fluctuation_eq N ht0 ht1
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hadm : Admissible P gapsArcProfile (gapsScaleAt N t ht0 ht1) 0 d :=
    hd _ (gapsScaleAt_tendsto N t ht0 ht1)
  have hN1 : 1 ≤ (N : ℝ) * (gapsScaleAt N t ht0 ht1 N).val := by
    rw [gapsScaleAt_self]
    linarith
  obtain ⟨hF, _, hineq⟩ := hbound (gapsScaleAt N t ht0 ht1) hadm N hN1
  have hfun : testAtScale gapsArcProfile (gapsScaleAt N t ht0 ht1 N) = arcIndicator 0 (t / 2) := by
    rw [testAtScale_gapsArcProfile, gapsScaleAt_self, show 2 * t / 4 = t / 2 by ring]
  have hsub : (⟨testAtScale gapsArcProfile (gapsScaleAt N t ht0 ht1 N),
      testAtScaleL1 gapsArcProfile (gapsScaleAt N t ht0 ht1 N)⟩ :
        {f : UnitAddCircle → ℝ // Integrable f volume}) =
      ⟨arcIndicator 0 (t / 2), hmem.integrable one_le_two⟩ :=
    Subtype.ext hfun
  have hmean : ∫ X, fluctuation ⟨testAtScale gapsArcProfile (gapsScaleAt N t ht0 ht1 N),
      testAtScaleL1 gapsArcProfile (gapsScaleAt N t ht0 ht1 N)⟩ X
        ∂(gibbsMeasure P N) = 0 := by
    rw [hsub]
    exact integral_fluctuation_eq_zero P N hmem
  have hsqF : Integrable (fun X => fluctuation ⟨testAtScale gapsArcProfile
      (gapsScaleAt N t ht0 ht1 N), testAtScaleL1 gapsArcProfile (gapsScaleAt N t ht0 ht1 N)⟩ X ^ 2)
        (gibbsMeasure P N) := by
    rw [hsub]
    exact (memLp_fluctuation P N hmem).integrable_sq
  have hvarEq := toReal_variance_eq_integral_sq (gibbsMeasure P N) _ hF hmean hsqF
  have hpt' : ∀ X : Configuration N, fluctuation ⟨testAtScale gapsArcProfile
      (gapsScaleAt N t ht0 ht1 N), testAtScaleL1 gapsArcProfile (gapsScaleAt N t ht0 ht1 N)⟩ X =
        arcCount 0 (t / 2) X - (N : ℝ) * t := by
    intro X
    rw [hsub]
    exact hpt X
  have hsqEq : ∫ X, fluctuation ⟨testAtScale gapsArcProfile (gapsScaleAt N t ht0 ht1 N),
      testAtScaleL1 gapsArcProfile (gapsScaleAt N t ht0 ht1 N)⟩ X ^ 2 ∂(gibbsMeasure P N) =
        ∫ X, (arcCount 0 (t / 2) X - (N : ℝ) * t) ^ 2 ∂(gibbsMeasure P N) := by
    simp only [hpt']
  rw [hvarEq, hsqEq, circleVariance_gapsArcProfile, gapsScaleAt_self,
    show 2 * t / 2 = t by ring] at hineq
  have hVt : periodicZeta (parametersExponent P) (t : UnitAddCircle) ≤ K₀ * t ^ s := hV t ht0 ht1
  have hbase : 1 ≤ (N : ℝ) * (2 * t) := by linarith
  have hcancel := rpow_mul_rpow_neg_cancel (N : ℝ) (2 * t) s (by positivity) (by positivity)
  have hsimp : ((N : ℝ) * (2 * t)) ^ s * ((2 * t) ^ (-s) * countVariance P *
      periodicZeta (parametersExponent P) (t : UnitAddCircle)) =
        (N : ℝ) ^ s * (countVariance P * periodicZeta (parametersExponent P) (t : UnitAddCircle)) := by
    calc _ = ((N : ℝ) * (2 * t)) ^ s * (2 * t) ^ (-s) *
          (countVariance P * periodicZeta (parametersExponent P) (t : UnitAddCircle)) := by ring
      _ = _ := by rw [hcancel]
  rw [hsimp] at hineq
  have hI := (abs_le.mp hineq).2
  have hA : (N : ℝ) ^ s * (countVariance P * periodicZeta (parametersExponent P) (t : UnitAddCircle)) ≤
      countVariance P * K₀ * ((N : ℝ) * t) ^ s := by
    have hmul : countVariance P * periodicZeta (parametersExponent P) (t : UnitAddCircle) ≤
        countVariance P * (K₀ * t ^ s) := mul_le_mul_of_nonneg_left hVt hv.le
    rw [Real.mul_rpow (by positivity) ht0.le]
    calc (N : ℝ) ^ s * (countVariance P * periodicZeta (parametersExponent P) (t : UnitAddCircle))
        ≤ (N : ℝ) ^ s * (countVariance P * (K₀ * t ^ s)) :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = countVariance P * K₀ * ((N : ℝ) ^ s * t ^ s) := by ring
  have he : max (2 * s - 1) (2 * (0 : ℝ)) + ε ≤ s := by
    have h1 : 2 * s - 1 ≤ s - ε := by linarith
    have h2 : 2 * (0 : ℝ) ≤ s - ε := by linarith
    have := max_le h1 h2
    linarith
  have hB1 : ((N : ℝ) * (2 * t)) ^ (max (2 * s - 1) (2 * (0 : ℝ)) + ε) ≤ ((N : ℝ) * (2 * t)) ^ s :=
    Real.rpow_le_rpow_of_exponent_le hbase he
  have hB2 : ((N : ℝ) * (2 * t)) ^ s = (2 : ℝ) ^ s * ((N : ℝ) * t) ^ s := by
    rw [show (N : ℝ) * (2 * t) = 2 * ((N : ℝ) * t) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
  have hB3 : (2 : ℝ) ^ s ≤ 2 := by
    calc (2 : ℝ) ^ s ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1.le
      _ = 2 := Real.rpow_one 2
  have hQ : 0 ≤ ((N : ℝ) * t) ^ s := by positivity
  have hB : C * ((N : ℝ) * (2 * t)) ^ (max (2 * s - 1) (2 * (0 : ℝ)) + ε) ≤
      2 * C * ((N : ℝ) * t) ^ s := by
    have h4 : C * ((N : ℝ) * (2 * t)) ^ (max (2 * s - 1) (2 * (0 : ℝ)) + ε) ≤
        C * ((2 : ℝ) ^ s * ((N : ℝ) * t) ^ s) := by
      rw [← hB2]
      exact mul_le_mul_of_nonneg_left (hB1) hC.le
    have h5 : (2 : ℝ) ^ s * ((N : ℝ) * t) ^ s ≤ 2 * ((N : ℝ) * t) ^ s :=
      mul_le_mul_of_nonneg_right hB3 hQ
    nlinarith [hC.le]
  calc _ ≤ C * ((N : ℝ) * (2 * t)) ^ (max (2 * s - 1) (2 * (0 : ℝ)) + ε) +
          (N : ℝ) ^ s * (countVariance P * periodicZeta (parametersExponent P) (t : UnitAddCircle)) :=
        sub_le_iff_le_add.mp hI
    _ ≤ 2 * C * ((N : ℝ) * t) ^ s + countVariance P * K₀ * ((N : ℝ) * t) ^ s :=
        add_le_add hB hA
    _ = (countVariance P * K₀ + 2 * C) * ((N : ℝ) * t) ^ s := by ring

end Riesz1

end
end
