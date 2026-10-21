/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscCountsLaws
public import Riesz1.CLT.GapsDiscStrips
public import Riesz1.CLT.MainConclusions
public import Riesz1.ToMathlib.BLCoupling
public import Riesz1.Kernel.AdmissibleExamplesPositive
public import Riesz1.Kernel.AdmissibleExamplesCompact

/-!
# Interval counts at a fixed scale

Part of Corollary 1 at a fixed scale `g ∈ (0, 1]`. The count of
the arc of half-width `a g` is, up to the factor `1/sqrt(V_s(2ag))`, the CLT statistic of the
profile `arcProfile (a g)` at scale one. The CLT rate at scale one (the conclusion of
Theorem 3, taken as an explicit hypothesis) and the bounded-Lipschitz scaling
`blDistance_map_mul_left_le` give convergence of the count law at the fixed scale `g`.

The file also gives the variance bound at scale one, used in the coupling of the next file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Riesz1

/-- The constant scale `g` on every particle number. -/
def constScales (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1) : Scales := fun _ => ⟨g, hg0, hg1⟩

/-- The constant scale one. -/
def oneScales : Scales := fun _ => ⟨1, zero_lt_one, le_rfl⟩

/-- The scale-one circle variance of the arc profile is `v_s V_s(2a)`. -/
lemma circleVariance_arcProfile_one (P : Parameters) {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1 / 2) :
    (circleVariance P (arcProfile h) ⟨1, zero_lt_one, le_rfl⟩).toReal =
      countVariance P * periodicZeta (parametersExponent P) ((2 * h : ℝ) : UnitAddCircle) := by
  rw [circleVariance_arcProfile hh0 hh1 P ⟨1, zero_lt_one, le_rfl⟩]
  simp only [Real.one_rpow, one_mul, mul_one]

/-- The normal law of variance `x` (for `x ≥ 0`), as a probability measure. -/
def normalProbOf (x : ℝ) : ProbabilityMeasure ℝ :=
  ⟨normalLaw (Real.toNNReal x), by unfold normalLaw; infer_instance⟩

/-- Scaling a normal law of variance `σ²` by `κ` with `κ² σ² = v` gives the normal law of variance
`v`. -/
lemma normalProbOf_map (κ σ v : ℝ) (hσ : 0 ≤ σ) (hv : 0 ≤ v) (h : κ ^ 2 * σ = v) :
    (normalProbOf σ).map (κ * ·) = normalProbOf v :=
  Subtype.ext (normalLaw_map_mul_real κ σ v hσ hv h)

/-- The `ℝ≥0∞`-valued circle variance and its real value have the same `ℝ≥0` truncation. -/
lemma toNNReal_toReal_eq (x : ℝ≥0∞) : Real.toNNReal x.toReal = x.toNNReal := by
  simp [ENNReal.toReal]

/-- The normal probability of the variance `σ²` given as the `toNNReal` of an `ℝ≥0∞`-valued
variance, as used in Theorem 3. -/
lemma normalProbOf_eq_normalLaw_toNNReal (x : ℝ≥0∞) :
    normalProbOf x.toReal = ⟨normalLaw x.toNNReal, by unfold normalLaw; infer_instance⟩ :=
  Subtype.ext (congrArg normalLaw (toNNReal_toReal_eq x))

/-- The law of the normalized count of profile `arcProfile a` at scale `ℓ` is the law of the CLT
statistic pushed forward by `κ`, and the normal limit of the count is the normal limit of the
statistic pushed forward by `κ`. Hence the bounded-Lipschitz distance of the count law to the
limit of variance `v_s` is at most `max(1, κ)` times that of the statistic. -/
lemma blDistance_countLaw_le (P : Parameters) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (ell : Scales) (N : ℕ+)
    (hσ : 0 < (circleVariance P (arcProfile a) (ell N)).toReal) :
    blDistance (countLaw P ha0 ha1 ell N) (normalProbOf (countVariance P)) ≤
      ENNReal.ofReal (max 1 (arcKappa P a ha0 ha1 (ell N))) *
        blDistance (statLaw P ha0 ha1 ell N)
          (normalProbOf ((circleVariance P (arcProfile a) (ell N)).toReal)) := by
  set σ2 := (circleVariance P (arcProfile a) (ell N)).toReal with hσ2
  have hv : 0 < countVariance P := gapsDisc_countVariance_pos P
  have hκ : 0 < arcKappa P a ha0 ha1 (ell N) := by
    unfold arcKappa
    exact div_pos (Real.sqrt_pos.mpr hv) (Real.sqrt_pos.mpr hσ)
  have hsq : arcKappa P a ha0 ha1 (ell N) ^ 2 * σ2 = countVariance P := by
    unfold arcKappa
    rw [div_pow, Real.sq_sqrt hv.le, Real.sq_sqrt hσ.le]
    field_simp
  have hlim : normalProbOf (countVariance P) =
      (normalProbOf σ2).map (arcKappa P a ha0 ha1 (ell N) * ·) :=
    (normalProbOf_map _ σ2 _ hσ.le hv.le hsq).symm
  rw [countLaw_eq_map_statLaw, hlim]
  exact blDistance_map_mul_left_le hκ _ _

/-- The second moment of the centred arc count at scale one, at a fixed half-width. This is the
variance conclusion of Theorem 2 at the scale sequence `1`. -/
lemma arc_scale_one_integral_sq_le (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hQV : Internal.QuantitativeVarianceConclusion beta s hbeta hs hs1) (h : ℝ) (hh0 : 0 < h)
    (hh1 : h < 1 / 2) :
    ∃ K : ℝ, ∀ N : ℕ+,
      ∫ X, (arcCount 0 h X - (N : ℝ) * (2 * h)) ^ 2
        ∂(gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N) ≤ K * (N : ℝ) ^ s := by
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hPdef
  obtain ⟨d, hd⟩ := admissible_arcIndicator P hh0 hh1 0
  have hε : 0 < min s (1 - s) / 2 := by
    have : 0 < min s (1 - s) := lt_min hs (by linarith)
    linarith
  have hεs : min s (1 - s) / 2 ≤ s := by linarith [min_le_left s (1 - s)]
  have hε1 : min s (1 - s) / 2 ≤ 1 - s := by linarith [min_le_right s (1 - s)]
  obtain ⟨C, hC, hbound⟩ := (hQV (arcProfile h) 0 d).2.1 _ hε
  refine ⟨(circleVariance P (arcProfile h) ⟨1, zero_lt_one, le_rfl⟩).toReal + C, fun N => ?_⟩
  have hN1 : 1 ≤ (N : ℝ) * (oneScales N).val := by
    simp [oneScales]
    exact_mod_cast N.pos
  obtain ⟨hF, _, hineq⟩ := hbound oneScales hd N hN1
  have hmem : MemLp (arcIndicator 0 h) 2 volume := by
    simpa using (memLp_arcIndicator 0 h).re
  have hsub : (⟨testAtScale (arcProfile h) (oneScales N),
      testAtScaleL1 (arcProfile h) (oneScales N)⟩ :
        {f : UnitAddCircle → ℝ // Integrable f volume}) =
      ⟨arcIndicator 0 h, hmem.integrable one_le_two⟩ := by
    apply Subtype.ext
    have := testAtScale_arcProfile hh0 hh1 (oneScales N)
    have hval : (oneScales N).val = 1 := rfl
    rw [hval, mul_one] at this
    exact this
  have hpt : ∀ X : Configuration N,
      fluctuation ⟨testAtScale (arcProfile h) (oneScales N),
        testAtScaleL1 (arcProfile h) (oneScales N)⟩ X =
          arcCount 0 h X - (N : ℝ) * (2 * h) := by
    intro X
    rw [hsub]
    exact (arcCount_sub_eq_fluctuation 0 hh0.le hh1.le _ X).symm
  have hmean : ∫ X, fluctuation ⟨testAtScale (arcProfile h) (oneScales N),
      testAtScaleL1 (arcProfile h) (oneScales N)⟩ X ∂(gibbsMeasure P N) = 0 := by
    rw [hsub]
    exact integral_fluctuation_eq_zero P N hmem
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hsqF : Integrable (fun X => fluctuation ⟨testAtScale (arcProfile h) (oneScales N),
      testAtScaleL1 (arcProfile h) (oneScales N)⟩ X ^ 2) (gibbsMeasure P N) := by
    rw [hsub]
    exact (memLp_fluctuation P N hmem).integrable_sq
  have hvarEq := toReal_variance_eq_integral_sq (gibbsMeasure P N) _ hF hmean hsqF
  have hsqEq : ∫ X, fluctuation ⟨testAtScale (arcProfile h) (oneScales N),
      testAtScaleL1 (arcProfile h) (oneScales N)⟩ X ^ 2 ∂(gibbsMeasure P N) =
        ∫ X, (arcCount 0 h X - (N : ℝ) * (2 * h)) ^ 2 ∂(gibbsMeasure P N) := by
    simp only [hpt]
  rw [hvarEq, hsqEq] at hineq
  have hval : (oneScales N).val = 1 := rfl
  have hσ : (circleVariance P (arcProfile h) (oneScales N)).toReal =
      (circleVariance P (arcProfile h) ⟨1, zero_lt_one, le_rfl⟩).toReal := rfl
  rw [hval, mul_one, hσ] at hineq
  have hsN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast N.pos
  have he' : max (2 * s - 1) (2 * (0 : ℝ)) + min s (1 - s) / 2 ≤ s := by
    have h1 : 2 * s - 1 ≤ s - min s (1 - s) / 2 := by linarith
    have h2 : 2 * (0 : ℝ) ≤ s - min s (1 - s) / 2 := by linarith
    have := max_le h1 h2
    linarith
  have hC' : C * (N : ℝ) ^ (max (2 * s - 1) (2 * (0 : ℝ)) + min s (1 - s) / 2) ≤ C * (N : ℝ) ^ s :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hsN he') hC.le
  have h1 := (abs_le.mp hineq).2
  have key : ∫ X, (arcCount 0 h X - (N : ℝ) * (2 * h)) ^ 2 ∂(gibbsMeasure P N) ≤
      (N : ℝ) ^ s * (circleVariance P (arcProfile h) ⟨1, zero_lt_one, le_rfl⟩).toReal +
        C * (N : ℝ) ^ s := by
    linarith [h1, hC']
  calc ∫ X, (arcCount 0 h X - (N : ℝ) * (2 * h)) ^ 2 ∂(gibbsMeasure P N)
      ≤ (N : ℝ) ^ s * (circleVariance P (arcProfile h) ⟨1, zero_lt_one, le_rfl⟩).toReal +
        C * (N : ℝ) ^ s := key
    _ = ((circleVariance P (arcProfile h) ⟨1, zero_lt_one, le_rfl⟩).toReal + C) * (N : ℝ) ^ s := by
        ring


/-- The inverse square root of the variance factor at scale one. -/
lemma inv_sqrt_scale_one (s N V : ℝ) (hN : 0 < N) (hV : 0 < V) :
    1 / Real.sqrt (N ^ s * V) = 1 / Real.sqrt V * N ^ (-s / 2) := by
  have := inv_sqrt_eq_normalization s N 1 1 V hN one_pos one_pos hV
  simpa [Real.one_rpow, Real.sqrt_one, mul_one, one_mul] using this

/-- The scale-one CLT rate: for the arc profile of half-width `h`, the bounded-Lipschitz distance of
the scale-one statistic to its normal limit is at most `C N^e` with `e < 0`. This is the
quantitative conclusion of Theorem 3 at the constant scale one. -/
lemma clt_scale_one_rate (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hCLT : Internal.CLTConclusion beta s hbeta hs hs1) (h : ℝ) (hh0 : 0 < h) (hh1 : h < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℝ, e < 0 ∧ ∀ N : ℕ+,
      blDistance (statLaw ⟨(beta, s), hbeta, hs, hs1⟩ hh0 hh1 oneScales N)
          (normalProbOf (circleVariance ⟨(beta, s), hbeta, hs, hs1⟩ (arcProfile h)
            ⟨1, zero_lt_one, le_rfl⟩).toReal) ≤
        ENNReal.ofReal (C * (N : ℝ) ^ e) := by
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hPdef
  obtain ⟨d, hd⟩ := admissible_arcIndicator P hh0 hh1 0
  have hr : 0 < (2 - s) * (s - 2 * (0 : ℝ)) / (2 * (4 + s)) := by
    apply div_pos
    · apply mul_pos <;> linarith
    · linarith
  have hm : max ((s - 1) / 2) (-((2 - s) * (s - 2 * (0 : ℝ)) / (2 * (4 + s)))) < 0 :=
    max_lt (by linarith) (by linarith)
  obtain ⟨C, hC, hbound⟩ := (hCLT (arcProfile h) 0 d).2
    (-(max ((s - 1) / 2) (-((2 - s) * (s - 2 * (0 : ℝ)) / (2 * (4 + s))))) / 2) (by linarith)
  refine ⟨C, hC, max ((s - 1) / 2) (-((2 - s) * (s - 2 * (0 : ℝ)) / (2 * (4 + s)))) / 2,
    by linarith, fun N => ?_⟩
  have hmeso : Mesoscopic oneScales := by
    unfold Mesoscopic oneScales
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1) |>.congr fun n => by simp
  obtain ⟨-, hN⟩ := hbound oneScales hd hmeso
  obtain ⟨law, hlawEq, hbd⟩ := hN N (by simp [oneScales]; exact_mod_cast N.pos)
  have hstat : statLaw P hh0 hh1 oneScales N = law := Subtype.ext hlawEq.symm
  have heq : normalProbOf (circleVariance P (arcProfile h) ⟨1, zero_lt_one, le_rfl⟩).toReal =
      ⟨normalLaw (circleVariance P (arcProfile h) (oneScales N)).toNNReal,
        by unfold normalLaw; infer_instance⟩ :=
    normalProbOf_eq_normalLaw_toNNReal _
  rw [hstat, heq]
  have e1 : (N : ℝ) * (oneScales N).val = N := by simp [oneScales]
  have e2 : ∀ x : ℝ, -x / 2 + x = x / 2 := fun x => by ring
  rw [e1, e2] at hbd
  exact hbd

/-- The fixed-scale count CLT: at a constant scale `g ∈ (0, 1]`, the count law converges to the
normal law of variance `v_s`, with the bounded-Lipschitz distance tending to zero along particle
numbers `n + 1`. -/
theorem fixed_scale_tendsto (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hCLT : Internal.CLTConclusion beta s hbeta hs hs1) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1) :
    Tendsto (fun n : ℕ => blDistance
        (countLaw ⟨(beta, s), hbeta, hs, hs1⟩ ha0 ha1 (constScales g hg0 hg1) (particleNumber n))
        (normalProbOf (countVariance ⟨(beta, s), hbeta, hs, hs1⟩))) atTop (𝓝 0) := by
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hPdef
  have hh0 : 0 < a * g := mul_pos ha0 hg0
  have hh1 : a * g < 1 / 2 := by nlinarith
  obtain ⟨C, hC, e, he, hrate⟩ := clt_scale_one_rate beta s hbeta hs hs1 hCLT (a * g) hh0 hh1
  have hv : 0 < countVariance P := gapsDisc_countVariance_pos P
  have hVpos : 0 < periodicZeta (parametersExponent P) ((2 * a * g : ℝ) : UnitAddCircle) :=
    periodicZeta_pos _ (by positivity) (by nlinarith)
  set V := periodicZeta (parametersExponent P) ((2 * a * g : ℝ) : UnitAddCircle) with hVdef
  set κ : ℝ := 1 / Real.sqrt V with hκdef
  have hκ : 0 < κ := by
    rw [hκdef]
    exact div_pos one_pos (Real.sqrt_pos.mpr hVpos)
  -- the fixed-scale count is `κ` times the scale-one statistic of the profile `arcProfile (a g)`
  have hpt : ∀ (N : ℕ+) (X : Configuration N),
      normalizedCount P a ha0 ha1 (constScales g hg0 hg1) N X =
        κ * normalizedStatistic P (arcProfile (a * g)) oneScales N X := by
    intro N X
    have hsc : (constScales g hg0 hg1 N).val = g := rfl
    have hso : (oneScales N).val = 1 := rfl
    rw [normalizedCount_eq_arcCount, normalizedStatistic_arcProfile P hh0 hh1 oneScales N X, hsc,
      hso, mul_one, mul_one]
    have hN : (0 : ℝ) < N := by positivity
    have hinv := inv_sqrt_scale_one P.val.2 (N : ℝ) V hN hVpos
    rw [hκdef, div_eq_mul_one_div _ (Real.sqrt ((N : ℝ) ^ P.val.2 * V)), hinv]
    ring
  have hE1 : ∀ N : ℕ+, countLaw P ha0 ha1 (constScales g hg0 hg1) N =
      (statLaw P hh0 hh1 oneScales N).map (κ * ·) := by
    intro N
    apply Subtype.ext
    unfold countLaw statLaw
    change (gibbsMeasure P N).map (normalizedCount P a ha0 ha1 (constScales g hg0 hg1) N) =
      ((gibbsMeasure P N).map (normalizedStatistic P (arcProfile (a * g)) oneScales N)).map
        (κ * ·)
    rw [Measure.map_map (measurable_const_mul _)
      (measurable_normalizedStatistic_arcProfile P hh0 hh1 oneScales)]
    congr 1
    funext X
    exact hpt N X
  -- the limit variance: `κ² σ₁² = v_s` for the scale-one variance `σ₁² = v_s V_s(2ag)`
  have hσ1 : (circleVariance P (arcProfile (a * g)) ⟨1, zero_lt_one, le_rfl⟩).toReal =
      countVariance P * periodicZeta (parametersExponent P) ((2 * (a * g) : ℝ) : UnitAddCircle) :=
    circleVariance_arcProfile_one P hh0 hh1
  have hVeq : (2 * a * g : ℝ) = 2 * (a * g) := by ring
  have hσ1' : (circleVariance P (arcProfile (a * g)) ⟨1, zero_lt_one, le_rfl⟩).toReal =
      countVariance P * V := by
    rw [hσ1, hVdef, hVeq]
  have hσnn : 0 ≤ (circleVariance P (arcProfile (a * g)) ⟨1, zero_lt_one, le_rfl⟩).toReal := by
    rw [hσ1']
    positivity
  have hE2 : normalProbOf (countVariance P) =
      (normalProbOf (circleVariance P (arcProfile (a * g)) ⟨1, zero_lt_one, le_rfl⟩).toReal).map
        (κ * ·) := by
    symm
    apply normalProbOf_map κ _ _ hσnn hv.le
    rw [hσ1', hκdef, div_pow, one_pow, Real.sq_sqrt hVpos.le]
    field_simp
  -- the scale-one CLT rate and the scaling bound
  have hpn : ∀ n : ℕ, ((particleNumber n : ℕ+) : ℝ) = (n : ℝ) + 1 := fun n => by
    simp [particleNumber]
  have hp0 : (0 : ℝ) ≤ max 1 κ := zero_le_one.trans (le_max_left _ _)
  have hbd : ∀ n : ℕ, blDistance (countLaw P ha0 ha1 (constScales g hg0 hg1) (particleNumber n))
      (normalProbOf (countVariance P)) ≤
        ENNReal.ofReal (max 1 κ * (C * ((particleNumber n : ℕ+) : ℝ) ^ e)) := by
    intro n
    rw [hE1, hE2]
    refine (blDistance_map_mul_left_le hκ _ _).trans ?_
    have hrate_n := hrate (particleNumber n)
    calc ENNReal.ofReal (max 1 κ) * blDistance (statLaw P hh0 hh1 oneScales (particleNumber n))
          (normalProbOf (circleVariance P (arcProfile (a * g)) ⟨1, zero_lt_one, le_rfl⟩).toReal)
        ≤ ENNReal.ofReal (max 1 κ) * ENNReal.ofReal (C * ((particleNumber n : ℕ+) : ℝ) ^ e) :=
          by gcongr
      _ = ENNReal.ofReal (max 1 κ * (C * ((particleNumber n : ℕ+) : ℝ) ^ e)) :=
          (ENNReal.ofReal_mul hp0).symm
  have hreal : Tendsto (fun n : ℕ => max 1 κ * (C * ((particleNumber n : ℕ+) : ℝ) ^ e)) atTop
      (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => ((particleNumber n : ℕ+) : ℝ)) atTop atTop := by
      simp_rw [hpn]
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hpow : Tendsto (fun n : ℕ => ((particleNumber n : ℕ+) : ℝ) ^ e) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).comp hp
      simp only [neg_neg] at h
      exact h
    simpa using (hpow.const_mul C).const_mul (max 1 κ)
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (max 1 κ * (C * ((particleNumber n : ℕ+) : ℝ) ^ e)))
      atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hreal
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le) hbd

end Riesz1

end
end
