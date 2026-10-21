/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscCountsFixed
public import Riesz1.CLT.GapsDiscCountsPos

/-!
# Interval counts along scales tending to zero

Part of Corollary 1, the case of a limit scale zero. For a scale
sequence `ℓ_N → 0` with `N ℓ_N → ∞`, the compact branch makes the
profile `arcProfile a` admissible, and Theorem 3 gives the rate of the scaled statistic. The factor
`κ(ℓ) = arcKappa` stays bounded for small scales, because `V_s(t) ≥ c t^s` near zero.

A subsequence along which the scales tend to zero is extended to a full scale sequence by filler
values (`exists_filler`), which keeps the admissibility and the mesoscopic condition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Riesz1

/-- The bounded-below periodic zeta function gives a uniform bound on `arcKappa` at small scales:
`arcKappa P a (ℓ) ≤ 1/sqrt(c (2a)^s)` whenever `2aℓ ≤ 1/2`. -/
lemma arcKappa_le_const (P : Parameters) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (c : ℝ)
    (hc : 0 < c)
    (hlow : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
      c * t ^ (parametersExponent P).val ≤ periodicZeta (parametersExponent P) (t : UnitAddCircle))
    (ell : Scale) (hℓ : 2 * a * ell.val ≤ 1 / 2) :
    arcKappa P a ha0 ha1 ell ≤ 1 / Real.sqrt (c * (2 * a) ^ P.val.2) := by
  have hℓ0 : 0 < ell.val := ell.property.1
  have hℓ1 : ell.val ≤ 1 := ell.property.2
  have ht0 : 0 < 2 * a * ell.val := by positivity
  have hv : 0 < countVariance P := gapsDisc_countVariance_pos P
  have hlowV := hlow (2 * a * ell.val) ht0 hℓ
  have hsig : countVariance P * (c * (2 * a) ^ P.val.2) ≤
      (circleVariance P (arcProfile a) ell).toReal := by
    rw [circleVariance_arcProfile ha0 ha1 P ell]
    have hs : (2 * a * ell.val) ^ P.val.2 = (2 * a) ^ P.val.2 * ell.val ^ P.val.2 :=
      Real.mul_rpow (by positivity) hℓ0.le
    have hneg : ell.val ^ (-P.val.2) * ell.val ^ P.val.2 = 1 := by
      rw [← Real.rpow_add hℓ0, neg_add_cancel, Real.rpow_zero]
    have hVb' : c * (2 * a) ^ P.val.2 * ell.val ^ P.val.2 ≤
        periodicZeta (parametersExponent P) ((2 * a * ell.val : ℝ) : UnitAddCircle) := by
      have hlowV := hlow (2 * a * ell.val) ht0 hℓ
      have e : (parametersExponent P).val = P.val.2 := rfl
      rw [e, hs] at hlowV
      simpa only [mul_assoc] using hlowV
    have hpos : 0 ≤ ell.val ^ (-P.val.2) * countVariance P :=
      mul_nonneg (Real.rpow_nonneg hℓ0.le _) hv.le
    calc countVariance P * (c * (2 * a) ^ P.val.2)
        = ell.val ^ (-P.val.2) * countVariance P *
            (c * (2 * a) ^ P.val.2 * ell.val ^ P.val.2) := by
          linear_combination (-(countVariance P * (c * (2 * a) ^ P.val.2))) * hneg
      _ ≤ ell.val ^ (-P.val.2) * countVariance P *
            periodicZeta (parametersExponent P) ((2 * a * ell.val : ℝ) : UnitAddCircle) :=
          mul_le_mul_of_nonneg_left hVb' hpos
  have hσpos : 0 < c * (2 * a) ^ P.val.2 := by
    have : 0 < (2 * a) ^ P.val.2 := Real.rpow_pos_of_pos (by positivity) _
    positivity
  have hsqrt : 0 < Real.sqrt (countVariance P * (c * (2 * a) ^ P.val.2)) :=
    Real.sqrt_pos.mpr (mul_pos hv hσpos)
  unfold arcKappa
  have h1 : Real.sqrt (countVariance P) / Real.sqrt (circleVariance P (arcProfile a) ell).toReal ≤
      Real.sqrt (countVariance P) / Real.sqrt (countVariance P * (c * (2 * a) ^ P.val.2)) := by
    apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
    · exact Real.sqrt_pos.mpr (mul_pos hv hσpos)
    · exact Real.sqrt_le_sqrt hsig
  refine h1.trans (le_of_eq ?_)
  rw [Real.sqrt_mul hv.le]
  have hsv : 0 < Real.sqrt (countVariance P) := Real.sqrt_pos.mpr hv
  field_simp

/-- The CLT rate for an admissible scale sequence: the bounded-Lipschitz distance of the statistic
at scale `ℓ_N` to its normal limit is at most `C (N ℓ_N)^e` with `e < 0` (Theorem 3). -/
lemma clt_rate_general (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hCLT : Internal.CLTConclusion beta s hbeta hs hs1) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (ell : Scales) (d : TestData)
    (hadm : Admissible ⟨(beta, s), hbeta, hs, hs1⟩ (arcProfile a) ell 0 d)
    (hmeso : Mesoscopic ell) :
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℝ, e < 0 ∧ ∀ N : ℕ+, 1 ≤ (N : ℝ) * (ell N).val →
      blDistance (statLaw ⟨(beta, s), hbeta, hs, hs1⟩ ha0 ha1 ell N)
          (normalProbOf (circleVariance ⟨(beta, s), hbeta, hs, hs1⟩ (arcProfile a) (ell N)).toReal) ≤
        ENNReal.ofReal (C * ((N : ℝ) * (ell N).val) ^ e) := by
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hPdef
  have hr : 0 < (2 - s) * (s - 2 * (0 : ℝ)) / (2 * (4 + s)) := by
    apply div_pos
    · apply mul_pos <;> linarith
    · linarith
  have hm : max ((s - 1) / 2) (-((2 - s) * (s - 2 * (0 : ℝ)) / (2 * (4 + s)))) < 0 :=
    max_lt (by linarith) (by linarith)
  obtain ⟨C, hC, hbound⟩ := (hCLT (arcProfile a) 0 d).2
    (-(max ((s - 1) / 2) (-((2 - s) * (s - 2 * (0 : ℝ)) / (2 * (4 + s))))) / 2) (by linarith)
  refine ⟨C, hC, max ((s - 1) / 2) (-((2 - s) * (s - 2 * (0 : ℝ)) / (2 * (4 + s)))) / 2,
    by linarith, fun N hN => ?_⟩
  obtain ⟨-, hN'⟩ := hbound ell hadm hmeso
  obtain ⟨law, hlawEq, hbd⟩ := hN' N hN
  have hstat : statLaw P ha0 ha1 ell N = law := Subtype.ext hlawEq.symm
  have heq : normalProbOf (circleVariance P (arcProfile a) (ell N)).toReal =
      ⟨normalLaw (circleVariance P (arcProfile a) (ell N)).toNNReal,
        by unfold normalLaw; infer_instance⟩ :=
    normalProbOf_eq_normalLaw_toNNReal _
  rw [hstat, heq]
  have e2 : ∀ x : ℝ, -x / 2 + x = x / 2 := fun x => by ring
  rw [e2] at hbd
  exact hbd

/-- **Counts along a scale sequence tending to zero.** If `ℓ_N → 0` with `N ℓ_N → ∞`, the
bounded-Lipschitz distance of the count law to the normal limit of variance `v_s` tends to zero. -/
theorem counts_zero_tendsto (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hCLT : Internal.CLTConclusion beta s hbeta hs hs1) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (ell : Scales) (hmeso : Mesoscopic ell)
    (h0 : Tendsto (fun n => (ell (particleNumber n)).val) atTop (𝓝 0)) :
    Tendsto (fun n => blDistance
        (countLaw ⟨(beta, s), hbeta, hs, hs1⟩ ha0 ha1 ell (particleNumber n))
        (normalProbOf (countVariance ⟨(beta, s), hbeta, hs, hs1⟩))) atTop (𝓝 0) := by
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hPdef
  obtain ⟨d, hd⟩ := admissible_compact_arcIndicator P (c := 0) (a := a) ha0 (by simpa using ha1)
  have hadm : Admissible P (arcProfile a) ell 0 d := hd ell h0
  obtain ⟨C, hC, e, he, hrate⟩ := clt_rate_general beta s hbeta hs hs1 hCLT a ha0 ha1 ell d hadm
    hmeso
  obtain ⟨c, hc, hlow⟩ := periodicZeta_ge_mul_rpow_of_le (parametersExponent P)
    (T := 1 / 2) (by norm_num) le_rfl
  set K₁ : ℝ := 1 / Real.sqrt (c * (2 * a) ^ P.val.2) with hK₁
  have hev1 : ∀ᶠ n in atTop, 2 * a * (ell (particleNumber n)).val ≤ 1 / 2 := by
    have hT : Tendsto (fun n => 2 * a * (ell (particleNumber n)).val) atTop (𝓝 0) := by
      simpa using h0.const_mul (2 * a)
    exact hT.eventually (eventually_le_nhds (by norm_num))
  have hpow : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) * (ell (particleNumber n)).val) ^ e) atTop
      (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).comp hmeso
    simp only [neg_neg] at h
    exact h
  have hbd : ∀ᶠ n in atTop, blDistance (countLaw P ha0 ha1 ell (particleNumber n))
      (normalProbOf (countVariance P)) ≤
        ENNReal.ofReal (max 1 K₁ * (C * (((n + 1 : ℕ) : ℝ) * (ell (particleNumber n)).val) ^ e)) := by
    filter_upwards [hev1, hmeso.eventually_ge_atTop 1] with n h1 h2
    have hℓ0 : 0 < (ell (particleNumber n)).val := (ell _).property.1
    have hℓ1 : (ell (particleNumber n)).val ≤ 1 := (ell _).property.2
    have hσpos : 0 < (circleVariance P (arcProfile a) (ell (particleNumber n))).toReal := by
      rw [circleVariance_arcProfile ha0 ha1 P]
      have ht0 : 0 < 2 * a * (ell (particleNumber n)).val := by positivity
      have ht1 : 2 * a * (ell (particleNumber n)).val < 1 := by nlinarith
      have hV := periodicZeta_pos (parametersExponent P) ht0 ht1
      have hv : 0 < countVariance P := gapsDisc_countVariance_pos P
      have hp : 0 < (ell (particleNumber n)).val ^ (-P.val.2) :=
        Real.rpow_pos_of_pos hℓ0 _
      positivity
    have hscale := blDistance_countLaw_le P ha0 ha1 ell (particleNumber n) hσpos
    have hκ := arcKappa_le_const P ha0 ha1 c hc hlow (ell (particleNumber n)) h1
    have hrate_n := hrate (particleNumber n) h2
    have hp1 : (0 : ℝ) ≤ max 1 K₁ := zero_le_one.trans (le_max_left _ _)
    calc blDistance (countLaw P ha0 ha1 ell (particleNumber n)) (normalProbOf (countVariance P))
        ≤ ENNReal.ofReal (max 1 (arcKappa P a ha0 ha1 (ell (particleNumber n)))) *
          blDistance (statLaw P ha0 ha1 ell (particleNumber n))
            (normalProbOf ((circleVariance P (arcProfile a) (ell (particleNumber n))).toReal)) :=
          hscale
      _ ≤ ENNReal.ofReal (max 1 K₁) * ENNReal.ofReal (C * (((n + 1 : ℕ) : ℝ) *
            (ell (particleNumber n)).val) ^ e) := by
          gcongr
          exact hrate_n
      _ = ENNReal.ofReal (max 1 K₁ * (C * (((n + 1 : ℕ) : ℝ) *
            (ell (particleNumber n)).val) ^ e)) := (ENNReal.ofReal_mul hp1).symm
  have hreal : Tendsto (fun n : ℕ => max 1 K₁ * (C * (((n + 1 : ℕ) : ℝ) *
      (ell (particleNumber n)).val) ^ e)) atTop (𝓝 0) := by
    simpa using (hpow.const_mul C).const_mul (max 1 K₁)
  have hlim := ENNReal.tendsto_ofReal hreal
  simp only [ENNReal.ofReal_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => zero_le) hbd

/-- The particle numbers `n + 1` are injective in `n`. -/
lemma particleNumber_eq_iff {m n : ℕ} : particleNumber m = particleNumber n ↔ m = n := by
  constructor
  · intro h
    have := congrArg (fun M : ℕ+ => (M : ℕ)) h
    simpa [particleNumber] using this
  · rintro rfl
    rfl

/-- The scale `1/sqrt(M)` at the particle number `M`. It is a positive scale tending to zero. -/
def sqrtScale (M : ℕ+) : Scale :=
  ⟨1 / Real.sqrt (M : ℝ), by
    have h1 : (1 : ℝ) ≤ (M : ℝ) := Nat.one_le_cast.mpr M.pos
    have hs : (1 : ℝ) ≤ Real.sqrt (M : ℝ) := by
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (M : ℝ) := Real.sqrt_le_sqrt h1
    have hpos : 0 < Real.sqrt (M : ℝ) := by linarith
    exact ⟨one_div_pos.mpr hpos, (div_le_one hpos).mpr hs⟩⟩

/-- **Filler scales.** Given a subsequence `T` of particle indices on which the scales tend to zero
and keep `N ℓ_N → ∞`, there is a full scale sequence agreeing with `ℓ` on the subsequence, which is
mesoscopic and tends to zero. -/
theorem exists_filler (ell : Scales) (T : ℕ → ℕ) (_hT : Tendsto T atTop atTop)
    (h0 : Tendsto (fun k => (ell (particleNumber (T k))).val) atTop (𝓝 0))
    (hM : Tendsto (fun k => ((T k + 1 : ℕ) : ℝ) * (ell (particleNumber (T k))).val) atTop atTop) :
    ∃ ell' : Scales, (∀ k, ell' (particleNumber (T k)) = ell (particleNumber (T k))) ∧
      Mesoscopic ell' ∧ Tendsto (fun n => (ell' (particleNumber n)).val) atTop (𝓝 0) := by
  classical
  let S : ℕ+ → Prop := fun M => ∃ k, particleNumber (T k) = M
  let ell' : Scales := fun M => if S M then ell M else sqrtScale M
  have hS_iff : ∀ n : ℕ, S (particleNumber n) ↔ ∃ k, T k = n := fun n =>
    exists_congr fun k => particleNumber_eq_iff
  have hv1 : ∀ n : ℕ, (∃ k, T k = n) → ell' (particleNumber n) = ell (particleNumber n) :=
    fun n h => ite_eq_left ((hS_iff n).mpr h)
  have hv2 : ∀ n : ℕ, ¬ (∃ k, T k = n) → ell' (particleNumber n) = sqrtScale (particleNumber n) :=
    fun n h => ite_eq_right (fun h' => h ((hS_iff n).mp h'))
  have hsq_val : ∀ n : ℕ, (sqrtScale (particleNumber n)).val = 1 / Real.sqrt ((n : ℝ) + 1) := by
    intro n
    simp only [sqrtScale, particleNumber_cast]
  have hK : ∀ K : ℝ, ∃ K₁ : ℕ, ∀ k, K₁ ≤ k → K ≤ ((T k + 1 : ℕ) : ℝ) * (ell (particleNumber (T k))).val := by
    intro K
    obtain ⟨K₁, hK₁⟩ := eventually_atTop.mp (hM.eventually_ge_atTop K)
    exact ⟨K₁, hK₁⟩
  refine ⟨ell', fun k => hv1 (T k) ⟨k, rfl⟩, ?_, ?_⟩
  · -- the mesoscopic condition
    refine tendsto_atTop.2 fun K => ?_
    obtain ⟨K₁, hK₁⟩ := hK K
    obtain ⟨N₁, hN₁⟩ := exists_nat_ge (K ^ 2)
    filter_upwards [eventually_ge_atTop ((Finset.range K₁).sup T + N₁ + 1)] with n hn
    by_cases hS : ∃ k, T k = n
    · obtain ⟨k, hk⟩ := hS
      have hk1 : K₁ ≤ k := by
        by_contra hlt
        push Not at hlt
        have hle : T k ≤ (Finset.range K₁).sup T := Finset.le_sup (f := T) (Finset.mem_range.mpr hlt)
        omega
      have hmain := hK₁ k hk1
      rw [hk] at hmain
      show K ≤ ((n + 1 : ℕ) : ℝ) * (ell' (particleNumber n)).val
      rw [hv1 n ⟨k, hk⟩]
      exact hmain
    · show K ≤ ((n + 1 : ℕ) : ℝ) * (ell' (particleNumber n)).val
      rw [hv2 n hS, hsq_val n]
      have hn1 : K ^ 2 ≤ (n : ℝ) + 1 := by
        have hNn : (N₁ : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (by omega : N₁ ≤ n)
        linarith
      have hpos : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have e : ((n + 1 : ℕ) : ℝ) * (1 / Real.sqrt ((n : ℝ) + 1)) = Real.sqrt ((n : ℝ) + 1) := by
        have hsq : Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) = (n : ℝ) + 1 :=
          Real.mul_self_sqrt (by positivity)
        push_cast
        field_simp
        linarith [hsq]
      rw [e]
      calc K ≤ |K| := le_abs_self K
        _ = Real.sqrt (K ^ 2) := (Real.sqrt_sq_eq_abs K).symm
        _ ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt hn1
  · -- the values tend to zero
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp h0 ε hε)
    have hsq : Tendsto (fun n : ℕ => 1 / Real.sqrt ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp h1
      have h3 : Tendsto (fun n : ℕ => (Real.sqrt ((n : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp h2
      simpa only [one_div] using h3
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hsq ε hε)
    filter_upwards [eventually_ge_atTop ((Finset.range K₀).sup T + N₂ + 1)] with n hn
    by_cases hS : ∃ k, T k = n
    · obtain ⟨k, hk⟩ := hS
      have hk1 : K₀ ≤ k := by
        by_contra hlt
        push Not at hlt
        have hle : T k ≤ (Finset.range K₀).sup T := Finset.le_sup (f := T) (Finset.mem_range.mpr hlt)
        omega
      have hmain := hK₀ k hk1
      rw [hk] at hmain
      show dist (ell' (particleNumber n)).val 0 < ε
      rw [hv1 n ⟨k, hk⟩]
      exact hmain
    · show dist (ell' (particleNumber n)).val 0 < ε
      rw [hv2 n hS, hsq_val n]
      exact hN₂ n (by omega)

end Riesz1

end
end
