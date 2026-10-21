/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscSelectedCount
public import Riesz1.CLT.GapsDiscCounts
public import Riesz1.CLT.GapsDiscCountsLaws
public import Riesz1.CLT.GapsDiscRotation
public import Riesz1.CLT.GapsDiscScale
public import Riesz1.CLT.GapsDiscStripsVariance
public import Riesz1.CLT.TestConvergence
public import Riesz1.CLT.VaryingLimit
public import Riesz1.ToMathlib.BLCoupling
public import Riesz1.ToMathlib.CdfSandwich
public import Riesz1.Bridges.IndicatorArc

/-!
# The selected count CLT

Part of the proof of Corollary 1. For integers `1 ≤ k_N ≤ ⌊N/2⌋` with
`k_N → ∞`, the selected discrepancy `Δ_N` satisfies `Δ_N / b_{N,k_N} → N(0, v_s)` in law.

The proof has three steps. First, the centred open-arc count `C_N(0, k/N)` of the selected count
has the same bounded-Lipschitz law as the normalized arc count at the scale `ℓ_N = 2k_N/N`, because
the Gibbs law is invariant under rotation. The count theorem `counts_tendsto` then gives its normal
limit. Second, the tail bound `selected_count_tail` shows that `(Δ_N - C_N)/b_N` is small in
probability. Third, the two steps combine through the bounded-Lipschitz coupling bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Riesz1

/-- Rotation invariance of the normalized arc count: the law of `(arcCount c h - k) / b` under the
Gibbs measure does not depend on the centre `c`. The rotation `x ↦ x - c` carries the arc about `c`
to the arc about `0`. -/
theorem integral_arcCount_rotate (P : Parameters) (N : ℕ+) (c : UnitAddCircle) (h k b : ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ X, f ((arcCount c h X - k) / b) ∂(gibbsMeasure P N) =
      ∫ X, f ((arcCount 0 h X - k) / b) ∂(gibbsMeasure P N) := by
  have hΦ : Measurable (fun y : ℝ => f ((y - k) / b)) :=
    hf.comp ((measurable_id.sub_const k).div_const b)
  have key := integral_rotate_linearStatistic P N (arcIndicator 0 h) (-c)
    (fun y => f ((y - k) / b)) hΦ (measurable_arcIndicator 0 h)
  have hfun : (fun x : UnitAddCircle => arcIndicator 0 h (x + -c)) = arcIndicator c h := by
    funext x
    exact (arcIndicator_eq_arcIndicator_zero_add_neg c h x).symm
  rw [hfun] at key
  exact key

/-- The law of a real function of the configuration under the Gibbs measure. -/
lemma integral_gibbsProb_map (P : Parameters) (N : ℕ+) {Y : Configuration N → ℝ}
    (hY : Measurable Y) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂((gibbsProb P N).map Y : Measure ℝ) = ∫ X, f (Y X) ∂(gibbsMeasure P N) :=
  integral_map hY.aemeasurable hf.aestronglyMeasurable

/-- The bounded-Lipschitz distance from a normalized arc count to any fixed law does not depend on
the centre of the arc. -/
theorem blDistance_map_arcCount_rotate (P : Parameters) (N : ℕ+) (c : UnitAddCircle) (h k b : ℝ)
    (ν : ProbabilityMeasure ℝ) :
    blDistance ((gibbsProb P N).map (fun X => (arcCount c h X - k) / b)) ν =
      blDistance ((gibbsProb P N).map (fun X => (arcCount 0 h X - k) / b)) ν := by
  refine blDistance_eq_of_integral_eq fun f hf => ?_
  have hfm : Measurable f := hf.1.continuous.measurable
  have hY : ∀ c' : UnitAddCircle, Measurable (fun X : Configuration N => (arcCount c' h X - k) / b) :=
    fun c' => ((measurable_arcCount c' h).sub_const k).div_const b
  rw [integral_gibbsProb_map P N (hY c) hfm, integral_gibbsProb_map P N (hY 0) hfm]
  exact integral_arcCount_rotate P N c h k b f hfm

/-- The lower bound `2 ≤ N` makes `k` admissible: `1 ≤ k` and `k ≤ N/2` give `k < N`. -/
lemma selected_lt_of_valid {N : ℕ+} {k : ℕ} (h : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) : k < (N : ℕ) := by
  have := N.pos
  omega

/-- The particle number `N = n + 1` of the `n`-th term of a sequence in `particleNumber` has
`2 ≤ N`. -/
lemma two_le_particleNumber_succ (n : ℕ) : 2 ≤ ((particleNumber (n + 1) : ℕ+) : ℕ) := by
  change 2 ≤ n + 1 + 1
  omega

/-- The scale `ℓ_N = 2 k_N / N` of the selected count. At the particle numbers `N ≥ 2`, where the
admissibility `1 ≤ k_N ≤ N/2` is assumed, the value is `2 k_N / N ∈ (0, 1]`. At `N < 2` the scale is
the constant `1`, which the statements never use. -/
def selectedScale (k : ℕ+ → ℕ) (hk : ∀ N : ℕ+, 2 ≤ (N : ℕ) → 1 ≤ k N ∧ k N ≤ (N : ℕ) / 2) :
    Scales :=
  fun N => if h : 2 ≤ (N : ℕ) then
    ⟨2 * (k N : ℝ) / (N : ℝ), by
      have h1 := (hk N h).1
      have h1' := (hk N h).2
      have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
      have hk1 : (1 : ℝ) ≤ (k N : ℝ) := by exact_mod_cast h1
      constructor
      · positivity
      · rw [div_le_one hN]
        have h2 : 2 * k N ≤ (N : ℕ) := by omega
        have h3 : ((2 * k N : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast h2
        push_cast at h3
        linarith⟩
  else ⟨1, zero_lt_one, le_rfl⟩

lemma selectedScale_val (k : ℕ+ → ℕ) (hk : ∀ N : ℕ+, 2 ≤ (N : ℕ) → 1 ≤ k N ∧ k N ≤ (N : ℕ) / 2)
    {N : ℕ+} (h : 2 ≤ (N : ℕ)) :
    (selectedScale k hk N).val = 2 * (k N : ℝ) / (N : ℝ) := by
  unfold selectedScale
  simp only [h, ↓reduceDIte]

/-- The normalized arc count at the selected scale is the centred arc count at the arc of half-width
`k/(2N)` about `0`, divided by the gap scale `b_{N,k}`. -/
lemma normalizedCount_selectedScale (P : Parameters) (k : ℕ+ → ℕ)
    (hk : ∀ N : ℕ+, 2 ≤ (N : ℕ) → 1 ≤ k N ∧ k N ≤ (N : ℕ) / 2) {N : ℕ+} (h : 2 ≤ (N : ℕ))
    (X : Configuration N) :
    normalizedCount P (1 / 4) (by norm_num) (by norm_num) (selectedScale k hk) N X =
      (arcCount 0 ((k N : ℝ) / (2 * (N : ℝ))) X - (k N : ℝ)) /
        gapScale (parametersExponent P) N (k N) := by
  have hval := selectedScale_val k hk h
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  have hc : (1 / 4 : ℝ) * (selectedScale k hk N).val = (k N : ℝ) / (2 * (N : ℝ)) := by
    rw [hval]
    field_simp
    ring
  have hd : 2 * (1 / 4 : ℝ) * (selectedScale k hk N).val = (k N : ℝ) / (N : ℝ) := by
    rw [hval]
    field_simp
    ring
  have hn : 2 * (1 / 4 : ℝ) * (N : ℝ) * (selectedScale k hk N).val = (k N : ℝ) := by
    rw [hval]
    field_simp
    ring
  unfold normalizedCount gapScale
  rw [hc, hd, hn]
  rfl

/-- The selected discrepancy normalized by `b_{N,k}`, as a function of the configuration. -/
def selectedNormalized (P : Parameters) (k : ℕ+ → ℕ)
    (hk : ∀ N : ℕ+, 2 ≤ (N : ℕ) → 1 ≤ k N ∧ k N ≤ (N : ℕ) / 2) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (X : Configuration N) : ℝ :=
  (selectedDiscrepancy X (k N) (selected_lt_of_valid (hk N hN)) : ℝ) /
    gapScale (parametersExponent P) N (k N)

/-- The selected scale is mesoscopic: `N ℓ_N = 2 k_N` tends to infinity. -/
lemma selectedScale_mesoscopic (k : ℕ+ → ℕ)
    (hk : ∀ N : ℕ+, 2 ≤ (N : ℕ) → 1 ≤ k N ∧ k N ≤ (N : ℕ) / 2)
    (hkt : Tendsto (fun n => k (particleNumber n)) atTop atTop) :
    Mesoscopic (selectedScale k hk) := by
  unfold Mesoscopic
  have hlim : Tendsto (fun n : ℕ => 2 * (k (particleNumber n) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hkt).const_mul_atTop two_pos
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h2 : 2 ≤ ((particleNumber n : ℕ+) : ℕ) := by
    change 2 ≤ n + 1
    omega
  show 2 * (k (particleNumber n) : ℝ) =
    ((n + 1 : ℕ) : ℝ) * (selectedScale k hk (particleNumber n)).val
  rw [selectedScale_val k hk h2]
  have hcast : (((particleNumber n : ℕ+) : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := rfl
  rw [hcast]
  have hpos : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

namespace Internal

/-- The selected count CLT, part of the proof of Corollary 1. Under the two main theorems as
hypotheses, in the form of the conclusions `Internal.QuantitativeVarianceConclusion` and
`Internal.CLTConclusion`, and the Prékopa–Leindler inequality `External.PrekopaLeindler`, the
selected discrepancy normalized by `b_{N,k_N}` converges in law to the normal law of variance
`v_s = countVariance P`. -/
theorem selected_count_law_of_variance_clt (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hQV : Internal.QuantitativeVarianceConclusion beta s hbeta hs hs1)
    (hCLT : Internal.CLTConclusion beta s hbeta hs hs1)
    (k : ℕ+ → ℕ) (hk : ∀ N : ℕ+, 2 ≤ (N : ℕ) → 1 ≤ k N ∧ k N ≤ (N : ℕ) / 2)
    (hkt : Tendsto (fun n => k (particleNumber n)) atTop atTop) :
    ConvergesInLaw
      (fun n => (gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ (particleNumber (n + 1))).map
        (selectedNormalized ⟨(beta, s), hbeta, hs, hs1⟩ k hk (particleNumber (n + 1))
          (two_le_particleNumber_succ n)))
      (normalLaw (countVariance ⟨(beta, s), hbeta, hs, hs1⟩).toNNReal) := by
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hP
  have hkt' : Tendsto (fun n => k (particleNumber (n + 1))) atTop atTop :=
    hkt.comp (tendsto_add_atTop_nat 1)
  -- The normalized arc counts at the selected scale converge in law (`counts_tendsto`).
  have hcount := counts_tendsto beta s hbeta hs hs1 hQV hCLT (1 / 4) (by norm_num) (by norm_num)
    (selectedScale k hk) (selectedScale_mesoscopic k hk hkt)
  have hcount' := hcount.comp (tendsto_add_atTop_nat 1)
  -- The midpoint laws: the centred arc counts `C_N(0, k/N)`, normalized by `b_{N,k}`.
  let mid : ℕ → ProbabilityMeasure ℝ := fun n =>
    (gibbsProb P (particleNumber (n + 1))).map (fun X =>
      selectedCentredCount (particleNumber (n + 1)) (k (particleNumber (n + 1))) X /
        gapScale (parametersExponent P) (particleNumber (n + 1)) (k (particleNumber (n + 1))))
  -- The midpoint laws converge to the normal law, by the rotation identity and `counts_tendsto`.
  have h₂ : Tendsto (fun n => blDistance (mid n) (normalProbOf (countVariance P))) atTop
      (𝓝 0) := by
    refine hcount'.congr (fun n => ?_)
    have hrot := blDistance_map_arcCount_rotate P (particleNumber (n + 1))
      ((((k (particleNumber (n + 1)) : ℝ) / (2 * ((particleNumber (n + 1) : ℕ) : ℝ))) :
        ℝ) : UnitAddCircle)
      ((k (particleNumber (n + 1)) : ℝ) / (2 * ((particleNumber (n + 1) : ℕ) : ℝ)))
      (k (particleNumber (n + 1)) : ℝ)
      (gapScale (parametersExponent P) (particleNumber (n + 1)) (k (particleNumber (n + 1))))
      (normalProbOf (countVariance P))
    have hfun : normalizedCount P (1 / 4) (by norm_num) (by norm_num) (selectedScale k hk)
          (particleNumber (n + 1)) =
        fun X => (arcCount 0 ((k (particleNumber (n + 1)) : ℝ) /
          (2 * ((particleNumber (n + 1) : ℕ) : ℝ))) X - (k (particleNumber (n + 1)) : ℝ)) /
          gapScale (parametersExponent P) (particleNumber (n + 1)) (k (particleNumber (n + 1))) :=
      funext fun X => normalizedCount_selectedScale P k hk (two_le_particleNumber_succ n) X
    show blDistance (countLaw P (by norm_num) (by norm_num) (selectedScale k hk)
        (particleNumber (n + 1))) (normalProbOf (countVariance P)) =
      blDistance (mid n) (normalProbOf (countVariance P))
    unfold countLaw
    rw [hfun, ← hrot]
    rfl
  -- The gap scale tends to infinity and `N` dominates any fixed multiple of it eventually.
  have hb : Tendsto (fun n => gapScale (parametersExponent P) (particleNumber (n + 1))
      (k (particleNumber (n + 1)))) atTop atTop :=
    gapsDisc_gapScale_tendsto_atTop (parametersExponent P) (fun n => particleNumber (n + 1))
      (fun n => k (particleNumber (n + 1))) hkt'
      (Eventually.of_forall fun n => hk _ (two_le_particleNumber_succ n))
  have hNt : Tendsto (fun n : ℕ => ((particleNumber (n + 1) : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => by
      change (n : ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ)
      exact_mod_cast Nat.le_succ_of_le (Nat.le_succ n)) tendsto_natCast_atTop_atTop
  obtain ⟨C0, hC0, htail⟩ := selected_count_tail hPL beta s hbeta hs hs1
  -- The discrepancy and the centred count agree in probability at the scale `b_{N,k}`.
  have h₁ : Tendsto (fun n => blDistance
      ((gibbsProb P (particleNumber (n + 1))).map
        (selectedNormalized P k hk (particleNumber (n + 1)) (two_le_particleNumber_succ n)))
      (mid n)) atTop (𝓝 0) := by
    refine tendsto_zero_of_forall_ofReal fun δ hδ => ?_
    set R : ℝ := 8 * C0 / δ with hR_def
    have hR : 0 < R := by positivity
    filter_upwards [hb.eventually_ge_atTop (1024 * C0 / δ ^ 3), hNt.eventually_gt_atTop (4 * R)]
      with n hbn hNn
    set N : ℕ+ := particleNumber (n + 1) with hN_def
    have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
    have hN2 : 2 ≤ (N : ℕ) := two_le_particleNumber_succ n
    have hkN := hk N hN2
    set b : ℝ := gapScale (parametersExponent P) N (k N) with hb_def
    have hbpos : 0 < b := gapsDisc_gapScale_pos _ N (k N) hkN.1 hkN.2
    set M : ℝ := δ / 4 * b with hM_def
    have hM : 0 < M := by positivity
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
    have hRN : R / (N : ℝ) < 1 / 4 := by
      rw [div_lt_iff₀ hNpos]
      linarith
    -- the tail bound for the discrepancy and the centred count
    have htb := htail N (k N) (selected_lt_of_valid hkN) hkN.1 (by omega) hN2 R M hR hM hRN
    have hPS : (gibbsMeasure P N {X : Configuration N |
        M < |((selectedDiscrepancy X (k N) (selected_lt_of_valid hkN) : ℤ) : ℝ) -
          selectedCentredCount N (k N) X|}).toReal ≤ δ / 4 := by
      have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top htb
      rw [ENNReal.toReal_ofReal (by positivity)] at h1
      have hR8 : C0 / R = δ / 8 := by
        rw [hR_def]
        field_simp
      have h4 : 4 * R / M ≤ δ / 8 := by
        have hδ3 : 0 < δ ^ 3 := by positivity
        have hbn' : 1024 * C0 ≤ b * δ ^ 3 := by
          have := (div_le_iff₀ hδ3).1 hbn
          linarith
        rw [div_le_iff₀ hM, hR_def, hM_def]
        have e : 4 * (8 * C0 / δ) = 32 * C0 / δ := by ring
        rw [e, div_le_iff₀ hδ]
        nlinarith
      linarith
    -- the coupling bound, with the event rewritten as the tail event
    have hXm : Measurable (fun ω : Configuration N =>
        ((selectedDiscrepancy ω (k N) (selected_lt_of_valid hkN) : ℤ) : ℝ) / b) := by
      have := measurable_selectedDiscrepancy (k N) (selected_lt_of_valid hkN)
      fun_prop
    have hYm : Measurable (fun ω : Configuration N => selectedCentredCount N (k N) ω / b) :=
      ((measurable_arcCount _ _).sub_const _).div_const b
    have hset : {ω : Configuration N | δ / 4 <
        |((selectedDiscrepancy ω (k N) (selected_lt_of_valid hkN) : ℤ) : ℝ) / b -
          selectedCentredCount N (k N) ω / b|} =
        {X : Configuration N | M < |((selectedDiscrepancy X (k N) (selected_lt_of_valid hkN) : ℤ) : ℝ) -
          selectedCentredCount N (k N) X|} := by
      ext ω
      simp only [Set.mem_ofPred_eq, hM_def]
      rw [← sub_div, abs_div, abs_of_pos hbpos, lt_div_iff₀ hbpos]
    have hcoup : blDistance
        ((gibbsProb P (particleNumber (n + 1))).map
          (selectedNormalized P k hk (particleNumber (n + 1)) (two_le_particleNumber_succ n)))
        (mid n) ≤ ENNReal.ofReal (δ / 4 + 2 * (gibbsMeasure P N
          {ω : Configuration N | δ / 4 <
            |((selectedDiscrepancy ω (k N) (selected_lt_of_valid hkN) : ℤ) : ℝ) / b -
              selectedCentredCount N (k N) ω / b|}).toReal) :=
      blDistance_map_le_of_measure_gt (gibbsMeasure P N) hXm hYm (by positivity)
    rw [hset] at hcoup
    refine hcoup.trans (ENNReal.ofReal_le_ofReal ?_)
    linarith
  refine convergesInLaw_of_blDistance_varying_limit
    (fun n => (gibbsProb P (particleNumber (n + 1))).map
      (selectedNormalized P k hk (particleNumber (n + 1)) (two_le_particleNumber_succ n)))
    mid (normalProbOf (countVariance P)) h₁ h₂

/-- **Selected count**, part of the proof of Corollary 1, under the two main theorems as
hypotheses (in the form of their conclusions) and the Prékopa–Leindler inequality
`External.PrekopaLeindler`. Two assertions: the tail bound
`P(|Δ_N - C_N(0,k_N/N)| > M) ≤ C/R + 4R/M` for `R/N < 1/4`, which is `selected_count_tail`, and
the normal limit `Δ_N / b_{N,k_N} → N(0, v_s)`, which is `selected_count_law_of_variance_clt`. -/
theorem selected_count_of_variance_clt (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hQV : Internal.QuantitativeVarianceConclusion beta s hbeta hs hs1)
    (hCLT : Internal.CLTConclusion beta s hbeta hs hs1)
    (k : ℕ+ → ℕ) (hk : ∀ N : ℕ+, 2 ≤ (N : ℕ) → 1 ≤ k N ∧ k N ≤ (N : ℕ) / 2)
    (hkt : Tendsto (fun n => k (particleNumber n)) atTop atTop) :
    (
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (k : ℕ) (hk : k < (N : ℕ)), 1 ≤ k → 2 * k ≤ (N : ℕ) →
      2 ≤ (N : ℕ) → ∀ R M : ℝ, 0 < R → 0 < M → R / (N : ℝ) < 1 / 4 →
        gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N
          {X | M < |((selectedDiscrepancy X k hk : ℤ) : ℝ) - selectedCentredCount N k X|} ≤
            ENNReal.ofReal (C / R + 4 * R / M)) ∧
        ConvergesInLaw
      (fun n => (gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ (particleNumber (n + 1))).map
        (selectedNormalized ⟨(beta, s), hbeta, hs, hs1⟩ k hk (particleNumber (n + 1))
          (two_le_particleNumber_succ n)))
      (normalLaw (countVariance ⟨(beta, s), hbeta, hs, hs1⟩).toNNReal) := by
  exact ⟨selected_count_tail hPL beta s hbeta hs hs1,
    selected_count_law_of_variance_clt hPL beta s hbeta hs hs1 hQV hCLT k hk hkt⟩

end Internal

end Riesz1

end
end
