/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscSelectedLaw
public import Riesz1.Unconditional.GapsDiscIncrements
public import Riesz1.ToMathlib.CdfSandwich
public import Riesz1.CLT.DistributionFunction

/-!
# The gap CLT at the selected particle

Part of the proof of Corollary 1. For integers `1 ≤ k_N ≤ ⌊N/2⌋` with
`k_N → ∞`, the centred gap at the nearest particle `J`, `(S_{J,k_N} - k_N) / b_{N,k_N}`, converges in
law to the normal law of variance `v_s`.

The proof passes through distribution functions. The discrepancy `Δ_N / b_N` has distribution
functions `F_N(x)` converging to `Φ(x)` (`selected_count_law_of_variance_clt`). The inversion
identity `{r ≤ Δ} = {S_{J,k} - k + r + T_r ≤ 0}` and the short-increment bound
`P(|T_r| > ε b) → 0` (`gapsDisc_increment_probability`) sandwich the event `{G ≤ u}` between the
events `{r₋ ≤ Δ}` and `{r₊ ≤ Δ}` with thresholds `r_± ≈ -(u ± ε) b`, up to small errors. The
thresholds move with `N`, so the moving-threshold squeeze `tendsto_cdf_moving` and the symmetry of
the normal law `gaussianReal_cdf_neg` give the limit `Φ(u)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace Riesz1

/-- The integer threshold event `{r ≤ Δ}` has probability one minus the probability of
`{Δ/b ≤ (r - 1)/b}`, for a positive scale `b`. -/
lemma toReal_thresh_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Δ : Ω → ℤ} (hΔ : Measurable Δ) {b : ℝ} (hb : 0 < b) (r : ℤ) :
    (μ {ω | (r : ℝ) ≤ (Δ ω : ℝ)}).toReal =
      1 - (μ {ω | (Δ ω : ℝ) / b ≤ ((r : ℝ) - 1) / b}).toReal := by
  have h1 : {ω | (r : ℝ) ≤ (Δ ω : ℝ)} = {ω | r ≤ Δ ω} := by
    ext ω
    simp only [mem_ofPred_eq, Int.cast_le]
  have h2 : {ω | (Δ ω : ℝ) / b ≤ ((r : ℝ) - 1) / b} = {ω | Δ ω ≤ r - 1} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [div_le_div_iff_of_pos_right hb]
    constructor
    · intro h
      have h' : (Δ ω : ℝ) ≤ ((r - 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast h'
    · intro h
      have h' : (Δ ω : ℝ) ≤ ((r - 1 : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      linarith
  rw [h1, h2]
  exact int_ge_toReal_eq_one_sub μ hΔ r

/-- An integer `r` with `|r| < k` and `2k ≤ N` satisfies the index constraints of the inversion
identity: `1 ≤ k + r < N`. -/
lemma valid_of_abs_lt {N k : ℕ} (_hk1 : 1 ≤ k) (h2k : 2 * k ≤ N) {r : ℤ}
    (hr : |(r : ℝ)| < k) : 1 ≤ (k : ℤ) + r ∧ (k : ℤ) + r < N := by
  have hz : |r| < (k : ℤ) := by
    have h' : ((|r| : ℤ) : ℝ) < (k : ℝ) := by rw [Int.cast_abs]; exact hr
    exact_mod_cast h'
  have := abs_lt.1 hz
  omega

/-- The inversion identity in normalized form: `r ≤ Δ` holds exactly when the normalized
centred block, the normalized threshold and the normalized increment sum to a nonpositive number. -/
lemma selected_identity_normalized {N : ℕ+} {k : ℕ} (hk : k < (N : ℕ)) {b : ℝ} (hb : 0 < b)
    (r : ℤ) (X : Configuration N)
    (hX : r ≤ selectedDiscrepancy X k hk ↔
      blockLength X (nearestLabel X) k - k + (r : ℝ) + selectedIncrement X k r ≤ 0) :
    (r : ℝ) ≤ ((selectedDiscrepancy X k hk : ℤ) : ℝ) ↔
      (blockLength X (nearestLabel X) k - k) / b + (r : ℝ) / b + selectedIncrement X k r / b ≤ 0 := by
  have hcast : (r : ℝ) ≤ ((selectedDiscrepancy X k hk : ℤ) : ℝ) ↔ r ≤ selectedDiscrepancy X k hk :=
    Int.cast_le
  have hsum : (blockLength X (nearestLabel X) k - k) / b + (r : ℝ) / b +
      selectedIncrement X k r / b =
      (blockLength X (nearestLabel X) k - k + (r : ℝ) + selectedIncrement X k r) / b := by
    ring
  rw [hcast, hX, hsum, div_le_iff₀ hb, zero_mul]

/-- The distribution functions of the normalized gap are controlled by those of the normalized
discrepancy. This is the CDF form of the gap CLT at the selected particle. The
hypotheses are the convergence of the discrepancy distribution functions to a continuous,
symmetric limit `Φ` and the two short-increment and inversion facts of
`Riesz1.Unconditional.GapsDiscIncrements`. -/
theorem gap_cdf_of_discrepancy_cdf (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ → ℕ+} {kk : ℕ → ℕ}
    (hvalid : ∀ n, 1 ≤ kk n ∧ kk n ≤ (N n : ℕ) / 2)
    (hkt : Tendsto kk atTop atTop)
    (Φ : ℝ → ℝ) (hΦc : Continuous Φ) (hΦsym : ∀ x, 1 - Φ (-x) = Φ x)
    (hCDF : ∀ x : ℝ, Tendsto (fun n =>
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)
          {X : Configuration (N n) |
            ((selectedDiscrepancy X (kk n) (selected_lt_of_valid (hvalid n)) : ℤ) : ℝ) /
              gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) ≤ x}).toReal)
      atTop (𝓝 (Φ x))) (u : ℝ) :
    Tendsto (fun n => (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)
        {X : Configuration (N n) |
          centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X (nearestLabel X) (kk n) (hvalid n) ≤ u}).toReal)
      atTop (𝓝 (Φ u)) := by
  -- Standing facts about the sequence: positivity, divergence of the scale, and `b/k → 0`.
  have hPN : ∀ n, IsProbabilityMeasure
      (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)) :=
    fun n => (modelWellDefined _ (N n)).2.2
  have hbt : Tendsto (fun n => gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n)) atTop atTop :=
    gapsDisc_gapScale_tendsto_atTop _ N kk hkt (Eventually.of_forall hvalid)
  have hratio : Tendsto (fun n => gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) /
      (kk n : ℝ)) atTop (𝓝 0) :=
    gapsDisc_gapScale_div_tendsto_zero _ N kk hkt (Eventually.of_forall hvalid)
  have hbpos : ∀ n, 0 < gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) := fun n =>
    gapsDisc_gapScale_pos _ (N n) (kk n) (hvalid n).1 (hvalid n).2
  have hinv_b : Tendsto (fun n => 1 / gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hbt
  -- The distribution function of the normalized discrepancy, and its monotonicity.
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ → ℝ, ∀ n x, F n x =
      (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)
        {X : Configuration (N n) |
          ((selectedDiscrepancy X (kk n) (selected_lt_of_valid (hvalid n)) : ℤ) : ℝ) /
            gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) ≤ x}).toReal :=
    ⟨_, fun _ _ => rfl⟩
  have hFc : ∀ x : ℝ, Tendsto (fun n => F n x) atTop (𝓝 (Φ x)) := fun x => by
    simpa only [hF] using hCDF x
  have hFmono : ∀ n, Monotone (F n) := fun n x y hxy => by
    rw [hF, hF]
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono fun ω hω => le_trans hω hxy)
  -- The inversion identity, with the thresholds written as `rH`, `rL`.
  have hprob : ∀ n (r : ℤ), (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)
      {X : Configuration (N n) | (r : ℝ) ≤ ((selectedDiscrepancy X (kk n)
        (selected_lt_of_valid (hvalid n)) : ℤ) : ℝ)}).toReal =
      1 - F n (((r : ℝ) - 1) / gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n)) := by
    intro n r
    rw [hF]
    exact toReal_thresh_eq _ (measurable_selectedDiscrepancy (kk n)
      (selected_lt_of_valid (hvalid n))) (hbpos n) r
  -- A threshold `m` within distance one of `-c b` satisfies `|m| ≤ (|c| + 1) b` when `b ≥ 1`.
  have hthr : ∀ (c b : ℝ) (m : ℤ), 1 ≤ b → -c * b - 1 < (m : ℝ) → (m : ℝ) < -c * b + 1 →
      |(m : ℝ)| ≤ (|c| + 1) * b := by
    intro c b m hb h1 h2
    have hcb : |-c * b| = |c| * b := by
      rw [abs_mul, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < b)]
    have hm : |(m : ℝ)| ≤ |-c * b| + 1 := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le (-c * b), le_abs_self (-c * b)]
    have hexp : (|c| + 1) * b = |c| * b + b := by ring
    rw [hcb] at hm
    linarith
  -- The gap probabilities.
  obtain ⟨Gp, hGp⟩ : ∃ Gp : ℕ → ℝ, ∀ n, Gp n =
      (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)
        {X : Configuration (N n) |
          centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X (nearestLabel X) (kk n) (hvalid n) ≤ u}).toReal :=
    ⟨_, fun _ => rfl⟩
  -- For every `ε > 0`, the gap probability is sandwiched between two sequences with limits
  -- `Φ(u - ε)` and `Φ(u + ε)`.
  have key : ∀ ε : ℝ, 0 < ε → ∃ Lf Uf : ℕ → ℝ,
      (∀ᶠ n in atTop, Lf n ≤ Gp n ∧ Gp n ≤ Uf n) ∧
      Tendsto Lf atTop (𝓝 (Φ (u - ε))) ∧ Tendsto Uf atTop (𝓝 (Φ (u + ε))) := by
    intro ε hε
    have hA : 0 < |u| + |ε| + 2 := by positivity
    obtain ⟨rH, hrH⟩ : ∃ rH : ℕ → ℤ, ∀ n, rH n =
        ⌈-(u - ε) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n)⌉ := ⟨_, fun _ => rfl⟩
    obtain ⟨rL, hrL⟩ : ∃ rL : ℕ → ℤ, ∀ n, rL n =
        ⌊-(u + ε) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n)⌋ := ⟨_, fun _ => rfl⟩
    -- the ceiling and floor facts
    have hrHb : ∀ n, -(u - ε) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) ≤
        (rH n : ℝ) := fun n => by rw [hrH n]; exact Int.le_ceil _
    have hrHu : ∀ n, (rH n : ℝ) < -(u - ε) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) + 1 :=
      fun n => by rw [hrH n]; exact Int.ceil_lt_add_one _
    have hrLb : ∀ n, -(u + ε) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) - 1 <
        (rL n : ℝ) := fun n => by
      rw [hrL n]
      have := Int.lt_floor_add_one (-(u + ε) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n))
      linarith
    have hrLu : ∀ n, (rL n : ℝ) ≤ -(u + ε) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) :=
      fun n => by rw [hrL n]; exact Int.floor_le _
    -- eventually: the thresholds are small compared with `k`, and valid for the inversion identity
    have hsmall : ∀ᶠ n in atTop, 1 ≤ gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) ∧
        (|u| + |ε| + 2) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) < (kk n : ℝ) := by
      have hlt := Filter.Tendsto.eventually_lt_const
        (show (0 : ℝ) < 1 / (|u| + |ε| + 2) by positivity) hratio
      filter_upwards [hlt, hbt.eventually_ge_atTop 1,
        Eventually.of_forall fun n => (hvalid n).1] with n hn hb1 hk1
      refine ⟨hb1, ?_⟩
      have hkpos : (0 : ℝ) < (kk n : ℝ) := by
        have : (1 : ℝ) ≤ (kk n : ℝ) := by exact_mod_cast hk1
        linarith
      rw [div_lt_div_iff₀ hkpos (by positivity)] at hn
      linarith
    have hrHabs : ∀ᶠ n in atTop, |(rH n : ℝ)| ≤ (|u| + |ε| + 2) *
        gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) ∧
        |(rH n : ℝ)| < (kk n : ℝ) := by
      filter_upwards [hsmall] with n hn
      have h1 : |(rH n : ℝ)| ≤ (|u - ε| + 1) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) :=
        hthr (u - ε) _ (rH n) hn.1 (by linarith [hrHb n]) (hrHu n)
      have h2 : |u - ε| ≤ |u| + |ε| := abs_sub u ε
      have h3 : (|u - ε| + 1) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) ≤
          (|u| + |ε| + 2) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) := by
        have := hbpos n
        nlinarith
      exact ⟨h1.trans h3, lt_of_le_of_lt (h1.trans h3) hn.2⟩
    have hrLabs : ∀ᶠ n in atTop, |(rL n : ℝ)| ≤ (|u| + |ε| + 2) *
        gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) ∧
        |(rL n : ℝ)| < (kk n : ℝ) := by
      filter_upwards [hsmall] with n hn
      have h1 : |(rL n : ℝ)| ≤ (|u + ε| + 1) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) :=
        hthr (u + ε) _ (rL n) hn.1 (hrLb n) (by linarith [hrLu n, hbpos n])
      have h2 : |u + ε| ≤ |u| + |ε| := abs_add_le u ε
      have h3 : (|u + ε| + 1) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) ≤
          (|u| + |ε| + 2) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) := by
        have := hbpos n
        nlinarith
      exact ⟨h1.trans h3, lt_of_le_of_lt (h1.trans h3) hn.2⟩
    -- the increment probabilities tend to zero at both thresholds
    have hAs : (0 : ℝ) < |u| + |ε| + 2 := hA
    obtain ⟨pH, hpH⟩ : ∃ p : ℕ → ℝ, ∀ n, p n =
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)
          {X : Configuration (N n) | ε ≤ |selectedIncrement X (kk n) (rH n) /
            gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n)|}).toReal := ⟨_, fun _ => rfl⟩
    obtain ⟨pL, hpL⟩ : ∃ p : ℕ → ℝ, ∀ n, p n =
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)
          {X : Configuration (N n) | ε ≤ |selectedIncrement X (kk n) (rL n) /
            gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n)|}).toReal := ⟨_, fun _ => rfl⟩
    have habs_nat : ∀ z : ℤ, ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := fun z => by
      have h := Int.natCast_natAbs z
      rw [← Int.cast_abs, ← h]
      exact (Int.cast_natCast _).symm
    have hpH0 : Tendsto pH atTop (𝓝 0) := by
      have hinc := gapsDisc_increment_probability hBE hPL beta s hbeta hs hs1 (ι := ℕ) (l := atTop) N kk hkt
        (Eventually.of_forall hvalid) (|u| + |ε| + 2) hAs rH
        (by filter_upwards [hrHabs] with n hn
            rw [habs_nat]
            exact hn.1) ε hε
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hinc
      simp only [ENNReal.toReal_zero] at h
      refine h.congr fun n => ?_
      simp only [Function.comp_apply, hpH]
    have hpL0 : Tendsto pL atTop (𝓝 0) := by
      have hinc := gapsDisc_increment_probability hBE hPL beta s hbeta hs hs1 (ι := ℕ) (l := atTop) N kk hkt
        (Eventually.of_forall hvalid) (|u| + |ε| + 2) hAs rL
        (by filter_upwards [hrLabs] with n hn
            rw [habs_nat]
            exact hn.1) ε hε
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hinc
      simp only [ENNReal.toReal_zero] at h
      refine h.congr fun n => ?_
      simp only [Function.comp_apply, hpL]
    -- the threshold distribution functions converge: `(r - 1)/b → -(u ∓ ε)`
    have hcH : Tendsto (fun n => ((rH n : ℝ) - 1) /
        gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n)) atTop (𝓝 (-(u - ε))) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (g := fun n => -(u - ε) - 1 / gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n))
        (h := fun _ => -(u - ε)) ?_ tendsto_const_nhds ?_ ?_
      · simpa using (tendsto_const_nhds (x := -(u - ε))).sub hinv_b
      · filter_upwards with n
        have hb := hbpos n
        have hid : ((rH n : ℝ) - 1) / gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) -
            (-(u - ε) - 1 / gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n)) =
            ((rH n : ℝ) + (u - ε) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n)) /
              gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) := by
          field_simp
          ring
        have hnn : 0 ≤ ((rH n : ℝ) + (u - ε) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n)) /
            gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) :=
          div_nonneg (by linarith [hrHb n]) hb.le
        linarith
      · filter_upwards with n
        have hb := hbpos n
        rw [div_le_iff₀ hb]
        linarith [hrHu n]
    have hcL : Tendsto (fun n => ((rL n : ℝ) - 1) /
        gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n)) atTop (𝓝 (-(u + ε))) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (g := fun n => -(u + ε) - 2 * (1 / gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n)))
        (h := fun _ => -(u + ε)) ?_ tendsto_const_nhds ?_ ?_
      · simpa using (tendsto_const_nhds (x := -(u + ε))).sub (hinv_b.const_mul 2)
      · filter_upwards with n
        have hb := hbpos n
        have hid : ((rL n : ℝ) - 1) / gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) -
            (-(u + ε) - 2 * (1 / gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n))) =
            ((rL n : ℝ) + 1 + (u + ε) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n)) /
              gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) := by
          field_simp
          ring
        have hnn : 0 ≤ ((rL n : ℝ) + 1 + (u + ε) * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n)) /
            gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) :=
          div_nonneg (by linarith [hrLb n]) hb.le
        linarith
      · filter_upwards with n
        have hb := hbpos n
        rw [div_le_iff₀ hb]
        linarith [hrLu n]
    -- the limits of the threshold probabilities, by the moving-threshold squeeze and symmetry
    have hH : Tendsto (fun n => (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)
        {X : Configuration (N n) | (rH n : ℝ) ≤ ((selectedDiscrepancy X (kk n)
          (selected_lt_of_valid (hvalid n)) : ℤ) : ℝ)}).toReal) atTop (𝓝 (Φ (u - ε))) := by
      have h1 := tendsto_cdf_moving hFmono hFc hΦc hcH
      have h2 : Tendsto (fun n => 1 - F n (((rH n : ℝ) - 1) /
          gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n))) atTop
          (𝓝 (1 - Φ (-(u - ε)))) := tendsto_const_nhds.sub h1
      rw [hΦsym (u - ε)] at h2
      exact h2.congr fun n => (hprob n (rH n)).symm
    have hU : Tendsto (fun n => (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)
        {X : Configuration (N n) | (rL n : ℝ) ≤ ((selectedDiscrepancy X (kk n)
          (selected_lt_of_valid (hvalid n)) : ℤ) : ℝ)}).toReal) atTop (𝓝 (Φ (u + ε))) := by
      have h1 := tendsto_cdf_moving hFmono hFc hΦc hcL
      have h2 : Tendsto (fun n => 1 - F n (((rL n : ℝ) - 1) /
          gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n))) atTop
          (𝓝 (1 - Φ (-(u + ε)))) := tendsto_const_nhds.sub h1
      rw [hΦsym (u + ε)] at h2
      exact h2.congr fun n => (hprob n (rL n)).symm
    -- the lower and upper sequences
    obtain ⟨Lf, hLf⟩ : ∃ Lf : ℕ → ℝ, ∀ n, Lf n = (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters)
        (N n) {X : Configuration (N n) | (rH n : ℝ) ≤ ((selectedDiscrepancy X (kk n)
          (selected_lt_of_valid (hvalid n)) : ℤ) : ℝ)}).toReal - pH n := ⟨_, fun _ => rfl⟩
    obtain ⟨Uf, hUf⟩ : ∃ Uf : ℕ → ℝ, ∀ n, Uf n = (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters)
        (N n) {X : Configuration (N n) | (rL n : ℝ) ≤ ((selectedDiscrepancy X (kk n)
          (selected_lt_of_valid (hvalid n)) : ℤ) : ℝ)}).toReal + pL n := ⟨_, fun _ => rfl⟩
    refine ⟨Lf, Uf, ?_, ?_, ?_⟩
    · -- the sandwich of the gap probability at every large index
      filter_upwards [hrHabs, hrLabs] with n hnH hnL
      have hvH := valid_of_abs_lt (N := (N n : ℕ)) (k := kk n) (hvalid n).1
        (by have := (hvalid n).2; omega) hnH.2
      have hvL := valid_of_abs_lt (N := (N n : ℕ)) (k := kk n) (hvalid n).1
        (by have := (hvalid n).2; omega) hnL.2
      have hidH : ∀ X : Configuration (N n), (rH n : ℝ) ≤ ((selectedDiscrepancy X (kk n)
          (selected_lt_of_valid (hvalid n)) : ℤ) : ℝ) ↔
          centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X (nearestLabel X) (kk n) (hvalid n) +
            (rH n : ℝ) / gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) +
            selectedIncrement X (kk n) (rH n) / gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) ≤ 0 := by
        intro X
        have hX := Set.ext_iff.1 ((gapsDisc_inversion_label.{0, 0} hBE hPL beta s hbeta hs hs1).2.2
          (N n) (kk n) (selected_lt_of_valid (hvalid n)) (rH n) hvH.1 hvH.2).2 X
        unfold centeredGap
        exact selected_identity_normalized _ (hbpos n) (rH n) X hX
      have hidL : ∀ X : Configuration (N n), (rL n : ℝ) ≤ ((selectedDiscrepancy X (kk n)
          (selected_lt_of_valid (hvalid n)) : ℤ) : ℝ) ↔
          centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X (nearestLabel X) (kk n) (hvalid n) +
            (rL n : ℝ) / gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) +
            selectedIncrement X (kk n) (rL n) / gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n) ≤ 0 := by
        intro X
        have hX := Set.ext_iff.1 ((gapsDisc_inversion_label.{0, 0} hBE hPL beta s hbeta hs hs1).2.2
          (N n) (kk n) (selected_lt_of_valid (hvalid n)) (rL n) hvL.1 hvL.2).2 X
        unfold centeredGap
        exact selected_identity_normalized _ (hbpos n) (rL n) X hX
      have hsw := sandwich_toReal_le (u := u) (ε := ε)
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n))
        (fun X => centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X (nearestLabel X) (kk n) (hvalid n))
        (fun X => ((selectedDiscrepancy X (kk n) (selected_lt_of_valid (hvalid n)) : ℤ) : ℝ))
        (fun r X => selectedIncrement X (kk n) r / gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n))
        hε (rL n) (rH n) (gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (kk n)) (hbpos n)
        hidL hidH
        (by rw [div_le_iff₀ (hbpos n)]; linarith [hrLu n])
        (by rw [le_div_iff₀ (hbpos n)]; linarith [hrHb n])
      beta_reduce at hsw
      rw [hGp, hLf, hUf, hpH, hpL]
      constructor <;> linarith [hsw.1, hsw.2]
    · have h := hH.sub hpH0
      rw [sub_zero] at h
      exact h.congr fun n => (hLf n).symm
    · have h := hU.add hpL0
      rw [add_zero] at h
      exact h.congr fun n => (hUf n).symm
  -- The gap probability converges, by the two bounds for every `ε`.
  have hGt : Tendsto Gp atTop (𝓝 (Φ u)) := by
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
        ((hΦc.tendsto u).eventually (lt_mem_nhds ha))
      obtain ⟨Lf, Uf, hsand, hL, -⟩ := key (δ / 2) (by positivity)
      have hy : a < Φ (u - δ / 2) := hball (by
        rw [Real.dist_eq, show u - δ / 2 - u = -(δ / 2) by ring, abs_neg, abs_of_pos (by positivity)]
        linarith)
      filter_upwards [hL.eventually (lt_mem_nhds hy), hsand] with n hn1 hn2
      exact lt_of_lt_of_le hn1 hn2.1
    · obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
        ((hΦc.tendsto u).eventually (gt_mem_nhds ha))
      obtain ⟨Lf, Uf, hsand, -, hU⟩ := key (δ / 2) (by positivity)
      have hy : Φ (u + δ / 2) < a := hball (by
        rw [Real.dist_eq, show u + δ / 2 - u = δ / 2 by ring, abs_of_pos (by positivity)]
        linarith)
      filter_upwards [hU.eventually (gt_mem_nhds hy), hsand] with n hn1 hn2
      exact lt_of_le_of_lt hn2.2 hn1
  exact hGt.congr hGp


/-- The centred gap at the nearest particle is a measurable function of the configuration. -/
lemma measurable_centeredGap_nearest {N : ℕ+} (s : RieszExponent) (k : ℕ)
    (hk : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) :
    Measurable (fun X : Configuration N => centeredGap s X (nearestLabel X) k hk) := by
  have hm (a : ℤ) : Measurable (fun X : Configuration N => cyclicLift X (nearestLabel X + a)) := by
    have h : Measurable (fun q : Configuration N × ℤ => cyclicLift q.1 (q.2 + a)) :=
      measurable_from_prod_countable_left (fun j : ℤ => measurable_cyclicLift (N := N) (j + a))
    exact h.comp (measurable_id.prodMk (measurable_nearestLabel N))
  have h0 : Measurable (fun X : Configuration N => cyclicLift X (nearestLabel X)) := by
    simpa using hm 0
  have hblock : Measurable (fun X : Configuration N => blockLength X (nearestLabel X) k) := by
    unfold blockLength
    exact (measurable_const.mul ((hm (k : ℤ)).sub h0))
  unfold centeredGap
  exact (hblock.sub_const _).div_const _

/-- The selected discrepancy normalized by `b_{N,k}` is a measurable function. -/
lemma measurable_selectedNormalized (P : Parameters) (k : ℕ+ → ℕ)
    (hk : ∀ N : ℕ+, 2 ≤ (N : ℕ) → 1 ≤ k N ∧ k N ≤ (N : ℕ) / 2) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    Measurable (selectedNormalized P k hk N hN) := by
  unfold selectedNormalized
  exact ((Measurable.of_discrete : Measurable (fun n : ℤ => (n : ℝ))).comp
    (measurable_selectedDiscrepancy (k N) (selected_lt_of_valid (hk N hN)))).div_const _

namespace Internal

/-- The gap CLT at the selected particle, part of the proof of Corollary 1, with the two main
theorems as hypotheses (in the form of their conclusions), the Bakry–Émery criterion `hBE` and the
Prékopa–Leindler inequality `hPL`. The centred gap `(S_{J,k_N} - k_N) / b_{N,k_N}` at the nearest
particle converges in law to the normal law of variance `v_s = countVariance P`. -/
theorem selected_gap_law_of_variance_clt (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hQV : Internal.QuantitativeVarianceConclusion beta s hbeta hs hs1)
    (hCLT : Internal.CLTConclusion beta s hbeta hs hs1)
    (k : ℕ+ → ℕ) (hk : ∀ N : ℕ+, 2 ≤ (N : ℕ) → 1 ≤ k N ∧ k N ≤ (N : ℕ) / 2)
    (hkt : Tendsto (fun n => k (particleNumber n)) atTop atTop) :
    ConvergesInLaw
      (fun n => (gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ (particleNumber (n + 1))).map
        (fun X => centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X (nearestLabel X)
          (k (particleNumber (n + 1))) (hk _ (two_le_particleNumber_succ n))))
      (normalLaw (countVariance ⟨(beta, s), hbeta, hs, hs1⟩).toNNReal) := by
  have hCount := selected_count_law_of_variance_clt hPL beta s hbeta hs hs1 hQV hCLT k hk hkt
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hP
  have hPN : ∀ N : ℕ+, IsProbabilityMeasure (gibbsMeasure P N) := fun N => (modelWellDefined P N).2.2
  have hv0 : (countVariance P).toNNReal ≠ 0 :=
    (Real.toNNReal_pos.2 (gapsDisc_countVariance_pos P)).ne'
  have hνprob : IsProbabilityMeasure (normalLaw (countVariance P).toNNReal) := by
    unfold normalLaw
    infer_instance
  have hatom : ∀ t : ℝ, normalLaw (countVariance P).toNNReal {t} = 0 := fun t =>
    (gaussianReal_absolutelyContinuous 0 hv0) Real.volume_singleton
  set Φ : ℝ → ℝ := fun x => ProbabilityTheory.cdf (normalLaw (countVariance P).toNNReal) x with hΦ_def
  have hΦc : Continuous Φ :=
    continuous_iff_continuousAt.2 fun x =>
      (measure_singleton_eq_zero_iff_continuousAt_cdf _ x).1 (hatom x)
  have hΦsym : ∀ x, 1 - Φ (-x) = Φ x := fun x => gaussianReal_cdf_neg hv0 x
  -- the distribution functions of the normalized discrepancy
  have hCDF : ∀ x : ℝ, Tendsto (fun n =>
      (gibbsMeasure P (particleNumber (n + 1))
        {X : Configuration (particleNumber (n + 1)) |
          ((selectedDiscrepancy X (k (particleNumber (n + 1)))
            (selected_lt_of_valid (hk _ (two_le_particleNumber_succ n))) : ℤ) : ℝ) /
            gapScale (⟨s, hs, hs1⟩ : RieszExponent) (particleNumber (n + 1))
              (k (particleNumber (n + 1))) ≤ x}).toReal) atTop (𝓝 (Φ x)) := by
    intro x
    have h := (convergesInLaw_iff_tendsto_measure_Iic _ _ hCount.1 hCount.2.1).1 hCount x (hatom x)
    have h' := (ENNReal.tendsto_toReal_iff (fun n => measure_ne_top _ _) (measure_ne_top _ _)).2 h
    have hlim : (normalLaw (countVariance P).toNNReal (Iic x)).toReal = Φ x := by
      simp only [hΦ_def]
      rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
    rw [← hlim]
    refine h'.congr fun n => ?_
    rw [Measure.map_apply (measurable_selectedNormalized P k hk (particleNumber (n + 1))
      (two_le_particleNumber_succ n)) measurableSet_Iic]
    rfl
  -- the gap distribution functions
  have hG := gap_cdf_of_discrepancy_cdf hBE hPL beta s hbeta hs hs1
    (N := fun n => particleNumber (n + 1)) (kk := fun n => k (particleNumber (n + 1)))
    (fun n => hk _ (two_le_particleNumber_succ n)) (hkt.comp (tendsto_add_atTop_nat 1)) Φ hΦc hΦsym
    hCDF
  -- the gap laws converge in law, by the distribution functions
  refine (convergesInLaw_iff_tendsto_measure_Iic _ _ ?_ hνprob).2 fun t ht => ?_
  · intro n
    exact (Measure.isProbabilityMeasure_map_iff
      (measurable_centeredGap_nearest (⟨s, hs, hs1⟩ : RieszExponent) _ _).aemeasurable).2 (hPN _)
  · have h2 : Tendsto (fun n => ((gibbsMeasure P (particleNumber (n + 1))).map
        (fun X => centeredGap (⟨s, hs, hs1⟩ : RieszExponent) X (nearestLabel X)
          (k (particleNumber (n + 1))) (hk _ (two_le_particleNumber_succ n)))
        (Iic t)).toReal) atTop (𝓝 (Φ t)) := by
      refine (hG t).congr fun n => ?_
      rw [Measure.map_apply (measurable_centeredGap_nearest (⟨s, hs, hs1⟩ : RieszExponent) _ _)
        measurableSet_Iic]
      rfl
    have hlim : (normalLaw (countVariance P).toNNReal (Iic t)).toReal = Φ t := by
      simp only [hΦ_def]
      rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
    rw [← hlim] at h2
    exact (ENNReal.tendsto_toReal_iff (fun n => measure_ne_top _ _) (measure_ne_top _ _)).1 h2

end Internal

end Riesz1

end
end
