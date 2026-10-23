/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopMomentsCount
public import Riesz1.Auxiliary.RigidityConclusion
public import Riesz1.Auxiliary.LoopMomentsBlocks
public import Riesz1.ToMathlib.Moments.Decay

/-!
# Discrepancies of microscopic arcs

The moments part of Lemma B.2, the discrepancy claim: for `1 ≤ r ≤ N/2`,
`‖ν(J)‖_{L^p} ≤ C r^{s/2+δ}`, where `ν(J) = M_J - |J|` and `δ` is below the rigidity threshold.

The arc count at the centre `arcCentre N a r` with half length `arcRadius N r` is the count
`M_J` of the arc, and the rigidity estimate of the arc count is a tail bound for `ν(J)`. The
tail-to-moment bound `lintegral_pow_le_tail_bound` combines it with the count moments.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace Riesz1

variable {N : ℕ+}

/-- The real point `x₀` whose image is the arc centre. -/
theorem dist_lt_iff_exists_int (t x0 ℓ : ℝ) :
    dist (t : UnitAddCircle) (x0 : UnitAddCircle) < ℓ ↔ ∃ n : ℤ, |t + n - x0| < ℓ := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
  constructor
  · intro h
    refine ⟨-round (t - x0), ?_⟩
    convert h using 2
    push_cast
    ring
  · rintro ⟨n, hn⟩
    refine lt_of_le_of_lt (round_le (t - x0) (-(n : ℤ))) ?_
    convert hn using 2
    push_cast
    ring

/-- The arc condition on the lift `N t + n N` is the distance condition on the unit circle. -/
theorem arc_condition_iff_abs (a r : ℝ) (hN : (0 : ℝ) < N) (t : ℝ) (n : ℤ) :
    (a < (N : ℝ) * t + n * N ∧ (N : ℝ) * t + n * N < a + r) ↔
      |t + n - (a + r / 2) / (N : ℝ)| < arcRadius N r := by
  have hNx0 : (N : ℝ) * ((a + r / 2) / (N : ℝ)) = a + r / 2 := by
    field_simp
  have hℓN : arcRadius N r * (N : ℝ) = r / 2 := by
    unfold arcRadius
    field_simp
  have e : (N : ℝ) * (t + n - (a + r / 2) / (N : ℝ)) = (N : ℝ) * t + n * N - (a + r / 2) := by
    linear_combination (-1 : ℝ) * hNx0
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (N : ℝ) * (-arcRadius N r) < (N : ℝ) * (t + n - (a + r / 2) / (N : ℝ)) := by
      rw [e]
      linarith [hℓN]
    exact ⟨lt_of_mul_lt_mul_left h1' hN.le, lt_of_mul_lt_mul_left (by rw [e]; linarith [hℓN])
      hN.le⟩
  · rintro ⟨h1, h2⟩
    have h1' := mul_lt_mul_of_pos_left h1 hN
    have h2' := mul_lt_mul_of_pos_left h2 hN
    rw [e] at h1' h2'
    constructor <;> linarith [hℓN]

/-- The arc count at the centre counts the particles of the arc. -/
theorem arcCount_arcCentre (a r : ℝ) (hN : (0 : ℝ) < N) (X : Configuration N) :
    arcCount (arcCentre N a r) (arcRadius N r) X = loopCount a r X := by
  unfold arcCount loopCount
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have key : dist ((X.val i : ℝ) : UnitAddCircle) (arcCentre N a r) < arcRadius N r ↔
      loopPos X i ∈ microArc N a r := by
    unfold arcCentre
    rw [dist_lt_iff_exists_int, loopPos, coe_mem_microArc_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, (arc_condition_iff_abs a r hN (X.val i) n).mpr hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, (arc_condition_iff_abs a r hN (X.val i) n).mp hn⟩
  exact if_congr key rfl rfl

/-- The arclength of the microscopic arc is its length. -/
theorem volume_microArc {a r : ℝ} (_hr : 0 < r) (hrN : r ≤ N) :
    volume (microArc N a r) = ENNReal.ofReal r := by
  have hmp := AddCircle.measurePreserving_mk (N : ℝ) a
  have hS : MeasurableSet (microArc N a r) := measurableSet_microArc N a r
  rw [← hmp.measure_preimage hS.nullMeasurableSet, Measure.restrict_apply' measurableSet_Ioc]
  have hset : ((fun t : ℝ => (t : AddCircle (N : ℝ))) ⁻¹' microArc N a r) ∩ Ioc a (a + N) =
      Ioo a (a + r) := by
    ext t
    constructor
    · rintro ⟨ht1, ht2⟩
      obtain ⟨s, hs, hst⟩ := ht1
      have hsIoc : s ∈ Ioc a (a + N) := ⟨hs.1, by linarith [hs.2]⟩
      have : s = t := (AddCircle.coe_eq_coe_iff_of_mem_Ioc hsIoc ht2).mp hst
      rw [← this]
      exact hs
    · intro ht
      refine ⟨⟨t, ht, rfl⟩, ⟨ht.1, by linarith [ht.2]⟩⟩
  rw [hset, Real.volume_Ioo]
  congr 1
  ring

/-- The power of a difference is at most `2^{k-1}` times the sum of the powers. -/
theorem abs_sub_pow_le_two_pow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {k : ℕ} (_hk : 1 ≤ k) :
    |x - y| ^ k ≤ 2 ^ (k - 1) * (x ^ k + y ^ k) := by
  have h1 : |x - y| ≤ x + y := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  calc |x - y| ^ k ≤ (x + y) ^ k := pow_le_pow_left₀ (abs_nonneg _) h1 k
    _ ≤ 2 ^ (k - 1) * (x ^ k + y ^ k) := add_pow_le hx hy k

namespace Internal

/-- **Discrepancy moments**, the moments part of Lemma B.2 (the discrepancy bound
`‖ν(J)‖_p ≤ C r^{s/2+δ}`). Conditionally on the rigidity conclusion at `beta, s`: there is a
threshold `eps0 > 0` such that for every `0 < δ < min(s/2, eps0)` and every `p ≥ 1` there is
`C > 0`, depending only on `beta, s, δ, p`, with `‖ν(J)‖_{L^p} ≤ C r^{s/2+δ}` for every `N ≥ 2`,
every arc `J` of length `1 ≤ r ≤ N/2` and every `hPL`. -/
theorem discrepancy_eLpNorm_of_rigidity (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hRig : Internal.RigidityConclusion beta s hbeta hs hs1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 → ∀ p : ℝ, 1 ≤ p →
      ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+), 2 ≤ (N : ℕ) →
        ∀ (a r : ℝ), 1 ≤ r → r ≤ (N : ℝ) / 2 →
          eLpNorm (fun X : Configuration N => loopDiscrepancy a r X) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
            ENNReal.ofReal (C * r ^ (s / 2 + δ)) := by
  obtain ⟨eps0, heps0, hbound⟩ := hRig
  refine ⟨eps0, heps0, fun δ hδ hδlt p hp => ?_⟩
  obtain ⟨c, C, hc, hC, hgap⟩ := hbound δ hδ (lt_of_lt_of_le hδlt (min_le_right _ _))
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hP
  set m : ℕ := ⌈p⌉₊ with hm_def
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := hp.trans (Nat.le_ceil p)
    exact_mod_cast this
  have hpm : p ≤ (m : ℝ) := Nat.le_ceil p
  set x : ℝ := s / 2 + δ with hx_def
  have hx : 0 < x := by rw [hx_def]; positivity
  -- Second moments of the count, from `loopCount_eLpNorm` at exponent `2m`.
  have hm2 : 1 ≤ 2 * m := by omega
  obtain ⟨CL, hCL, hcount⟩ := loopCount_eLpNorm P (p := ((2 * m : ℕ) : ℝ))
    (by exact_mod_cast hm2)
  set D2 : ℝ := 2 ^ (2 * m - 1) * (CL ^ (2 * m) + 1) with hD2_def
  have hD2 : 0 < D2 := by positivity
  set κ : ℝ := D2 ^ (((2 * m : ℕ) : ℝ)⁻¹) with hκ_def
  have hκ2 : κ ^ (2 * m) = D2 := Real.rpow_inv_natCast_pow hD2.le (by omega)
  have hκpos : 0 < κ := by positivity
  -- The exponential tail: `r^β exp(-c'' r^a')` is bounded for `r ≥ 1`.
  set a' : ℝ := δ / (4 * (s + 2)) with ha'_def
  have ha' : 0 < a' := by rw [ha'_def]; positivity
  set c'' : ℝ := c / (2 * 2 ^ a') with hc''_def
  have hc'' : 0 < c'' := by rw [hc''_def]; positivity
  set β : ℝ := (m : ℝ) - x * (m : ℝ) with hβ_def
  obtain ⟨Kd, hKd0, hKd⟩ := rpow_mul_exp_neg_bounded (β := β) ha' hc''
  set K2 : ℝ := 1 + κ ^ m * 2 ^ m * Real.sqrt C * Kd with hK2_def
  have hK2 : 0 < K2 := by positivity
  refine ⟨K2 ^ ((m : ℝ)⁻¹), by positivity, fun hPL N hN a r hr1 hrN => ?_⟩
  have hr0 : (0 : ℝ) < r := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hrN' : r ≤ (N : ℝ) := by
    have : (0 : ℝ) ≤ N := hNpos.le
    linarith
  have hμ : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  -- The discrepancy is the count minus the length.
  have hν_eq : ∀ X : Configuration N, loopDiscrepancy a r X = loopCount a r X - r := by
    intro X
    unfold loopDiscrepancy
    rw [volume_microArc hr0 hrN', ENNReal.toReal_ofReal hr0.le]
  have hνmeas : Measurable (fun X : Configuration N => loopDiscrepancy a r X) := by
    simp_rw [hν_eq]
    exact (measurable_loopCount a r).sub measurable_const
  -- Second moment of the discrepancy, from the second moment of the count.
  have hM2 : ∫⁻ X : Configuration N, ENNReal.ofReal ((loopCount a r X) ^ (2 * m))
      ∂gibbsMeasure P N ≤ ENNReal.ofReal ((CL * (1 + r)) ^ (2 * m)) := by
    have h := lintegral_pow_le_of_eLpNorm_le (μ := gibbsMeasure P N)
      (measurable_loopCount a r) hm2 (by positivity) (hcount hPL N hN a r hr0 hrN')
    simpa only [abs_of_nonneg (loopCount_nonneg a r _)] using h
  have hpt2 : ∀ X : Configuration N, ENNReal.ofReal (|loopDiscrepancy a r X| ^ (2 * m)) ≤
      ENNReal.ofReal (2 ^ (2 * m - 1)) * ENNReal.ofReal ((loopCount a r X) ^ (2 * m)) +
        ENNReal.ofReal (2 ^ (2 * m - 1) * r ^ (2 * m)) := by
    intro X
    have hb := abs_sub_pow_le_two_pow (loopCount_nonneg a r X) hr0.le (k := 2 * m) (by omega)
    have hM := pow_nonneg (loopCount_nonneg a r X) (2 * m)
    have hR := pow_nonneg hr0.le (2 * m)
    rw [hν_eq]
    calc ENNReal.ofReal (|loopCount a r X - r| ^ (2 * m))
        ≤ ENNReal.ofReal (2 ^ (2 * m - 1) * ((loopCount a r X) ^ (2 * m) + r ^ (2 * m))) :=
          ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal (2 ^ (2 * m - 1)) * ENNReal.ofReal ((loopCount a r X) ^ (2 * m)) +
            ENNReal.ofReal (2 ^ (2 * m - 1) * r ^ (2 * m)) := by
          rw [mul_add, ENNReal.ofReal_add (mul_nonneg (by positivity) hM)
            (mul_nonneg (by positivity) hR), ENNReal.ofReal_mul (by positivity)]
  have hmomν : ∫⁻ X : Configuration N, ENNReal.ofReal (|loopDiscrepancy a r X| ^ (2 * m))
      ∂gibbsMeasure P N ≤ ENNReal.ofReal (D2 * (1 + r) ^ (2 * m)) := by
    calc ∫⁻ X : Configuration N, ENNReal.ofReal (|loopDiscrepancy a r X| ^ (2 * m))
          ∂gibbsMeasure P N
        ≤ ∫⁻ X : Configuration N, (ENNReal.ofReal (2 ^ (2 * m - 1)) *
            ENNReal.ofReal ((loopCount a r X) ^ (2 * m)) +
              ENNReal.ofReal (2 ^ (2 * m - 1) * r ^ (2 * m))) ∂gibbsMeasure P N :=
          lintegral_mono hpt2
      _ = ENNReal.ofReal (2 ^ (2 * m - 1)) * ∫⁻ X : Configuration N,
            ENNReal.ofReal ((loopCount a r X) ^ (2 * m)) ∂gibbsMeasure P N +
            ENNReal.ofReal (2 ^ (2 * m - 1) * r ^ (2 * m)) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          simp
      _ ≤ ENNReal.ofReal (2 ^ (2 * m - 1)) * ENNReal.ofReal ((CL * (1 + r)) ^ (2 * m)) +
            ENNReal.ofReal (2 ^ (2 * m - 1) * r ^ (2 * m)) :=
          add_le_add (mul_le_mul_of_nonneg_left hM2 zero_le) le_rfl
      _ ≤ ENNReal.ofReal (D2 * (1 + r) ^ (2 * m)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [hD2_def, mul_pow]
          have hr2 : r ^ (2 * m) ≤ (1 + r) ^ (2 * m) := pow_le_pow_left₀ hr0.le (by linarith) _
          nlinarith [mul_le_mul_of_nonneg_left hr2 (by positivity : (0:ℝ) ≤ 2 ^ (2 * m - 1))]
  -- The tail from the rigidity conclusion, at the level `t = (r/2)^x`.
  set t : ℝ := (r / 2) ^ x with ht_def
  set q_t : ℝ := C * Real.exp (-c * (r / 2) ^ a') with hq_def
  have hℓpos : 0 < arcRadius N r := by unfold arcRadius; positivity
  have hℓle : arcRadius N r ≤ 1 / 4 := by
    unfold arcRadius
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have htail : gibbsMeasure P N {X | t ≤ |loopDiscrepancy a r X|} ≤ ENNReal.ofReal q_t := by
    have h := (hgap N).2 (arcCentre N a r) (arcRadius N r) hℓpos hℓle
    have e1 : (N : ℝ) * arcRadius N r = r / 2 := by
      unfold arcRadius
      field_simp
    have e2 : 2 * (N : ℝ) * arcRadius N r = r := by
      unfold arcRadius
      field_simp
    rw [e1, e2] at h
    simp only [arcCount_arcCentre _ _ hNpos] at h
    have hset : {X : Configuration N | t ≤ |loopDiscrepancy a r X|} =
        {X : Configuration N | |loopCount a r X - r| ≥ (r / 2) ^ x} := by
      ext X
      simp only [mem_ofPred_eq, hν_eq, ge_iff_le]
      rfl
    rw [hset]
    exact h
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by positivity) _
  have hq0 : 0 ≤ q_t := by rw [hq_def]; positivity
  have hM0 : 0 ≤ κ * (1 + r) := by positivity
  have hmom_ν : ∫⁻ X : Configuration N, ENNReal.ofReal (|loopDiscrepancy a r X| ^ (2 * m))
      ∂gibbsMeasure P N ≤ ENNReal.ofReal ((κ * (1 + r)) ^ (2 * m)) := by
    refine hmomν.trans (le_of_eq ?_)
    congr 1
    rw [mul_pow, hκ2]
  have hmain := lintegral_pow_le_tail_bound (μ := gibbsMeasure P N) hνmeas (m := m) (t := t)
    (M := κ * (1 + r)) (q := q_t) ht0 hM0 hq0 hmom_ν htail
  -- Absorb the polynomial factors into `r^{xm}`.
  set R : ℝ := r ^ x with hR_def
  have hR0 : 0 ≤ R := by rw [hR_def]; positivity
  have ht_le : t ≤ R := by
    rw [ht_def, hR_def]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hx.le
  have htm : t ^ m ≤ R ^ m := pow_le_pow_left₀ ht0 ht_le m
  have hsqrt : Real.sqrt q_t = Real.sqrt C * Real.exp (-c'' * r ^ a') := by
    rw [hq_def, Real.sqrt_mul hC.le]
    congr 1
    rw [show Real.exp (-c * (r / 2) ^ a') = Real.exp (-(c / 2) * (r / 2) ^ a') ^ 2 by
      rw [← Real.exp_nat_mul]
      congr 1
      ring]
    rw [Real.sqrt_sq (Real.exp_nonneg _)]
    congr 1
    rw [Real.div_rpow hr0.le (by norm_num), hc''_def]
    field_simp
  have hmR : r ^ m = R ^ m * r ^ β := by
    have hexp : x * (m : ℝ) + β = (m : ℝ) := by
      rw [hβ_def]
      ring
    rw [hR_def, ← Real.rpow_natCast (r ^ x) m, ← Real.rpow_mul hr0.le, ← Real.rpow_add hr0, hexp,
      Real.rpow_natCast]
  have hκ_term : (κ * (1 + r)) ^ m * Real.sqrt q_t ≤ κ ^ m * 2 ^ m * Real.sqrt C * Kd * R ^ m := by
    have h12 : (κ * (1 + r)) ^ m ≤ κ ^ m * 2 ^ m * r ^ m := by
      rw [mul_pow, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hκpos.le m)
      have h2r : (1 + r) ≤ 2 * r := by linarith
      calc (1 + r) ^ m ≤ (2 * r) ^ m := pow_le_pow_left₀ (by linarith) h2r m
        _ = 2 ^ m * r ^ m := mul_pow 2 r m
    have hdec := hKd r hr1
    calc (κ * (1 + r)) ^ m * Real.sqrt q_t
        ≤ (κ ^ m * 2 ^ m * r ^ m) * (Real.sqrt C * Real.exp (-c'' * r ^ a')) := by
          rw [hsqrt]
          exact mul_le_mul h12 le_rfl (by positivity) (by positivity)
      _ = κ ^ m * 2 ^ m * Real.sqrt C * (R ^ m * (r ^ β * Real.exp (-c'' * r ^ a'))) := by
          rw [hmR]
          ring
      _ ≤ κ ^ m * 2 ^ m * Real.sqrt C * (R ^ m * Kd) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdec (pow_nonneg hR0 m))
            (by positivity)
      _ = κ ^ m * 2 ^ m * Real.sqrt C * Kd * R ^ m := by ring
  have hsum_bound : t ^ m + (κ * (1 + r)) ^ m * Real.sqrt q_t ≤ K2 * R ^ m := by
    have hK : K2 * R ^ m = R ^ m + κ ^ m * 2 ^ m * Real.sqrt C * Kd * R ^ m := by
      rw [hK2_def]
      ring
    linarith
  have hfinal_lint : ∫⁻ X : Configuration N, ENNReal.ofReal (|loopDiscrepancy a r X| ^ m)
      ∂gibbsMeasure P N ≤ ENNReal.ofReal ((K2 ^ ((m : ℝ)⁻¹) * R) ^ m) := by
    rw [mul_pow, Real.rpow_inv_natCast_pow hK2.le (by omega)]
    exact hmain.trans (ENNReal.ofReal_le_ofReal (hsum_bound))
  have hB0 : 0 ≤ K2 ^ ((m : ℝ)⁻¹) * R := by positivity
  have hE := eLpNorm_le_of_lintegral_pow_le (μ := gibbsMeasure P N) hνmeas hm1 hB0 hfinal_lint
  calc eLpNorm (fun X : Configuration N => loopDiscrepancy a r X) (ENNReal.ofReal p)
        (gibbsMeasure P N)
      ≤ eLpNorm (fun X : Configuration N => loopDiscrepancy a r X) (ENNReal.ofReal m)
          (gibbsMeasure P N) := eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpm)
    _ ≤ ENNReal.ofReal (K2 ^ ((m : ℝ)⁻¹) * r ^ (s / 2 + δ)) := hE

end Internal

end Riesz1

end
end
