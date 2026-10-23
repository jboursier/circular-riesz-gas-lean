/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.RigidityConclusion
public import Riesz1.Rigidity.BlockMoments
public import Riesz1.ToMathlib.Moments.LpBounds
public import Riesz1.ToMathlib.Moments.Decay

/-!
# Block deviations from the lattice

The moments part of Lemma B.2, the last claim: for `1 ≤ k ≤ N/2`,
`‖S_{i,k} - k‖_{L^p} ≤ C k^{s/2+δ}`, where `S_{i,k} = N (x_{i+k} - x_i)` and `δ` is below the
rigidity threshold.

The proof splits the deviation at the level `k^{s/2+δ}`. Below the level, the moment bound of
the block (`Riesz1.blockLength_moments`) and the stretched exponential tail of the gap rigidity
conclusion (passed as the hypothesis `Riesz1.Internal.RigidityConclusion`) control the moment.
Above it, the tail-to-moment bound `lintegral_pow_le_tail_bound` applies. The polynomial factor
is absorbed into the stretched exponential by `rpow_mul_exp_neg_bounded`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

namespace Internal

/-- **Block deviations**, the moments part of Lemma B.2 (the last claim). Conditionally
on the rigidity conclusion at `beta, s`: there is a threshold `eps0 > 0` such that for every
`0 < δ < min(s/2, eps0)` and every `p ≥ 1` there is `C > 0`, depending only on `beta, s, δ, p`,
with `‖S_{i,k} - k‖_{L^p} ≤ C k^{s/2+δ}` for every `N ≥ 2`, label `i` and `1 ≤ k ≤ N/2`. -/
theorem blockDeviation_eLpNorm_of_rigidity (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hRig : Internal.RigidityConclusion beta s hbeta hs hs1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 → ∀ p : ℝ, 1 ≤ p →
      ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+), 2 ≤ (N : ℕ) →
        ∀ (i : Fin (N : ℕ)) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
          eLpNorm (fun X : Configuration N => blockLength X (i : ℕ) k - k) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
            ENNReal.ofReal (C * (k : ℝ) ^ (s / 2 + δ)) := by
  obtain ⟨eps0, heps0, hbound⟩ := hRig
  refine ⟨eps0, heps0, fun δ hδ hδlt p hp => ?_⟩
  obtain ⟨c, C, hc, hC, hgap⟩ := hbound δ hδ (lt_of_lt_of_le hδlt (min_le_right _ _))
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hP
  set m : ℕ := ⌈p⌉₊ with hm_def
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := hp.trans (Nat.le_ceil p)
    exact_mod_cast this
  have hpm : p ≤ (m : ℝ) := Nat.le_ceil p
  have hm2 : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by
    have : (0 : ℝ) < m := by exact_mod_cast hm1
    push_cast
    positivity
  obtain ⟨Cm, hCm, hmom⟩ := blockLength_moments (((2 * m : ℕ) : ℝ)) hm2
  -- The `2m`-th moment of the deviation, with the constant `D`, and its root `κ`.
  set D : ℝ := 2 ^ (2 * m - 1) * (Cm + 1) with hD_def
  have hD : 0 < D := by positivity
  set κ : ℝ := D ^ (((2 * m : ℕ) : ℝ)⁻¹) with hκ_def
  have hκ2 : κ ^ (2 * m) = D := Real.rpow_inv_natCast_pow hD.le (by omega)
  have hκpos : 0 < κ := by positivity
  -- The exponential tail: `k^{β} exp(-(c/2) k^a)` is bounded for `k ≥ 1`.
  set a : ℝ := δ / (4 * (s + 2)) with ha_def
  have ha : 0 < a := by positivity
  set β : ℝ := (m : ℝ) - (s / 2 + δ) * (m : ℝ) with hβ_def
  obtain ⟨Kdec, hKdec0, hKdec⟩ := rpow_mul_exp_neg_bounded (β := β) ha (half_pos hc)
  set Kfin : ℝ := 1 + κ ^ m * Real.sqrt C * Kdec with hKfin_def
  have hKfin : 0 < Kfin := by positivity
  refine ⟨Kfin ^ ((m : ℝ)⁻¹), by positivity, fun hPL N hN i k hk1 hk2 => ?_⟩
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
  set t : ℝ := (k : ℝ) ^ (s / 2 + δ) with ht_def
  have ht0 : 0 ≤ t := Real.rpow_nonneg hk_pos.le _
  have hprob : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hZmeas : Measurable (fun X : Configuration N => blockLength X (i : ℕ) k - k) :=
    (measurable_blockLength _ _).sub measurable_const
  -- The `2m`-th moment of the deviation is at most `(κ k)^{2m}`.
  have hS0 : ∀ X : Configuration N, 0 ≤ blockLength X (i : ℕ) k := fun X =>
    (blockLength_pos X (i : ℕ) hk1).le
  have hpt : ∀ X : Configuration N, ENNReal.ofReal (|blockLength X (i : ℕ) k - k| ^ (2 * m)) ≤
      ENNReal.ofReal (2 ^ (2 * m - 1)) * ENNReal.ofReal (blockLength X (i : ℕ) k ^ (2 * m)) +
        ENNReal.ofReal (2 ^ (2 * m - 1) * (k : ℝ) ^ (2 * m)) := by
    intro X
    have hSk : |blockLength X (i : ℕ) k - k| ≤ blockLength X (i : ℕ) k + k := by
      rw [abs_le]
      constructor <;> linarith [hS0 X]
    have h1 : |blockLength X (i : ℕ) k - k| ^ (2 * m) ≤
        (blockLength X (i : ℕ) k + k) ^ (2 * m) :=
      pow_le_pow_left₀ (abs_nonneg _) hSk _
    have h2 : (blockLength X (i : ℕ) k + k) ^ (2 * m) ≤
        2 ^ (2 * m - 1) * (blockLength X (i : ℕ) k ^ (2 * m) + (k : ℝ) ^ (2 * m)) :=
      add_pow_le (hS0 X) hk_pos.le _
    calc ENNReal.ofReal (|blockLength X (i : ℕ) k - k| ^ (2 * m))
        ≤ ENNReal.ofReal (2 ^ (2 * m - 1) * (blockLength X (i : ℕ) k ^ (2 * m) +
            (k : ℝ) ^ (2 * m))) := ENNReal.ofReal_le_ofReal (h1.trans h2)
      _ = _ := by
          rw [mul_add, ENNReal.ofReal_add (mul_nonneg (by positivity) (pow_nonneg (hS0 X) _))
            (by positivity), ENNReal.ofReal_mul (by positivity)]
  have hmoment_raw := hmom hPL P N hN (i : ℕ) k hk1
  simp_rw [Real.rpow_natCast] at hmoment_raw
  have hmoment : ∫⁻ X, ENNReal.ofReal (|blockLength X (i : ℕ) k - k| ^ (2 * m))
      ∂gibbsMeasure P N ≤ ENNReal.ofReal (D * (k : ℝ) ^ (2 * m)) := by
    calc ∫⁻ X, ENNReal.ofReal (|blockLength X (i : ℕ) k - k| ^ (2 * m)) ∂gibbsMeasure P N
        ≤ ∫⁻ X, (ENNReal.ofReal (2 ^ (2 * m - 1)) * ENNReal.ofReal (blockLength X (i : ℕ) k ^
            (2 * m)) + ENNReal.ofReal (2 ^ (2 * m - 1) * (k : ℝ) ^ (2 * m)))
            ∂gibbsMeasure P N := lintegral_mono hpt
      _ = ENNReal.ofReal (2 ^ (2 * m - 1)) * ∫⁻ X, ENNReal.ofReal (blockLength X (i : ℕ) k ^
            (2 * m)) ∂gibbsMeasure P N + ENNReal.ofReal (2 ^ (2 * m - 1) * (k : ℝ) ^ (2 * m)) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ,
            lintegral_const_mul _ (((measurable_blockLength _ _).pow_const _).ennreal_ofReal)]
          simp
      _ ≤ ENNReal.ofReal (2 ^ (2 * m - 1)) * ENNReal.ofReal (Cm * (k : ℝ) ^ (2 * m)) +
            ENNReal.ofReal (2 ^ (2 * m - 1) * (k : ℝ) ^ (2 * m)) :=
          add_le_add (mul_le_mul_of_nonneg_left hmoment_raw.2 zero_le) le_rfl
      _ = ENNReal.ofReal (D * (k : ℝ) ^ (2 * m)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add
            (mul_nonneg (by positivity) (mul_nonneg hCm.le (pow_nonneg hk_pos.le _)))
            (mul_nonneg (by positivity) (pow_nonneg hk_pos.le _))]
          congr 1
          rw [hD_def]
          ring
  -- The tail from rigidity, at the level `t = k^{s/2+δ}`.
  have htail : gibbsMeasure P N {X | t ≤ |blockLength X (i : ℕ) k - k|} ≤
      ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ a)) := (hgap N).1 i k hk1 hk2
  have hq0 : 0 ≤ C * Real.exp (-c * (k : ℝ) ^ a) := by positivity
  have hmain := lintegral_pow_le_tail_bound (μ := gibbsMeasure P N) hZmeas (m := m) (t := t)
    (M := κ * k) (q := C * Real.exp (-c * (k : ℝ) ^ a)) ht0 (by positivity) hq0
    (by rw [mul_pow, hκ2]; exact hmoment) htail
  -- Absorb the factor `k^{m - (s/2+δ)m}` into the stretched exponential.
  have hsqrt : Real.sqrt (C * Real.exp (-c * (k : ℝ) ^ a)) =
      Real.sqrt C * Real.exp (-(c / 2) * (k : ℝ) ^ a) := by
    rw [Real.sqrt_mul hC.le]
    congr 1
    rw [show Real.exp (-c * (k : ℝ) ^ a) = Real.exp (-(c / 2) * (k : ℝ) ^ a) ^ 2 by
      rw [← Real.exp_nat_mul]
      congr 1
      ring]
    exact Real.sqrt_sq (Real.exp_nonneg _)
  have hkm : (k : ℝ) ^ m = t ^ m * (k : ℝ) ^ β := by
    rw [ht_def, ← Real.rpow_natCast ((k : ℝ) ^ (s / 2 + δ)) m, ← Real.rpow_mul hk_pos.le,
      ← Real.rpow_natCast (k : ℝ) m, ← Real.rpow_add hk_pos]
    congr 1
    rw [hβ_def]
    ring
  have hmain2 : (κ * k) ^ m * Real.sqrt (C * Real.exp (-c * (k : ℝ) ^ a)) ≤
      κ ^ m * Real.sqrt C * Kdec * t ^ m := by
    have hK := hKdec (k : ℝ) (by exact_mod_cast hk1)
    rw [mul_pow, hsqrt, hkm]
    calc κ ^ m * (t ^ m * (k : ℝ) ^ β) * (Real.sqrt C * Real.exp (-(c / 2) * (k : ℝ) ^ a))
        = κ ^ m * Real.sqrt C * (t ^ m * ((k : ℝ) ^ β * Real.exp (-(c / 2) * (k : ℝ) ^ a))) := by
          ring
      _ ≤ κ ^ m * Real.sqrt C * (t ^ m * Kdec) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK (pow_nonneg ht0 _)) (by positivity)
      _ = κ ^ m * Real.sqrt C * Kdec * t ^ m := by ring
  have hsum_bound : t ^ m + (κ * k) ^ m * Real.sqrt (C * Real.exp (-c * (k : ℝ) ^ a)) ≤
      Kfin * t ^ m := by
    have hK : Kfin * t ^ m = t ^ m + κ ^ m * Real.sqrt C * Kdec * t ^ m := by
      rw [hKfin_def]
      ring
    linarith [hmain2]
  have hfinal_lint : ∫⁻ X, ENNReal.ofReal (|blockLength X (i : ℕ) k - k| ^ m)
      ∂gibbsMeasure P N ≤ ENNReal.ofReal ((Kfin ^ ((m : ℝ)⁻¹) * t) ^ m) := by
    rw [mul_pow, Real.rpow_inv_natCast_pow hKfin.le (by omega)]
    exact hmain.trans (ENNReal.ofReal_le_ofReal hsum_bound)
  have hB0 : 0 ≤ Kfin ^ ((m : ℝ)⁻¹) * t := by positivity
  have hE := eLpNorm_le_of_lintegral_pow_le (μ := gibbsMeasure P N) hZmeas hm1 hB0 hfinal_lint
  calc eLpNorm (fun X : Configuration N => blockLength X (i : ℕ) k - k) (ENNReal.ofReal p)
        (gibbsMeasure P N)
      ≤ eLpNorm (fun X : Configuration N => blockLength X (i : ℕ) k - k) (ENNReal.ofReal m)
          (gibbsMeasure P N) := eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpm)
    _ ≤ ENNReal.ofReal (Kfin ^ ((m : ℝ)⁻¹) * t) := hE

end Internal

end Riesz1

end
end
