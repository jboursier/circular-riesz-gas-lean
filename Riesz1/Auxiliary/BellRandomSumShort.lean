/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.RigidityConclusion
public import Riesz1.Auxiliary.BellRandomSumEvents
public import Riesz1.ToMathlib.LogConcave.GapIBP

/-!
# Summable comparison error for a short block

Split at the rigidity cutoff. On the good event the derivative bound applies
at the block scale. On the bad event Cauchy--Schwarz combines inverse moments
with the rigidity tail. Inverse moments also cover bounded block lengths.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

namespace Internal

/-- A uniform, summable error for each short block, conditional on rigidity. -/
theorem bell_random_short_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hRig : RigidityConclusion beta s hbeta hs hs1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+),
      2 ≤ (N : ℕ) → ∀ (i : Fin (N : ℕ)) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
      ∀ (ℓ : ℝ) (ψ : ℝ → ℝ), 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      |(∫ X : Configuration N, bellKernel s N ℓ ψ (blockLength X (i : ℕ) k)
          ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) -
        bellKernel s N ℓ ψ (k : ℝ)| ≤
          C * bellConstant ℓ ψ * (k : ℝ) ^ (-1 - s / 4) := by
  let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
  obtain ⟨eps0, heps0, htail⟩ := hRig
  let eps := min (eps0 / 2) (s / 8)
  have heps : 0 < eps := lt_min (by positivity) (by positivity)
  have heps0' : eps < eps0 := (min_le_left _ _).trans_lt (by linarith)
  have hepss : eps ≤ s / 8 := min_le_right _ _
  let t := s / 2 + eps
  have ht : t < 1 := by dsimp [t]; linarith
  obtain ⟨c, Ct, hc, hCt, htail⟩ := htail eps heps heps0'
  let a := eps / (4 * (s + 2))
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨K0, hK0⟩ := Filter.tendsto_atTop_atTop.mp
    (tendsto_rpow_atTop (show 0 < 1 - t by linarith)) 2
  let K := max K0 1
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hcut (x : ℝ) (hx : 0 < x) (hxK : K ≤ x) : x ^ t ≤ x / 2 := by
    have hh := mul_le_mul_of_nonneg_right
      (hK0 x ((le_max_left _ _).trans hxK)) (Real.rpow_nonneg hx.le t)
    rw [← Real.rpow_add hx, show 1 - t + t = 1 by ring, Real.rpow_one] at hh
    linarith
  obtain ⟨Cq, hCq, hq⟩ := bell_kernel s hs hs1
  obtain ⟨M, hM, hweight⟩ := bell_value_weight_second_moment P
  obtain ⟨Ci, _, hiq⟩ := bell_random_kernel_integrable P
  let b := 1 - 3 * s / 4
  have hb : 0 < b := by dsimp [b]; linarith
  obtain ⟨B, hB, hdec⟩ := gap_exp_neg_mul_le (half_pos hc)
    (p := b / a) (div_nonneg hb.le ha.le)
  let L := (1 / 2 : ℝ) ^ (-1 - s)
  let D := L + Real.sqrt M * Real.sqrt Ct * B + Real.sqrt M * K ^ b + 1
  have hD : 0 < D := by dsimp [D, L]; positivity
  refine ⟨Cq * D, mul_pos hCq hD, ?_⟩
  intro hPL N _hN i k hk hkN ℓ ψ hℓ hℓ1 hNℓ hψ hper
  have := (modelWellDefined P N).2.2
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkN' : k < (N : ℕ) := by omega
  have hkhalf : (k : ℝ) ≤ (N : ℝ) / 2 := by
    have hh : 2 * k ≤ (N : ℕ) := by omega
    have hh' : 2 * (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hh
    linarith
  have hA : 0 ≤ Cq * bellConstant ℓ ψ :=
    mul_nonneg hCq.le (mul_nonneg hℓ.le (bellEnergy_nonneg hℓ))
  obtain ⟨hiW, hbW⟩ := hweight hPL N (i : ℕ) k hk hkN
  have hW := (measurable_bellValueWeight s N (i : ℕ) k).aestronglyMeasurable
    (μ := gibbsMeasure P N)
  have hW0 := bellValueWeight_nonneg s (i : ℕ) hk hkN'
  have hqi : Integrable (fun X : Configuration N =>
      bellKernel s N ℓ ψ (blockLength X (i : ℕ) k)) (gibbsMeasure P N) :=
    (hiq hPL N (i : ℕ) k hk hkN' ℓ ψ hℓ hℓ1 hNℓ hψ hper).1
  let f : Configuration N → ℝ := fun X =>
    bellKernel s N ℓ ψ (blockLength X (i : ℕ) k) - bellKernel s N ℓ ψ (k : ℝ)
  have hiDiff : Integrable f (gibbsMeasure P N) := hqi.sub (integrable_const _)
  have hpoint (X : Configuration N) : |f X| ≤
      (Cq * bellConstant ℓ ψ) * bellValueWeight s (i : ℕ) k X :=
    bell_kernel_value_weight hℓ hCq.le (hq N ℓ ψ N.pos hℓ hℓ1 hNℓ hψ hper).2.2.1
      (i : ℕ) hk hkN' X
  have heq : (∫ X, f X ∂gibbsMeasure P N) =
      (∫ X : Configuration N, bellKernel s N ℓ ψ (blockLength X (i : ℕ) k)
        ∂gibbsMeasure P N) - bellKernel s N ℓ ψ (k : ℝ) := by
    dsimp [f]
    rw [integral_sub hqi (integrable_const _)]
    simp
  have hsqrtM : Real.sqrt (M * (k : ℝ) ^ (-2 * s)) =
      Real.sqrt M * (k : ℝ) ^ (-s) := by
    rw [Real.sqrt_mul hM.le, Real.sqrt_eq_rpow ((k : ℝ) ^ (-2 * s)), ← Real.rpow_mul hk0.le]
    congr 2
    ring
  rw [← heq]
  by_cases hkK : K ≤ (k : ℝ)
  · let E : Set (Configuration N) := {X | (k : ℝ) ^ t < |blockLength X (i : ℕ) k - k|}
    have hE : MeasurableSet E := measurableSet_lt measurable_const
      (continuous_abs.measurable.comp ((measurable_blockLength _ _).sub_const _))
    have hprob : (gibbsMeasure P N).real E ≤ Ct * Real.exp (-c * (k : ℝ) ^ a) := by
      have hh := (htail N).1 i k hk hkN
      have hsub : E ⊆ {X | (k : ℝ) ^ t ≤ |blockLength X (i : ℕ) k - k|} := by
        intro X hX
        change (k : ℝ) ^ t ≤ |blockLength X (i : ℕ) k - k|
        exact (show (k : ℝ) ^ t < |blockLength X (i : ℕ) k - k| from hX).le
      have htailE : gibbsMeasure P N E ≤ ENNReal.ofReal (Ct * Real.exp (-c * (k : ℝ) ^ a)) :=
        (measure_mono hsub).trans hh
      have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top htailE
      rw [ENNReal.toReal_ofReal (by positivity)] at hh'
      exact hh'
    have hgood (X : Configuration N) (hX : X ∈ Eᶜ) :
        |f X| ≤ Cq * bellConstant ℓ ψ * L * (k : ℝ) ^ (-1 - s + t) := by
      have hX' : |blockLength X (i : ℕ) k - k| ≤ (k : ℝ) ^ t :=
        (not_lt.mp (show ¬(k : ℝ) ^ t < |blockLength X (i : ℕ) k - k| from hX))
      exact bell_kernel_good_event hs hs1 N.pos hℓ hψ hCq.le
        (hq N ℓ ψ N.pos hℓ hℓ1 hNℓ hψ hper).2.2.2 hk0 hkhalf
        (hcut k hk0 hkK) hX'
    have hsplit := bell_integral_good_bad hiDiff hW hW0 hiW hE hA
      (by dsimp [L]; positivity) hgood hpoint hbW hprob
    have hsqrtC : Real.sqrt (Ct * Real.exp (-c * (k : ℝ) ^ a)) =
        Real.sqrt Ct * Real.exp (-(c / 2) * (k : ℝ) ^ a) := by
      rw [Real.sqrt_mul hCt.le]
      congr 1
      rw [show Real.exp (-c * (k : ℝ) ^ a) =
          Real.exp (-(c / 2) * (k : ℝ) ^ a) ^ 2 by
        rw [← Real.exp_nat_mul]; congr 1; ring, Real.sqrt_sq (Real.exp_nonneg _)]
    rw [hsqrtM, hsqrtC] at hsplit
    -- The two terms retain the derivative scale and the exponential tail.
    have hevent : |∫ X, f X ∂gibbsMeasure P N| ≤ Cq * bellConstant ℓ ψ *
        (L * (k : ℝ) ^ (-1 - s / 2 + eps) + Real.sqrt M * Real.sqrt Ct *
          ((k : ℝ) ^ (-s) * Real.exp (-(c / 2) * (k : ℝ) ^ a))) := by
      convert hsplit using 1
      dsimp [t]
      ring_nf
    have hsmall : (k : ℝ) ^ (-1 - s / 2 + eps) ≤ (k : ℝ) ^ (-1 - s / 4) :=
      Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
    have hexp : Real.exp (-(c / 2) * (k : ℝ) ^ a) ≤ B * (k : ℝ) ^ (-b) := by
      convert hdec ((k : ℝ) ^ a) (by positivity) using 1
      rw [← Real.rpow_mul hk0.le]
      congr 2
      field_simp
    have hpower : (k : ℝ) ^ (-s) * (k : ℝ) ^ (-b) = (k : ℝ) ^ (-1 - s / 4) := by
      rw [← Real.rpow_add hk0]
      congr 1
      dsimp [b]
      ring
    calc _ ≤ Cq * bellConstant ℓ ψ *
          (L * (k : ℝ) ^ (-1 - s / 2 + eps) + Real.sqrt M * Real.sqrt Ct *
            ((k : ℝ) ^ (-s) * Real.exp (-(c / 2) * (k : ℝ) ^ a))) := hevent
      _ ≤ Cq * bellConstant ℓ ψ *
          (L * (k : ℝ) ^ (-1 - s / 4) + Real.sqrt M * Real.sqrt Ct *
            ((k : ℝ) ^ (-s) * (B * (k : ℝ) ^ (-b)))) := by
              dsimp [L]
              gcongr
      _ = Cq * bellConstant ℓ ψ *
          ((L + Real.sqrt M * Real.sqrt Ct * B) * (k : ℝ) ^ (-1 - s / 4)) := by
            rw [show (k : ℝ) ^ (-s) * (B * (k : ℝ) ^ (-b)) =
              B * ((k : ℝ) ^ (-s) * (k : ℝ) ^ (-b)) by ring, hpower]
            ring
      _ ≤ Cq * bellConstant ℓ ψ * (D * (k : ℝ) ^ (-1 - s / 4)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hh : 0 ≤ Real.sqrt M * K ^ b := by positivity
        dsimp [D]
        linarith
      _ = _ := by ring
  · have hbound := bell_integral_good_bad hiDiff hW hW0 hiW MeasurableSet.univ hA
      (le_refl (0 : ℝ)) (by simp) hpoint hbW (measureReal_le_one (μ := gibbsMeasure P N)
        (s := Set.univ))
    simp only [zero_add, Real.sqrt_one, mul_one] at hbound
    rw [hsqrtM] at hbound
    have hsmall : (k : ℝ) ^ (-s) ≤ K ^ b * (k : ℝ) ^ (-1 - s / 4) := by
      have hh := Real.rpow_le_rpow hk0.le (not_le.mp hkK).le hb.le
      have hpow : (k : ℝ) ^ b * (k : ℝ) ^ (-1 - s / 4) = (k : ℝ) ^ (-s) := by
        rw [← Real.rpow_add hk0]
        congr 1
        dsimp [b]
        ring
      rw [← hpow]
      exact mul_le_mul_of_nonneg_right hh (by positivity)
    calc _ ≤ (Cq * bellConstant ℓ ψ) * (Real.sqrt M * (k : ℝ) ^ (-s)) := hbound
      _ ≤ (Cq * bellConstant ℓ ψ) *
          (Real.sqrt M * (K ^ b * (k : ℝ) ^ (-1 - s / 4))) := by gcongr
      _ = Cq * bellConstant ℓ ψ *
          ((Real.sqrt M * K ^ b) * (k : ℝ) ^ (-1 - s / 4)) := by ring
      _ ≤ Cq * bellConstant ℓ ψ * (D * (k : ℝ) ^ (-1 - s / 4)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hh : 0 ≤ L + Real.sqrt M * Real.sqrt Ct * B := by dsimp [L]; positivity
        dsimp [D]
        linarith
      _ = _ := by ring

end Internal

end Riesz1

end
