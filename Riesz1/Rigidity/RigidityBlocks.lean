/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.RigidityBlocksLocal
public import Riesz1.Rigidity.RigidityBlocksCyclic
public import Riesz1.Rigidity.RigidityBlocksRates

/-!
# Concentration of the block difference

Part of the proof of Theorem 1, with constants chosen
before the cutoff, particle number, cyclic label and scale. The proof
works for every positive `ε`, not only for `ε` in `(0,1)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- **Concentration of the block difference**, part of Theorem 1.
The Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler inequality
`External.PrekopaLeindler` are taken as hypotheses.
The constants depend only on `P = (β,s)` and `ε`, and are chosen even
before these proof arguments. -/
theorem almost_optimal_rigidity_blocks (P : Parameters) {ε : ℝ} (hε : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (_hBE : External.BakryEmery)
      (_hPL : External.PrekopaLeindler) (N : ℕ+) (_hN : 2 ≤ (N : ℕ))
      (i : ℤ) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
      (gibbsMeasure P N).real
          {X | (k : ℝ) ^ ((parametersExponent P).val / 2 + ε) / 3 ≤
            |centeredBlockDiff X i k|} ≤
        C * Real.exp (-c * (k : ℝ) ^ (ε / (2 * ((parametersExponent P).val + 2)))) := by
  let s := (parametersExponent P).val
  have hs : 0 < s := (parametersExponent P).2.1
  let γ := ε / (2 * (s + 2))
  let δ := s / 2 + ε
  have hparams := Internal.rigidityBlocks_power_parameters hs hε
  have hγ : 0 < γ := hparams.1
  let b := P.val.1 * rigidityCurvatureConstant s
  have hb : 0 < b := mul_pos P.2.1 (rigidityCurvatureConstant_pos (parametersExponent P))
  let d₁ := b / (288 * (3 : ℝ) ^ ((1 + γ) * (s + 2)))
  let d₂ := b / (72 * (3 : ℝ) ^ (s + 1))
  have hd₁ : 0 < d₁ := by dsimp [d₁]; positivity
  have hd₂ : 0 < d₂ := by dsimp [d₂]; positivity
  let c := min blockMomentExponent (min d₁ d₂)
  have hc : 0 < c := lt_min blockMomentExponent_pos (lt_min hd₁ hd₂)
  have hc₀ : c ≤ blockMomentExponent := min_le_left _ _
  have hc₁ : c ≤ d₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hc₂ : c ≤ d₂ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨C₀, hC₀, hlocal⟩ := Internal.rigidityBlocks_local_tail P hγ
  let C := 5 + Real.exp (6 * c * C₀)
  have hC : 0 < C := by dsimp [C]; positivity
  have hC5 : 5 ≤ C := by dsimp [C]; linarith [Real.exp_pos (6 * c * C₀)]
  refine ⟨c, C, hc, hC, ?_⟩
  intro hBE hPL N hN i k hk hkN
  let := isProbabilityMeasure_gibbsMeasure P N
  have hkN' : 2 * k ≤ (N : ℕ) := by omega
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  let v := (k : ℝ) ^ δ / 3
  have hv : 0 < v := by dsimp [v]; positivity
  have hkγ : 0 ≤ (k : ℝ) ^ γ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  change (gibbsMeasure P N).real {X | v ≤ |centeredBlockDiff X i k|} ≤
    C * Real.exp (-c * (k : ℝ) ^ γ)
  by_cases hloc : 3 * k < (N : ℕ)
  · by_cases hlarge : 2 * C₀ ≤ v
    · have ht := hlocal hBE hPL N hN forcingCutoff isForcingCutoff_forcingCutoff i k hk hloc v hv hlarge
      have hrate := Internal.rigidityBlocks_local_exponent hs hε hb hk1
      have hmain : c * (k : ℝ) ^ γ ≤ b * (3 * (k : ℝ) + 1) * (2 * k + 1) * v ^ 2 /
          (32 * (((3 * k : ℕ) : ℝ) ^ (1 + γ)) ^ (s + 2)) := by
        have hr : d₁ * (k : ℝ) ^ γ ≤ b * (3 * (k : ℝ) + 1) * (2 * k + 1) * v ^ 2 /
            (32 * (((3 * k : ℕ) : ℝ) ^ (1 + γ)) ^ (s + 2)) := by
          simpa only [Nat.cast_mul, Nat.cast_ofNat, d₁, γ, v, δ] using hrate
        exact (mul_le_mul_of_nonneg_right hc₁ hkγ).trans hr
      have hexp := Real.exp_le_exp.mpr (neg_le_neg hmain)
      have herr := Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hc₀ hkγ))
      calc (gibbsMeasure P N).real {X | v ≤ |centeredBlockDiff X i k|} ≤
          2 * Real.exp (-(b * (3 * (k : ℝ) + 1) * (2 * k + 1) * v ^ 2) /
              (32 * (((3 * k : ℕ) : ℝ) ^ (1 + γ)) ^ (s + 2))) +
            3 * Real.exp (-blockMomentExponent * (k : ℝ) ^ γ) := ht
        _ ≤ 5 * Real.exp (-c * (k : ℝ) ^ γ) := by
          simp only [neg_div, neg_mul] at hexp herr ⊢
          linarith
        _ ≤ _ := mul_le_mul_of_nonneg_right hC5 (Real.exp_pos _).le
    · have hγδ : γ ≤ δ := by dsimp only [γ, δ]; linarith [hparams.2.1]
      have hpow : (k : ℝ) ^ γ ≤ (k : ℝ) ^ δ := Real.rpow_le_rpow_of_exponent_le hk1 hγδ
      have hsmall : c * (k : ℝ) ^ γ ≤ 6 * c * C₀ := by
        have hvlt : (k : ℝ) ^ δ < 6 * C₀ := by
          change ¬2 * C₀ ≤ (k : ℝ) ^ δ / 3 at hlarge
          linarith
        nlinarith
      have hone : 1 ≤ Real.exp (6 * c * C₀) * Real.exp (-c * (k : ℝ) ^ γ) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp_iff.mpr (by linarith)
      calc (gibbsMeasure P N).real {X | v ≤ |centeredBlockDiff X i k|} ≤ 1 := measureReal_le_one
        _ ≤ Real.exp (6 * c * C₀) * Real.exp (-c * (k : ℝ) ^ γ) := hone
        _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.exp_pos _).le
  · have ht := rigidityBlocks_full_tail hBE hPL P N hN i hk hkN' hv
    have hn : (0 : ℝ) < N := by exact_mod_cast N.pos
    have hnx : (N : ℝ) ≤ 3 * (k : ℝ) := by exact_mod_cast (show (N : ℕ) ≤ 3 * k by omega)
    have hxm : (k : ℝ) ≤ cyclicRepSpan N k + 1 := by
      exact_mod_cast (rigidityBlocks_span_bounds hk hkN').1
    have hr : d₂ * (k : ℝ) ^ γ ≤ b * (N : ℝ) * (cyclicRepSpan N k + 1) * v ^ 2 /
        (8 * (N : ℝ) ^ (s + 2)) :=
      Internal.rigidityBlocks_full_exponent hs hε hb hk1 hn hnx hxm
    have hmain := (mul_le_mul_of_nonneg_right hc₂ hkγ).trans hr
    have hexp := Real.exp_le_exp.mpr (neg_le_neg hmain)
    calc (gibbsMeasure P N).real {X | v ≤ |centeredBlockDiff X i k|} ≤
        2 * Real.exp (-(b * (N : ℝ) * (cyclicRepSpan N k + 1) * v ^ 2) /
          (8 * (N : ℝ) ^ (s + 2))) := ht
      _ ≤ 2 * Real.exp (-c * (k : ℝ) ^ γ) := by
        simp only [neg_div, neg_mul] at hexp ⊢
        exact mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

end Riesz1

end
