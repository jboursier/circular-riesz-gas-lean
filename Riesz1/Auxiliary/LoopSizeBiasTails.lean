/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopSizeBiasMoments
public import Riesz1.Auxiliary.LoopCutoffComplete
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Cutoff probabilities and gap tails under the preceding-particle law

The remaining "in particular" assertions of the size-bias part of Lemma 5.8:
arbitrarily large inverse powers survive size bias, and a stretched exponential tail
retains its exponent, with the decay coefficient divided by two.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

theorem measurable_loopCutoff (s γ ε : ℝ) (N : ℕ+) (ℓ : ℝ) : Measurable (loopCutoff s γ ε N ℓ) := by
  unfold loopCutoff cutoffC gradLift
  fun_prop

theorem loopCutoff_anchorCoords (s γ ε : ℝ) (n : ℕ) (ℓ : ℝ) (X : Configuration n.succPNat) :
    loopCutoff s γ ε n.succPNat ℓ (anchorVector (anchorCoords n X.val).2) =
      loopCutoff s γ ε n.succPNat ℓ X.val := by
  have he : (fun i => anchorVector (anchorCoords n X.val).2 i + X.val 0) = X.val := by
    funext i
    linarith [apply_eq_anchor_add n X.val i]
  rw [← loopCutoff_add_const s γ ε n.succPNat ℓ (anchorVector (anchorCoords n X.val).2) (X.val 0), he]

namespace Internal

/-- Every inverse-power cutoff probability holds under `w P*`.
The base estimate is used at power `2 B₀`, so the final power is exactly `B₀`. -/
theorem loopSizeBiased_cutoff_probability_of_rigidity (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (hRig : RigidityConclusion β s hβ hs hs1) (hPL : External.PrekopaLeindler)
    (γ ε : ℝ) (hγ : 1 < γ) (hε : 0 < ε) (hε1 : ε < min (1 / 8) ((1 - s / 2) / 8))
    {B₀ : ℝ} (hB₀ : 0 < B₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 → 1 ≤ (n + 2 : ℕ) * ℓ →
      loopSizeBiasedLaw ⟨(β, s), hβ, hs, hs1⟩ n
        {y | loopCutoff s γ ε (n + 1).succPNat ℓ (anchorVector y) ≠ 1} ≤
          ENNReal.ofReal (C * (((n + 2 : ℕ) : ℝ) * ℓ) ^ (-B₀)) := by
  obtain ⟨D, hD, hd⟩ := loopSizeWeight_eLpNorm_two_uniform
  obtain ⟨B, hB, hb⟩ := loopCutoff_probability_of_rigidity β s hβ hs hs1 hPL hRig
    γ ε hγ hε hε1 (2 * B₀) (by positivity)
  refine ⟨D * B ^ (1 / 2 : ℝ), mul_pos hD (Real.rpow_pos_of_pos hB _), ?_⟩
  intro n ℓ hℓ hℓ1 hK
  let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
  let E : Set (Fin (n + 1) → ℝ) :=
    {y | loopCutoff s γ ε (n + 1).succPNat ℓ (anchorVector y) ≠ 1}
  have hE : MeasurableSet E := (measurableSet_eq_fun
    ((measurable_loopCutoff s γ ε _ ℓ).comp (measurable_anchorVector _)) measurable_const).compl
  have ha : Measurable (fun X : Configuration (n + 1).succPNat => (anchorCoords (n + 1) X.val).2) :=
    measurable_snd.comp (measurable_anchorCoords_config (n + 1))
  have hbase : anchoredLaw P (n + 1) E ≤
      ENNReal.ofReal (B * (((n + 2 : ℕ) : ℝ) * ℓ) ^ (-(2 * B₀))) := by
    rw [← map_snd_gibbsMeasure P (n + 1), Measure.map_apply ha hE]
    have he : (fun X : Configuration (n + 1).succPNat => (anchorCoords (n + 1) X.val).2) ⁻¹' E =
        {X | loopCutoff s γ ε (n + 1).succPNat ℓ X.val ≠ 1} := by
      ext X
      change loopCutoff s γ ε (n + 1).succPNat ℓ (anchorVector (anchorCoords (n + 1) X.val).2) ≠ 1 ↔ _
      rw [loopCutoff_anchorCoords]
      rfl
    rw [he]
    have hh := hb (n + 1).succPNat (by simp) ℓ hℓ hℓ1 hK
    have hNr : ((n + 1).succPNat : ℝ) = ((n + 2 : ℕ) : ℝ) := by
      simp only [Nat.succPNat_coe, Nat.cast_succ]
    rw [hNr] at hh
    exact hh

  apply (loopSizeBiased_measure_le P n hE).trans
  calc
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal (B * (((n + 2 : ℕ) : ℝ) * ℓ) ^ (-(2 * B₀))) ^ (1 / 2 : ℝ) := by
      gcongr
      exact hd hPL P n
    _ = _ := by
      have hK0 : 0 < ((n + 2 : ℕ) : ℝ) * ℓ := by linarith
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        ← ENNReal.ofReal_mul hD.le, Real.mul_rpow hB.le (Real.rpow_nonneg hK0.le _),
        ← Real.rpow_mul hK0.le]
      congr 1
      have he : -(2 * B₀) * (1 / 2 : ℝ) = -B₀ := by ring
      rw [he]
      ring

/-- Stretched exponential block-gap tails under `w P*`, with the original threshold and
stretch exponent. Only the multiplicative and decay constants change. -/
theorem loopSizeBiased_gap_tail_of_rigidity (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (hRig : RigidityConclusion β s hβ hs hs1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < eps0 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (n : ℕ)
        (i : Fin (((n + 1).succPNat : ℕ))) (k : ℕ), 1 ≤ k → k ≤ (n + 2) / 2 →
        loopSizeBiasedLaw ⟨(β, s), hβ, hs, hs1⟩ n
          {y | |loopAnchoredBlock n (i : ℕ) k y - k| ≥ (k : ℝ) ^ (s / 2 + δ)} ≤
            ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (δ / (4 * (s + 2))))) := by
  obtain ⟨D, hD, hd⟩ := loopSizeWeight_eLpNorm_two_uniform
  obtain ⟨eps0, heps0, hr⟩ := hRig
  refine ⟨eps0, heps0, fun δ hδ hδlt => ?_⟩
  obtain ⟨c, B, hc, hB, hb⟩ := hr δ hδ hδlt
  refine ⟨c / 2, D * B ^ (1 / 2 : ℝ), by positivity,
    mul_pos hD (Real.rpow_pos_of_pos hB _), ?_⟩
  intro hPL n i k hk hkN
  let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
  let E : Set (Fin (n + 1) → ℝ) :=
    {y | |loopAnchoredBlock n (i : ℕ) k y - k| ≥ (k : ℝ) ^ (s / 2 + δ)}
  have hE : MeasurableSet E := measurableSet_le measurable_const
    ((measurable_loopAnchoredBlock n (i : ℕ) k).sub_const _).abs
  have ha : Measurable (fun X : Configuration (n + 1).succPNat => (anchorCoords (n + 1) X.val).2) :=
    measurable_snd.comp (measurable_anchorCoords_config (n + 1))
  have hbase : anchoredLaw P (n + 1) E ≤
      ENNReal.ofReal (B * Real.exp (-c * (k : ℝ) ^ (δ / (4 * (s + 2))))) := by
    rw [← map_snd_gibbsMeasure P (n + 1), Measure.map_apply ha hE]
    simpa only [E, Set.preimage_ofPred_eq, loopAnchoredBlock_anchorCoords, blockLength] using
      (hb (n + 1).succPNat).1 i k hk hkN
  apply (loopSizeBiased_measure_le P n hE).trans
  calc
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal (B * Real.exp (-c * (k : ℝ) ^ (δ / (4 * (s + 2))))) ^ (1 / 2 : ℝ) := by
      gcongr
      exact hd hPL P n
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        ← ENNReal.ofReal_mul hD.le, Real.mul_rpow hB.le (Real.exp_pos _).le, ← Real.exp_mul]
      congr 1
      have he : (-c * (k : ℝ) ^ (δ / (4 * (s + 2)))) * (1 / 2 : ℝ) =
          -(c / 2) * (k : ℝ) ^ (δ / (4 * (s + 2))) := by ring
      rw [he]
      ring

end Internal

end Riesz1

end
