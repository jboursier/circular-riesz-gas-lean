/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopSizeBiasLaw
public import Riesz1.Auxiliary.LoopMomentsBlocks
public import Riesz1.Rigidity.InverseBlocks

/-!
# Block moments under the preceding-particle law

The moment assertions in the "in particular" clause of the size-bias part of
Lemma 5.8. Inverse moments are unconditional. Fluctuation moments
are conditional on rigidity.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- The microscopic length of the block starting at integer label `j` with `k` edges,
in anchored coordinates. -/
def loopAnchoredBlock (n : ℕ) (j : ℤ) (k : ℕ) (y : Fin (n + 1) → ℝ) : ℝ :=
  (n + 2 : ℕ) * (anchoredCyclicOffset (n + 1) y (j + k) - anchoredCyclicOffset (n + 1) y j)

theorem measurable_loopAnchoredBlock (n : ℕ) (j : ℤ) (k : ℕ) :
    Measurable (loopAnchoredBlock n j k) :=
  ((measurable_anchoredCyclicOffset _ _).sub (measurable_anchoredCyclicOffset _ _)).const_mul _

theorem loopAnchoredBlock_anchorCoords (n : ℕ) (j : ℤ) (k : ℕ)
    (X : Configuration (n + 1).succPNat) :
    loopAnchoredBlock n j k (anchorCoords (n + 1) X.val).2 = blockLength X j k := by
  rw [blockLength, cyclicLift_eq_anchor_add, cyclicLift_eq_anchor_add]
  unfold loopAnchoredBlock
  simp only [Nat.succPNat_coe, Nat.cast_succ]
  ring

/-- Every inverse block moment has the same scale after size bias. Constants are chosen
before the particle number, integer label, and positive block length. -/
theorem loopSizeBiased_inverse_blocks (P : Parameters) {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (n : ℕ) (j : ℤ) (k : ℕ), 0 < k →
      (∫⁻ y, ENNReal.ofReal (loopAnchoredBlock n j k y ^ (-p)) ∂loopSizeBiasedLaw P n) ≤
        ENNReal.ofReal (C * (k : ℝ) ^ (-p)) := by
  obtain ⟨D, hD, hd⟩ := loopSizeWeight_eLpNorm_two_uniform
  obtain ⟨B, hB, hb⟩ := inverse_blocks_uniform P (p := 2 * p) (by positivity)
  refine ⟨D * B ^ (1 / 2 : ℝ), mul_pos hD (Real.rpow_pos_of_pos hB _), ?_⟩
  intro hPL n j k hk
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal (loopAnchoredBlock n j k y ^ (-p))
  have hF : Measurable F := ((measurable_loopAnchoredBlock n j k).pow_const (-p)).ennreal_ofReal
  have he : (∫⁻ y, F y ^ (2 : ℝ) ∂anchoredLaw P (n + 1)) =
      ∫⁻ X : Configuration (n + 1).succPNat, ENNReal.ofReal (blockLength X j k ^ (-(2 * p)))
        ∂gibbsMeasure P _ := by
    have ha : Measurable (fun X : Configuration (n + 1).succPNat => (anchorCoords (n + 1) X.val).2) :=
      measurable_snd.comp (measurable_anchorCoords_config (n + 1))
    rw [← map_snd_gibbsMeasure P (n + 1), lintegral_map (hF.pow_const 2) ha]
    apply lintegral_congr
    intro X
    dsimp only [F]
    rw [loopAnchoredBlock_anchorCoords, ENNReal.ofReal_rpow_of_nonneg
      (Real.rpow_nonneg (blockLength_pos X j hk).le _) (by norm_num),
      ← Real.rpow_mul (blockLength_pos X j hk).le]
    congr 2
    ring
  have hm := (hb hPL (n + 1).succPNat j k hk).choose_spec
  have h := sizeBiased_lintegral_le (anchoredLaw P (n + 1)) (measurable_loopSizeWeight n) hF
  change (∫⁻ y, F y ∂loopSizeBiasedLaw P n) ≤ _ at h
  apply h.trans
  rw [he]
  calc
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal (B * (k : ℝ) ^ (-(2 * p))) ^ (1 / 2 : ℝ) := by
      gcongr
      · exact hd hPL P n

    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hB.le (Real.rpow_nonneg hkr.le _)) (by norm_num),
        ← ENNReal.ofReal_mul hD.le, Real.mul_rpow hB.le (Real.rpow_nonneg hkr.le _),
        ← Real.rpow_mul hkr.le]
      congr 1
      have he : -(2 * p) * (1 / 2 : ℝ) = -p := by ring
      rw [he]
      ring

namespace Internal

/-- Block fluctuation `L^p` bounds retain their exponent after preceding-particle selection.
The small-exponent threshold of the paper is retained. -/
theorem loopSizeBiased_blockDeviation_of_rigidity (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (hRig : RigidityConclusion β s hβ hs hs1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 → ∀ p : ℝ, 1 ≤ p →
      ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (n : ℕ)
        (i : Fin (((n + 1).succPNat : ℕ))) (k : ℕ), 1 ≤ k → k ≤ (n + 2) / 2 →
        eLpNorm (fun y => loopAnchoredBlock n (i : ℕ) k y - k) (ENNReal.ofReal p)
          (loopSizeBiasedLaw ⟨(β, s), hβ, hs, hs1⟩ n) ≤
            ENNReal.ofReal (C * (k : ℝ) ^ (s / 2 + δ)) := by
  obtain ⟨D, hD, hd⟩ := loopSizeWeight_eLpNorm_two_uniform
  obtain ⟨eps0, heps0, hb⟩ := blockDeviation_eLpNorm_of_rigidity β s hβ hs hs1 hRig
  refine ⟨eps0, heps0, fun δ hδ hδlt p hp => ?_⟩
  obtain ⟨B, hB, hb'⟩ := hb δ hδ hδlt (2 * p) (by linarith)
  refine ⟨D ^ (1 / p) * B, mul_pos (Real.rpow_pos_of_pos hD _) hB, ?_⟩
  intro hPL n i k hk hkN
  let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
  let T : (Fin (n + 1) → ℝ) → ℝ := fun y => loopAnchoredBlock n (i : ℕ) k y - k
  have hT : Measurable T := (measurable_loopAnchoredBlock n (i : ℕ) k).sub_const _
  have hbase : eLpNorm T (ENNReal.ofReal (2 * p)) (anchoredLaw P (n + 1)) ≤
      ENNReal.ofReal (B * (k : ℝ) ^ (s / 2 + δ)) := by
    have ha : Measurable (fun X : Configuration (n + 1).succPNat => (anchorCoords (n + 1) X.val).2) :=
      measurable_snd.comp (measurable_anchorCoords_config (n + 1))
    rw [← map_snd_gibbsMeasure P (n + 1), eLpNorm_map_measure hT.aestronglyMeasurable ha.aemeasurable]
    simpa only [Function.comp_def, T, loopAnchoredBlock_anchorCoords] using
      hb' hPL (n + 1).succPNat (by simp) i k hk hkN
  apply (loopSizeBiased_eLpNorm_le P n hT (by linarith : 0 < p)).trans
  calc
    _ ≤ ENNReal.ofReal D ^ (1 / p) * ENNReal.ofReal (B * (k : ℝ) ^ (s / 2 + δ)) := by
      gcongr
      exact hd hPL P n
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg hD.le (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end Internal

end Riesz1

end
