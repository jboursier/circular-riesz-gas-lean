/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopExteriorProbability
public import Riesz1.Rigidity.RigidityTheorem
import all Mathlib.Data.PNat.Defs
import all Init.Data.Nat.Basic

/-!
# Moments of the preceding-particle displacement

The displacement moment estimate used in the exterior part of Lemma 5.8.
Both signs of the integer label are included. The displacement of the preceding
particle is bounded using its actual size-biased nearest gap. Rigidity is supplied
by the Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler inequality
`External.PrekopaLeindler`.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- The size weight has uniformly bounded moments of every order at least one,
before size bias. The bound is uniform even in the model parameters. -/
theorem loopSizeWeight_eLpNorm_uniform {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (P : Parameters) (n : ℕ),
      eLpNorm (loopSizeWeight n) (ENNReal.ofReal p) (anchoredLaw P (n + 1)) ≤
        ENNReal.ofReal C := by
  obtain ⟨B, hB, hb⟩ := blockLength_moments p (by linarith)
  refine ⟨B + 1, by positivity, fun hPL P n => ?_⟩
  have hm := (hb hPL P (n + 1).succPNat (by simp) 0 1 one_pos).2
  simp only [Nat.cast_one, Real.one_rpow, mul_one, boundary_blockLength_one_eq_gap] at hm
  have hpow : B ≤ (B + 1) ^ p := by
    apply (show B ≤ B + 1 by linarith).trans
    exact Real.self_le_rpow_of_one_le (by linarith) hp
  have hn := eLpNorm_le_of_lintegral_rpow_le (gibbsMeasure P (n + 1).succPNat)
    (measurable_gap 0) (fun X => (gap_pos X 0).le) (by linarith : 0 < p)
    (by positivity : 0 ≤ B + 1) (hm.trans (ENNReal.ofReal_le_ofReal hpow))
  have ha : Measurable (fun X : Configuration (n + 1).succPNat =>
      (anchorCoords (n + 1) X.val).2) :=
    measurable_snd.comp (measurable_anchorCoords_config (n + 1))
  rw [← map_snd_gibbsMeasure P (n + 1),
    eLpNorm_map_measure (measurable_loopSizeWeight n).aestronglyMeasurable ha.aemeasurable]
  simpa only [Function.comp_def, loopSizeWeight_anchorCoords] using hn

/-- All positive-displacement moments needed in the exterior force bound. The
preceding displacement lies strictly between zero and the size-biased gap. -/
theorem loopPrecedingD_eLpNorm_uniform {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (P : Parameters) (n : ℕ),
      MemLp (loopPrecedingD (N := (n + 1).succPNat)) (ENNReal.ofReal p)
        (loopPrecedingMeasure P _) ∧
      eLpNorm (loopPrecedingD (N := (n + 1).succPNat)) (ENNReal.ofReal p)
        (loopPrecedingMeasure P _) ≤ ENNReal.ofReal C := by
  obtain ⟨A, hA, ha⟩ := loopSizeWeight_eLpNorm_two_uniform
  obtain ⟨B, hB, hb⟩ := loopSizeWeight_eLpNorm_uniform (p := 2 * p) (by linarith)
  refine ⟨A ^ (1 / p) * B, by positivity, fun hPL P n => ?_⟩
  have hweight : eLpNorm (fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
      loopSizeWeight n (loopPrecedingOffsets X)) (ENNReal.ofReal p)
      (loopPrecedingMeasure P _) ≤ ENNReal.ofReal (A ^ (1 / p) * B) := by
    have ht := loopSizeBiased_eLpNorm_le P n (measurable_loopSizeWeight n)
      (by linarith : 0 < p)
    have hmap := eLpNorm_map_measure (μ := loopPrecedingMeasure P (n + 1).succPNat)
      (f := loopPrecedingOffsets (N := (n + 1).succPNat))
      (measurable_loopSizeWeight n).aestronglyMeasurable
      (measurable_loopPrecedingOffsets (n + 1).succPNat).aemeasurable (p := ENNReal.ofReal p)
    erw [map_loopPrecedingOffsets P n] at hmap
    erw [← hmap]
    apply ht.trans
    calc
      _ ≤ ENNReal.ofReal A ^ (1 / p) * ENNReal.ofReal B := by
        gcongr
        · exact ha hPL P n
        · exact hb hPL P n
      _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA.le (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
  have hn : eLpNorm (loopPrecedingD (N := (n + 1).succPNat)) (ENNReal.ofReal p)
      (loopPrecedingMeasure P _) ≤ ENNReal.ofReal (A ^ (1 / p) * B) := by
    apply le_trans (eLpNorm_mono_real (measurable_loopPrecedingD _).aestronglyMeasurable
      (fun X => ?_)) hweight
    rw [Real.norm_eq_abs, abs_of_pos (loopPrecedingD_mem X).1]
    exact (loopPrecedingD_mem_weight n X).2.le
  exact ⟨hn.trans_lt ENNReal.ofReal_lt_top, hn⟩

/-- Block fluctuation moments, transported to the actual preceding carrier, for
every integer starting label. Whole windings of the starting label are included. -/
theorem loopPreceding_blockDeviation_eLpNorm
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 →
      ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (j : ℤ) (k : ℕ),
        1 ≤ k → k ≤ (n + 2) / 2 →
        eLpNorm (fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
          loopAnchoredBlock n j k (loopPrecedingOffsets X) - k) (ENNReal.ofReal p)
          (loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ _) ≤
            ENNReal.ofReal (C * (k : ℝ) ^ (s / 2 + δ)) := by
  obtain ⟨eps0, heps0, ht⟩ := Internal.loopSizeBiased_blockDeviation_of_rigidity
    β s hβ hs hs1 (Internal.rigidityConclusion_of_externals hBE hPL β s hβ hs hs1)
  refine ⟨eps0, heps0, fun δ hδ hδ0 p hp => ?_⟩
  obtain ⟨C, hC, hb⟩ := ht δ hδ hδ0 p hp
  refine ⟨C, hC, fun n j k hk hkN => ?_⟩
  obtain ⟨i, hi, q, rfl⟩ := exists_nat_add_mul (N := (n + 1).succPNat) j
  have hm := (measurable_loopAnchoredBlock n (i : ℤ) k).sub_const (k : ℝ)
  have hmap := eLpNorm_map_measure (μ := loopPrecedingMeasure
    ⟨(β, s), hβ, hs, hs1⟩ (n + 1).succPNat)
    (f := loopPrecedingOffsets (N := (n + 1).succPNat)) hm.aestronglyMeasurable
    (measurable_loopPrecedingOffsets (n + 1).succPNat).aemeasurable (p := ENNReal.ofReal p)
  erw [map_loopPrecedingOffsets ⟨(β, s), hβ, hs, hs1⟩ n] at hmap
  have he : (fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
      loopAnchoredBlock n ((i : ℤ) + ((n + 1).succPNat : ℕ) * q) k (loopPrecedingOffsets X) - k) =
      (fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
        loopAnchoredBlock n (i : ℤ) k (loopPrecedingOffsets X) - k) := by
    funext X
    erw [loopAnchoredBlock_add_period]
  erw [he, ← hmap]
  exact hb hPL n ⟨i, hi⟩ k hk hkN

/-- The displacement moment estimate in the proof of the exterior part of
Lemma 5.8: both signs, including the antipodal label, with
the preceding displacement included and with membership certificates returned. -/
theorem loopPrecedingLift_displacement_eLpNorm
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 →
      ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (j : ℤ),
        1 ≤ j.natAbs → j.natAbs ≤ (n + 2) / 2 →
        let μ := loopPrecedingMeasure (⟨(β, s), hβ, hs, hs1⟩ : Parameters) (n + 1).succPNat
        let F := fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
          loopPrecedingLift X j - (j : ℝ)
        MemLp F (ENNReal.ofReal p) μ ∧
        eLpNorm F (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (C * |(j : ℝ)| ^ (s / 2 + δ)) := by
  obtain ⟨eps0, heps0, ht⟩ := loopPreceding_blockDeviation_eLpNorm
    hBE hPL β s hβ hs hs1
  refine ⟨eps0, heps0, fun δ hδ hδ0 p hp => ?_⟩
  obtain ⟨B, hB, hb⟩ := ht δ hδ hδ0 p hp
  obtain ⟨D, hD, hd⟩ := loopPrecedingD_eLpNorm_uniform hp
  refine ⟨B + D, by positivity, fun n j hj hjN => ?_⟩
  let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
  let μ := loopPrecedingMeasure P (n + 1).succPNat
  let F := fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
    loopPrecedingLift X j - (j : ℝ)
  let A := fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
    loopAnchoredBlock n (pairBase 0 j) j.natAbs (loopPrecedingOffsets X) - (j.natAbs : ℝ)
  have hF : Measurable F := (measurable_loopPrecedingLift _ _).sub_const _
  have hAm : Measurable A :=
    ((measurable_loopAnchoredBlock n _ _).comp (measurable_loopPrecedingOffsets _)).sub_const _
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hn : eLpNorm F (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal ((B + D) * |(j : ℝ)| ^ (s / 2 + δ)) := by
    calc
      _ ≤ eLpNorm (fun X => |A X| + loopPrecedingD X) (ENNReal.ofReal p) μ := by
        apply eLpNorm_mono_real hF.aestronglyMeasurable
        intro X
        exact loopPrecedingLift_displacement_le n X j
      _ ≤ eLpNorm (fun X => |A X|) (ENNReal.ofReal p) μ +
          eLpNorm (loopPrecedingD (N := (n + 1).succPNat)) (ENNReal.ofReal p) μ :=
        eLpNorm_add_le hpE
      _ ≤ ENNReal.ofReal (B * (j.natAbs : ℝ) ^ (s / 2 + δ)) + ENNReal.ofReal D := by
        rw [show (fun X => |A X|) = (fun X => ‖A X‖) by rfl, eLpNorm_norm A hAm.aestronglyMeasurable]
        exact add_le_add (hb n (pairBase 0 j) j.natAbs hj hjN) (hd hPL P n).2
      _ ≤ ENNReal.ofReal ((B + D) * |(j : ℝ)| ^ (s / 2 + δ)) := by
        rw [← ENNReal.ofReal_add (by positivity) hD.le, natAbs_cast_eq_abs]
        apply ENNReal.ofReal_le_ofReal
        have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
          rw [← natAbs_cast_eq_abs]
          exact_mod_cast hj
        have hpow : 1 ≤ |(j : ℝ)| ^ (s / 2 + δ) :=
          Real.one_le_rpow hj1 (by linarith)
        nlinarith
  exact ⟨hn.trans_lt ENNReal.ofReal_lt_top, hn⟩

/-- The probability assertion of the exterior part of Lemma 5.8, with
rigidity supplied by the Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler
inequality `External.PrekopaLeindler`. -/
theorem loopExteriorGood_probability
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 →
      ∃ c C K0 : ℝ, 0 < c ∧ 0 < C ∧ 1 ≤ K0 ∧
        ∀ (N : ℕ+) (ℓ γ : ℝ),
          2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → K0 ≤ (N : ℝ) * ℓ → 1 < γ →
          GradPartial N ℓ γ →
          loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N (loopExteriorGood N ℓ γ)ᶜ ≤
            ENNReal.ofReal (C * Real.exp (-c * gradM N ℓ γ ^ (δ / (4 * (s + 2))))) := by
  obtain ⟨eps0, heps0, ht⟩ := Internal.loopExteriorGood_probability_of_rigidity
    β s hβ hs hs1 (Internal.rigidityConclusion_of_externals hBE hPL β s hβ hs hs1)
  refine ⟨eps0, heps0, fun δ hδ hδ0 => ?_⟩
  obtain ⟨c, C, K0, hc, hC, hK0, hb⟩ := ht δ hδ hδ0
  exact ⟨c, C, K0, hc, hC, hK0, hb hPL⟩

end Riesz1

end
