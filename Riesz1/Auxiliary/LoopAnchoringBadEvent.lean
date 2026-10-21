/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopAnchoringVariance
public import Riesz1.Auxiliary.LoopLocalMomentsIntegral
public import Riesz1.ToMathlib.RestrictedL2L4

/-!
# The rare cutoff event in the anchoring bound

The fourth moments and every inverse-power cutoff probability in the anchoring part of
Lemma 5.8, on the actual preceding-particle carrier.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1

/-- The bad-cutoff probability on the preceding-particle probability space. -/
theorem loopAnchoring_bad_probability (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (γ ε B : ℝ) (hγ : 1 < γ) (hε : 0 < ε)
    (hεs : ε < min (1 / 8) ((1 - s / 2) / 8)) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ℓ : ℝ),
      0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n + 1).succPNat : ℝ) * ℓ →
      loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ (n + 1).succPNat
        {X | loopCutoff s γ ε (n + 1).succPNat ℓ (loopPrecedingY X) ≠ 1} ≤
          ENNReal.ofReal (C * (((n + 1).succPNat : ℝ) * ℓ) ^ (-B)) := by
  obtain ⟨C, hC, hb⟩ := Internal.loopSizeBiased_cutoff_probability_of_rigidity β s hβ hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL β s hβ hs hs1) hPL γ ε hγ hε hεs hB
  refine ⟨C, hC, fun n ℓ hℓ hℓ1 hK => ?_⟩
  let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
  let S := {y | loopCutoff s γ ε (n + 1).succPNat ℓ (anchorVector y) ≠ 1}
  have hS : MeasurableSet S := (measurableSet_eq_fun
    ((measurable_loopCutoff s γ ε _ ℓ).comp (measurable_anchorVector _)) measurable_const).compl
  have hmap := Measure.map_apply (μ := loopPrecedingMeasure P (n + 1).succPNat)
    (measurable_loopPrecedingOffsets (n + 1).succPNat) hS
  rw [map_loopPrecedingOffsets P n] at hmap
  have he : (loopPrecedingOffsets (N := (n + 1).succPNat)) ⁻¹' S =
      {X | loopCutoff s γ ε (n + 1).succPNat ℓ (loopPrecedingY X) ≠ 1} := by
    ext X
    change loopCutoff s γ ε (n + 1).succPNat ℓ (anchorVector (loopPrecedingOffsets X)) ≠ 1 ↔
      loopCutoff s γ ε (n + 1).succPNat ℓ (loopPrecedingY X) ≠ 1
    rw [loopPrecedingY_eq_anchorVector n X]
    rfl
  rw [he] at hmap
  rw [← hmap]
  exact hb n ℓ hℓ hℓ1 (by simpa only [Nat.succPNat_coe] using hK)

/-- The cutoff loop on the preceding-particle carrier is strongly measurable
almost everywhere, as a pullback from the size-biased law. -/
theorem loopAnchoring_F_preceding_aestronglyMeasurable {s γ ε ℓ : ℝ} {χ ψ : ℝ → ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hℓ : 0 < ℓ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hp : Function.Periodic ψ ℓ⁻¹) (P : Parameters) (n : ℕ) :
    AEStronglyMeasurable (fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
      loopCutoffF χ s γ ε (n + 1).succPNat ℓ ψ (loopPrecedingY X))
        (loopPrecedingMeasure P (n + 1).succPNat) := by
  have hm := (loopAnchoring_F_aestronglyMeasurable (γ := γ) (ε := ε)
    hs hs1 hℓ hχ hψ hχs hp P (n + 1)).mono_ac
      (show loopSizeBiasedLaw P n ≪ anchoredLaw P (n + 1) from withDensity_absolutelyContinuous _ _)
  rw [← map_loopPrecedingOffsets P n] at hm
  have hh : AEStronglyMeasurable (fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
      loopCutoffF χ s γ ε (n + 1).succPNat ℓ ψ (anchorVector (loopPrecedingOffsets X)))
        (loopPrecedingMeasure P (n + 1).succPNat) :=
    hm.comp_aemeasurable (measurable_loopPrecedingOffsets (n + 1).succPNat).aemeasurable
  exact hh.congr (ae_of_all _ fun X => congrArg
    (loopCutoffF χ s γ ε (n + 1).succPNat ℓ ψ) (loopPrecedingY_eq_anchorVector n X).symm)

/-- A polynomial fourth moment for the complete anchoring error, before
restricting to the rare event. -/
theorem loopAnchoring_error_four (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    {α γ ε : ℝ} (hα : s - 1 ≤ α) (hα2 : α < s / 2) (hγ : 1 < γ)
    (hε : 0 < ε) (hεs : ε ≤ 1 - s / 2)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
      0 < ℓ → 1 ≤ ((n + 1).succPNat : ℝ) * ℓ → 0 ≤ C₀ →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α)
        (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α)
        (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
      let μ := loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ (n + 1).succPNat
      let E := fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
        loopLocalLoop s (n + 1).succPNat ℓ γ (loopLocalTransport χ (n + 1).succPNat ℓ γ ψ) X -
          loopCutoffF χ s γ ε (n + 1).succPNat ℓ ψ (loopPrecedingY X)
      MemLp E 4 μ ∧ eLpNorm E 4 μ ≤
        ENNReal.ofReal (C * C₀ * (((n + 1).succPNat : ℝ) * ℓ) ^
          ((1 - s + α) + 2 * γ + ε * (s + 1))) := by
  obtain ⟨A, hA, ha⟩ := auxiliary_Loop_local_moments β s hβ hs hs1 hα hα2
    (p := 4) (by norm_num) hχ hχc hχs hχ1 hχ01
  obtain ⟨B, hB, hb⟩ := loopCutoffF_explicit_bound hs hs1 hα hα2 hγ hε hεs
    hχ hχc hχs hχ1 hχ01
  refine ⟨A + B, by linarith, fun n ℓ C₀ ψ hℓ hK hC₀ hψ hp hd hdd => ?_⟩
  let N := (n + 1).succPNat
  let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
  let μ := loopPrecedingMeasure P N
  let F := fun X : LoopPrecedingConfiguration N => loopCutoffF χ s γ ε N ℓ ψ (loopPrecedingY X)
  let L := loopLocalLoop s N ℓ γ (loopLocalTransport χ N ℓ γ ψ)
  let K : ℝ := (N : ℝ) * ℓ
  let b := (1 - s + α) + 2 * γ + ε * (s + 1)
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hFm : AEStronglyMeasurable F μ :=
    loopAnchoring_F_preceding_aestronglyMeasurable hs hs1 hℓ hχ hψ hχs hp P n
  have hFb : ∀ X, ‖F X‖ ≤ B * C₀ * K ^ b := by
    intro X
    exact hb C₀ N ℓ ψ (loopPrecedingY X) hC₀ (by simp [N]) hℓ hK hψ hp hd hdd
      (by
        rw [loopPrecedingY_eq_anchorVector n X]
        exact loopAnchoring_anchorVector_mem (loopPrecedingOffsets_mem X)) (loopPrecedingY_zero X)
  have hF : MemLp F 4 μ := MemLp.of_bound hFm _ (ae_of_all _ hFb)
  have hFn : eLpNorm F 4 μ ≤ ENNReal.ofReal (B * C₀ * K ^ b) := by
    simpa only [measure_univ, ENNReal.one_rpow, one_mul] using
      eLpNorm_le_of_ae_bound (μ := μ) hFm (ae_of_all _ hFb) (p := (4 : ℝ≥0∞))
  obtain ⟨hL, _, hLn⟩ := ha hPL N ℓ γ ψ C₀ (by simp [N]) hℓ hK hγ hC₀ hψ hp hd hdd
  norm_num only [ENNReal.ofReal_ofNat] at hL hLn
  have hLn' : eLpNorm L 4 μ ≤ ENNReal.ofReal (A * C₀ * K ^ b) := by
    apply (le_trans le_self_add hLn).trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
    dsimp [b]
    have : 0 ≤ ε * (s + 1) := mul_nonneg hε.le (by linarith)
    linarith
  refine ⟨hL.sub hF, ?_⟩
  calc
    _ ≤ eLpNorm L 4 μ + eLpNorm F 4 μ := eLpNorm_sub_le (by norm_num)
    _ ≤ ENNReal.ofReal (A * C₀ * K ^ b) + ENNReal.ofReal (B * C₀ * K ^ b) := add_le_add hLn' hFn
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- The entire anchoring error has second norm `O(C₀ K⁻¹⁰)` on the bad
cutoff event. The displacement path estimate is not used in this step. -/
theorem loopAnchoring_bad_error (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    {α γ ε : ℝ} (hα : s - 1 ≤ α) (hα2 : α < s / 2) (hγ : 1 < γ)
    (hε : 0 < ε) (hεs : ε < min (1 / 8) ((1 - s / 2) / 8))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
      0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n + 1).succPNat : ℝ) * ℓ → 0 ≤ C₀ →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α)
        (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α)
        (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
      let μ := loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ (n + 1).succPNat
      let S := {X | loopCutoff s γ ε (n + 1).succPNat ℓ (loopPrecedingY X) ≠ 1}
      let E := fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
        loopLocalLoop s (n + 1).succPNat ℓ γ (loopLocalTransport χ (n + 1).succPNat ℓ γ ψ) X -
          loopCutoffF χ s γ ε (n + 1).succPNat ℓ ψ (loopPrecedingY X)
      eLpNorm E 2 (μ.restrict S) ≤
        ENNReal.ofReal (C * C₀ * (((n + 1).succPNat : ℝ) * ℓ) ^ (-10 : ℝ)) := by
  have hεs' : ε ≤ 1 - s / 2 := by
    have := hεs.trans_le (min_le_right _ _)
    linarith
  let d := (1 - s + α) + 2 * γ + ε * (s + 1)
  let B := 4 * (d + 10)
  have hB : 0 < B := by
    have : 0 < ε * (s + 1) := mul_pos hε (by linarith)
    dsimp [B, d]
    linarith
  obtain ⟨A, hA, hmom⟩ := loopAnchoring_error_four hPL β s hβ hs hs1 hα hα2 hγ
    hε hεs' hχ hχc hχs hχ1 hχ01
  obtain ⟨Q, hQ, hprob⟩ := loopAnchoring_bad_probability hBE hPL β s hβ hs hs1
    γ ε B hγ hε hεs hB
  refine ⟨A * Q ^ (1 / 4 : ℝ), by positivity, ?_⟩
  intro n ℓ C₀ ψ hℓ hℓ1 hK hC₀ hψ hp hd hdd
  let μ := loopPrecedingMeasure (⟨(β, s), hβ, hs, hs1⟩ : Parameters) (n + 1).succPNat
  let S := {X | loopCutoff s γ ε (n + 1).succPNat ℓ (loopPrecedingY X) ≠ 1}
  let E := fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
    loopLocalLoop s (n + 1).succPNat ℓ γ (loopLocalTransport χ (n + 1).succPNat ℓ γ ψ) X -
      loopCutoffF χ s γ ε (n + 1).succPNat ℓ ψ (loopPrecedingY X)
  let K := ((n + 1).succPNat : ℝ) * ℓ
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  obtain ⟨hE, hEn⟩ := hmom n ℓ C₀ ψ hℓ hK hC₀ hψ hp hd hdd
  calc
    _ ≤ eLpNorm E 4 μ * μ S ^ (1 / 4 : ℝ) :=
      eLpNorm_two_restrict_le_four hE.aestronglyMeasurable S
    _ ≤ ENNReal.ofReal (A * C₀ * K ^ d) *
        ENNReal.ofReal (Q * K ^ (-B)) ^ (1 / 4 : ℝ) := by
      apply mul_le_mul' hEn
      exact ENNReal.rpow_le_rpow (hprob n ℓ hℓ hℓ1 hK) (by norm_num)
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        ← ENNReal.ofReal_mul (by positivity),
        Real.mul_rpow hQ.le (Real.rpow_nonneg hK0.le _), ← Real.rpow_mul hK0.le]
      have he : d + -B * (1 / 4) = (-10 : ℝ) := by dsimp [B]; ring
      have hpow : K ^ d * K ^ (-B * (1 / 4)) = K ^ (-10 : ℝ) := by
        rw [← Real.rpow_add hK0, he]
      congr 1
      calc
        _ = A * Q ^ (1 / 4 : ℝ) * C₀ * (K ^ d * K ^ (-B * (1 / 4))) := by ring
        _ = _ := by rw [hpow]

end Riesz1

end
