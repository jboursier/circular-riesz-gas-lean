/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalizationTail
public import Riesz1.Auxiliary.LoopLocalizationGlobalMoments
public import Riesz1.Auxiliary.LoopLocalizationFull
public import Riesz1.ToMathlib.VarianceTwoErrors

/-!
# Polynomial loop errors and bounded scale variance

The crude loop estimate and the first derivative envelope control the variance
directly below a fixed scale threshold. Polynomial localization moments also
control the error on the exceptional event at large scales.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1

private theorem norm_sub_le_three {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (U V W : Ω → ℝ) :
    eLpNorm (U - W) p μ ≤ eLpNorm (U - V) p μ + (eLpNorm V p μ + eLpNorm W p μ) := by
  have he : U - W = (U - V) + (V - W) := by
    funext X
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [he]
  exact (eLpNorm_add_le hp).trans (add_le_add le_rfl (eLpNorm_sub_le hp))

/-- A polynomial bound for the entire localization error, on the original
preceding-particle law. No lower-scale asymptotic assumption is used. -/
theorem loopLocalization_polynomial_error
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    {α γ : ℝ} (hα : s - 1 ≤ α) (hα2 : α < s / 2) (hγ : 2 ≤ γ)
    {p : ℝ} (hp : 1 ≤ p)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ) (ψ : ℝ → ℝ) (C0 : ℝ),
      2 ≤ (N : ℕ) → 0 < ℓ → 1 ≤ (N : ℝ) * ℓ →
      0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤
        C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      let b0 := loopLocalTransport χ N ℓ γ ψ
      let F := fun X : LoopPrecedingConfiguration N =>
        loopArcL s N (loopScaleField ((N : ℝ) * ℓ) ψ) X.val -
        loopLocalLoop s N ℓ γ b0 X - loopLocalBackground s N ℓ γ b0
      let μ := loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N
      MemLp F (ENNReal.ofReal p) μ ∧ eLpNorm F (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C * C0 * ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ)) := by
  obtain ⟨A, hA, htail⟩ := loopLocalization_tail_eLpNorm hBE hPL hβ hs hs1
    hα hα2 (p := p) hp hχ hχc hχs hχ1 hχ01
  obtain ⟨B, hB, hglobal⟩ := loopLocalization_global_moments hBE hPL hβ hs hs1
    hα hα2 (p := p) hp hχ hχc hχs hχ1 hχ01
  obtain ⟨D, hD, hlocal⟩ := auxiliary_Loop_local_moments β s hβ hs hs1
    hα hα2 (p := p) hp hχ hχc hχs hχ1 hχ01
  refine ⟨A + B + D, by positivity, ?_⟩
  intro N ℓ ψ C0 hN hℓ hK hC0 hψ hpψ hd hdd
  let K := (N : ℝ) * ℓ
  let d := (1 - s + α) + 2 * γ
  let μ := loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N
  let b0 := loopLocalTransport χ N ℓ γ ψ
  let U := fun X : LoopPrecedingConfiguration N => loopArcL s N (loopScaleField K ψ) X.val
  let V := fun X : LoopPrecedingConfiguration N => loopArcL s N b0 X.val
  let W := fun X : LoopPrecedingConfiguration N =>
    loopLocalLoop s N ℓ γ b0 X + loopLocalBackground s N ℓ γ b0
  have he : (fun X : LoopPrecedingConfiguration N =>
      loopArcL s N (loopScaleField K ψ) X.val - loopLocalLoop s N ℓ γ b0 X -
      loopLocalBackground s N ℓ γ b0) = U - W := by funext X; dsimp [U, W]; ring
  have hn : eLpNorm (U - W) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ((A + B + D) * C0 * K ^ d) := by
    by_cases hP : GradPartial N ℓ γ
    · have ht := (htail N ℓ γ ψ C0 hℓ hK hγ hP hC0 hψ hpψ hd hdd).2
      have hg := (hglobal N ℓ γ ψ C0 hℓ hK (by linarith) hC0 hψ hpψ hd hdd).2
      have hl := (hlocal hPL N ℓ γ ψ C0 hN hℓ hK (by linarith) hC0 hψ hpψ hd hdd).2.2
      have hc : eLpNorm (fun _ : LoopPrecedingConfiguration N =>
          loopLocalBackground s N ℓ γ b0) (ENNReal.ofReal p) μ = ENNReal.ofReal |loopLocalBackground s N ℓ γ b0| := by
        rw [eLpNorm_const' _ (ENNReal.ofReal_pos.mpr (by linarith : 0 < p)).ne' ENNReal.ofReal_ne_top,
          measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs]
      have hw : eLpNorm W (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (D * C0 * K ^ d) := by
        apply (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hp)).trans
        rw [hc]
        exact hl
      have hpow1 : K ^ (2 - s - γ * (1 - s)) ≤ K ^ d := by
        apply Real.rpow_le_rpow_of_exponent_le hK
        dsimp [d]
        nlinarith
      have hpow2 : K ^ ((1 - s + α) + γ) ≤ K ^ d := by
        apply Real.rpow_le_rpow_of_exponent_le hK
        dsimp [d]
        linarith
      have ht' : eLpNorm (U - V) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (A * C0 * K ^ d) :=
        ht.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow1 (by positivity)))
      have hg' : eLpNorm V (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (B * C0 * K ^ d) :=
        hg.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow2 (by positivity)))
      calc
        _ ≤ eLpNorm (U - V) (ENNReal.ofReal p) μ + (eLpNorm V (ENNReal.ofReal p) μ + eLpNorm W (ENNReal.ofReal p) μ) := norm_sub_le_three μ (ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr hp) U V W
        _ ≤ ENNReal.ofReal (A * C0 * K ^ d) +
            (ENNReal.ofReal (B * C0 * K ^ d) + ENNReal.ofReal (D * C0 * K ^ d)) :=
          add_le_add ht' (add_le_add hg' hw)
        _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
    · have hz : U - W = 0 := by
        ext X
        have h := loopLocalization_full_error_zero (s := s) hP hℓ χ hpψ X
        change U X - W X = 0
        dsimp [U, W]
        dsimp [K, b0]
        linarith
      rw [hz, eLpNorm_zero]
      exact bot_le
  dsimp only
  rw [he]
  exact ⟨hn.trans_lt ENNReal.ofReal_lt_top, hn⟩

/-- Below a fixed scale threshold, the crude loop bound and the first
derivative envelope bound the variance uniformly in the particle number. -/
theorem loopLocalization_bounded_variance
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    {β s α : ℝ} (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (hα : s - 1 ≤ α) (K0 : ℝ) (hK0 : 1 ≤ K0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ C0 : ℝ) (ψ : ℝ → ℝ),
      0 < ℓ → 1 ≤ (N : ℝ) * ℓ → (N : ℝ) * ℓ ≤ K0 →
      0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
      letI := (modelWellDefined P N).2.2
      let F := fun X : Configuration N => loopArcL s N (loopScaleField ((N : ℝ) * ℓ) ψ) X
      ∃ hF : MemLp F 2 (gibbsMeasure P N),
        variance (gibbsMeasure P N) F (hF.integrable one_le_two) ≤
          ENNReal.ofReal (C * C0 ^ 2) := by
  obtain ⟨A, hA, hcrude⟩ := auxiliary_Loop_crude hBE hPL hβ hs hs1
    (p := 2) (by norm_num)
  let B := 6 + (2 : ℝ) ^ (2 - s) * (2 * (1 + 1 / (1 - s)))
  let D := A * B * K0 ^ ((1 - s + α) + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D ^ 2, sq_pos_of_pos hD, ?_⟩
  intro N ℓ C0 ψ hℓ hK hKK0 hC0 hψ hp hd
  let K := (N : ℝ) * ℓ
  let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
  let F := fun X : Configuration N => loopArcL s N (loopScaleField K ψ) X
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hKpos : 0 < K := by dsimp [K]; linarith
  have hscale : (N : ℝ) / K = ℓ⁻¹ := by dsimp [K]; field_simp
  have hcells := Internal.loopLocalization_cell_sum_envelope hs1
    (by linarith : 0 ≤ 1 - s + α) hK hC0 N (b := loopScaleField K ψ)
    (fun z => by rw [loopLocalization_deriv_scaleField hKpos.ne' hψ, hscale]; exact hd _)
  have hnorm : eLpNorm F 2 (gibbsMeasure P N) ≤ ENNReal.ofReal (D * C0) := by
    have hh := hcrude N (loopScaleField K ψ)
      ((loopScaleField_contDiff hψ).of_le (by simp)) (loopLocalization_scaleField_periodic hp)
    norm_num only [ENNReal.ofReal_ofNat] at hh
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ A * (B * C0 * K ^ ((1 - s + α) + 1)) :=
        mul_le_mul_of_nonneg_left hcells hA.le
      _ ≤ A * (B * C0 * K0 ^ ((1 - s + α) + 1)) := by
        gcongr
        linarith
      _ = D * C0 := by dsimp [D]; ring
  have hF : MemLp F 2 (gibbsMeasure P N) := hnorm.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hF, ?_⟩
  calc
    _ ≤ ∫⁻ X, ENNReal.ofReal ((F X - 0) ^ 2) ∂gibbsMeasure P N :=
      variance_le_lintegral_sq_sub _ hF 0
    _ = eLpNorm F 2 (gibbsMeasure P N) ^ 2 := by
      simp only [sub_zero]
      exact lintegral_sq_eq_eLpNorm_two_sq hF.aestronglyMeasurable
    _ ≤ ENNReal.ofReal (D * C0) ^ 2 := pow_le_pow_left' hnorm 2
    _ = ENNReal.ofReal (D ^ 2 * C0 ^ 2) := by
      rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ D * C0), mul_pow]

end Riesz1

end
