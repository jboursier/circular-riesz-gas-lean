/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlUniformEnvelope
public import Riesz1.Variance.VarAlPiecesCompleteMacro
public import Riesz1.Variance.VarAlPiecesCompleteCompact
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Summing the translated single-singularity loop estimates

The finite-sum step of Proposition 5.9. The coefficient is chosen
before the particle count, observation scale, pieces, and translations.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- Remove the auxiliary localization cutoff from the single-envelope API. -/
theorem varAlFinal_envelope
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) {α A ε : ℝ} (hα : P.val.2 - 1 ≤ α) (hα2 : α < P.val.2 / 2)
    (hA : 0 < A) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ) (ψ : ℝ → ℝ),
      0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ x, |deriv ψ x| ≤ A * gradWeightOne P.val.2 (1 - P.val.2 + α)
        ((N : ℝ) * ℓ) ℓ⁻¹ x) →
      (∀ x, |deriv (deriv ψ) x| ≤ A * gradWeightTwo P.val.2 (1 - P.val.2 + α)
        ((N : ℝ) * ℓ) ℓ⁻¹ x) →
      ∃ hi : Integrable (fun X : Configuration N =>
          loopFunctional P.val.2 (N : ℕ) (loopScaleField ℓ ψ) X.val) (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ hi ≤
          ENNReal.ofReal (C * ((N : ℝ) * ℓ) ^ (ε + max 1 (2 * (1 - P.val.2 + α)))) := by
  let χ : ContDiffBump (0 : ℝ) := ⟨1 / 8, 3 / 16, by norm_num, by norm_num⟩
  let γ := max (max 4 (2 / P.val.2)) (loopLocalizationExponent P.val.2)
  have hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4) := by
    rw [χ.tsupport_eq]
    intro x hx
    have hx' : |x| ≤ 3 / 16 := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, χ] using hx
    exact ⟨by linarith [neg_le_abs x], by linarith [le_abs_self x]⟩
  obtain ⟨C, hC, hall⟩ := varAl_loop_variance_envelope hBE hPL P hα hα2
    (le_max_left _ _) (le_max_right _ _) hA hε χ.contDiff χ.hasCompactSupport hχs
    (fun x hx => χ.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, χ] using hx))
    (fun _ => ⟨χ.nonneg, χ.le_one⟩)
  exact ⟨C, hC, fun N ℓ ψ hℓ hℓ1 hK hψ hp h1 h2 => by
    have := (modelWellDefined P N).2.2
    obtain ⟨hF, hv⟩ := hall N ℓ ψ hℓ hℓ1 hK hψ hp h1 h2
    exact ⟨hF.integrable one_le_two, hv⟩⟩

/-- The finite-piece reduction of Proposition 5.9, including zero pieces.
The decomposition premises are internal analytic inputs. -/
theorem varAlFinal_finite_pieces
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (m : ℕ) {α A ε : ℝ}
    (hα : P.val.2 - 1 ≤ α) (hα2 : α < P.val.2 / 2)
    (hA : 0 < A) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ) (ψ : ℝ → ℝ)
      (φ : Fin m → ℝ → ℝ), 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) ℓ⁻¹) →
      (∀ x, ψ x = ∑ j, φ j x) →
      (∀ j, ∃ a : ℝ,
        (∀ x, |deriv (fun t => φ j (t + a)) x| ≤ A *
          gradWeightOne P.val.2 (1 - P.val.2 + α) ((N : ℝ) * ℓ) ℓ⁻¹ x) ∧
        (∀ x, |deriv (deriv (fun t => φ j (t + a))) x| ≤ A *
          gradWeightTwo P.val.2 (1 - P.val.2 + α) ((N : ℝ) * ℓ) ℓ⁻¹ x)) →
      ∃ hi : Integrable (fun X : Configuration N =>
          loopFunctional P.val.2 (N : ℕ) (loopScaleField ℓ ψ) X.val) (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ hi ≤
          ENNReal.ofReal (C * ((N : ℝ) * ℓ) ^ (ε + max 1 (2 * (1 - P.val.2 + α)))) := by
  classical
  obtain ⟨B, hB, hsingle⟩ := varAlFinal_envelope hBE hPL P hα hα2 hA hε
  refine ⟨(m : ℝ) ^ 2 * B + 1, by positivity, ?_⟩
  intro N ℓ ψ φ hℓ hℓ1 hK hφ hsum henv
  have hper := fun j => (hφ j).2
  have hlip := fun j => lipschitz_of_periodic_contDiff (inv_pos.mpr hℓ) (hφ j).1 (hper j)
  obtain ⟨⟨hi, hj, hsumV⟩, hshift⟩ := varAl_pieces_loop_variance P hPL N P.2.2.1
    P.2.2.2 hℓ hℓ1 m ψ φ hsum hper hlip
  let D := ((N : ℝ) * ℓ) ^ (ε + max 1 (2 * (1 - P.val.2 + α)))
  have hD : 0 ≤ D := Real.rpow_nonneg (by linarith) _
  have hpiece (j : Fin m) : variance (gibbsMeasure P N) _ (hj j) ≤ ENNReal.ofReal (B * D) := by
    obtain ⟨a, h1, h2⟩ := henv j
    obtain ⟨ha, hb, heq⟩ := hshift j a
    have hs : ContDiff ℝ ∞ (fun t => φ j (t + a)) :=
      (hφ j).1.comp (contDiff_id.add contDiff_const)
    have hp : Function.Periodic (fun t => φ j (t + a)) ℓ⁻¹ := by
      intro t
      dsimp only
      rw [show t + ℓ⁻¹ + a = (t + a) + ℓ⁻¹ by ring, hper j]
    obtain ⟨hc, hv⟩ := hsingle N ℓ _ hℓ hℓ1 hK hs hp h1 h2
    exact heq.symm.le.trans hv
  refine ⟨hi, hsumV.trans ?_⟩
  calc
    _ ≤ (m : ℝ≥0∞) * ∑ _j : Fin m, ENNReal.ofReal (B * D) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hpiece j) zero_le
    _ = ENNReal.ofReal ((m : ℝ) ^ 2 * B * D) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by dsimp [D] at *; nlinarith)

end Riesz1.Internal

end
