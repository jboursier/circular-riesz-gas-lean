/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalizationTailSupport
public import Riesz1.Auxiliary.LoopLocalizationEnvelopeCells
public import Riesz1.Auxiliary.LoopLocalizationAlgebra

/-!
# The global loop tail removed by spatial localization

The first error term of the localization part of Lemma 5.8, with
the entire bounded scale range and the actual periodic cutoff transport.
-/

public section

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal ContDiff

namespace Riesz1

/-- Microscopic scaling cancels in the first derivative, for any nonzero scale. -/
theorem loopLocalization_deriv_scaleField {K : ℝ} (hK : K ≠ 0)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (z : ℝ) :
    deriv (loopScaleField K ψ) z = deriv ψ (z / K) := by
  have hd := ((hψ.differentiable (by simp) (z / K)).hasDerivAt.comp z
    ((hasDerivAt_id z).div_const K)).const_mul K
  have he : K * (deriv ψ (z / K) * (1 / K)) = deriv ψ (z / K) := by field_simp
  rw [he] at hd
  exact hd.deriv

/-- The microscopic uncut transport has period `N`. -/
theorem loopLocalization_scaleField_periodic {N : ℕ+} {ℓ : ℝ}
    {ψ : ℝ → ℝ} (hp : Function.Periodic ψ ℓ⁻¹) :
    Function.Periodic (loopScaleField ((N : ℝ) * ℓ) ψ) (N : ℝ) := by
  intro z
  have he : (z + N) / ((N : ℝ) * ℓ) = z / ((N : ℝ) * ℓ) + ℓ⁻¹ := by field_simp
  simp only [loopScaleField, he]
  rw [hp]

/-- The derivative-tail cell estimate in the first display of the localization
proof. The constant is uniform in `γ ≥ 2` and all `K ≥ 1`. -/
theorem loopLocalization_difference_cell_sum {s α : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hα : s - 1 ≤ α) (hα2 : α < s / 2) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ : ℝ) (ψ : ℝ → ℝ) (C0 : ℝ),
      0 < ℓ → 1 ≤ (N : ℝ) * ℓ → 2 ≤ γ → GradPartial N ℓ γ →
      0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤
        C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      ∑ m ∈ range (N : ℕ), cellSup
        (loopScaleField ((N : ℝ) * ℓ) ψ - loopLocalTransport χ N ℓ γ ψ) m ≤
        C * C0 * ((N : ℝ) * ℓ) ^ (2 - s) * gradM N ℓ γ ^ (s - 1) := by
  obtain ⟨A, hA, henv⟩ := loopTransport_envelope hs hs1 hα hα2 hχ hχc hχs hχ1 hχ01
  obtain ⟨B, hB, htail⟩ := Internal.loopLocalization_cell_sum_tail hs1
    (by linarith : 0 ≤ 1 - s + α)
  refine ⟨B * (1 + A), mul_pos hB (by linarith), ?_⟩
  intro N ℓ γ ψ C0 hℓ hK hγ hP hC0 hψ hp hd hdd
  let K := (N : ℝ) * ℓ
  let b := loopScaleField K ψ
  let b0 := loopLocalTransport χ N ℓ γ ψ
  have hK0 : 0 < K := by dsimp [K]; linarith
  have hscale : (N : ℝ) / K = ℓ⁻¹ := by dsimp [K]; field_simp
  have hb : ContDiff ℝ ∞ b := loopScaleField_contDiff hψ
  have hb0 : ContDiff ℝ ∞ b0 := contDiff_loopLocalTransport hχ hψ hχs N hℓ γ
  have hdiff : ∀ z, |deriv (b - b0) z| ≤
      ((1 + A) * C0) * gradWeightOne s (1 - s + α) K ((N : ℝ) / K) (z / K) := by
    intro z
    rw [deriv_sub ((hb.differentiable (by simp)).differentiableAt)
      ((hb0.differentiable (by simp)).differentiableAt)]
    rw [loopLocalization_deriv_scaleField hK0.ne' hψ,
      deriv_loopLocalTransport hχ hψ hχs N hℓ γ, hscale]
    calc
      _ ≤ |deriv ψ (z / K)| + |deriv (loopTransport χ N ℓ γ ψ) (z / K)| := abs_sub _ _
      _ ≤ C0 * gradWeightOne s (1 - s + α) K ℓ⁻¹ (z / K) +
          A * C0 * gradWeightOne s (1 - s + α) K ℓ⁻¹ (z / K) :=
        add_le_add (hd _) (henv N ℓ γ ψ C0 hℓ hK (by linarith) hC0 hψ hp hd hdd _).1
      _ = _ := by ring
  have hKM : K ^ (2 : ℝ) ≤ gradM N ℓ γ :=
    Real.rpow_le_rpow_of_exponent_le hK hγ
  have ht := htail N K (gradM N ℓ γ) ((1 + A) * C0) (b - b0) hK hKM
    (by positivity) hdiff
    (fun z hz => loopLocalization_difference_deriv_zero hℓ hP hχ1 hp hz)
  convert ht using 1
  ring

/-- The crude loop bound turns the derivative-tail sum into the required
`K^(2-s-γ(1-s))` global-loop error, for every scale `K ≥ 1`. -/
theorem loopLocalization_tail_eLpNorm
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    {β s : ℝ} (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    {α p : ℝ} (hα : s - 1 ≤ α) (hα2 : α < s / 2) (hp : 1 ≤ p)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ : ℝ) (ψ : ℝ → ℝ) (C0 : ℝ),
      0 < ℓ → 1 ≤ (N : ℝ) * ℓ → 2 ≤ γ → GradPartial N ℓ γ →
      0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤
        C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      let F := fun X : LoopPrecedingConfiguration N =>
        loopArcL s N (loopScaleField ((N : ℝ) * ℓ) ψ) X.val -
          loopArcL s N (loopLocalTransport χ N ℓ γ ψ) X.val
      let μ := loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N
      MemLp F (ENNReal.ofReal p) μ ∧ eLpNorm F (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C * C0 * ((N : ℝ) * ℓ) ^ (2 - s - γ * (1 - s))) := by
  obtain ⟨A, hA, hcells⟩ := loopLocalization_difference_cell_sum hs hs1 hα hα2
    hχ hχc hχs hχ1 hχ01
  obtain ⟨B, hB, hcrude⟩ := Internal.loopLocalization_crude_difference hBE hPL hβ hs hs1 hp
  refine ⟨B * A, mul_pos hB hA, ?_⟩
  intro N ℓ γ ψ C0 hℓ hK hγ hP hC0 hψ hpψ hd hdd
  let K := (N : ℝ) * ℓ
  have hK0 : 0 < K := by dsimp [K]; linarith
  have hb : ContDiff ℝ 1 (loopScaleField K ψ) :=
    (loopScaleField_contDiff (ℓ := K) hψ).of_le (by simp)
  have hb0 : ContDiff ℝ 1 (loopLocalTransport χ N ℓ γ ψ) :=
    (contDiff_loopLocalTransport hχ hψ hχs N hℓ γ).of_le (by simp)
  have h := hcrude N _ _ hb hb0 (loopLocalization_scaleField_periodic hpψ)
    (loopLocalTransport_periodic hℓ χ hpψ)
  have hn : eLpNorm (fun X : LoopPrecedingConfiguration N =>
      loopArcL s N (loopScaleField K ψ) X.val -
      loopArcL s N (loopLocalTransport χ N ℓ γ ψ) X.val) (ENNReal.ofReal p)
      (loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N) ≤
      ENNReal.ofReal (B * A * C0 * K ^ (2 - s - γ * (1 - s))) := by
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    have ht := mul_le_mul_of_nonneg_left
      (hcells N ℓ γ ψ C0 hℓ hK hγ hP hC0 hψ hpψ hd hdd) hB.le
    have he : K ^ (2 - s) * gradM N ℓ γ ^ (s - 1) = K ^ (2 - s - γ * (1 - s)) := by
      dsimp [gradM]
      rw [← Real.rpow_mul hK0.le, ← Real.rpow_add hK0]
      congr 1
      ring
    calc
      _ ≤ B * (A * C0 * K ^ (2 - s) * gradM N ℓ γ ^ (s - 1)) := ht
      _ = B * A * C0 * (K ^ (2 - s) * gradM N ℓ γ ^ (s - 1)) := by ring
      _ = _ := by rw [he]
  exact ⟨hn.trans_lt ENNReal.ofReal_lt_top, hn⟩

end Riesz1

end
