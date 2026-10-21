/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlSingularGeometry
public import Riesz1.Auxiliary.GradientSplittingEstimatesComplete

/-!
# Coordinate domination of the singular loop field

Proposition 5.9, the deterministic step before applying
augmented comparison. The cutoff uses the larger window `I_{2γ}`.
-/

@[expose] public section

noncomputable section

open Finset Set
open scoped ContDiff

namespace Riesz1

/-- Spatial cutoff supplies the support premise of gradient splitting. -/
theorem varAlSingular_transport_support {χ : ℝ → ℝ}
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4)) {N : ℕ+} {ℓ γ : ℝ}
    (hℓ : 0 < ℓ) (ψ : ℝ → ℝ) :
    GradPartial N ℓ γ → ∀ y : ℝ,
      (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) →
        loopTransport χ N ℓ γ ψ (y / ℓ) = 0 := by
  intro hp y hy
  have hK0 : 0 < (N : ℝ) * ℓ := mul_pos (by exact_mod_cast N.pos) hℓ
  have ht : 0 < gradT N ℓ γ := by
    rw [gradT, ite_eq_left hp]
    exact div_pos (Real.rpow_pos_of_pos hK0 _) (by exact_mod_cast N.pos)
  unfold loopTransport
  rw [ite_eq_left hp]
  have heq : ℓ * loopCircleRep ℓ (y / ℓ) = y - (⌊y + 1 / 2⌋ : ℤ) := by
    unfold loopCircleRep
    field_simp
  have hfar : 1 / 4 ≤ |ℓ * loopCircleRep ℓ (y / ℓ) / gradT N ℓ γ| := by
    rw [heq, abs_div, abs_of_pos ht, le_div_iff₀ ht]
    linarith [hy ⌊y + 1 / 2⌋]
  have hn : ℓ * loopCircleRep ℓ (y / ℓ) / gradT N ℓ γ ∉ tsupport χ := by
    intro hh
    have := abs_lt.mpr (hχs hh)
    linarith
  rw [image_eq_zero_of_notMem_tsupport hn, zero_mul]

/-- Coordinatewise comparison with the augmented weights. All constants
are chosen before the scale, particle number and transport. The loss
exponent is chosen before epsilon, the amplitude and the spatial cutoff. -/
theorem varAlSingular_field_bound {s α γ : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hα : s - 1 ≤ α) (hα2 : α < s / 2)
    (hγ : max 4 (2 / s) ≤ γ) :
    ∃ εstar κ : ℝ, 0 < εstar ∧ 0 < κ ∧
      ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4) →
        (∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ ε : ℝ, 0 < ε → ε < εstar → ∃ C : ℝ, 0 < C ∧
        ∀ (N : ℕ+) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
          2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → 0 ≤ C₀ →
          ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
          (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
          (∀ t, |deriv (deriv ψ) t| ≤
            C₀ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
          ∀ X ∈ orderedDomain N, X ⟨0, N.pos⟩ = 0 → ∀ k : Fin (N : ℕ),
            loopCutoff s γ ε N ℓ X *
                |gradVfield s (loopTransport χ N ℓ γ ψ) N ℓ γ X k| ≤
              C * C₀ * ((N : ℝ) * ℓ) ^ (κ * ε) * loopCutoff s γ ε N ℓ X *
                ((N : ℝ) * augmentedComparisonWeight N ((N : ℝ) * ℓ) s
                  (1 - s + α) ε k) := by
  classical
  have hγ1 : 1 < γ := by have := (le_max_left _ _).trans hγ; linarith
  obtain ⟨εg, hεg, κg, hκg, hg⟩ := gradient_splitting_estimates hs0 hs1 hα hα2 hγ
  let εstar := min εg ((1 - s / 2) / 8)
  refine ⟨εstar, κg + 3, by dsimp [εstar]; exact lt_min hεg (by linarith), by linarith, ?_⟩
  intro χ hχ hχc hχs hχ1 hχ01 ε hε hεs
  have hεg' : ε < εg := hεs.trans_le (min_le_left _ _)
  have hεsmall : ε < (1 - s / 2) / 8 := hεs.trans_le (min_le_right _ _)
  obtain ⟨Cg, hCg, hgrad⟩ := hg ε hε hεg'
  obtain ⟨Ce, hCe, he⟩ := loopTransport_envelope hs0 hs1 hα hα2 hχ hχc hχs hχ1 hχ01
  refine ⟨8 * Cg * (Ce + 1), by positivity, ?_⟩
  intro N ℓ C₀ ψ hN hℓ hℓ1 hK hC₀ hψ hp h1 h2 X hXD hX0 k
  let K := (N : ℝ) * ℓ
  have hK0 : 0 < K := by dsimp [K]; linarith
  let η := loopCutoff s γ ε N ℓ X
  have hη : 0 ≤ η := (loopCutoff_mem_Icc s γ ε ℓ X).1
  by_cases hηzero : η = 0
  · change η * _ ≤ _ * η * _
    rw [hηzero, zero_mul, mul_zero, zero_mul]
  have hevent := varAl_gradEvent_mono hℓ hK (show γ ≤ 2 * γ by linarith)
    (gradEvent_of_loopCutoff_pos hℓ (⟨X, hXD⟩ : Configuration N) (lt_of_le_of_ne hη (Ne.symm hηzero)))
  have hψγ := contDiff_loopTransport hχ hψ hχs N hℓ γ
  have hpγ := loopTransport_periodic (N := N) (γ := γ) hℓ χ hp
  have hbound := hgrad N ℓ (Ce * C₀) (loopTransport χ N ℓ γ ψ) hN hℓ hℓ1 hK
    (mul_nonneg hCe hC₀) hψγ hpγ
    (fun t => (he N ℓ γ ψ C₀ hℓ hK hγ1 hC₀ hψ hp h1 h2 t).1)
    (fun t => (he N ℓ γ ψ C₀ hℓ hK hγ1 hC₀ hψ hp h1 h2 t).2)
    (varAlSingular_transport_support hχs hℓ ψ)
  by_cases hk : ∃ j ∈ gradLabels N ℓ γ, gradIndex N j = k
  · obtain ⟨j, hj, rfl⟩ := hk
    have hanchor : |(N : ℝ) * gradLift N X 0| ≤ K ^ ε := by
      have hz : gradLift N X 0 = 0 := by simpa [gradLift, gradIndex] using hX0
      rw [hz, mul_zero, abs_zero]
      positivity
    have hV := (hbound.2.2.1 X hXD hevent hanchor).1 j hj
    have hw := varAlSingular_spatial_bound hs0 hs1 (by linarith : 0 ≤ 1 - s + α)
      (by linarith : 1 - s + α ≤ 1) hγ1 hε hεsmall hℓ hK hevent hX0 hj
    rw [gradEst_Vfield_eq_lab _ _ hℓ.le hj]
    have hstep := hV.trans (mul_le_mul_of_nonneg_left hw (by positivity))
    have hmul := mul_le_mul_of_nonneg_left hstep hη
    have hpow : K ^ (κg * ε) * K ^ (3 * ε) = K ^ ((κg + 3) * ε) := by
      rw [← Real.rpow_add hK0]
      congr 1
      ring
    have hnn : 0 ≤ C₀ * K ^ ((κg + 3) * ε) * η *
        ((N : ℝ) * augmentedComparisonWeight N K s (1 - s + α) ε (gradIndex N j)) := by
      apply mul_nonneg
      · positivity
      · exact mul_nonneg (by positivity) (augmentedComparisonWeight_nonneg hK0.le _)
    change η * _ ≤ _
    calc η * |gradVlab s (loopTransport χ N ℓ γ ψ) N ℓ γ X j| ≤
        (8 * Cg * Ce) * (C₀ * K ^ ((κg + 3) * ε) * η *
          ((N : ℝ) * augmentedComparisonWeight N K s (1 - s + α) ε (gradIndex N j))) := by
          convert hmul using 1
          dsimp only [K]
          rw [← hpow]
          ring
      _ ≤ _ := by
        have hc : 8 * Cg * Ce ≤ 8 * Cg * (Ce + 1) := by nlinarith
        convert mul_le_mul_of_nonneg_right hc hnn using 1
        ring
  · have hz := (gradEst_fields_support (s := s) (loopTransport χ N ℓ γ ψ) X k
      (fun j hj heq => hk ⟨j, hj, heq⟩)).1
    rw [hz, abs_zero, mul_zero]
    apply mul_nonneg
    · positivity
    · exact mul_nonneg (by positivity) (augmentedComparisonWeight_nonneg hK0.le _)

end Riesz1

end
