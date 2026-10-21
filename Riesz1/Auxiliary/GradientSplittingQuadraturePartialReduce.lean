/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingQuadratureGeometry
public import Riesz1.Auxiliary.GradientSplittingQuadratureFull

/-!
# Exact partial-window decomposition of the reference field

The quadrature part of Lemma 5.7. All geometric and integrability obligations
in `gradV2_eq_split` are derived from the hypotheses of the paper. In particular, the
kernel boundary term is retained. It need not vanish in a partial window.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The partial-window reduction, with all certificates derived from the envelopes and event. -/
theorem gradV2_partial_split {s α γ ε ℓ C0 : ℝ} {N : ℕ+} {ψ : ℝ → ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hα0 : s - 1 ≤ α) (hα1 : α < s / 2)
    (hγ : 0 ≤ γ) (hε : ε ≤ γ * (1 - s / 2)) (hN : 2 ≤ (N : ℕ))
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hK : 1 ≤ (N : ℝ) * ℓ) (hP : GradPartial N ℓ γ)
    (hC0 : 0 ≤ C0) (hψ : ContDiff ℝ ∞ ψ) (hper : Function.Periodic ψ ℓ⁻¹)
    (h1 : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t)
    (h2 : ∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t)
    (hsupp : ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    (X : Fin (N : ℕ) → ℝ) (hX : gradEvent s γ ε N ℓ X)
    (hanchor : |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε)
    {i : ℤ} (hi : i ∈ gradLabels N ℓ γ) :
    gradVdisc2 s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i =
      2 * deriv ψ (gradLift N X i / ℓ) *
        ((N : ℝ) ^ (1 - s) *
            (gradKernelH s (gradT N ℓ γ - gradLift N X i)
              - gradKernelH s (-gradT N ℓ γ - gradLift N X i))
          - (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
              deriv (gradKernelH s) (((j - i : ℤ) : ℝ) / (N : ℝ)))
        + 2 * ((∑ j ∈ (gradLabels N ℓ γ).erase i,
            gradCellR s (N : ℕ) ℓ ψ (gradLift N X i) ((j - i : ℤ) : ℝ))
          - ∫ v in (-gradM N ℓ γ - (N : ℝ) * gradLift N X i)..
              (gradM N ℓ γ - (N : ℝ) * gradLift N X i),
                gradCellR s (N : ℕ) ℓ ψ (gradLift N X i) v) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hM0 : 0 < gradM N ℓ γ := Real.rpow_pos_of_pos (by linarith) _
  have ht : gradT N ℓ γ = gradM N ℓ γ / N := by simp [gradT, hP]
  have ht0 : 0 < gradT N ℓ γ := by rw [ht]; positivity
  have hx := gradPartial_anchor_lift_bound hs0 hγ hε hK hP hX hanchor hi
  have hxabs : |gradLift N X i| ≤ 3 * gradT N ℓ γ := by
    rw [abs_mul, abs_of_pos hNpos] at hx
    rw [ht, ← mul_div_assoc, le_div_iff₀ hNpos]
    nlinarith
  have ht1 : gradT N ℓ γ < 1 / 8 := by
    rw [ht, div_lt_iff₀ hNpos]
    linarith [hP]
  have ha1 : |-gradT N ℓ γ - gradLift N X i| < 1 := by
    have := abs_sub (-gradT N ℓ γ) (gradLift N X i)
    rw [abs_neg, abs_of_pos ht0] at this
    linarith
  have hb1 : |gradT N ℓ γ - gradLift N X i| < 1 := by
    have := abs_sub (gradT N ℓ γ) (gradLift N X i)
    rw [abs_of_pos ht0] at this
    linarith
  have he0 : (N : ℝ) * (-gradT N ℓ γ - gradLift N X i) =
      -gradM N ℓ γ - (N : ℝ) * gradLift N X i := by rw [ht]; field_simp
  have he1 : (N : ℝ) * (gradT N ℓ γ - gradLift N X i) =
      gradM N ℓ γ - (N : ℝ) * gradLift N X i := by rw [ht]; field_simp
  have hhalf := intervalIntegrable_gradCellR_half hs0 hs1 hα0 hα1 hN hℓ hℓ1 hK hC0
    hψ hper h1 h2 (x := gradLift N X i)
  have hR : IntervalIntegrable (gradCellR s (N : ℕ) ℓ ψ (gradLift N X i)) volume
      ((N : ℝ) * (-gradT N ℓ γ - gradLift N X i))
      ((N : ℝ) * (gradT N ℓ γ - gradLift N X i)) := by
    rw [he0, he1]
    have hab : -gradM N ℓ γ - (N : ℝ) * gradLift N X i ≤
        gradM N ℓ γ - (N : ℝ) * gradLift N X i := by linarith
    have hr0 := gradPartial_background_range hP hx (left_mem_Icc.mpr hab)
    have hr1 := gradPartial_background_range hP hx (right_mem_Icc.mpr hab)
    refine intervalIntegrable_of_le_of_le (by linarith) hhalf ?_ hab ?_
    · linarith [(abs_le.mp hr0.2.le).1]
    · linarith [(abs_le.mp hr1.2.le).2]
  have hq0 : -gradT N ℓ γ - gradLift N X i = 0 → deriv ψ (gradLift N X i / ℓ) = 0 := by
    intro hz
    exact gradPartial_endpoint_deriv_zero hψ hℓ.ne' hP hM0 hsupp (Or.inl (by linarith))
  have hq1 : gradT N ℓ γ - gradLift N X i = 0 → deriv ψ (gradLift N X i / ℓ) = 0 := by
    intro hz
    exact gradPartial_endpoint_deriv_zero hψ hℓ.ne' hP hM0 hsupp (Or.inr (by linarith))
  have hpaths : ∀ j ∈ (gradLabels N ℓ γ).erase i,
      2 * |gradPathIncr N ℓ γ i j| ≤ (N : ℤ) ∧ gradPathIncr N ℓ γ i j ≠ 0 := by
    intro j hj
    obtain ⟨hne, hjl⟩ := Finset.mem_erase.mp hj
    exact ⟨two_abs_gradPathIncr_le hi hjl, gradPathIncr_ne_zero hi hjl hne⟩
  have hsplit := gradV2_eq_split hψ hℓ (by simpa [one_div] using hper) hs0 hs1
    (fun _ => hsupp) X i (-gradT N ℓ γ - gradLift N X i)
    (gradT N ℓ γ - gradLift N X i)
    (by simp [gradBLo, hP]) (by simp [gradBHi, hP]) (by linarith)
    ha1 hb1 hq0 hq1 hR hpaths
  simpa only [he0, he1, gradPathIncr, hP, ↓reduceIte] using hsplit

end

end Riesz1
