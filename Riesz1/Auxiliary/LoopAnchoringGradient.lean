/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopAnchoringDifferential

/-!
# Translation derivative bound outside the fundamental chart

The derivative bound needed in the anchoring part of Lemma 5.8.
The quadrature, displacement and packing estimates hold for arbitrary
real vectors. Assemble them with the collision-free differential identity.
-/

@[expose] public section

open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The common-translation derivative bound for a collision-free real vector,
including a negative anchor. Constants have the dependence stated in the paper. -/
theorem loopAnchoring_translation_gradient {s α γ : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hα0 : s - 1 ≤ α) (hα1 : α < s / 2)
    (hγ : max 4 (2 / s) ≤ γ) :
    ∃ εstar : ℝ, 0 < εstar ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < εstar →
      ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
        2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → 0 ≤ C₀ →
        ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
        (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
        (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
        (GradPartial N ℓ γ → ∀ y : ℝ,
          (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) →
        ∀ X : Fin (N : ℕ) → ℝ,
          (∀ i ∈ gradLabels N ℓ γ, ∀ j ∈ gradLabels N ℓ γ, i ≠ j →
            ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0) →
          gradEvent s γ ε N ℓ X →
          |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε →
          |∑ k : Fin (N : ℕ), fderiv ℝ (gradLoop s ψ N ℓ γ) X (Pi.single k 1)| ≤
            C * C₀ * (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α + κ * ε) := by
  have hγ4 : 4 ≤ γ := (le_max_left _ _).trans hγ
  have hγs : 2 / s ≤ γ := (le_max_right _ _).trans hγ
  have hγ1 : 1 < γ := by linarith
  obtain ⟨εd, hεd, κd, hκd, hd⟩ := gradEst_displacement hs0 hs1 hα0 hα1 hγ4
  let εstar := min εd (min (γ * (1 - s / 2)) ((1 - s / 2) / 8))
  let κq : ℝ := 2
  let κv := κd + κq
  let κ := κv + 2
  have hκv : 0 < κv := by dsimp [κv, κq]; linarith
  have hκ : 0 < κ := by dsimp [κ]; linarith
  refine ⟨εstar, by
    have hγ0 : 0 < γ := by linarith
    have hs2 : 0 < 1 - s / 2 := by linarith
    dsimp [εstar]
    positivity, κ, hκ, fun ε hε hεs => ?_⟩
  have hεd' : ε < εd := hεs.trans_le (min_le_left _ _)
  have hεrest := hεs.trans_le (min_le_right _ _)
  have hεq' : ε < γ * (1 - s / 2) := hεrest.trans_le (min_le_left _ _)
  have hεp : ε < (1 - s / 2) / 8 := hεrest.trans_le (min_le_right _ _)
  obtain ⟨Cd, hCd, hd'⟩ := hd ε hε hεd'
  obtain ⟨Cq, hCq, hq'⟩ := gradV2_window_bound hs0 hs1 hα0 hα1 hγ4 hγs hε hεq'
  obtain ⟨Cp, hCp, hp'⟩ := gradEst_sum_envelope hs0 hs1 (by linarith : 0 ≤ 1 - s + α)
    (by linarith : 1 - s + α < 1 - s / 2) hγ1 ε hε hεp
  let Cv := Cd + Cq
  let C := Cv * Cp + 1
  have hCv : 0 < Cv := by dsimp [Cv]; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have htC : Cv * Cp ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, fun N ℓ C₀ ψ hN hℓ hℓ1 hK hC₀ hψ hper h1 h2 hsupp X hNonInt hX hanchor => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hK0 : 0 < (N : ℝ) * ℓ := by linarith
  let R (i : ℤ) := ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) +
    (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) /
      (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)
  have hR (i : ℤ) : 0 ≤ R i := by
    have := gradWeightTwo_nonneg_unconditional s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
    have := circDist_nonneg 1 (gradLift N X i)
    dsimp [R]
    positivity
  have hv (i : ℤ) (hi : i ∈ gradLabels N ℓ γ) :
      |gradVlab s ψ N ℓ γ X i| ≤ Cv * C₀ * ((N : ℝ) * ℓ) ^ (κv * ε) * R i := by
    have hdisp := hd' C₀ hC₀ N ℓ X ψ i hN hℓ hℓ1 hK hψ hper h1 h2 hX hanchor hi
    have hquad' := hq' N ℓ C₀ X ψ i hN hℓ hℓ1 hK hC₀ hψ hper h1 h2 hsupp hX hanchor hi
    have hdisp' := hdisp.trans (Internal.gradEst_bound_mono hCd.le (le_refl Cd) hC₀ (hR i) hK
      (mul_le_mul_of_nonneg_right (by dsimp [κv]; linarith : κd ≤ κv) hε.le))
    have hquad'' := hquad'.trans (Internal.gradEst_bound_mono hCq.le (le_refl Cq) hC₀ (hR i) hK
      (mul_le_mul_of_nonneg_right (by dsimp [κv]; linarith : κq ≤ κv) hε.le))
    calc |gradVlab s ψ N ℓ γ X i| = |gradV1lab s ψ N ℓ γ X i +
        (gradVdisc2 s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i)| := by rw [gradV1lab]; ring_nf
      _ ≤ |gradV1lab s ψ N ℓ γ X i| + |gradVdisc2 s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i| := abs_add_le _ _
      _ ≤ Cd * C₀ * ((N : ℝ) * ℓ) ^ (κv * ε) * R i +
          Cq * C₀ * ((N : ℝ) * ℓ) ^ (κv * ε) * R i := add_le_add hdisp' hquad''
      _ = _ := by dsimp [Cv]; ring
  have hsum := loopAnchoring_sum_fderiv hψ hℓ hper hs0 hs1 hsupp hNonInt
  have hp := hp' N ℓ X hN hℓ hℓ1 hK hX
  change ∑ i ∈ gradLabels N ℓ γ, R i ≤ _ at hp
  have hpow : ((N : ℝ) * ℓ) ^ (κv * ε) * ((N : ℝ) * ℓ) ^ (1 - s + α + 2 * ε) =
      ((N : ℝ) * ℓ) ^ (1 - s + α + (κv + 2) * ε) := by
    rw [← Real.rpow_add hK0]
    congr 1
    ring
  rw [hsum]
  calc |∑ i ∈ gradLabels N ℓ γ, gradVlab s ψ N ℓ γ X i|
      ≤ ∑ i ∈ gradLabels N ℓ γ, |gradVlab s ψ N ℓ γ X i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ gradLabels N ℓ γ, Cv * C₀ * ((N : ℝ) * ℓ) ^ (κv * ε) * R i := Finset.sum_le_sum hv
    _ = (Cv * C₀ * ((N : ℝ) * ℓ) ^ (κv * ε)) * ∑ i ∈ gradLabels N ℓ γ, R i := by rw [Finset.mul_sum]
    _ ≤ (Cv * C₀ * ((N : ℝ) * ℓ) ^ (κv * ε)) * (Cp * (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α + 2 * ε)) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (Cv * Cp) * (C₀ * (N : ℝ)) * ((N : ℝ) * ℓ) ^ (1 - s + α + (κv + 2) * ε) * 1 := by
        calc _ = (Cv * Cp) * (C₀ * (N : ℝ)) *
            (((N : ℝ) * ℓ) ^ (κv * ε) * ((N : ℝ) * ℓ) ^ (1 - s + α + 2 * ε)) := by ring
          _ = _ := by rw [hpow]; ring
    _ ≤ C * (C₀ * (N : ℝ)) * ((N : ℝ) * ℓ) ^ (1 - s + α + κ * ε) * 1 :=
        Internal.gradEst_bound_mono (mul_nonneg hCv.le hCp.le) htC (mul_nonneg hC₀ hN0.le)
          zero_le_one hK (by dsimp [κ]; nlinarith)
    _ = _ := by ring

end

end Riesz1
