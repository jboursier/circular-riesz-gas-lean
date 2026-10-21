/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalMomentsDefs
public import Riesz1.Auxiliary.LoopExteriorCancellation
public import Riesz1.Auxiliary.GradientSplittingConvolutionLattice

/-!
# Support separation for spatial loop localization

The cutoff transport vanishes at all exterior particles on the exterior good
event, and throughout the exterior background. These are deterministic facts
used by the partial-window expansion in Lemma 5.8.
-/

public section

noncomputable section

open Set

namespace Riesz1

/-- In a partial window the localized transport is supported inside the
microscopic circular ball of radius `M/4`. -/
theorem loopLocalTransport_zero_of_circDist {N : ℕ+} {ℓ γ : ℝ}
    (hℓ : 0 < ℓ) (hP : GradPartial N ℓ γ) {χ : ℝ → ℝ}
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4)) (ψ : ℝ → ℝ)
    {z : ℝ} (hz : gradM N ℓ γ / 4 ≤ circDist (N : ℝ) z) :
    loopLocalTransport χ N ℓ γ ψ z = 0 := by
  let K := (N : ℝ) * ℓ
  let M := gradM N ℓ γ
  let q := loopCircleRep ℓ (z / K)
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hK : 0 < K := mul_pos hN hℓ
  have hM : 0 < M := Real.rpow_pos_of_pos hK γ
  have hscale : (N : ℝ) / K = ℓ⁻¹ := by dsimp [K]; field_simp
  have hq : circDist (N : ℝ) z / K ≤ |q| := by
    rw [← circDist_scale hK, hscale]
    have h := circDist_le_abs_sub_int_mul (inv_pos.mpr hℓ) (z / K) ⌊ℓ * (z / K) + 1 / 2⌋
    simpa only [q, loopCircleRep, div_eq_mul_inv] using h
  have harg : ℓ * q / gradT N ℓ γ = K * q / M := by
    simp only [gradT, hP, ↓reduceIte]
    dsimp [K, M]
    field_simp
  have hzero : χ (ℓ * q / gradT N ℓ γ) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hc
    have habs : |ℓ * q / gradT N ℓ γ| < 1 / 4 := abs_lt.mpr (hχs hc)
    rw [harg, abs_div, abs_mul, abs_of_pos hK, abs_of_pos hM,
      div_lt_iff₀ hM] at habs
    have hq' := (div_le_iff₀ hK).mp hq
    dsimp only [M] at habs
    nlinarith
  change K * (if GradPartial N ℓ γ then
    χ (ℓ * q / gradT N ℓ γ) * (ψ q - ψ (1 / (2 * ℓ))) else ψ (z / K)) = 0
  simp only [hP, ↓reduceIte, hzero, zero_mul, mul_zero]

/-- On the good event, every exterior particle is outside the support of the
localized transport, including exterior lifts across the period boundary. -/
theorem loopLocalTransport_zero_exterior {N : ℕ+} {ℓ γ : ℝ}
    (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (hP : GradPartial N ℓ γ) {χ : ℝ → ℝ}
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4)) (ψ : ℝ → ℝ)
    {X : LoopPrecedingConfiguration N} (hX : X ∈ loopExteriorGood N ℓ γ)
    {j : ℤ} (hj : j ∈ loopExteriorLabels N ℓ γ) :
    loopLocalTransport χ N ℓ γ ψ (loopPrecedingLift X j) = 0 := by
  apply loopLocalTransport_zero_of_circDist hℓ hP hχs ψ
  have hM : 0 ≤ gradM N ℓ γ := (Real.one_le_rpow hK hγ).trans' zero_le_one
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hd : gradM N ℓ γ / 2 ≤ latticeDist (N : ℝ) (loopPrecedingLift X j) := by
    apply loopExterior_latticeDist_lower hN
    · rcases loopExteriorLift_barriers hK hγ hP hX hj with hp | hn
      · rw [abs_of_nonneg (by linarith [hp.1])]; exact hp.1
      · rw [abs_of_nonpos (by linarith [hn.2])]; linarith [hn.2]
    · rcases loopExteriorLift_barriers hK hγ hP hX hj with hp | hn
      · rw [abs_of_nonneg (by linarith [hp.1])]; linarith [hp.2]
      · rw [abs_of_nonpos (by linarith [hn.2])]; linarith [hn.1]
  change gradM N ℓ γ / 4 ≤ latticeDist (N : ℝ) (loopPrecedingLift X j)
  linarith

/-- The exterior background is also disjoint from the cutoff support. -/
theorem loopLocalTransport_zero_exteriorBackground {N : ℕ+} {ℓ γ : ℝ}
    (hℓ : 0 < ℓ) (hP : GradPartial N ℓ γ) {χ : ℝ → ℝ}
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4)) (ψ : ℝ → ℝ)
    {u : ℝ} (hu : u ∈ loopExteriorBackground N ℓ γ) :
    loopLocalTransport χ N ℓ γ ψ u = 0 := by
  apply loopLocalTransport_zero_of_circDist hℓ hP hχs ψ
  have hM : 0 < gradM N ℓ γ :=
    Real.rpow_pos_of_pos (mul_pos (by exact_mod_cast N.pos) hℓ) γ
  have hU := hu.1
  have hnot := hu.2
  have hout : gradM N ℓ γ < |u| := by
    by_contra! h
    exact hnot (abs_le.mp h)
  have hin : |u| ≤ (N : ℝ) / 2 := abs_le.mpr ⟨by linarith [hU.1], hU.2⟩
  change gradM N ℓ γ / 4 ≤ latticeDist (N : ℝ) u
  apply loopExterior_latticeDist_lower (by exact_mod_cast N.pos)
  · linarith
  · change gradM N ℓ γ < (N : ℝ) / 8 at hP
    linarith

end Riesz1

end
