/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopCutoffEnvelope

/-!
# Smoothness and periodicity of the localized transport

The cutoff data part of Lemma 5.8. In a partial window the cutoff vanishes in
a neighborhood of the antipodal seam. Thus its representative formula is smooth globally.
-/

public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Riesz1

theorem loopTransport_periodic {N : ℕ+} {ℓ γ : ℝ} (hℓ : 0 < ℓ) (χ : ℝ → ℝ)
    {ψ : ℝ → ℝ} (hp : Function.Periodic ψ ℓ⁻¹) :
    Function.Periodic (loopTransport χ N ℓ γ ψ) ℓ⁻¹ := by
  intro u
  by_cases h : GradPartial N ℓ γ
  · simp only [loopTransport, h, ↓reduceIte]
    rw [← one_div ℓ, loopCircleRep_add_period hℓ]
  · simp only [loopTransport, h, ↓reduceIte]
    exact hp u

/-- The localized profile is smooth on the whole real line and hence on its circle.
The conclusion holds for all real `γ` and every positive scale. -/
theorem contDiff_loopTransport {χ ψ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hψ : ContDiff ℝ ∞ ψ) (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (N : ℕ+) {ℓ : ℝ} (hℓ : 0 < ℓ) (γ : ℝ) :
    ContDiff ℝ ∞ (loopTransport χ N ℓ γ ψ) := by
  by_cases hP : GradPartial N ℓ γ
  swap
  · have he : loopTransport χ N ℓ γ ψ = ψ := by
      funext u
      simp only [loopTransport, hP, ↓reduceIte]
    rw [he]
    exact hψ
  let L := ℓ⁻¹
  let τ := gradT N ℓ γ
  let R := τ / ℓ
  let c := ψ (1 / (2 * ℓ))
  have hL : 0 < L := inv_pos.mpr hℓ
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hK : 0 < (N : ℝ) * ℓ := mul_pos hN hℓ
  have hτ : τ = gradM N ℓ γ / N := by simp only [τ, gradT, hP, ↓reduceIte]
  have hτ0 : 0 < τ := by
    rw [hτ]
    exact div_pos (Real.rpow_pos_of_pos hK _) hN
  have hτ1 : τ < 1 / 8 := by
    rw [hτ, div_lt_iff₀ hN]
    have h := hP
    change gradM N ℓ γ < (N : ℝ) / 8 at h
    linarith
  have hR : 0 < R := div_pos hτ0 hℓ
  have hRL : R < L := by
    change τ / ℓ < ℓ⁻¹
    rw [inv_eq_one_div, div_lt_div_iff_of_pos_right hℓ]
    linarith
  have hhalf : 1 / (2 * ℓ) = L / 2 := by dsimp [L]; field_simp
  have hrep (v : ℝ) : loopCircleRep ℓ (v + L) = loopCircleRep ℓ v := by
    simpa only [L, one_div] using loopCircleRep_add_period hℓ v
  have hLT (u : ℝ) : loopTransport χ N ℓ γ ψ u =
      loopProfile χ ψ R c (loopCircleRep ℓ u) := by
    simp only [loopTransport, hP, ↓reduceIte, loopProfile, c]
    congr 2
    dsimp [R, τ]
    rw [div_div_eq_mul_div, mul_comm ℓ]
  have hp : Function.Periodic (loopTransport χ N ℓ γ ψ) L := by
    intro v
    rw [hLT, hLT, hrep]
  have hprofile : ContDiff ℝ ∞ (loopProfile χ ψ R c) :=
    (hχ.comp (contDiff_id.div_const R)).mul (hψ.sub contDiff_const)
  have hlocal (u : ℝ) (hu : |u| < L / 2) :
      ContDiffAt ℝ ∞ (loopTransport χ N ℓ γ ψ) u := by
    apply hprofile.contDiffAt.congr_of_eventuallyEq
    have hu' := abs_lt.mp hu
    filter_upwards [Ioo_mem_nhds hu'.1 hu'.2] with v hv
    rw [hLT, loopCircleRep_eq_self hℓ (by rw [hhalf]; linarith [hv.1])
      (by rw [hhalf]; linarith [hv.2])]
  have hzero (v : ℝ) (hv1 : -(3 * L / 4) < v) (hv2 : v < -(L / 4)) :
      loopTransport χ N ℓ γ ψ v = 0 := by
    rw [hLT]
    apply loopTransport_zero_of_far hχs hR
    have hbig : L / 4 < |loopCircleRep ℓ v| := by
      rcases le_or_gt (-(L / 2)) v with hv | hv
      · rw [loopCircleRep_eq_self hℓ (by rw [hhalf]; linarith)
          (by rw [hhalf]; linarith), abs_of_neg (by linarith)]
        linarith
      · have he : loopCircleRep ℓ v = v + L := by
          rw [← hrep v]
          exact loopCircleRep_eq_self hℓ (by rw [hhalf]; linarith) (by rw [hhalf]; linarith)
        rw [he, abs_of_pos (by linarith)]
        linarith
    linarith
  have hseam : ContDiffAt ℝ ∞ (loopTransport χ N ℓ γ ψ) (-(L / 2)) := by
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (by linarith : -(3 * L / 4) < -(L / 2))
      (by linarith : -(L / 2) < -(L / 4))] with v hv
    exact hzero v hv.1 hv.2
  rw [contDiff_iff_contDiffAt]
  intro t
  let m : ℤ := -⌊ℓ * t + 1 / 2⌋
  have hrt : loopCircleRep ℓ t = t + (m : ℝ) * L := by
    dsimp [loopCircleRep, m, L]
    push_cast
    ring
  have hr := loopCircleRep_mem_Ico hℓ t
  rw [hhalf] at hr
  have hc : ContDiffAt ℝ ∞ (loopTransport χ N ℓ γ ψ) (loopCircleRep ℓ t) := by
    rcases eq_or_lt_of_le hr.1 with he | he
    · rw [← he]
      exact hseam
    · exact hlocal _ (abs_lt.mpr ⟨he, hr.2⟩)
  rw [hrt] at hc
  have hh := hc.comp t (contDiffAt_id.add contDiffAt_const)
  have heq : (fun u => loopTransport χ N ℓ γ ψ (u + (m : ℝ) * L)) =
      loopTransport χ N ℓ γ ψ := funext fun u => hp.int_mul m u
  simpa only [Function.comp_def, id_eq, heq] using hh

end Riesz1

end
