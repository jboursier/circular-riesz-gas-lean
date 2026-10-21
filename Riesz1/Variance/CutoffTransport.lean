/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopCutoffSmooth
public import Riesz1.Auxiliary.LoopCutoffEnvelope

/-!
# The spatial transport of the localized loop: definition tests and derivative bounds

This file treats the spatially cut off transport `ψ_γ` and the fact that derivative bounds
persist after the spatial cutoff.

* The transport `ψ_γ` is `Riesz1.loopTransport`, defined in
  `Riesz1/Auxiliary/LoopCutoffDefs.lean` on the whole circle through the representative
  `loopCircleRep`. The two lemmas `loopTransport_of_not_partial` and `loopTransport_eq_formula`
  check it against the paper: a full window makes no change, and on the fundamental domain
  `|u| < (2ℓ)^{-1}` the transport is given by `χ(ℓu/t_γ)(ψ(u) - ψ((2ℓ)^{-1}))`.
* The derivative bounds, smoothness and periodicity of `ψ_γ` are
  `loopTransport_envelope`, `contDiff_loopTransport` and `loopTransport_periodic`.
  The support clause of the derivative bounds is `loopTransport_eq_zero_of_far`.
* `Riesz1.derivative_bounds_cutoff_L2641` assembles the statement. Its constant
  depends only on `s`, `α` and `χ`, which is stronger than the paper, where it may also depend on
  `γ` and `C₀`.

The cutoff `χ` is a smooth function with values in `[0, 1]`, supported in `(-1/4, 1/4)` (its
closed support is a compact subset of that interval, as the proof of the derivative bounds uses) and
equal to one on `[-1/8, 1/8]`.
-/

@[expose] public section

open Set
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- Test of the definition of `ψ_γ`: a full window makes no change, `ψ_γ = ψ`. -/
lemma loopTransport_of_not_partial {χ ψ : ℝ → ℝ} {N : ℕ+} {ℓ γ : ℝ}
    (hP : ¬GradPartial N ℓ γ) : loopTransport χ N ℓ γ ψ = ψ := by
  funext u
  simp only [loopTransport, hP, ↓reduceIte]

/-- Test of the definition of `ψ_γ`: in a partial window, on the fundamental domain
`|u| < (2ℓ)^{-1}` the transport is given by `ψ_γ(u) = χ(ℓu/t_γ)(ψ(u) - ψ((2ℓ)^{-1}))`. -/
lemma loopTransport_eq_formula {χ ψ : ℝ → ℝ} {N : ℕ+} {ℓ γ : ℝ} (hℓ : 0 < ℓ)
    (hP : GradPartial N ℓ γ) {u : ℝ} (hu : |u| < 1 / (2 * ℓ)) :
    loopTransport χ N ℓ γ ψ u = χ (ℓ * u / gradT N ℓ γ) * (ψ u - ψ (1 / (2 * ℓ))) := by
  have hb := abs_lt.mp hu
  simp only [loopTransport, hP, ↓reduceIte]
  rw [loopCircleRep_eq_self hℓ hb.1.le hb.2]

/-- The representative times `ℓ` is `y` minus the integer `⌊y + 1/2⌋`, the integer nearest to `y`. -/
lemma ell_mul_loopCircleRep {ℓ : ℝ} (hℓ : 0 < ℓ) (y : ℝ) :
    ℓ * loopCircleRep ℓ (y / ℓ) = y - ((⌊y + 1 / 2⌋ : ℤ) : ℝ) := by
  have hℓy : ℓ * (y / ℓ) = y := by field_simp
  have hfl : ℓ * (((⌊y + 1 / 2⌋ : ℤ) : ℝ) / ℓ) = ((⌊y + 1 / 2⌋ : ℤ) : ℝ) := by field_simp
  unfold loopCircleRep
  rw [mul_sub, hℓy, hfl]

/-- The support clause of the derivative bounds. In a partial window, `ψ_γ(y/ℓ) = 0` whenever
every integer `m` has `t_γ/4 ≤ |y - m|`. The point `ℓ · loopCircleRep` is `y` shifted to the
nearest integer, and the cutoff `χ` vanishes at its argument `(y - n)/t_γ` once
`|(y - n)/t_γ| ≥ 1/4`. -/
lemma loopTransport_eq_zero_of_far {χ ψ : ℝ → ℝ} (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    {N : ℕ+} {ℓ γ : ℝ} (hℓ : 0 < ℓ) (hP : GradPartial N ℓ γ) (y : ℝ)
    (hy : ∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) :
    loopTransport χ N ℓ γ ψ (y / ℓ) = 0 := by
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have ht : 0 < gradT N ℓ γ := by
    unfold gradT
    simp only [hP, ↓reduceIte]
    exact div_pos (Real.rpow_pos_of_pos (mul_pos hN hℓ) γ) hN
  have hn := hy ⌊y + 1 / 2⌋
  have hfar : 1 / 4 ≤ |(y - ((⌊y + 1 / 2⌋ : ℤ) : ℝ)) / gradT N ℓ γ| := by
    rw [abs_div, abs_of_pos ht, le_div_iff₀ ht]
    linarith
  have hnot : (ℓ * loopCircleRep ℓ (y / ℓ) / gradT N ℓ γ) ∉ tsupport χ := by
    intro h
    rw [ell_mul_loopCircleRep hℓ y] at h
    have hin := abs_lt.mpr (hχs h)
    linarith
  simp only [loopTransport, hP, ↓reduceIte]
  rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul]

/-- **Derivative bounds persist after the spatial cutoff**, with the
transport `ψ_γ = loopTransport χ N ℓ γ ψ`. For a smooth `1/ℓ`-periodic `ψ` with
`|ψ'| ≤ C₀ w₁` and `|ψ''| ≤ C₀ w₂` (the weights of Lemma 5.7 at `K = Nℓ`),
the transport is smooth and `1/ℓ`-periodic, and it satisfies the same two envelopes with a constant
`C` depending only on `s`, `α` and `χ`. In a partial window, `ψ_γ(y/ℓ) = 0` for every real `y`
whose distance to every integer is at least `t_γ/4`. -/
theorem derivative_bounds_cutoff_L2641 {s α : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα : s - 1 ≤ α) (hα2 : α < s / 2) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4)) (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ+) (ℓ γ C₀ : ℝ) (ψ : ℝ → ℝ),
      0 < ℓ → 1 ≤ (N : ℝ) * ℓ → 1 < γ → 0 ≤ C₀ →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      ContDiff ℝ ∞ (loopTransport χ N ℓ γ ψ) ∧
      Function.Periodic (loopTransport χ N ℓ γ ψ) ℓ⁻¹ ∧
      (∀ t, |deriv (loopTransport χ N ℓ γ ψ) t| ≤
          C * C₀ * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t ∧
        |deriv (deriv (loopTransport χ N ℓ γ ψ)) t| ≤
          C * C₀ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) ∧
      (GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) →
        loopTransport χ N ℓ γ ψ (y / ℓ) = 0) := by
  have hχc : HasCompactSupport χ :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport χ)
      (fun x hx => Ioo_subset_Icc_self (hχs hx))
  obtain ⟨C, hC, henv⟩ := loopTransport_envelope hs0 hs1 hα hα2 hχ hχc hχs hχ1 hχ01
  refine ⟨C, hC, fun N ℓ γ C₀ ψ hℓ hK hγ hC₀ hψ hp h1 h2 => ?_⟩
  exact ⟨contDiff_loopTransport hχ hψ hχs N hℓ γ, loopTransport_periodic hℓ χ hp,
    henv N ℓ γ ψ C₀ hℓ hK hγ hC₀ hψ hp h1 h2, fun hP y hy => loopTransport_eq_zero_of_far hχs hℓ hP y hy⟩

end

end Riesz1
