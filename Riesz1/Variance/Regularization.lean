/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Mollifier.RegularizationSobolev
public import Riesz1.ToMathlib.MollifierPointwise.Circle
public import Riesz1.Frozen.CircleSobolev
public import Mathlib.Tactic

/-!
# Regularization estimates

Lemma 5.1. Fix a mollifier `ρ` (`IsMollifier ρ`) and a number
`0 ≤ γ < 1`. Then one constant `C > 0`, depending only on `ρ` and `γ`, satisfies the following.

* Fourier regularization on the unit circle: for `0 < s < 1`,
  `δ > 0`, `0 < h ≤ 1` and `ξ ∈ H^{(1-s)/2+δ}`, the two Sobolev bounds hold with `C` in place of
  `C_ρ`, where `r = min δ 1`.
* Sup bound on the circle of length `L ≥ 1`: the convolution
  `f_h = circleMollify ρ L h f` satisfies `|f_h(x)| ≤ C max(|x|, h)^(-γ)`.
* Derivative bound for `γ > 0`: `|f_h'(x)| ≤ C max(|x|, h)^(-1-γ)`.
* Derivative bound for `γ = 0`: `|f_h'(x)| ≤ C (1 + log(L/h)) max(|x|, h)^(-1)`.
* Tail variant for `γ = 0`: for each `0 < s < 1` there is `C'`, depending on `ρ` and `s`, with
  `|f_h'(x)| ≤ C' (1 + |log h|) max(|x|, h)^(-1)` under the extra bound `|f'(y)| ≤ |y|^(s-3)`
  for `|y| ≥ 1`.

Here `|y|` is the distance `circDist L y` to `0` on the circle of length `L`. A real function on
that circle is represented by an `L`-periodic, locally integrable `f : ℝ → ℝ`, as in
`Riesz1.circleMollify`.

Main result: `Riesz1.regularization_estimates`. It is assembled from `Riesz1.regularization_sobolev`
and the `circleMollify` bounds of `Riesz1.MollifierPointwise`.
-/

public section

open MeasureTheory

namespace Riesz1

/-- Lemma 5.1 (regularization estimates), with one constant `C` for all parts.

Let `ρ` be a mollifier and let `0 ≤ γ < 1`. Then there is `C > 0`, depending only on `ρ` and `γ`,
such that the following hold. The hypotheses on `ρ` are `IsMollifier ρ`, which is the assumption in
the paper, and `IsCircleMollifier ρ`. The second follows from the first, but it is taken as a
hypothesis: the definition of `IsCircleMollifier` is not exposed to this module, so the implication
cannot be proved here.

* Sobolev bounds: for all `0 < s < 1`, `δ > 0`, `0 < h ≤ 1` and `ξ ∈ H^{(1-s)/2+δ}` on the unit
  circle, with `σ = (1 - s) / 2` and `r = min δ 1`, the regularization `ξ_h` satisfies
  `‖ξ - ξ_h‖²_{H^σ} ≤ C h^{2r} ‖ξ‖²_{H^{σ+r}}` and
  `0 ≤ ‖ξ‖²_{H^σ} - ‖ξ_h‖²_{H^σ} ≤ C h^{2r} ‖ξ‖²_{H^{σ+r}}`.
  The paper takes `ξ` real. The bounds hold for complex `ξ` too, so the real hypothesis is
  dropped. This generalizes the statement of the paper.
* Sup bound: for `L ≥ 1` and a real, `L`-periodic, locally integrable `f` with
  `|f(y)| ≤ |y|^(-γ)` almost everywhere, `|f_h(x)| ≤ C max(|x|, h)^(-γ)`.
* For `γ > 0`: if `f` is differentiable off zero with `|f'(y)| ≤ |y|^(-1-γ)`, then `f_h` is
  differentiable and `|f_h'(x)| ≤ C max(|x|, h)^(-1-γ)`.
* For `γ = 0`: under the same hypotheses with exponent `-1`, `|f_h'(x)| ≤ C (1 + log(L/h))
  max(|x|, h)^(-1)`.
* For `γ = 0` and each `0 < s < 1`: there is `C'`, depending on `ρ` and `s`, such that under the
  extra bound `|f'(y)| ≤ |y|^(s-3)` for `|y| ≥ 1`, `|f_h'(x)| ≤ C' (1 + |log h|) max(|x|, h)^(-1)`.
-/
theorem regularization_estimates {ρ : ℝ → ℝ} (hρc : IsCircleMollifier ρ) (hρ : IsMollifier ρ)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (s δ h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (ξ : {f : UnitAddCircle → ℂ // MemLp f 2 volume}),
        0 < s → s < 1 → 0 < δ → CircleSobolev ((1 - s) / 2 + δ) ξ.1 →
          (circleSobolevSq ((1 - s) / 2)
              (subL2 ξ (regularizeL2 hρc ⟨h, hh⟩ hh1 ξ))).toReal ≤
            C * h ^ (2 * min δ 1) * (circleSobolevSq ((1 - s) / 2 + min δ 1) ξ).toReal ∧
          0 ≤ (circleSobolevSq ((1 - s) / 2) ξ).toReal -
              (circleSobolevSq ((1 - s) / 2)
                (regularizeL2 hρc ⟨h, hh⟩ hh1 ξ)).toReal ∧
            (circleSobolevSq ((1 - s) / 2) ξ).toReal -
                (circleSobolevSq ((1 - s) / 2)
                  (regularizeL2 hρc ⟨h, hh⟩ hh1 ξ)).toReal ≤
              C * h ^ (2 * min δ 1) * (circleSobolevSq ((1 - s) / 2 + min δ 1) ξ).toReal) ∧
      (∀ L : ℝ, 1 ≤ L → ∀ f : ℝ → ℝ, Function.Periodic f L → LocallyIntegrable f volume →
        (∀ᵐ y ∂(volume : Measure ℝ), circDist L y ≠ 0 → |f y| ≤ circDist L y ^ (-γ)) →
        ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
          |circleMollify ρ L h f x| ≤ C * (max (circDist L x) h) ^ (-γ)) ∧
      (0 < γ → ∀ L : ℝ, 1 ≤ L → ∀ f : ℝ → ℝ, Function.Periodic f L → LocallyIntegrable f volume →
        (∀ y : ℝ, circDist L y ≠ 0 → DifferentiableAt ℝ f y) →
        (∀ y : ℝ, circDist L y ≠ 0 → |deriv f y| ≤ circDist L y ^ (-1 - γ)) →
        ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ, ∃ D : ℝ,
          HasDerivAt (circleMollify ρ L h f) D x ∧
            |D| ≤ C * (max (circDist L x) h) ^ (-1 - γ)) ∧
      (γ = 0 → ∀ L : ℝ, 1 ≤ L → ∀ f : ℝ → ℝ, Function.Periodic f L → LocallyIntegrable f volume →
        (∀ y : ℝ, circDist L y ≠ 0 → DifferentiableAt ℝ f y) →
        (∀ y : ℝ, circDist L y ≠ 0 → |deriv f y| ≤ circDist L y ^ (-1 - γ)) →
        ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ, ∃ D : ℝ,
          HasDerivAt (circleMollify ρ L h f) D x ∧
            |D| ≤ C * (1 + Real.log (L / h)) * (max (circDist L x) h) ^ (-1 : ℝ)) ∧
      (γ = 0 → ∀ s : ℝ, 0 < s → s < 1 → ∃ C' : ℝ, 0 < C' ∧
        ∀ L : ℝ, 1 ≤ L → ∀ f : ℝ → ℝ, Function.Periodic f L → LocallyIntegrable f volume →
        (∀ y : ℝ, circDist L y ≠ 0 → DifferentiableAt ℝ f y) →
        (∀ y : ℝ, circDist L y ≠ 0 → |deriv f y| ≤ circDist L y ^ (-1 - γ)) →
        (∀ y : ℝ, 1 ≤ circDist L y → |deriv f y| ≤ circDist L y ^ (s - 3)) →
        ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ, ∃ D : ℝ,
          HasDerivAt (circleMollify ρ L h f) D x ∧
            |D| ≤ C' * (1 + |Real.log h|) * (max (circDist L x) h) ^ (-1 : ℝ)) := by
  obtain ⟨C₁, hC₁, hsob⟩ := regularization_sobolev hρc
  obtain ⟨C₂, hC₂, hsup⟩ := circleMollify_sup_bound ρ hρ hγ0 hγ1
  -- The derivative constant depends on the case `γ > 0` or `γ = 0`, so the two cases are split
  -- here and the constant is recorded once for both.
  obtain ⟨C₃, hC₃, hpos, hlog⟩ : ∃ C₃ : ℝ, 0 < C₃ ∧
      (0 < γ → ∀ L : ℝ, 1 ≤ L → ∀ f : ℝ → ℝ, Function.Periodic f L → LocallyIntegrable f volume →
        (∀ y : ℝ, circDist L y ≠ 0 → DifferentiableAt ℝ f y) →
        (∀ y : ℝ, circDist L y ≠ 0 → |deriv f y| ≤ circDist L y ^ (-1 - γ)) →
        ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ, ∃ D : ℝ,
          HasDerivAt (circleMollify ρ L h f) D x ∧
            |D| ≤ C₃ * (max (circDist L x) h) ^ (-1 - γ)) ∧
      (γ = 0 → ∀ L : ℝ, 1 ≤ L → ∀ f : ℝ → ℝ, Function.Periodic f L → LocallyIntegrable f volume →
        (∀ y : ℝ, circDist L y ≠ 0 → DifferentiableAt ℝ f y) →
        (∀ y : ℝ, circDist L y ≠ 0 → |deriv f y| ≤ circDist L y ^ (-1 - γ)) →
        ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ, ∃ D : ℝ,
          HasDerivAt (circleMollify ρ L h f) D x ∧
            |D| ≤ C₃ * (1 + Real.log (L / h)) * (max (circDist L x) h) ^ (-1 : ℝ)) := by
    rcases hγ0.eq_or_lt with h0 | hγpos
    · subst h0
      obtain ⟨C₃, hC₃, hlog⟩ := circleMollify_deriv_bound_log ρ hρ
      refine ⟨C₃, hC₃, fun h => (lt_irrefl _ h).elim,
        fun _ L hL f hper hloc hdiff hfd h hh hh1 x => ?_⟩
      obtain ⟨D, hD, hDb⟩ := hlog L hL f hper hloc hdiff
        (fun y hy => by simpa only [sub_zero] using hfd y hy) h hh hh1 x
      exact ⟨D, hD, hDb⟩
    · obtain ⟨C₃, hC₃, hpos⟩ := circleMollify_deriv_bound_pos ρ hρ hγpos hγ1
      exact ⟨C₃, hC₃, fun _ => hpos, fun h0 => absurd h0 hγpos.ne'⟩
  refine ⟨C₁ + C₂ + C₃, by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · -- Sobolev bounds: the constant `C₁` of `regularization_sobolev` is raised to `C₁ + C₂ + C₃`.
    intro s δ h hh hh1 ξ hs0 hs1 hδ hξ
    have hfin : circleSobolevSq ((1 - s) / 2 + δ) ξ < ⊤ := by
      obtain ⟨_, hfin⟩ := hξ
      exact hfin
    obtain ⟨hA, hB, hC⟩ := hsob s δ h hh hh1 ξ hs0 hs1 hδ hfin
    have hw : 0 ≤ h ^ (2 * min δ 1) := Real.rpow_nonneg hh.le _
    have hT : 0 ≤ (circleSobolevSq ((1 - s) / 2 + min δ 1) ξ).toReal := ENNReal.toReal_nonneg
    have hCle : C₁ ≤ C₁ + C₂ + C₃ := by linarith
    have hmono := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hw) hT
    exact ⟨le_trans hA hmono, hB, le_trans hC hmono⟩
  · -- Sup bound: the constant `C₂` is raised to `C₁ + C₂ + C₃`.
    intro L hL f hper hloc hf h hh hh1 x
    refine le_trans (hsup L hL f hper hloc hf h hh hh1 x) ?_
    exact mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (le_trans hh.le (le_max_right _ _)) _)
  · -- Derivative bound for `γ > 0`.
    intro hγ L hL f hper hloc hdiff hfd h hh hh1 x
    obtain ⟨D, hD, hDb⟩ := hpos hγ L hL f hper hloc hdiff hfd h hh hh1 x
    refine ⟨D, hD, le_trans hDb ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (le_trans hh.le (le_max_right _ _)) _)
  · -- Derivative bound for `γ = 0`, with the factor `1 + log(L/h) ≥ 0`.
    intro h0 L hL f hper hloc hdiff hfd h hh hh1 x
    obtain ⟨D, hD, hDb⟩ := hlog h0 L hL f hper hloc hdiff hfd h hh hh1 x
    refine ⟨D, hD, le_trans hDb ?_⟩
    have hlogn : 0 ≤ 1 + Real.log (L / h) := by
      have := Real.log_nonneg ((one_le_div hh).2 (le_trans hh1 hL))
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hlogn)
      (Real.rpow_nonneg (le_trans hh.le (le_max_right _ _)) _)
  · -- Tail variant for `γ = 0`: its own constant `C'` depends on `s`.
    intro h0 s hs0 hs1
    obtain ⟨C', hC', hT⟩ := circleMollify_deriv_bound_log_tail ρ hρ s hs0 hs1
    refine ⟨C', hC', fun L hL f hper hloc hdiff hfd htail h hh hh1 x => ?_⟩
    have hfd' : ∀ y : ℝ, circDist L y ≠ 0 → |deriv f y| ≤ circDist L y ^ (-1 : ℝ) :=
      fun y hy => by simpa only [h0, sub_zero] using hfd y hy
    obtain ⟨D, hD, hDb⟩ := hT L hL f hper hloc hdiff hfd' htail h hh hh1 x
    exact ⟨D, hD, hDb⟩

end Riesz1

end
