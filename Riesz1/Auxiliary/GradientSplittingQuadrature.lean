/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingQuadraturePartialLarge
public import Riesz1.Auxiliary.GradientSplittingQuadratureCrude

/-!
# Quadrature part of the gradient splitting

The complete quadrature part of Lemma 5.7: both window types and
all scales `Nℓ ≥ 1`, with `κ = 2`. The constants are chosen before `N, ℓ, C0, ψ, X`.
The field is extended by zero outside the label window.
-/

@[expose] public section

open Set MeasureTheory
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The reference field, including its prescribed zero
extension outside the label window. -/
def gradV2lab (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ)
    (X : Fin (N : ℕ) → ℝ) (i : ℤ) : ℝ :=
  if i ∈ gradLabels N ℓ γ then gradVdisc2 s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i else 0

/-- On the window, the reference field is the discrete part plus background. -/
lemma gradV2lab_eq {s ℓ γ : ℝ} {ψ : ℝ → ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    {i : ℤ} (hi : i ∈ gradLabels N ℓ γ) :
    gradV2lab s ψ N ℓ γ X i = gradVdisc2 s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i := by
  simp only [gradV2lab, hi, ↓reduceIte]

/-- Outside the window, the reference field has its prescribed value zero. -/
lemma gradV2lab_eq_zero {s ℓ γ : ℝ} {ψ : ℝ → ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    {i : ℤ} (hi : i ∉ gradLabels N ℓ γ) : gradV2lab s ψ N ℓ γ X i = 0 := by
  simp only [gradV2lab, hi, ↓reduceIte]

/-- Convert the crude field bound into the target weights on a bounded window.
This internal lemma makes no assertion about the field's analytic estimates. -/
lemma gradQuad_crude_to_target {s a N ℓ C C0 E H x V : ℝ} (hs : 0 ≤ s)
    (hN : 0 < N) (hℓ : 0 < ℓ) (hC : 0 ≤ C) (hC0 : 0 ≤ C0) (hE : 1 ≤ E)
    (hH : 0 ≤ H) (hx : |N * x| ≤ 3 * H)
    (hV : |V| ≤ C * C0 * N * (N * ℓ) ^ a) :
    |V| ≤ C * (1 + 3 * H) ^ (1 + s / 2) * C0 * E *
      (ℓ⁻¹ * gradWeightTwo s a (N * ℓ) ℓ⁻¹ (x / ℓ) +
        N * (N * ℓ) ^ a / (1 + N * circDist 1 x) ^ (1 + s / 2)) := by
  let D := (1 + 3 * H) ^ (1 + s / 2)
  let T := ℓ⁻¹ * gradWeightTwo s a (N * ℓ) ℓ⁻¹ (x / ℓ) +
    N * (N * ℓ) ^ a / (1 + N * circDist 1 x) ^ (1 + s / 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hW := gradWeightTwo_nonneg_unconditional s a (N * ℓ) ℓ⁻¹ (x / ℓ)
  have hcd := circDist_nonneg 1 x
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hr : N * circDist 1 x ≤ 3 * H := by
    have hc := mul_le_mul_of_nonneg_left (circDist_le_abs_self one_pos x) hN.le
    have he : N * |x| = |N * x| := by rw [abs_mul, abs_of_pos hN]
    rw [he] at hc
    exact hc.trans hx
  have hden0 : 0 < (1 + N * circDist 1 x) ^ (1 + s / 2) := by positivity
  have hden : (1 + N * circDist 1 x) ^ (1 + s / 2) ≤ D :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hA : 0 ≤ ℓ⁻¹ * gradWeightTwo s a (N * ℓ) ℓ⁻¹ (x / ℓ) := by positivity
  have hNK : 0 ≤ N * (N * ℓ) ^ a := by positivity
  have hscale : N * (N * ℓ) ^ a ≤ D * T := by
    have hmul : N * (N * ℓ) ^ a ≤ D * (N * (N * ℓ) ^ a / (1 + N * circDist 1 x) ^ (1 + s / 2)) := by
      rw [← mul_div_assoc, le_div_iff₀ hden0]
      nlinarith [mul_le_mul_of_nonneg_left hden hNK]
    exact hmul.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hA) hD)
  calc _ ≤ _ := hV
       _ = C * C0 * (N * (N * ℓ) ^ a) := by ring
       _ ≤ C * C0 * (D * T) := mul_le_mul_of_nonneg_left hscale (mul_nonneg hC hC0)
       _ ≤ C * D * C0 * E * T := by
        nlinarith [mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ C * C0 * D * T)]

theorem gradV2_window_bound {s α γ ε : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα0 : s - 1 ≤ α) (hα1 : α < s / 2)
    (hγ4 : 4 ≤ γ) (hγs : 2 / s ≤ γ) (hε0 : 0 < ε) (hε : ε < γ * (1 - s / 2)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ+) (ℓ C0 : ℝ) (X : Fin (N : ℕ) → ℝ) (ψ : ℝ → ℝ) (i : ℤ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) →
      gradEvent s γ ε N ℓ X →
      |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε → i ∈ gradLabels N ℓ γ →
      |gradVdisc2 s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i|
        ≤ C * C0 * ((N : ℝ) * ℓ) ^ (2 * ε) *
          (ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
            + (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) /
              (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)) := by
  obtain ⟨Cl, K₀, hCl, hK₀, hl⟩ := gradV2_partial_large_bound hs0 hs1 hα0 hα1 hγ4 hγs hε0 hε
  have hH : 1 ≤ K₀ ^ γ := Real.one_le_rpow hK₀ (by linarith)
  obtain ⟨Cb, hCb, hb⟩ := gradV2_partial_crude_bound hs0 hs1 hα0 hα1 (by linarith) hε.le hH
  obtain ⟨Cf, hCf, hf⟩ := gradV2_full_bound hs0 hs1 hα0 hα1 hε0
  let D := (1 + 3 * K₀ ^ γ) ^ (1 + s / 2)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨Cl + Cb * D + Cf, by positivity, ?_⟩
  intro N ℓ C0 X ψ i hN hℓ hℓ1 hK hC0 hψ hper h1 h2 hsupp hX hanchor hi
  let T := ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) +
    (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) /
      (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)
  let E := ((N : ℝ) * ℓ) ^ (2 * ε)
  have hW := gradWeightTwo_nonneg_unconditional s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹
    (gradLift N X i / ℓ)
  have hcd := circDist_nonneg 1 (gradLift N X i)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hE : 1 ≤ E := Real.one_le_rpow hK (by linarith)
  have hCET : 0 ≤ C0 * E * T := by positivity
  by_cases hP : GradPartial N ℓ γ
  · by_cases hlarge : K₀ ≤ (N : ℝ) * ℓ
    · have hh := hl N ℓ C0 X ψ i hN hℓ hℓ1 hlarge hP hC0 hψ hper h1 h2 (hsupp hP) hX hanchor hi
      exact hh.trans (by
        change Cl * C0 * E * T ≤ (Cl + Cb * D + Cf) * C0 * E * T
        nlinarith [mul_nonneg (by positivity : 0 ≤ Cb * D + Cf) hCET])
    · have hMH : gradM N ℓ γ ≤ K₀ ^ γ :=
        Real.rpow_le_rpow (by linarith) (le_of_not_ge hlarge) (by linarith)
      have hh := hb N ℓ C0 X ψ i hN hℓ hℓ1 hK hP hMH hC0 hψ hper h1 h2 (hsupp hP) hX hanchor hi
      have hx := gradPartial_anchor_lift_bound hs0 (by linarith) hε.le hK hP hX hanchor hi
      have hct := gradQuad_crude_to_target hs0.le hNpos hℓ hCb.le hC0 hE
        (by linarith : 0 ≤ K₀ ^ γ) (hx.trans (by linarith)) hh
      calc _ ≤ Cb * D * C0 * E * T := hct
           _ ≤ _ := by
            change _ ≤ (Cl + Cb * D + Cf) * C0 * E * T
            nlinarith [mul_nonneg (by positivity : 0 ≤ Cl + Cf) hCET]
  · have hh := hf N ℓ γ C0 ψ X i hN hP hℓ hℓ1 hK hC0 hψ hper h1 h2 hi
    have hpow : ((N : ℝ) * ℓ) ^ ε ≤ E := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
    calc _ ≤ _ := hh
         _ ≤ Cf * C0 * E * T := by gcongr
         _ ≤ _ := by
          change _ ≤ (Cl + Cb * D + Cf) * C0 * E * T
          nlinarith [mul_nonneg (by positivity : 0 ≤ Cl + Cb * D) hCET]

/-- The quadrature part of Lemma 5.7, all assertions and both windows.
One may take `ε_* = γ(1-s/2)` and `κ = 2`, independently of `ε` and of all scale,
profile and configuration data. -/
theorem gradient_splitting_quadrature {s α γ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα0 : s - 1 ≤ α) (hα1 : α < s / 2) (hγ : max 4 (2 / s) ≤ γ) :
    ∃ εstar κ : ℝ, 0 < εstar ∧ 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < εstar →
    ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ+) (ℓ C0 : ℝ) (ψ : ℝ → ℝ) (X : Fin (N : ℕ) → ℝ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → 0 ≤ C0 →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (GradPartial N ℓ γ → ∀ y : ℝ,
        (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) →
      gradEvent s γ ε N ℓ X →
      |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε → ∀ i : ℤ,
      |gradV2lab s ψ N ℓ γ X i| ≤ C * C0 * ((N : ℝ) * ℓ) ^ (κ * ε) *
        (ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) +
          (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) /
            (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)) := by
  have hγ4 : 4 ≤ γ := (le_max_left _ _).trans hγ
  have hγs : 2 / s ≤ γ := (le_max_right _ _).trans hγ
  refine ⟨γ * (1 - s / 2), 2, mul_pos (by linarith) (by linarith), by norm_num, ?_⟩
  intro ε hε hεstar
  obtain ⟨C, hC, hbound⟩ := gradV2_window_bound hs0 hs1 hα0 hα1 hγ4 hγs hε hεstar
  refine ⟨C, hC, ?_⟩
  intro N ℓ C0 ψ X hN hℓ hℓ1 hK hC0 hψ hper h1 h2 hsupp hX hanchor i
  by_cases hi : i ∈ gradLabels N ℓ γ
  · rw [gradV2lab_eq hi]
    exact hbound N ℓ C0 X ψ i hN hℓ hℓ1 hK hC0 hψ hper h1 h2 hsupp hX hanchor hi
  · rw [gradV2lab_eq_zero hi, abs_zero]
    have hW := gradWeightTwo_nonneg_unconditional s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹
      (gradLift N X i / ℓ)
    have hd := circDist_nonneg 1 (gradLift N X i)
    positivity

end

end Riesz1
