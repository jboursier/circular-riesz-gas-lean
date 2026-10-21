/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Elementary.Covariance
public import Riesz1.ToMathlib.Elementary.Absorption

/-!
# Covariance signs and sublinear absorption

The assembled statement of the algebraic part of Lemma 4.5. It collects the two covariance
signs (Chebyshev's association inequality for a monotone pair and for an antitone and a monotone
function of a random variable) and the two absorption bounds, with the constants of the paper.

Each part is proved in `Riesz1.ToMathlib.Elementary`. The statement drops the interval, Borel and
random-variable hypotheses, the sign conditions `0 ≤ u` and `0 ≤ v`, and the condition `0 < A` in
the one-term bound. The proofs do not use them, so dropping them only generalizes the statement.
-/

public section

open MeasureTheory

universe u

namespace Riesz1

/-- The algebraic part of Lemma 4.5. Let `Y` take values in a set `I`, and let `a` and `b`
be integrable together with `a ∘ Y`, `b ∘ Y` and `(a ∘ Y) (b ∘ Y)`. If `a` and `b` are monotone on
`I`, the covariance is nonnegative. If `a` is antitone and `b` monotone on `I`, the covariance is
nonpositive. Let `M ≥ 0` satisfy `M ≤ A M^u + B M^v` with `A, B > 0` and `u, v < 1`. Then
`M ≤ max {(4A)^(1/(1-u)), (4B)^(1/(1-v))}`. Let `M ≤ M^u + A` with `u < 1`. Then
`M ≤ max {2^(1/(1-u)), 2A}`. -/
theorem no_explosion_algebra :
    (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (I : Set ℝ) (Y : Ω → ℝ), (∀ ω, Y ω ∈ I) → ∀ a b : ℝ → ℝ, MonotoneOn a I →
      MonotoneOn b I → Integrable (fun ω => a (Y ω)) P → Integrable (fun ω => b (Y ω)) P →
      Integrable (fun ω => a (Y ω) * b (Y ω)) P →
      0 ≤ ∫ ω, a (Y ω) * b (Y ω) ∂P - (∫ ω, a (Y ω) ∂P) * ∫ ω, b (Y ω) ∂P) ∧
    (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (I : Set ℝ) (Y : Ω → ℝ), (∀ ω, Y ω ∈ I) → ∀ a b : ℝ → ℝ, AntitoneOn a I →
      MonotoneOn b I → Integrable (fun ω => a (Y ω)) P → Integrable (fun ω => b (Y ω)) P →
      Integrable (fun ω => a (Y ω) * b (Y ω)) P →
      ∫ ω, a (Y ω) * b (Y ω) ∂P - (∫ ω, a (Y ω) ∂P) * ∫ ω, b (Y ω) ∂P ≤ 0) ∧
    (∀ M A B u v : ℝ, 0 ≤ M → 0 < A → 0 < B → u < 1 → v < 1 →
      M ≤ A * M ^ u + B * M ^ v →
      M ≤ max ((4 * A) ^ (1 / (1 - u))) ((4 * B) ^ (1 / (1 - v)))) ∧
    (∀ M A u : ℝ, 0 ≤ M → u < 1 → M ≤ M ^ u + A →
      M ≤ max ((2 : ℝ) ^ (1 / (1 - u))) (2 * A)) :=
  ⟨fun _ _ _ _ _ _ hYI _ _ ha hb hia hib hiab =>
      covariance_nonneg_of_monotone _ hYI _ _ ha hb hia hib hiab,
    fun _ _ _ _ _ _ hYI _ _ ha hb hia hib hiab =>
      covariance_nonpos_of_antitone_monotone _ hYI _ _ ha hb hia hib hiab,
    fun M A B u v hM hA hB hu hv h => le_max_of_le_add_rpow M A B u v hM hA hB hu hv h,
    fun M A u hM hu h => le_max_of_le_rpow_add M A u hM hu h⟩

end Riesz1
