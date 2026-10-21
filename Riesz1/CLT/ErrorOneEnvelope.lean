/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriConclusion

/-!
# The derivative envelope of the product `q_N` (Theorem 3)

For the variance bound of Theorem 3, Lemma 5.2 is applied to `q_N` with the
centre `c = 0`, the radius `R = 2` and the exponent `λ = 0`. The derivative of `q_N` has the
uniform bound `A`, and it vanishes at circle distance at least two from the origin (the compact
support of the profile). Then the envelope holds with the factor `2A`.

Lemma `Riesz1.Internal.deriv_le_aPrioriEnvelope` is this deterministic statement. It uses only
the pointwise bound and the vanishing, not the Gibbs law.
-/

@[expose] public section

noncomputable section

namespace Riesz1.Internal

/-- The envelope is nonnegative for every real `d` and positive scale. -/
lemma aPrioriEnvelope_nonneg (s lam K R d : ℝ) (hK : 0 < K) (hd : 0 ≤ d) :
    0 ≤ aPrioriEnvelope s lam K R d := by
  unfold aPrioriEnvelope
  have h1 : 0 ≤ (if d ≤ R then ((max d K⁻¹) ^ (1 + lam))⁻¹ else 0) := by
    split_ifs
    · exact inv_nonneg.mpr (Real.rpow_nonneg (le_trans (inv_nonneg.mpr hK.le) (le_max_right _ _)) _)
    · exact le_rfl
  have h2 : 0 ≤ (if R ≤ d then (d ^ (3 - s))⁻¹ else 0) := by
    split_ifs
    · exact inv_nonneg.mpr (Real.rpow_nonneg hd _)
    · exact le_rfl
  exact add_nonneg h1 h2

/-- **Envelope of `q_N`.** Let `K ≥ 1`, let `A ≥ 0`, and let `g : ℝ → ℝ` have derivative bounded
by `A` everywhere. Suppose its derivative vanishes at every `u` with circle distance at least
two from the centre `c`, where the distance is `|centralRep L (u - c)|`. Then every `u` obeys
`|g'(u)| ≤ 2A · aPrioriEnvelope s 0 K 2 d(u)`, the envelope of Lemma 5.2 with `λ = 0`
and radius two. -/
lemma deriv_le_aPrioriEnvelope (s K A c : ℝ) (L : Length) (g : ℝ → ℝ)
    (hK : 1 ≤ K) (hA : 0 ≤ A)
    (hbound : ∀ u : ℝ, |deriv g u| ≤ A)
    (hvanish : ∀ u : ℝ, 2 ≤ |centralRep L ((u - c : ℝ) : Circle L)| → deriv g u = 0) :
    ∀ u : ℝ, |deriv g u| ≤
      2 * A * aPrioriEnvelope s 0 K 2 |centralRep L ((u - c : ℝ) : Circle L)| := by
  intro u
  set d := |centralRep L ((u - c : ℝ) : Circle L)| with hd_def
  have hd : 0 ≤ d := abs_nonneg _
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  rcases le_total d 2 with h2 | h2
  · -- Inside the radius: the singular term dominates `1/2` on the whole range.
    have hmax : max d K⁻¹ ≤ 2 := by
      refine max_le h2 ?_
      have : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
      linarith
    have hpos : 0 < max d K⁻¹ := lt_of_lt_of_le (inv_pos.mpr hK0) (le_max_right _ _)
    have hfirst : (1 : ℝ) / 2 ≤ (if d ≤ 2 then ((max d K⁻¹) ^ (1 + 0 : ℝ))⁻¹ else 0) := by
      simp only [h2, ↓reduceIte, add_zero, Real.rpow_one]
      calc (1 : ℝ) / 2 = (2 : ℝ)⁻¹ := by norm_num
        _ ≤ (max d K⁻¹)⁻¹ := inv_anti₀ hpos hmax
    have hsecond : 0 ≤ (if 2 ≤ d then (d ^ (3 - s))⁻¹ else 0) := by
      split_ifs
      · exact inv_nonneg.mpr (Real.rpow_nonneg hd _)
      · exact le_rfl
    have henv : (1 : ℝ) / 2 ≤ aPrioriEnvelope s 0 K 2 d := by
      unfold aPrioriEnvelope
      have : (0 : ℝ) ≤ (if 2 ≤ d then (d ^ (3 - s))⁻¹ else 0) := hsecond
      linarith
    calc |deriv g u| ≤ A := hbound u
      _ ≤ 2 * A * aPrioriEnvelope s 0 K 2 d := by
        have := mul_le_mul_of_nonneg_left henv (by linarith : (0 : ℝ) ≤ 2 * A)
        linarith
  · -- Outside the radius: the derivative vanishes, and the envelope is nonnegative.
    have hzero : deriv g u = 0 := hvanish u h2
    rw [hzero, abs_zero]
    exact mul_nonneg (by linarith) (aPrioriEnvelope_nonneg s 0 K 2 d hK0 hd)

end Riesz1.Internal

end
end
