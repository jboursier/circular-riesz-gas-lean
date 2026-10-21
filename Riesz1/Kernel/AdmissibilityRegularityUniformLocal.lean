/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityAbsoluteContinuity
public import Riesz1.ToMathlib.PuncturedOscillatoryUniform

/-!
# Uniform bounded-region oscillatory estimates for the admissible transport

On a fixed real interval containing all fixed marks, sufficiently enlarged circles have
no wrapping distances. The uniform primitive bound and (A3) then give one oscillatory
constant and frequency threshold for all these circles. This is a local step of the admissibility
regularity lemma.
-/

public section

open MeasureTheory Set

namespace Riesz1.Internal

/-- The bounded part of the cutoff argument, uniform in the circle length. This analytic
helper has the transport bounds as premises. No uniform Fourier conclusion is assumed. -/
theorem uniform_local_oscillatory_of_transport_bounds (P : Parameters)
    (p : ℕ+) (marks : Fin (p : ℕ) → ℝ) (α C δ M R : ℝ)
    (hα : P.val.2 - 1 ≤ α) (hδ : 0 < δ) (hδ1 : δ < P.val.2 - α)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hR : 1 ≤ R) (hmarks : ∀ j, |marks j| ≤ R) :
    ∃ K W : ℝ, 0 ≤ K ∧ 1 ≤ W ∧ ∀ L : Length, 4 * R ≤ L.val →
      ∀ ψ : ℝ → ℝ, (∀ x, |ψ x| ≤ M) →
      (∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
        ContDiffAt ℝ 2 ψ x ∧
        |deriv (deriv ψ) x| ≤ C *
          ((if dist (x : Circle L) 0 ≤ 1 then
              ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α)
            else 0) +
           (if 1 ≤ dist (x : Circle L) 0 then
              dist (x : Circle L) 0 ^ (-3 + P.val.2) else 0))) →
      IntervalIntegrable (deriv ψ) volume (-R) R ∧
      ∀ (χ : ℝ → ℂ) (c : ℂ), W ≤ ‖c‖ →
        (∀ t : ℝ, HasDerivAt χ (c * χ t) t) → (∀ t : ℝ, ‖χ t‖ = 1) →
        ‖∫ t in (-R)..R, ((deriv ψ t : ℝ) : ℂ) * χ t‖ ≤
          K * ‖c‖ ^ (α - P.val.2 + δ) := by
  classical
  let b := 1 - P.val.2 + α + δ
  have hb : 0 < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith
  let S : Finset ℝ := Finset.univ.image marks
  let A := (2 * R) ^ δ
  let H := (2 * R) ^ (1 + b)
  have hRp : 0 < R := by linarith
  have hA : 0 ≤ A := by positivity
  have hH : 0 ≤ H := by positivity
  have hD : 0 ≤ C * (H + A * (p : ℕ)) := by positivity
  obtain ⟨K, W, hK, hW, hosc⟩ := PuncturedDerivative.uniform_oscillatory_bound_finite
    hb hb1 hM S hD (by linarith : -R < R)
  refine ⟨K, W, hK, hW, fun L hL ψ hψ hreg => ?_⟩
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hdist (x : ℝ) (hx : x ∈ Ioo (-R) R) (j : Fin (p : ℕ)) :
      dist (x : Circle L) (marks j : Circle L) = |x - marks j| := by
    apply CircleSingularity.dist_coe_eq_abs_sub L.property
    have hxm : |x| ≤ R := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
    exact (abs_sub _ _).trans ((add_le_add hxm (hmarks j)).trans (by linarith))
  have hne (x : ℝ) (hx : x ∈ Ioo (-R) R \ (S : Set ℝ)) :
      ∀ j, (x : Circle L) ≠ (marks j : Circle L) := by
    intro j he
    have hz : |x - marks j| = 0 := by rw [← hdist x hx.1 j, he, dist_self]
    have he' : x = marks j := sub_eq_zero.mp (abs_eq_zero.mp hz)
    apply hx.2
    simp only [S, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨j, he'.symm⟩
  have hh := hosc ψ
    (fun x hx => (hreg x (hne x hx)).1.differentiableAt (by norm_num))
    (fun x hx => ((hreg x (hne x hx)).1.derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num))
    (fun x _ => hψ x) (fun x hx => ?_)
  · simpa only [show b - 1 = α - P.val.2 + δ by dsimp [b]; ring] using hh
  · let E := (x - -R) ^ (-1 - b) + (R - x) ^ (-1 - b) + ∑ y ∈ S, |x - y| ^ (-1 - b)
    have hxl : 0 ≤ x - -R := by linarith [hx.1.1]
    have hxr : 0 ≤ R - x := by linarith [hx.1.2]
    have hps : 0 ≤ ∑ y ∈ S, |x - y| ^ (-1 - b) :=
      Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
    have hE : 0 ≤ E := add_nonneg
      (add_nonneg (Real.rpow_nonneg hxl _) (Real.rpow_nonneg hxr _)) hps
    have hsE : (∑ y ∈ S, |x - y| ^ (-1 - b)) ≤ E := by
      dsimp [E]
      linarith [Real.rpow_nonneg (by linarith [hx.1.1] : 0 ≤ x - -R) (-1 - b),
        Real.rpow_nonneg (by linarith [hx.1.2] : 0 ≤ R - x) (-1 - b)]
    have hconst : 1 ≤ H * E := by
      have hp := Real.rpow_le_rpow_of_nonpos (by linarith [hx.1.1] : 0 < x - -R)
        (by linarith [hx.1.2] : x - -R ≤ 2 * R) (by linarith : -1 - b ≤ 0)
      have hcancel : H * (2 * R) ^ (-1 - b) = 1 := by
        dsimp [H]
        rw [← Real.rpow_add (by positivity : 0 < 2 * R),
          show (1 + b) + (-1 - b) = 0 by ring, Real.rpow_zero]
      calc 1 = H * (2 * R) ^ (-1 - b) := hcancel.symm
        _ ≤ H * (x - -R) ^ (-1 - b) := mul_le_mul_of_nonneg_left hp hH
        _ ≤ H * E := mul_le_mul_of_nonneg_left (by
          dsimp [E]
          linarith [Real.rpow_nonneg hxr (-1 - b)]) hH
    have hterm (j : Fin (p : ℕ)) :
        dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α) ≤ A * E := by
      rw [hdist x hx.1 j]
      have hd : 0 < |x - marks j| := by
        rw [← hdist x hx.1 j]
        exact dist_pos.mpr (hne x hx j)
      have hdR : |x - marks j| ≤ 2 * R :=
        (abs_sub _ _).trans (by linarith [hmarks j, abs_le.mpr ⟨hx.1.1.le, hx.1.2.le⟩])
      rw [show -2 + P.val.2 - α = δ + (-1 - b) by dsimp [b]; ring, Real.rpow_add hd]
      have hp := Real.rpow_le_rpow hd.le hdR hδ.le
      have hsingle : |x - marks j| ^ (-1 - b) ≤ ∑ y ∈ S, |x - y| ^ (-1 - b) :=
        Finset.single_le_sum (fun y _ => Real.rpow_nonneg (abs_nonneg _) _)
          (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      exact mul_le_mul hp (hsingle.trans hsE) (by positivity) hA
    have hsum : (∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α)) ≤
        (A * (p : ℕ)) * E := by
      have hs := Finset.sum_le_sum (s := Finset.univ) fun j _ => hterm j
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_comm, mul_left_comm, mul_assoc] using hs
    have hnear : (if dist (x : Circle L) 0 ≤ 1 then
        ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α) else 0) ≤
        (A * (p : ℕ)) * E := by
      split_ifs
      · exact hsum
      · positivity
    have htail : (if 1 ≤ dist (x : Circle L) 0 then
        dist (x : Circle L) 0 ^ (-3 + P.val.2) else 0) ≤ 1 := by
      split_ifs with hd
      · exact Real.rpow_le_one_of_one_le_of_nonpos hd (by linarith [P.property.2.2])
      · norm_num
    exact (hreg x (hne x hx)).2.trans (by
      change C * _ ≤ C * (H + A * (p : ℕ)) * E
      calc C * _ ≤ C * ((A * (p : ℕ)) * E + 1) :=
            mul_le_mul_of_nonneg_left (add_le_add hnear htail) hC
        _ ≤ C * ((A * (p : ℕ)) * E + H * E) :=
            mul_le_mul_of_nonneg_left (add_le_add le_rfl hconst) hC
        _ = _ := by ring)

end Riesz1.Internal
