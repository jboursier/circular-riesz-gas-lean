/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PuncturedTransportFinite
public import Riesz1.ToMathlib.FiniteMarkDistance
public import Riesz1.ToMathlib.CircleSingularityLocalization

/-!
# Uniform inner estimates on sufficiently large circles

Fixed real marks do not wrap on a fixed bounded interval when the circle is large
enough. The bounded primitive estimate then gives both a first derivative power
envelope and a uniform integral on that interval. This is an analytic helper for
Lemma 5.1.
-/

public section

open MeasureTheory Set

namespace Riesz1.CircleSingularity

/-- The inner first derivative envelope and integral bound, with constants preceding
both the circle length and the primitive. The lower length threshold prevents wrapping
on the bounded region containing the fixed real marks. -/
theorem uniform_inner_deriv_bounds {b C M R : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hR : 2 ≤ R)
    {ι : Type*} [Fintype ι] [Nonempty ι] (marks : ι → ℝ)
    (hmarks : ∀ j, |marks j| ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 4 * R ≤ T → ∀ f : ℝ → ℝ,
      (∀ x, |f x| ≤ M) →
      (∀ x : ℝ, (∀ j, (x : AddCircle T) ≠ (marks j : AddCircle T)) →
        DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ (deriv f) x ∧
        |deriv (deriv f) x| ≤ C *
          (1 + ∑ j, dist (x : AddCircle T) (marks j : AddCircle T) ^ (-1 - b))) →
      IntervalIntegrable (deriv f) volume (-R) R ∧
      (∫ x in (-R)..R, |deriv f x|) ≤ K ∧
      ∀ x : ℝ, |x| ≤ R / 2 → (∀ j, (x : AddCircle T) ≠ (marks j : AddCircle T)) →
        |deriv f x| ≤ K * cappedMarkDistance
          (fun j => (marks j : AddCircle T)) (x : AddCircle T) ^ (-b) := by
  classical
  let S := Finset.univ.image marks
  let H := (2 * R) ^ (1 + b)
  have hRp : 0 < R := by linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  obtain ⟨D, hD, hfinite⟩ := PuncturedDerivative.uniform_deriv_bounds_finite
    hb hb1 hM S (C := C * (H + Fintype.card ι)) (by positivity) (by linarith : -R < R)
  let K := D * (2 + (S.card : ℝ)) + D + 1
  have hDK : D ≤ K := by
    dsimp [K]
    linarith [mul_nonneg hD.le (show 0 ≤ 2 + (S.card : ℝ) by positivity)]
  have hscaled : D * (2 + (S.card : ℝ)) ≤ K := by dsimp [K]; linarith
  refine ⟨K, by dsimp [K]; positivity, fun T hT f hf hreg => ?_⟩
  have hTp : 0 < T := by linarith
  have : Fact (0 < T) := ⟨hTp⟩
  have hdist (x : ℝ) (hx : x ∈ Ioo (-R) R) (j : ι) :
      dist (x : AddCircle T) (marks j : AddCircle T) = |x - marks j| := by
    apply dist_coe_eq_abs_sub hTp
    exact (abs_sub _ _).trans ((add_le_add
      (abs_le.mpr ⟨hx.1.le, hx.2.le⟩) (hmarks j)).trans (by linarith))
  have hne (x : ℝ) (hx : x ∈ Ioo (-R) R \ (S : Set ℝ)) :
      ∀ j, (x : AddCircle T) ≠ (marks j : AddCircle T) := by
    intro j he
    have hz : |x - marks j| = 0 := by rw [← hdist x hx.1 j, he, dist_self]
    apply hx.2
    simp only [S, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨j, (sub_eq_zero.mp (abs_eq_zero.mp hz)).symm⟩
  have henv (x : ℝ) (hx : x ∈ Ioo (-R) R \ (S : Set ℝ)) :
      |deriv (deriv f) x| ≤ C * (H + Fintype.card ι) *
        ((x - -R) ^ (-1 - b) + (R - x) ^ (-1 - b) +
          ∑ y ∈ S, |x - y| ^ (-1 - b)) := by
    let E := (x - -R) ^ (-1 - b) + (R - x) ^ (-1 - b) +
      ∑ y ∈ S, |x - y| ^ (-1 - b)
    have hs : 0 ≤ ∑ y ∈ S, |x - y| ^ (-1 - b) :=
      Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
    have hl : 0 ≤ (x - -R) ^ (-1 - b) := Real.rpow_nonneg (by linarith [hx.1.1]) _
    have hr : 0 ≤ (R - x) ^ (-1 - b) := Real.rpow_nonneg (by linarith [hx.1.2]) _
    have hconst : 1 ≤ H * E := by
      have hp := Real.rpow_le_rpow_of_nonpos (by linarith [hx.1.1] : 0 < x - -R)
        (by linarith [hx.1.2] : x - -R ≤ 2 * R) (by linarith : -1 - b ≤ 0)
      have hcancel : H * (2 * R) ^ (-1 - b) = 1 := by
        dsimp [H]
        rw [← Real.rpow_add (by positivity : 0 < 2 * R),
          show (1 + b) + (-1 - b) = 0 by ring, Real.rpow_zero]
      calc 1 = H * (2 * R) ^ (-1 - b) := hcancel.symm
        _ ≤ H * (x - -R) ^ (-1 - b) := mul_le_mul_of_nonneg_left hp hH
        _ ≤ H * E := mul_le_mul_of_nonneg_left (by dsimp [E]; linarith) hH
    have hterm (j : ι) : dist (x : AddCircle T) (marks j : AddCircle T) ^ (-1 - b) ≤ E := by
      rw [hdist x hx.1 j]
      have hh := Finset.single_le_sum (f := fun y => |x - y| ^ (-1 - b))
        (fun y _ => Real.rpow_nonneg (abs_nonneg _) _)
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩ : marks j ∈ S)
      dsimp [E]
      linarith
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun j _ => hterm j
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    exact (hreg x (hne x hx)).2.2.trans (by
      change C * _ ≤ C * (H + Fintype.card ι) * E
      calc C * _ ≤ C * (H * E + (Fintype.card ι : ℝ) * E) :=
          mul_le_mul_of_nonneg_left (add_le_add hconst hsum) hC
        _ = _ := by ring)
  obtain ⟨hp, hi, hj⟩ := hfinite f (fun x hx => (hreg x (hne x hx)).1)
    (fun x hx => (hreg x (hne x hx)).2.1) (fun x _ => hf x) henv
  refine ⟨hi, hj.trans hDK, fun x hx hxm => ?_⟩
  have hxI : x ∈ Ioo (-R) R := by
    have hh := abs_le.mp hx
    constructor <;> linarith [hh.1, hh.2]
  have hxS : x ∉ (S : Set ℝ) := by
    simp only [S, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro j he
    exact hxm j (by rw [he])
  let r := cappedMarkDistance (fun j => (marks j : AddCircle T)) (x : AddCircle T)
  have hrp : 0 < r := cappedMarkDistance_pos _ _ hxm
  have hr1 : r ≤ 1 := cappedMarkDistance_le_one _ _
  have hone : 1 ≤ r ^ (-b) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hrp hr1 (by linarith)
  have hpl : (x - -R) ^ (-b) ≤ r ^ (-b) := by
    apply le_trans _ hone
    exact Real.rpow_le_one_of_one_le_of_nonpos (by
      have hh := abs_le.mp hx
      linarith [hh.1]) (by linarith)
  have hpr : (R - x) ^ (-b) ≤ r ^ (-b) := by
    apply le_trans _ hone
    exact Real.rpow_le_one_of_one_le_of_nonpos (by
      have hh := abs_le.mp hx
      linarith [hh.2]) (by linarith)
  have hps : (∑ y ∈ S, |x - y| ^ (-b)) ≤ (S.card : ℝ) * r ^ (-b) := by
    calc _ ≤ ∑ _y ∈ S, r ^ (-b) := by
          apply Finset.sum_le_sum
          intro y hy
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
          apply Real.rpow_le_rpow_of_nonpos hrp
          rw [← hdist x hxI j]
          exact cappedMarkDistance_le_dist _ _ j
          linarith
      _ = _ := by simp
  have he := hp x ⟨hxI, hxS⟩
  apply he.trans
  calc D * _ ≤ (D * (2 + (S.card : ℝ))) * r ^ (-b) := by
        nlinarith [mul_le_mul_of_nonneg_left hpl hD.le,
          mul_le_mul_of_nonneg_left hpr hD.le, mul_le_mul_of_nonneg_left hps hD.le]
    _ ≤ K * r ^ (-b) := mul_le_mul_of_nonneg_right hscaled (Real.rpow_nonneg hrp.le _)

end Riesz1.CircleSingularity
