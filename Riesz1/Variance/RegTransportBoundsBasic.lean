/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityUniformBound
public import Riesz1.Kernel.AdmissibilityRegularityAbsoluteContinuity
public import Riesz1.ToMathlib.FiniteMarkDistance

/-!
# Supremum and second derivative bounds for the unsmoothed transport

These are the supremum and `q'` clauses of Lemma 5.1.
The estimate is uniform over circle lengths and includes the endpoint exponent.
The representative has the transport coefficients and is absolutely continuous.
-/

public section

open MeasureTheory Set

namespace Riesz1
namespace Internal

/-- Collapse the (A3) envelope to the capped distance. The premises here are the
pointwise analytic bounds, under a distinct internal name. -/
theorem secondDeriv_le_cappedMarkDistance (P : Parameters) (L : Length)
    (p : ℕ+) (marks : Fin (p : ℕ) → ℝ) (α α' C : ℝ)
    (hα : P.val.2 - 1 ≤ α) (hα' : α ≤ α') (hC : 0 ≤ C)
    (ψ : ℝ → ℝ) (x : ℝ)
    (hx : ∀ j, (x : Circle L) ≠ (marks j : Circle L))
    (hbound : |deriv (deriv ψ) x| ≤ C *
      ((if dist (x : Circle L) 0 ≤ 1 then
          ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α)
        else 0) +
       (if 1 ≤ dist (x : Circle L) 0 then
          dist (x : Circle L) 0 ^ (-3 + P.val.2) else 0))) :
    |deriv (deriv ψ) x| ≤ (C * ((p : ℕ) + 1)) *
      cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^
        (-2 + P.val.2 - α') := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  let r := cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L)
  have hr : 0 < r := cappedMarkDistance_pos _ _ hx
  have hr1 : r ≤ 1 := cappedMarkDistance_le_one _ _
  have he : -2 + P.val.2 - α ≤ 0 := by linarith
  have hp : r ^ (-2 + P.val.2 - α) ≤ r ^ (-2 + P.val.2 - α') :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have hs : (∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α)) ≤
      (p : ℕ) * r ^ (-2 + P.val.2 - α') := by
    have hs := sum_dist_rpow_le_cappedMarkDistance
      (fun j => (marks j : Circle L)) (x : Circle L) hx he
    simp only [Fintype.card_fin] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left hp (by positivity))
  have hnear : (if dist (x : Circle L) 0 ≤ 1 then
      ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α) else 0) ≤
      (p : ℕ) * r ^ (-2 + P.val.2 - α') := by
    split_ifs
    · exact hs
    · positivity
  have hone : 1 ≤ r ^ (-2 + P.val.2 - α') :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
  have htail : (if 1 ≤ dist (x : Circle L) 0 then
      dist (x : Circle L) 0 ^ (-3 + P.val.2) else 0) ≤ r ^ (-2 + P.val.2 - α') := by
    split_ifs with hd
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hd
        (by linarith [P.property.2.2])).trans hone
    · positivity
  exact hbound.trans (by
    calc C * _ ≤ C * ((p : ℕ) * r ^ (-2 + P.val.2 - α') +
          r ^ (-2 + P.val.2 - α')) :=
            mul_le_mul_of_nonneg_left (add_le_add hnear htail) hC
      _ = _ := by ring)

end Internal

/-- Supremum and second-derivative clauses of Lemma 5.1, on one
absolutely continuous representative. The constant precedes every circle and profile.
Taking `α' = α` gives the power in the paper. Taking `α' = α + δ` includes its
endpoint clause. -/
theorem exists_uniform_transport_sup_secondDeriv (P : Parameters)
    (η B : ℝ) (p : ℕ+) (marks : Fin (p : ℕ) → ℝ) (α α' C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hα' : α ≤ α') :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Length)
      (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}),
      PrimitiveRegularity L η P.val.2 B f → TransportRegularity P L f p marks α C₀ →
      ∃ ψ : Circle L → ℝ, Continuous ψ ∧
        ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength L),
          (∀ k : ℤ, coeff L ⟨(fun x => (ψ x : ℂ)), complexL2Integrable L _ hψ⟩ k =
            transportCoeffs P L f k) ∧
          (∀ x, |ψ x| ≤ C) ∧
          LocallyIntegrable (deriv (fun t : ℝ => ψ (t : Circle L))) volume ∧
          (∀ a b : ℝ, AbsolutelyContinuousOnInterval
            (fun t : ℝ => ψ (t : Circle L)) a b) ∧
          ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
            ContDiffAt ℝ 2 (fun t : ℝ => ψ (t : Circle L)) x ∧
            |deriv (deriv (fun t : ℝ => ψ (t : Circle L))) x| ≤ C *
              cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^
                (-2 + P.val.2 - α') := by
  obtain ⟨M, hM, hreg⟩ := exists_uniform_regular_transport P η B hη hB
  let D : ℝ := C₀ * ((p : ℕ) + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨M + D + 1, by positivity, fun L f hprim htransport => ?_⟩
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨ψ, hc, hψ, hcoeff, hsup, hpoint⟩ := hreg L f p marks α C₀ hprim htransport
  have hi := Internal.locallyIntegrable_deriv_of_transport_bound P L marks α C₀
    hα0 hα1 hC₀ _ hpoint
  refine ⟨ψ, hc, hψ, hcoeff, fun x => (hsup x).trans (by linarith), hi, ?_, ?_⟩
  · apply PuncturedDerivative.absolutelyContinuousOnInterval_of_countable_exceptional
      (hc.comp (AddCircle.continuous_mk' L.val))
      (CircleSingularity.countable_marked_lifts (T := L.val) marks) _ hi
    intro x hx
    exact (hpoint x (by simpa only [mem_ofPred_eq, not_exists] using hx)).1.differentiableAt
      (by norm_num)
  · intro x hx
    refine ⟨(hpoint x hx).1, ?_⟩
    exact (Internal.secondDeriv_le_cappedMarkDistance P L p marks α α' C₀
      hα0 hα' hC₀ _ x hx (hpoint x hx).2).trans
      (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith)
        (Real.rpow_nonneg (cappedMarkDistance_pos _ _ hx).le _))

end Riesz1
