/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegTransportBoundsBasic
public import Riesz1.ToMathlib.CircleTransportPointwise

/-!
# Quantitative unsmoothed transport bounds on a fixed circle

This proves every bound of Lemma 5.1 on the macroscopic
unit circle, including the endpoint case with any permitted positive exponent increase.
The internal fixed-length version does not assert uniformity over enlarged circles.
The integral of the absolute derivative over one period is its arclength `L¹` norm.
-/

public section

open MeasureTheory Set

namespace Riesz1
namespace Internal

/-- The derivative of a circle lift is independent of the chosen real representative. -/
theorem deriv_circle_lift_eq_of_coe_eq (L : Length) (ψ : Circle L → ℝ) {x y : ℝ}
    (hxy : (x : Circle L) = (y : Circle L)) :
    deriv (fun t : ℝ => ψ (t : Circle L)) x =
      deriv (fun t : ℝ => ψ (t : Circle L)) y := by
  have heq : (fun t : ℝ => ψ (((x - y) + t : ℝ) : Circle L)) =
      (fun t : ℝ => ψ (t : Circle L)) := by
    funext t
    congr 1
    rw [QuotientAddGroup.mk_add, QuotientAddGroup.mk_sub, hxy, sub_self, zero_add]
  have hd := congrArg (fun f : ℝ → ℝ => deriv f y) heq
  rw [deriv_comp_const_add (f := fun u : ℝ => ψ (u : Circle L)) (a := x - y)] at hd
  simpa only [sub_add_cancel] using hd

/-- Fixed-circle version of the transport bounds. Its constant can depend on `L`.
Uniformity over enlarged circles is not a conclusion of this internal theorem. -/
theorem fixed_circle_regTransportBounds (P : Parameters) (L : Length)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hα' : α ≤ α')
    (hα'0 : P.val.2 - 1 < α')
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (hprim : PrimitiveRegularity L η P.val.2 B f)
    (hreg : TransportRegularity P L f n marks α C₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ ψ : Circle L → ℝ, Continuous ψ ∧
      ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength L),
        (∀ k : ℤ, coeff L ⟨(fun x => (ψ x : ℂ)), complexL2Integrable L _ hψ⟩ k =
          transportCoeffs P L f k) ∧
        LocallyIntegrable (deriv (fun t : ℝ => ψ (t : Circle L))) volume ∧
        (∀ u v : ℝ, AbsolutelyContinuousOnInterval (fun t : ℝ => ψ (t : Circle L)) u v) ∧
        (∀ y : Circle L, |ψ y| +
          (∫ t in (0 : ℝ)..L.val, |deriv (fun u : ℝ => ψ (u : Circle L)) t|) ≤ C) ∧
        ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
          ContDiffAt ℝ 2 (fun t : ℝ => ψ (t : Circle L)) x ∧
          |deriv (fun t : ℝ => ψ (t : Circle L)) x| ≤ C *
            cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^
              (-1 + P.val.2 - α') ∧
          |deriv (deriv (fun t : ℝ => ψ (t : Circle L))) x| ≤ C *
            cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^
              (-2 + P.val.2 - α') := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨D, hD, hbase⟩ := exists_uniform_transport_sup_secondDeriv P η B n marks
    α α' C₀ hη hB hC₀ hα0 hα1 hα'
  obtain ⟨ψ, hc, hψ, hcoeff, hsup, hi, hAC, hpoint⟩ := hbase L f hprim hreg
  let b := 1 - P.val.2 + α'
  have hb : 0 < b := by dsimp [b]; linarith
  have henv : ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
      |deriv (deriv (fun t : ℝ => ψ (t : Circle L))) x| ≤
        D * (1 + ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-1 - b)) := by
    intro x hx
    have he : -2 + P.val.2 - α' = -1 - b := by dsimp [b]; ring
    have hp := (hpoint x hx).2
    rw [he] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left
      (cappedMarkDistance_rpow_le_one_add_sum _ _ _) hD.le)
  obtain ⟨K, hK, hq⟩ := CircleSingularity.exists_abs_le_cappedMarkDistance_on_compact
    L.property hb hD.le (fun j => (marks j : Circle L))
    (deriv (fun t : ℝ => ψ (t : Circle L)))
    (fun x hx => ((hpoint x hx).1.derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)) henv (Icc 0 L.val) isCompact_Icc
  let J := ∫ t in (0 : ℝ)..L.val, |deriv (fun u : ℝ => ψ (u : Circle L)) t|
  let C := D + K + |J| + 1
  have hDC : D ≤ C := by dsimp [C]; linarith [abs_nonneg J]
  have hKC : K ≤ C := by dsimp [C]; linarith [abs_nonneg J]
  refine ⟨C, by dsimp [C]; positivity, ψ, hc, hψ, hcoeff, hi, hAC, ?_, ?_⟩
  · intro y
    change |ψ y| + J ≤ C
    dsimp [C]
    linarith [hsup y, le_abs_self J]
  · intro x hx
    refine ⟨(hpoint x hx).1, ?_, (hpoint x hx).2.trans ?_⟩
    · let y := (AddCircle.equivIco L.val 0 (x : Circle L)).val
      have hy : y ∈ Icc 0 L.val := by
        have hy' := (AddCircle.equivIco L.val 0 (x : Circle L)).property
        exact ⟨hy'.1, by simpa only [zero_add] using hy'.2.le⟩
      have hyx : (y : Circle L) = (x : Circle L) := AddCircle.coe_equivIco
      have hyq := hq y hy (fun j => by simpa only [hyx] using hx j)
      rw [deriv_circle_lift_eq_of_coe_eq L ψ hyx, hyx] at hyq
      have he : -b = -1 + P.val.2 - α' := by dsimp [b]; ring
      rw [he] at hyq
      exact hyq.trans (mul_le_mul_of_nonneg_right hKC
        (Real.rpow_nonneg (cappedMarkDistance_pos _ _ hx).le _))
    · exact mul_le_mul_of_nonneg_right hDC
        (Real.rpow_nonneg (cappedMarkDistance_pos _ _ hx).le _)

end Internal

/-- All unsmoothed transport estimates of Lemma 5.1 for a fixed
macroscopic profile. Set `α' = α` in the strict case, and `α' = α + δ` at the endpoint.
No scale sequence appears in this statement or in the choice of its constant. -/
theorem macroscopic_regTransportBounds (P : Parameters) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hα' : α ≤ α')
    (hα'0 : P.val.2 - 1 < α')
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ ψ : Circle unitLength → ℝ, Continuous ψ ∧
      ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength unitLength),
        (∀ k : ℤ, coeff unitLength
          ⟨(fun x => (ψ x : ℂ)), complexL2Integrable unitLength _ hψ⟩ k =
          transportCoeffs P unitLength ⟨p.val, p.property⟩ k) ∧
        LocallyIntegrable (deriv (fun t : ℝ => ψ (t : Circle unitLength))) volume ∧
        (∀ u v : ℝ, AbsolutelyContinuousOnInterval
          (fun t : ℝ => ψ (t : Circle unitLength)) u v) ∧
        (∀ y : Circle unitLength, |ψ y| +
          (∫ t in (0 : ℝ)..1, |deriv (fun u : ℝ => ψ (u : Circle unitLength)) t|) ≤ C) ∧
        ∀ x : ℝ, (∀ j, (x : Circle unitLength) ≠ (marks j : Circle unitLength)) →
          ContDiffAt ℝ 2 (fun t : ℝ => ψ (t : Circle unitLength)) x ∧
          |deriv (fun t : ℝ => ψ (t : Circle unitLength)) x| ≤ C *
            cappedMarkDistance (fun j => (marks j : Circle unitLength)) (x : Circle unitLength) ^
              (-1 + P.val.2 - α') ∧
          |deriv (deriv (fun t : ℝ => ψ (t : Circle unitLength))) x| ≤ C *
            cappedMarkDistance (fun j => (marks j : Circle unitLength)) (x : Circle unitLength) ^
              (-2 + P.val.2 - α') := by
  exact Internal.fixed_circle_regTransportBounds P unitLength η B n marks α α' C₀
    hη hB hC₀ hα0 hα1 hα' hα'0 ⟨p.val, p.property⟩ hprim hreg

end Riesz1
