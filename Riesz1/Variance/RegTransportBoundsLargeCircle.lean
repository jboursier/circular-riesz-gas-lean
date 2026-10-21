/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegTransportBoundsTails
public import Riesz1.Variance.RegTransportBoundsFixedCircle
public import Riesz1.ToMathlib.CircleTransportUniformInner
public import Riesz1.ToMathlib.IntegrableTwoTails

/-!
# Complete uniform transport estimates on sufficiently large circles

This proves every estimate of Lemma 5.1, with a common
constant chosen before the circle length, for all lengths exceeding a fixed threshold
in the fixed real marked-point data. The remaining range of bounded circle lengths
is not included in this theorem.
-/

public section

open MeasureTheory Set

namespace Riesz1.Internal

/-- All transport bounds, uniformly on sufficiently large observation circles.
The threshold and the bound depend only on fixed profile data. In particular the
pointwise first derivative estimate and its full-period integral have one constant
chosen before the scale. The theorem includes the endpoint by taking `α' > α`. -/
theorem exists_uniform_large_circle_regTransportBounds (P : Parameters)
    (p : Profile) (hp : CompactProfile p) (η B : ℝ)
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hα' : α ≤ α')
    (hα'0 : P.val.2 - 1 < α') (hα'1 : α' < P.val.2 / 2) :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧ ∀ a : Scale,
      L₀ ≤ (observationLength a).val →
      PrimitiveRegularity (observationLength a) η P.val.2 B
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ →
      TransportRegularity P (observationLength a)
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ n marks α C₀ →
      ∃ ψ : Circle (observationLength a) → ℝ, Continuous ψ ∧
        ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
          (∀ k : ℤ, coeff (observationLength a)
            ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
            transportCoeffs P (observationLength a)
              ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) ∧
          LocallyIntegrable (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) volume ∧
          (∀ u v : ℝ, AbsolutelyContinuousOnInterval
            (fun t : ℝ => ψ (t : Circle (observationLength a))) u v) ∧
          (∀ y : Circle (observationLength a), |ψ y| +
            (∫ t in (-(observationLength a).val / 2)..((observationLength a).val / 2),
              |deriv (fun u : ℝ => ψ (u : Circle (observationLength a))) t|) ≤ C) ∧
          (∀ x : ℝ, (∀ j, (x : Circle (observationLength a)) ≠
              (marks j : Circle (observationLength a))) →
            ContDiffAt ℝ 2 (fun t : ℝ => ψ (t : Circle (observationLength a))) x ∧
            |deriv (fun t : ℝ => ψ (t : Circle (observationLength a))) x| ≤ C *
              cappedMarkDistance (fun j => (marks j : Circle (observationLength a)))
                (x : Circle (observationLength a)) ^ (-1 + P.val.2 - α') ∧
            |deriv (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) x| ≤ C *
              cappedMarkDistance (fun j => (marks j : Circle (observationLength a)))
                (x : Circle (observationLength a)) ^ (-2 + P.val.2 - α')) ∧
          ∀ x : ℝ, 1 ≤ |x| → |x| ≤ (observationLength a).val / 2 →
            |deriv (fun t : ℝ => ψ (t : Circle (observationLength a))) x| ≤
              C * |x| ^ (P.val.2 - 2) ∧
            |deriv (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) x| ≤
              C * |x| ^ (P.val.2 - 3) := by
  classical
  obtain ⟨D, hD, hbase⟩ := exists_uniform_compact_transport_sup_secondDeriv_tails
    P p hp η B n marks α α' C₀ hη hB hC₀ hα0 hα1 hα'
  let b := 1 - P.val.2 + α'
  have hb : 0 < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith [P.property.2.1]
  let R := 2 + ∑ j, |marks j|
  have hR : 2 ≤ R := by
    dsimp [R]
    linarith [Finset.sum_nonneg (s := Finset.univ) (fun j _ => abs_nonneg (marks j))]
  have hmarks : ∀ j, |marks j| ≤ R := by
    intro j
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun i => |marks i|) (fun i _ => abs_nonneg (marks i)) (Finset.mem_univ j)
    dsimp [R]
    linarith
  obtain ⟨K, hK, hinner⟩ := CircleSingularity.uniform_inner_deriv_bounds
    hb hb1 hD.le hD.le hR marks hmarks
  let J := K + 2 * (D / (1 - P.val.2) * R ^ (P.val.2 - 1))
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact add_nonneg hK.le (mul_nonneg (by norm_num)
      (mul_nonneg (div_nonneg hD.le (by linarith [P.property.2.2]))
        (Real.rpow_nonneg (by linarith) _)))
  let C := D + K + J + 1
  have hDC : D ≤ C := by dsimp [C]; linarith
  have hKC : K ≤ C := by dsimp [C]; linarith
  refine ⟨C, 4 * R, by dsimp [C]; positivity, by linarith, fun a ha hprim hreg => ?_⟩
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨ψ, hc, hψ, hcoeff, hsup, hi, hAC, hpoint, htail⟩ := hbase a hprim hreg
  have henvelope (x : ℝ) (hx : ∀ j, (x : Circle L) ≠ (marks j : Circle L)) :
      DifferentiableAt ℝ (fun t : ℝ => ψ (t : Circle L)) x ∧
      DifferentiableAt ℝ (deriv (fun t : ℝ => ψ (t : Circle L))) x ∧
      |deriv (deriv (fun t : ℝ => ψ (t : Circle L))) x| ≤ D *
        (1 + ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-1 - b)) := by
    refine ⟨(hpoint x hx).1.differentiableAt (by norm_num),
      ((hpoint x hx).1.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num), ?_⟩
    have hh := (hpoint x hx).2
    rw [show -2 + P.val.2 - α' = -1 - b by dsimp [b]; ring] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (cappedMarkDistance_rpow_le_one_add_sum _ _ _) hD.le)
  obtain ⟨_, hJinner, hqinner⟩ := hinner L.val ha
    (fun t : ℝ => ψ (t : Circle L)) (fun t => hsup (t : Circle L)) henvelope
  have hwhole : IntervalIntegrable (deriv (fun t : ℝ => ψ (t : Circle L))) volume
      (-(L.val / 2)) (L.val / 2) := by
    apply IntegrableOn.intervalIntegrable
    exact hi.integrableOn_isCompact isCompact_uIcc
  have hJwhole := integral_abs_two_tails_le (q := deriv (fun t : ℝ => ψ (t : Circle L)))
    (R := R) (z := L.val / 2) (C := D) (e := P.val.2 - 2)
    (by linarith) (by change 4 * R ≤ L.val at ha; linarith) hD.le
    (by linarith [P.property.2.2]) hwhole hJinner
    (fun t ht htL => (htail t (by linarith) htL).1)
  have hJwhole' : (∫ t in (-L.val / 2)..(L.val / 2),
      |deriv (fun u : ℝ => ψ (u : Circle L)) t|) ≤ J := by
    simpa only [neg_div, J,
      show -(P.val.2 - 2) - 1 = 1 - P.val.2 by ring,
      show P.val.2 - 2 + 1 = P.val.2 - 1 by ring] using hJwhole
  refine ⟨ψ, hc, hψ, hcoeff, hi, hAC, ?_, ?_, ?_⟩
  · intro y
    dsimp [C]
    linarith [hsup y]
  · intro x hx
    refine ⟨(hpoint x hx).1, ?_, (hpoint x hx).2.trans
      (mul_le_mul_of_nonneg_right hDC
        (Real.rpow_nonneg (cappedMarkDistance_pos _ _ hx).le _))⟩
    let y := centralRep L (x : Circle L)
    have hyx : (y : Circle L) = (x : Circle L) := by
      dsimp [y, centralRep]
      exact AddCircle.coe_equivIco
    have hyL : |y| ≤ L.val / 2 := by
      have hh := centralRep_mem_Ico L (x : Circle L)
      exact abs_le.mpr ⟨hh.1, hh.2.le⟩
    have hym : ∀ j, (y : Circle L) ≠ (marks j : Circle L) := by
      simpa only [hyx] using hx
    have hrp := cappedMarkDistance_pos (fun j => (marks j : Circle L)) (y : Circle L) hym
    have hone : 1 ≤ cappedMarkDistance (fun j => (marks j : Circle L)) (y : Circle L) ^ (-b) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hrp
        (cappedMarkDistance_le_one _ _) (by linarith)
    have hq : |deriv (fun t : ℝ => ψ (t : Circle L)) y| ≤
        C * cappedMarkDistance (fun j => (marks j : Circle L)) (y : Circle L) ^ (-b) := by
      by_cases hy : |y| ≤ R / 2
      · exact (hqinner y hy hym).trans (mul_le_mul_of_nonneg_right hKC (by positivity))
      · have hy1 : 1 ≤ |y| := by linarith [lt_of_not_ge hy]
        have ht := (htail y hy1 hyL).1
        have hp := Real.rpow_le_one_of_one_le_of_nonpos hy1
          (by linarith [P.property.2.2] : P.val.2 - 2 ≤ 0)
        have htD : |deriv (fun t : ℝ => ψ (t : Circle L)) y| ≤ D :=
          ht.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hD.le)
        exact htD.trans (hDC.trans (le_mul_of_one_le_right (by dsimp [C]; positivity) hone))
    rw [deriv_circle_lift_eq_of_coe_eq L ψ hyx, hyx,
      show -b = -1 + P.val.2 - α' by dsimp [b]; ring] at hq
    exact hq
  · intro x hx hxL
    exact ⟨((htail x hx hxL).1).trans (mul_le_mul_of_nonneg_right hDC (by positivity)),
      ((htail x hx hxL).2).trans (mul_le_mul_of_nonneg_right hDC (by positivity))⟩

end Riesz1.Internal
